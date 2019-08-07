/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/Version.h"
#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FileHandling.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/System/Time.h"
#include "klee/Interpreter.h"
#include "klee/OptionCategories.h"
#include "klee/SolverCmdLine.h"
#include "klee/Statistics.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(4, 0)
#include <llvm/Bitcode/BitcodeReader.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>

#include <cerrno>
#include <ctime>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <sstream>


using namespace llvm;
using namespace klee;

namespace {
cl::opt<std::string>
InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));

cl::list<std::string>
InputArgv(cl::ConsumeAfter,
          cl::desc("<program arguments>..."));


/*** Startup options ***/

cl::OptionCategory StartCat("Startup options",
                            "These options affect how execution is started.");

cl::opt<std::string>
EntryPoint("entry-point",
           cl::desc("Function in which to start execution (default=main)"),
           cl::init("main"),
           cl::cat(StartCat));

cl::opt<std::string>
RunInDir("run-in-dir",
         cl::desc("Change to the given directory before starting execution (default=location of tested file)."),
         cl::cat(StartCat));

cl::opt<std::string>
OutputDir("output-dir",
          cl::desc("Directory in which to write results (default=klee-out-<N>)"),
          cl::init(""),
          cl::cat(StartCat));

/*** Replaying options ***/

cl::OptionCategory ReplayCat("Replaying options",
                             "These options impact replaying of test cases.");

cl::opt<bool>
ReplayKeepSymbolic("replay-keep-symbolic",
                   cl::desc("Replay the test cases only by asserting "
                            "the bytes, not necessarily making them concrete."),
                   cl::cat(ReplayCat));

cl::list<std::string>
ReplayKTestFile("replay-ktest-file",
                cl::desc("Specify a ktest file to use for replay"),
                cl::value_desc("ktest file"),
                cl::cat(ReplayCat));

cl::list<std::string>
ReplayKTestDir("replay-ktest-dir",
               cl::desc("Specify a directory to replay ktest files from"),
               cl::value_desc("output directory"),
               cl::cat(ReplayCat));

cl::opt<std::string>
ReplayPathFile("replay-path",
               cl::desc("Specify a path file to replay"),
               cl::value_desc("path file"),
               cl::cat(ReplayCat));
}

namespace klee {
extern cl::opt<std::string> MaxTime;
}

/***/

class KleeHandler : public InterpreterHandler {
private:
Interpreter *m_interpreter;
TreeStreamWriter *m_pathWriter, *m_symPathWriter;
std::unique_ptr<llvm::raw_ostream> m_infoFile;

// FPR: 出力用のostream
std::unique_ptr<llvm::raw_ostream> fprclap_path_os;
std::unique_ptr<llvm::raw_ostream> fprclap_rw_os;
std::unique_ptr<llvm::raw_ostream> fprclap_o_os;

SmallString<128> m_outputDirectory;

unsigned m_numTotalTests;           // Number of tests received from the interpreter
unsigned m_numGeneratedTests;       // Number of tests successfully generated
unsigned m_pathsExplored;       // number of paths explored so far

// used for writing .ktest files
int m_argc;
char **m_argv;

public:
KleeHandler(int argc, char **argv);
~KleeHandler();

llvm::raw_ostream &getInfoStream() const {
	return *m_infoFile;
}

// FPR: 開かれているostreamの取得
llvm::raw_ostream &fprclap_path() const {return *fprclap_path_os;}
llvm::raw_ostream &fprclap_rw() const {return *fprclap_rw_os;}
llvm::raw_ostream &fprclap_o() const {return *fprclap_o_os;}

/// Returns the number of test cases successfully generated so far
unsigned getNumTestCases() {
	return m_numGeneratedTests;
}
unsigned getNumPathsExplored() {
	return m_pathsExplored;
}
void incPathsExplored() {
	m_pathsExplored++;
}

void setInterpreter(Interpreter *i);

void processTestCase(const ExecutionState  &state,
                     const char *errorMessage,
                     const char *errorSuffix){
	// do nothing
};

std::string getOutputFilename(const std::string &filename);
std::unique_ptr<llvm::raw_fd_ostream> openOutputFile(const std::string &filename);
std::string getTestFilename(const std::string &suffix, unsigned id);
std::unique_ptr<llvm::raw_fd_ostream> openTestFile(const std::string &suffix, unsigned id);

// load a .path file
static void loadPathFile(std::string name,
                         std::vector<bool> &buffer);

static void getKTestFilesInDir(std::string directoryPath,
                               std::vector<std::string> &results);

static std::string getRunTimeLibraryPath(const char *argv0);
};

/**
   KleeHandlerのコンストラクタ
    出力先のファイル管理しかしていない
 */
KleeHandler::KleeHandler(int argc, char **argv)
	: m_interpreter(0), m_pathWriter(0), m_symPathWriter(0),
	m_outputDirectory(), m_numTotalTests(0), m_numGeneratedTests(0),
	m_pathsExplored(0), m_argc(argc), m_argv(argv) {

	/**
	   ファイルの出力先を管理(ここから下全て)
	 */
	bool dir_given = OutputDir != "";
	SmallString<128> directory(dir_given ? OutputDir : InputFile);

	if (!dir_given) sys::path::remove_filename(directory);
	if (auto ec = sys::fs::make_absolute(directory)) {
		klee_error("unable to determine absolute path: %s", ec.message().c_str());
	}

	if (dir_given) {
		// OutputDir
		if (mkdir(directory.c_str(), 0775) < 0)
			klee_error("cannot create \"%s\": %s", directory.c_str(), strerror(errno));

		m_outputDirectory = directory;
	} else {
		// "klee-out-<i>"
		int i = 0;
		for (; i <= INT_MAX; ++i) {
			SmallString<128> d(directory);
			llvm::sys::path::append(d, "klee-out-");
			raw_svector_ostream ds(d);
			ds << i;
			// SmallString is always up-to-date, no need to flush. See Support/raw_ostream.h

			// create directory and try to link klee-last
			if (mkdir(d.c_str(), 0775) == 0) {
				m_outputDirectory = d;

				SmallString<128> klee_last(directory);
				llvm::sys::path::append(klee_last, "klee-last");

				if (((unlink(klee_last.c_str()) < 0) && (errno != ENOENT)) ||
				    symlink(m_outputDirectory.c_str(), klee_last.c_str()) < 0) {

					klee_warning("cannot create klee-last symlink: %s", strerror(errno));
				}

				break;
			}

			// otherwise try again or exit on error
			if (errno != EEXIST)
				klee_error("cannot create \"%s\": %s", m_outputDirectory.c_str(), strerror(errno));
		}
		if (i == INT_MAX && m_outputDirectory.str().equals(""))
			klee_error("cannot create output directory: index out of range");
	}

	// klee_message("output directory is \"%s\"", m_outputDirectory.c_str());

	// open warnings.txt
	std::string file_path = getOutputFilename("warnings.txt");
	if ((klee_warning_file = fopen(file_path.c_str(), "w")) == NULL)
		klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

	// open messages.txt
	file_path = getOutputFilename("messages.txt");
	if ((klee_message_file = fopen(file_path.c_str(), "w")) == NULL)
		klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

	// open info
	m_infoFile = openOutputFile("info");

	// FPR
	fprclap_path_os = openOutputFile("fprclap_path.const");
	fprclap_rw_os = openOutputFile("fprclap_rw.const");
	fprclap_o_os = openOutputFile("fprclap_o.const");
}

/**
   デストラクタ
 */
KleeHandler::~KleeHandler() {
	delete m_pathWriter;
	delete m_symPathWriter;
	fclose(klee_warning_file);
	fclose(klee_message_file);
}

/**
   Interpreterというのは、LLVM中間言語を実行する仮想マシン（だと思う）
 */
void KleeHandler::setInterpreter(Interpreter *i) {
	m_interpreter = i;
}

/**
   出力先を取得するための便利関数
 */
std::string KleeHandler::getOutputFilename(const std::string &filename) {
	SmallString<128> path = m_outputDirectory;
	sys::path::append(path,filename);
	return path.str();
}

/**
   出力ファイルのファイルディスクリプタを取得するための便利関数。
 */
std::unique_ptr<llvm::raw_fd_ostream>
KleeHandler::openOutputFile(const std::string &filename) {
	std::string Error;
	std::string path = getOutputFilename(filename);
	auto f = klee_open_output_file(path, Error);
	if (!f) {
		klee_warning("error opening file \"%s\".  KLEE may have run out of file "
		             "descriptors: try to increase the maximum number of open file "
		             "descriptors by using ulimit (%s).",
		             path.c_str(), Error.c_str());
		return nullptr;
	}
	return f;
}

// load a .path file
void KleeHandler::loadPathFile(std::string name,
                               std::vector<bool> &buffer) {
	std::ifstream f(name.c_str(), std::ios::in | std::ios::binary);

	if (!f.good())
		llvm::errs() << "FPRCLAP: WARNING: Missing replay file: " << name << "\n";

	while (f.good()) {
		unsigned value;
		f >> value;
		buffer.push_back(!!value);
		f.get();
	}

}

std::string KleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env)
    return std::string(env);

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(
      llvm::sys::fs::getMainExecutable(argv0, MainExecAddr)
      );

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);

  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR ))
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,
               toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  }
  else
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                       libDir.c_str() << "\n");
  return libDir.str();
}

//===----------------------------------------------------------------------===//
// main Driver function
//
static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  // This version always reads response files
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

// This is a terrible hack until we get some real modeling of the
// system. All we do is check the undefined symbols and warn about
// any "unrecognized" externals and about any obviously unsafe ones.

// Symbols we explicitly support
static const char *modelledExternals[] = {
	"_ZTVN10__cxxabiv117__class_type_infoE",
	"_ZTVN10__cxxabiv120__si_class_type_infoE",
	"_ZTVN10__cxxabiv121__vmi_class_type_infoE",

	// special functions
	"_assert",
	"__assert_fail",
	"__assert_rtn",
	"__errno_location",
	"__error",
	"calloc",
	"_exit",
	"exit",
	"free",
	"abort",
	"klee_abort",
	"klee_assume",
	"klee_check_memory_access",
	"klee_define_fixed_object",
	"klee_get_errno",
	"klee_get_valuef",
	"klee_get_valued",
	"klee_get_valuel",
	"klee_get_valuell",
	"klee_get_value_i32",
	"klee_get_value_i64",
	"klee_get_obj_size",
	"klee_is_symbolic",
	"klee_make_symbolic",
	"klee_mark_global",
	"klee_open_merge",
	"klee_close_merge",
	"klee_prefer_cex",
	"klee_posix_prefer_cex",
	"klee_print_expr",
	"klee_print_range",
	"klee_report_error",
	"klee_set_forking",
	"klee_silent_exit",
	"klee_warning",
	"klee_warning_once",
	"klee_stack_trace",
	"llvm.dbg.declare",
	"llvm.dbg.value",
	"llvm.va_start",
	"llvm.va_end",
	"malloc",
	"realloc",
	"memalign",
	"_ZdaPv",
	"_ZdlPv",
	"_Znaj",
	"_Znwj",
	"_Znam",
	"_Znwm",
	"__ubsan_handle_add_overflow",
	"__ubsan_handle_sub_overflow",
	"__ubsan_handle_mul_overflow",
	"__ubsan_handle_divrem_overflow",
};

// Symbols we aren't going to warn about
static const char *dontCareExternals[] = {

	// static information, pretty ok to return
	"getegid",
	"geteuid",
	"getgid",
	"getuid",
	"getpid",
	"gethostname",
	"getpgrp",
	"getppid",
	"getpagesize",
	"getpriority",
	"getgroups",
	"getdtablesize",
	"getrlimit",
	"getrlimit64",
	"getcwd",
	"getwd",
	"gettimeofday",
	"uname",

	// fp stuff we just don't worry about yet
	"frexp",
	"ldexp",
	"__isnan",
	"__signbit",

	// FPR suppress warnings
	"pthread_create",
	"pthread_join",
};

// Symbols we consider unsafe
static const char *unsafeExternals[] = {
	"fork", // oh lord
	"exec", // heaven help us
	"error", // calls _exit
	"raise", // yeah
	"kill", // mmmhmmm
};

#define NELEMS(array) (sizeof(array)/sizeof(array[0]))
void externalsAndGlobalsCheck(const llvm::Module *m) {
	std::map<std::string, bool> externals;
	std::set<std::string> modelled(modelledExternals,
	                               modelledExternals+NELEMS(modelledExternals));
	std::set<std::string> dontCare(dontCareExternals,
	                               dontCareExternals+NELEMS(dontCareExternals));
	std::set<std::string> unsafe(unsafeExternals,
	                             unsafeExternals+NELEMS(unsafeExternals));

	for (Module::const_iterator fnIt = m->begin(), fn_ie = m->end();
	     fnIt != fn_ie; ++fnIt) {
		if (fnIt->isDeclaration() && !fnIt->use_empty())
			externals.insert(std::make_pair(fnIt->getName(), false));
		for (Function::const_iterator bbIt = fnIt->begin(), bb_ie = fnIt->end();
		     bbIt != bb_ie; ++bbIt) {
			for (BasicBlock::const_iterator it = bbIt->begin(), ie = bbIt->end();
			     it != ie; ++it) {
				if (const CallInst *ci = dyn_cast<CallInst>(it)) {
					if (isa<InlineAsm>(ci->getCalledValue())) {
						klee_warning_once(&*fnIt,
						                  "function \"%s\" has inline asm",
						                  fnIt->getName().data());
					}
				}
			}
		}
	}

	for (Module::const_global_iterator
	     it = m->global_begin(), ie = m->global_end();
	     it != ie; ++it)
		if (it->isDeclaration() && !it->use_empty())
			externals.insert(std::make_pair(it->getName(), true));
	// and remove aliases (they define the symbol after global
	// initialization)
	for (Module::const_alias_iterator
	     it = m->alias_begin(), ie = m->alias_end();
	     it != ie; ++it) {
		std::map<std::string, bool>::iterator it2 =
			externals.find(it->getName());
		if (it2!=externals.end())
			externals.erase(it2);
	}

	std::map<std::string, bool> foundUnsafe;
	for (std::map<std::string, bool>::iterator
	     it = externals.begin(), ie = externals.end();
	     it != ie; ++it) {
		const std::string &ext = it->first;
		if (!modelled.count(ext) && (!dontCare.count(ext))) {
			if (unsafe.count(ext)) {
				foundUnsafe.insert(*it);
			} else {
				klee_warning("undefined reference to %s: %s",
				             it->second ? "variable" : "function",
				             ext.c_str());
			}
		}
	}

	for (std::map<std::string, bool>::iterator
	     it = foundUnsafe.begin(), ie = foundUnsafe.end();
	     it != ie; ++it) {
		const std::string &ext = it->first;
		klee_warning("undefined reference to %s: %s (UNSAFE)!",
		             it->second ? "variable" : "function",
		             ext.c_str());
	}
}

static Interpreter *theInterpreter = 0;

static bool interrupted = false;

// Pulled out so it can be easily called from a debugger.
extern "C"
void halt_execution() {
	theInterpreter->setHaltExecution(true);
}

extern "C"
void stop_forking() {
	theInterpreter->setInhibitForking(true);
}

static void interrupt_handle() {
	if (!interrupted && theInterpreter) {
		llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
		halt_execution();
		sys::SetInterruptFunction(interrupt_handle);
	} else {
		llvm::errs() << "KLEE: ctrl-c detected, exiting.\n";
		exit(1);
	}
	interrupted = true;
}

int main(int argc, char **argv, char **envp) {
	KCommandLine::HideOptions(llvm::cl::GeneralCategory);

	// LLVM初期化
	llvm::InitializeNativeTarget();

	// 引数の処理
	parseArguments(argc, argv);
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 9)
	sys::PrintStackTraceOnErrorSignal(argv[0]);
#else
	sys::PrintStackTraceOnErrorSignal();
#endif

	// SIGINTが来たときのコールバック関数を設定
	sys::SetInterruptFunction(interrupt_handle);

	// バイトコード読み込み
	std::string errorMsg;
	LLVMContext ctx;
	std::vector<std::unique_ptr<llvm::Module> > loadedModules;
	if (!klee::loadFile(InputFile, ctx, loadedModules, errorMsg)) {
        printf("Warning: Load file error: module\n");
		//klee_error("error loading program '%s': %s", InputFile.c_str(),
		  //         errorMsg.c_str());
	}
	// Load and link the whole files content. The assumption is that this is the
	// application under test.
	// Nothing gets removed in the first place.
	std::unique_ptr<llvm::Module> M(klee::linkModules(
						loadedModules, "" /* link all modules together */, errorMsg));
	if (!M) {
		klee_error("error loading program '%s': %s", InputFile.c_str(),
		           errorMsg.c_str());
	}
	// Push the module as the first entry
	loadedModules.emplace_back(std::move(M));

	// インタープリタの設定
	Interpreter::ModuleOptions Opts(KleeHandler::getRunTimeLibraryPath("klee"), EntryPoint,
	                                /*Optimize=*/ false,
	                                /*CheckDivZero=*/ false,
	                                /*CheckOvershift=*/ false);


	// 環境の生成
	int pArgc;
	char **pArgv;
	char **pEnvp;
	pEnvp = envp;

	// 実行のための引数を設定
	pArgc = InputArgv.size() + 1;
	pArgv = new char *[pArgc];
	for (unsigned i=0; i<InputArgv.size()+1; i++) {
		std::string &arg = (i==0 ? InputFile : InputArgv[i-1]);
		unsigned size = arg.size() + 1;
		char *pArg = new char[size];

		std::copy(arg.begin(), arg.end(), pArg);
		pArg[size - 1] = 0;

		pArgv[i] = pArg;
	}

	std::vector<bool> replayPath;

	//  実行再現するパスを指定するファイルのロード
	if (ReplayPathFile != "") {
		KleeHandler::loadPathFile(ReplayPathFile, replayPath);
	}

	Interpreter::InterpreterOptions IOpts;
	IOpts.MakeConcreteSymbolic = true;
	KleeHandler *handler = new KleeHandler(pArgc, pArgv);
	Interpreter *interpreter =
		theInterpreter = Interpreter::create(ctx, IOpts, handler);
	assert(interpreter);
	// FPR パスファイルの場所をExecutorに持たせる
	handler->replay_file = ReplayPathFile;
	handler->setInterpreter(interpreter);

	for (int i=0; i<argc; i++) {
		handler->getInfoStream() << argv[i] << (i+1<argc ? " " : "\n");
	}
	handler->getInfoStream() << "PID: " << getpid() << "\n";

	// Get the desired main function.  klee_main initializes uClibc
	// locale and other data and then calls main.

	auto finalModule = interpreter->setModule(loadedModules, Opts);
	Function *mainFn = finalModule->getFunction(EntryPoint);
	if (!mainFn) {
		klee_error("Entry function '%s' not found in module.", EntryPoint.c_str());
	}

	externalsAndGlobalsCheck(finalModule);

	if (ReplayPathFile != "") {
		interpreter->setReplayPath(&replayPath);
	}


	auto startTime = std::time(nullptr);
	{ // output clock info and start time
		std::stringstream startInfo;
		startInfo << time::getClockInfo()
		          << "Started: "
		          << std::put_time(std::localtime(&startTime), "%Y-%m-%d %H:%M:%S") << '\n';
		handler->getInfoStream() << startInfo.str();
		handler->getInfoStream().flush();
	}



	if (RunInDir != "") {
		int res = chdir(RunInDir.c_str());
		if (res < 0) {
			klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
			           sys::StrError(errno).c_str());
		}
	}


	interpreter->runFunctionAsMain(mainFn, pArgc, pArgv, pEnvp);


	auto endTime = std::time(nullptr);
	{ // output end and elapsed time
		std::uint32_t h;
		std::uint8_t m, s;
		std::tie(h,m,s) = time::seconds(endTime - startTime).toHMS();
		std::stringstream endInfo;
		endInfo << "Finished: "
		        << std::put_time(std::localtime(&endTime), "%Y-%m-%d %H:%M:%S") << '\n'
		        << "Elapsed: "
		        << std::setfill('0') << std::setw(2) << h
		        << ':'
		        << std::setfill('0') << std::setw(2) << +m
		        << ':'
		        << std::setfill('0') << std::setw(2) << +s
		        << '\n';
		handler->getInfoStream() << endInfo.str();
		handler->getInfoStream().flush();
	}

	delete handler;

	return 0;
}
