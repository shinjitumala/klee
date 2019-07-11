add_executable(fpr-clap
  main.cpp
)

set(KLEE_LIBS kleeCore)

target_link_libraries(fpr-clap ${KLEE_LIBS})

install(TARGETS fpr-clap RUNTIME DESTINATION bin)
# The KLEE binary depends on the runtimes
add_dependencies(klee BuildKLEERuntimes)
