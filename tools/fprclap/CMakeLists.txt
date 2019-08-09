add_executable(fprclap
  main.cpp
)

set(KLEE_LIBS kleeCore)

target_link_libraries(fprclap ${KLEE_LIBS})

install(TARGETS fprclap RUNTIME DESTINATION bin)
# The KLEE binary depends on the runtimes
add_dependencies(fprclap BuildKLEERuntimes)
