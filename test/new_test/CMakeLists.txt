set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

set(test_names
  aig
  aigvec
  arithmetic
  boolectornodemap
  bv
  comp
  exp
  hash
  inc
  inthash
  inthashmap
  lambda
  logic
  mc
  mem
  misc
  modelgen
  modelgensmt2
  nodemap
  normquant
  overflow
  parseerror
  prop
  propinv
  queue
  satmgr
  shift
  #testsmtaxioms.c
  sort
  special
  stack
  #testtestcases.c
  unionfind
  util
)

foreach(test ${test_names})
  add_executable (test${test} test_${test}.cpp)
  target_include_directories(test${test} PRIVATE ${PROJECT_SOURCE_DIR}/test/new_test)
  target_link_libraries(test${test} boolector m)
  target_link_libraries(test${test} gtest_main)
  set_target_properties(test${test} PROPERTIES OUTPUT_NAME test${test})
  add_test(${test} ${CMAKE_BINARY_DIR}/bin/tests/test${test})
endforeach()
