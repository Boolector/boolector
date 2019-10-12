set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

set(test_names
  aig
  aigvec
  arithmetic
  boolectornodemap
  bv
  comp
  #testexp.c
  #testhash.c
  #testinc.c
  #testinthash.c
  #testinthashmap.c
  #testlambda.c
  #testlogic.c
  #testmap.c
  #testmc.c
  #testmem.c
  #testmisc.c
  #testmodelgen.c
  #testmodelgensmt2.c
  #testnormquant.c
  #testoverflow.c
  #testparseerror.c
  #testprop.c
  #testpropinv.c
  #testqueue.c
  #testrunner.c
  #testsat.c
  #testshift.c
  #testsmtaxioms.c
  #testsort.c
  #testspecial.c
  #teststack.c
  #testtestcases.c
  #testunionfind.c
  #testutil.c
)

foreach(test ${test_names})
  add_executable (test${test} test_${test}.cpp)
  target_include_directories(test${test} PRIVATE ${PROJECT_SOURCE_DIR}/test/new_test)
  target_link_libraries(test${test} boolector m)
  target_link_libraries(test${test} gtest_main)
  set_target_properties(test${test} PROPERTIES OUTPUT_NAME test${test})
  add_test(${test} ${CMAKE_BINARY_DIR}/bin/tests/test${test})
endforeach()
