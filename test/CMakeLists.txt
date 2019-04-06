set(test_src_files
  test.c
  testaig.c
  testaigvec.c
  testarithmetic.c
  testboolectornodemap.c
  testbv.c
  testcomp.c
  testexp.c
  testhash.c
  testinc.c
  testinthash.c
  testinthashmap.c
  testlambda.c
  testlogic.c
  testmap.c
  testmc.c
  testmem.c
  testmisc.c
  testmodelgen.c
  testmodelgensmt2.c
  testnormquant.c
  testoverflow.c
  testparseerror.c
  testprop.c
  testpropinv.c
  testqueue.c
  testrunner.c
  testsat.c
  testshift.c
  testsmtaxioms.c
  testsort.c
  testspecial.c
  teststack.c
  testtestcases.c
  testutil.c
)

add_executable (testbtor ${test_src_files})
target_link_libraries(testbtor boolector m)
set_target_properties(testbtor PROPERTIES OUTPUT_NAME test)
