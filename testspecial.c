#include "btorexit.h"
#include "btormain.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdlib.h>
#include <string.h>

void
init_special_tests (void)
{
}

static void
run_test (char *name, int expected)
{
  int argc        = 3;
  char *full_name = (char *) malloc (sizeof (char) * (strlen (name) + 4 + 1));
  strcpy (full_name, "log/");
  strcat (full_name, name);
  char *argv[] = {"./boolector", "-q", full_name};
  assert (btor_main (argc, argv) == expected);
  free (full_name);
}

static void
run_sat_test (char *name)
{
  run_test (name, BTOR_SAT_EXIT);
}

static void
run_unsat_test (char *name)
{
  run_test (name, BTOR_UNSAT_EXIT);
}

static void
test_const1_special ()
{
  run_sat_test ("const1.btor");
}

static void
test_const2_special ()
{
  run_unsat_test ("const2.btor");
}

static void
test_var1_special ()
{
  run_sat_test ("var1.btor");
}

static void
test_var2_special ()
{
  run_sat_test ("var2.btor");
}

static void
test_rw1_special ()
{
  run_sat_test ("rw1.btor");
}

static void
test_rw2_special ()
{
  run_sat_test ("rw2.btor");
}

static void
test_rw3_special ()
{
  run_sat_test ("rw3.btor");
}

static void
test_rw4_special ()
{
  run_sat_test ("rw4.btor");
}

static void
test_rw5_special ()
{
  run_sat_test ("rw5.btor");
}

static void
test_rw6_special ()
{
  run_sat_test ("rw6.btor");
}

static void
test_rw7_special ()
{
  run_sat_test ("rw7.btor");
}

static void
test_rw8_special ()
{
  run_sat_test ("rw8.btor");
}

static void
test_rw9_special ()
{
  run_sat_test ("rw9.btor");
}

static void
test_rw10_special ()
{
  run_sat_test ("rw10.btor");
}

static void
test_rw11_special ()
{
  run_sat_test ("rw11.btor");
}

static void
test_rw12_special ()
{
  run_sat_test ("rw12.btor");
}

static void
test_rw13_special ()
{
  run_sat_test ("rw13.btor");
}

static void
test_rw14_special ()
{
  run_sat_test ("rw14.btor");
}

static void
test_rw15_special ()
{
  run_sat_test ("rw15.btor");
}

static void
test_sqrt4_special ()
{
  run_sat_test ("sqrt4.btor");
}

static void
test_sqrt5_special ()
{
  run_unsat_test ("sqrt5.btor");
}

static void
test_sqrt7_special ()
{
  run_unsat_test ("sqrt7.btor");
}

static void
test_sqrt9_special ()
{
  run_sat_test ("sqrt9.btor");
}

static void
test_sqrt13_special ()
{
  run_unsat_test ("sqrt13.btor");
}

static void
test_sqrt25_special ()
{
  run_sat_test ("sqrt25.btor");
}

static void
test_sqrt29_special ()
{
  run_unsat_test ("sqrt29.btor");
}

static void
test_sqrt31_special ()
{
  run_unsat_test ("sqrt31.btor");
}

static void
test_sqrt49_special ()
{
  run_sat_test ("sqrt49.btor");
}

static void
test_sqrt53_special ()
{
  run_unsat_test ("sqrt53.btor");
}

static void
test_sqrt65537_special ()
{
  run_unsat_test ("sqrt65537.btor");
}

static void
test_sqrt4294967297_special ()
{
  run_unsat_test ("sqrt4294967297.btor");
}

static void
test_sqrt4295098369_special ()
{
  run_sat_test ("sqrt4295098369.btor");
}

static void
test_sqrt18446744073709551617_special ()
{
  run_unsat_test ("sqrt18446744073709551617.btor");
}

static void
test_factor2209_special ()
{
  run_sat_test ("factor2209.btor");
}

static void
test_factor4294967295_special ()
{
  run_sat_test ("factor4294967295.btor");
}

static void
test_factor4294967297_special ()
{
  run_sat_test ("factor4294967297.btor");
}

static void
test_factor18446744073709551617const_special ()
{
  run_sat_test ("factor18446744073709551617const.btor");
}

static void
test_factor18446744073709551617xconst_special ()
{
  run_sat_test ("factor18446744073709551617xconst.btor");
}

static void
test_factor18446744073709551617yconst_special ()
{
  run_sat_test ("factor18446744073709551617yconst.btor");
}

static void
test_factor18446744073709551617reduced_special ()
{
  run_sat_test ("factor18446744073709551617reduced.btor");
}

static void
test_factor18446744073709551617_special ()
{
  run_sat_test ("factor18446744073709551617.btor");
}

static void
test_read1_special ()
{
  run_unsat_test ("read1.btor");
}

static void
test_read2_special ()
{
  run_unsat_test ("read2.btor");
}

static void
test_read3_special ()
{
  run_sat_test ("read3.btor");
}

static void
test_read4_special ()
{
  run_unsat_test ("read4.btor");
}

static void
test_read5_special ()
{
  run_unsat_test ("read5.btor");
}

static void
test_read6_special ()
{
  run_unsat_test ("read6.btor");
}

static void
test_read7_special ()
{
  run_unsat_test ("read7.btor");
}

static void
test_read8_special ()
{
  run_unsat_test ("read8.btor");
}

static void
test_read9_special ()
{
  run_unsat_test ("read9.btor");
}

static void
test_read10_special ()
{
  run_unsat_test ("read10.btor");
}

static void
test_read11_special ()
{
  run_unsat_test ("read11.btor");
}

static void
test_read12_special ()
{
  run_sat_test ("read12.btor");
}

static void
test_read13_special ()
{
  run_sat_test ("read13.btor");
}

static void
test_read14_special ()
{
  run_sat_test ("read14.btor");
}

static void
test_read15_special ()
{
  run_sat_test ("read15.btor");
}

static void
test_read16_special ()
{
  run_unsat_test ("read16.btor");
}

static void
test_read17_special ()
{
  run_unsat_test ("read17.btor");
}

static void
test_read18_special ()
{
  run_sat_test ("read18.btor");
}

static void
test_write1_special ()
{
  run_unsat_test ("write1.btor");
}

static void
test_write2_special ()
{
  run_unsat_test ("write2.btor");
}

static void
test_write3_special ()
{
  run_unsat_test ("write3.btor");
}

static void
test_write4_special ()
{
  run_unsat_test ("write4.btor");
}

static void
test_write5_special ()
{
  run_sat_test ("write5.btor");
}

static void
test_write6_special ()
{
  run_unsat_test ("write6.btor");
}

static void
test_write7_special ()
{
  run_unsat_test ("write7.btor");
}

static void
test_write8_special ()
{
  run_unsat_test ("write8.btor");
}

static void
test_write9_special ()
{
  run_unsat_test ("write9.btor");
}

static void
test_write10_special ()
{
  run_unsat_test ("write10.btor");
}

static void
test_write11_special ()
{
  run_sat_test ("write11.btor");
}

static void
test_write12_special ()
{
  run_sat_test ("write12.btor");
}

static void
test_arrayeq1_special ()
{
  run_sat_test ("arrayeq1.btor");
}

static void
test_arrayeq2_special ()
{
  run_unsat_test ("arrayeq2.btor");
}

static void
test_arrayeq3_special ()
{
  run_sat_test ("arrayeq3.btor");
}

static void
test_arrayeq4_special ()
{
  run_sat_test ("arrayeq4.btor");
}

static void
test_arrayeq5_special ()
{
  run_unsat_test ("arrayeq5.btor");
}

static void
test_arrayeq6_special ()
{
  run_sat_test ("arrayeq6.btor");
}

static void
test_arrayeq7_special ()
{
  run_unsat_test ("arrayeq7.btor");
}

static void
test_arrayeq8_special ()
{
  run_sat_test ("arrayeq8.btor");
}

static void
test_arrayeq9_special ()
{
  run_unsat_test ("arrayeq9.btor");
}

static void
test_arraycond1_special ()
{
  run_sat_test ("arraycond1.btor");
}

static void
test_arraycond2_special ()
{
  run_sat_test ("arraycond2.btor");
}

static void
test_arraycond3_special ()
{
  run_unsat_test ("arraycond3.btor");
}

static void
test_arraycond4_special ()
{
  run_sat_test ("arraycond4.btor");
}

void
run_special_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (const1_special);
  BTOR_RUN_TEST (const2_special);
  BTOR_RUN_TEST (var1_special);
  BTOR_RUN_TEST (var2_special);
  BTOR_RUN_TEST (rw1_special);
  BTOR_RUN_TEST (rw2_special);
  BTOR_RUN_TEST (rw3_special);
  BTOR_RUN_TEST (rw4_special);
  BTOR_RUN_TEST (rw5_special);
  BTOR_RUN_TEST (rw6_special);
  BTOR_RUN_TEST (rw7_special);
  BTOR_RUN_TEST (rw8_special);
  BTOR_RUN_TEST (rw9_special);
  BTOR_RUN_TEST (rw10_special);
  BTOR_RUN_TEST (rw11_special);
  BTOR_RUN_TEST (rw12_special);
  BTOR_RUN_TEST (rw13_special);
  BTOR_RUN_TEST (rw14_special);
  BTOR_RUN_TEST (rw15_special);
  BTOR_RUN_TEST (sqrt4_special);
  BTOR_RUN_TEST (sqrt5_special);
  BTOR_RUN_TEST (sqrt7_special);
  BTOR_RUN_TEST (sqrt9_special);
  BTOR_RUN_TEST (sqrt13_special);
  BTOR_RUN_TEST (sqrt25_special);
  BTOR_RUN_TEST (sqrt29_special);
  BTOR_RUN_TEST (sqrt31_special);
  BTOR_RUN_TEST (sqrt49_special);
  BTOR_RUN_TEST (sqrt53_special);
  BTOR_RUN_TEST (sqrt65537_special);
  BTOR_RUN_TEST (sqrt4294967297_special);
  BTOR_RUN_TEST (sqrt4295098369_special);
  BTOR_RUN_TEST (sqrt18446744073709551617_special);
  BTOR_RUN_TEST (factor2209_special);
  BTOR_RUN_TEST (factor4294967295_special);
  BTOR_RUN_TEST (factor4294967297_special);
  BTOR_RUN_TEST (factor18446744073709551617const_special);
  BTOR_RUN_TEST (factor18446744073709551617xconst_special);
  BTOR_RUN_TEST (factor18446744073709551617yconst_special);
  BTOR_RUN_TEST (factor18446744073709551617reduced_special);
  BTOR_RUN_TEST (factor18446744073709551617_special);
  BTOR_RUN_TEST (read1_special);
  BTOR_RUN_TEST (read2_special);
  BTOR_RUN_TEST (read3_special);
  BTOR_RUN_TEST (read4_special);
  BTOR_RUN_TEST (read5_special);
  BTOR_RUN_TEST (read6_special);
  BTOR_RUN_TEST (read7_special);
  BTOR_RUN_TEST (read8_special);
  BTOR_RUN_TEST (read9_special);
  BTOR_RUN_TEST (read10_special);
  BTOR_RUN_TEST (read11_special);
  BTOR_RUN_TEST (read12_special);
  BTOR_RUN_TEST (read13_special);
  BTOR_RUN_TEST (read14_special);
  BTOR_RUN_TEST (read15_special);
  BTOR_RUN_TEST (read16_special);
  BTOR_RUN_TEST (read17_special);
  BTOR_RUN_TEST (read18_special);
  BTOR_RUN_TEST (write1_special);
  BTOR_RUN_TEST (write2_special);
  BTOR_RUN_TEST (write3_special);
  BTOR_RUN_TEST (write4_special);
  BTOR_RUN_TEST (write5_special);
  BTOR_RUN_TEST (write6_special);
  BTOR_RUN_TEST (write7_special);
  BTOR_RUN_TEST (write8_special);
  BTOR_RUN_TEST (write9_special);
  BTOR_RUN_TEST (write10_special);
  BTOR_RUN_TEST (write11_special);
  BTOR_RUN_TEST (write12_special);
  BTOR_RUN_TEST (arrayeq1_special);
  BTOR_RUN_TEST (arrayeq2_special);
  BTOR_RUN_TEST (arrayeq3_special);
  BTOR_RUN_TEST (arrayeq4_special);
  BTOR_RUN_TEST (arrayeq5_special);
  BTOR_RUN_TEST (arrayeq6_special);
  BTOR_RUN_TEST (arrayeq7_special);
  BTOR_RUN_TEST (arrayeq8_special);
  BTOR_RUN_TEST (arrayeq9_special);
  BTOR_RUN_TEST (arraycond1_special);
  BTOR_RUN_TEST (arraycond2_special);
  BTOR_RUN_TEST (arraycond3_special);
  BTOR_RUN_TEST (arraycond4_special);
}

void
finish_special_tests (void)
{
}
