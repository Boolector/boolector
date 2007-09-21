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
  run_sat_test ("const1.in");
}

static void
test_const2_special ()
{
  run_unsat_test ("const2.in");
}

static void
test_var1_special ()
{
  run_sat_test ("var1.in");
}

static void
test_var2_special ()
{
  run_sat_test ("var2.in");
}

static void
test_rw1_special ()
{
  run_sat_test ("rw1.in");
}

static void
test_rw2_special ()
{
  run_sat_test ("rw2.in");
}

static void
test_rw3_special ()
{
  run_sat_test ("rw3.in");
}

static void
test_rw4_special ()
{
  run_sat_test ("rw4.in");
}

static void
test_rw5_special ()
{
  run_sat_test ("rw5.in");
}

static void
test_rw6_special ()
{
  run_sat_test ("rw6.in");
}

static void
test_rw7_special ()
{
  run_sat_test ("rw7.in");
}

static void
test_rw8_special ()
{
  run_sat_test ("rw8.in");
}

static void
test_rw9_special ()
{
  run_sat_test ("rw9.in");
}

static void
test_rw10_special ()
{
  run_sat_test ("rw10.in");
}

static void
test_rw11_special ()
{
  run_sat_test ("rw11.in");
}

static void
test_rw12_special ()
{
  run_sat_test ("rw12.in");
}

static void
test_rw13_special ()
{
  run_sat_test ("rw13.in");
}

static void
test_rw14_special ()
{
  run_sat_test ("rw14.in");
}

static void
test_rw15_special ()
{
  run_sat_test ("rw15.in");
}

static void
test_sqrt4_special ()
{
  run_sat_test ("sqrt4.in");
}

static void
test_sqrt5_special ()
{
  run_unsat_test ("sqrt5.in");
}

static void
test_sqrt7_special ()
{
  run_unsat_test ("sqrt7.in");
}

static void
test_sqrt9_special ()
{
  run_sat_test ("sqrt9.in");
}

static void
test_sqrt13_special ()
{
  run_unsat_test ("sqrt13.in");
}

static void
test_sqrt25_special ()
{
  run_sat_test ("sqrt25.in");
}

static void
test_sqrt29_special ()
{
  run_unsat_test ("sqrt29.in");
}

static void
test_sqrt31_special ()
{
  run_unsat_test ("sqrt31.in");
}

static void
test_sqrt49_special ()
{
  run_sat_test ("sqrt49.in");
}

static void
test_sqrt53_special ()
{
  run_unsat_test ("sqrt53.in");
}

static void
test_sqrt65537_special ()
{
  run_unsat_test ("sqrt65537.in");
}

static void
test_sqrt4294967297_special ()
{
  run_unsat_test ("sqrt4294967297.in");
}

static void
test_sqrt4295098369_special ()
{
  run_sat_test ("sqrt4295098369.in");
}

static void
test_sqrt18446744073709551617_special ()
{
  run_unsat_test ("sqrt18446744073709551617.in");
}

static void
test_factor2209_special ()
{
  run_sat_test ("factor2209.in");
}

static void
test_factor4294967295_special ()
{
  run_sat_test ("factor4294967295.in");
}

static void
test_factor4294967297_special ()
{
  run_sat_test ("factor4294967297.in");
}

static void
test_factor18446744073709551617const_special ()
{
  run_sat_test ("factor18446744073709551617const.in");
}

static void
test_factor18446744073709551617xconst_special ()
{
  run_sat_test ("factor18446744073709551617xconst.in");
}

static void
test_factor18446744073709551617yconst_special ()
{
  run_sat_test ("factor18446744073709551617yconst.in");
}

static void
test_factor18446744073709551617reduced_special ()
{
  run_sat_test ("factor18446744073709551617reduced.in");
}

static void
test_factor18446744073709551617_special ()
{
  run_sat_test ("factor18446744073709551617.in");
}

static void
test_read1_special ()
{
  run_unsat_test ("read1.in");
}

static void
test_read2_special ()
{
  run_unsat_test ("read2.in");
}

static void
test_read3_special ()
{
  run_sat_test ("read3.in");
}

static void
test_read4_special ()
{
  run_unsat_test ("read4.in");
}

static void
test_read5_special ()
{
  run_unsat_test ("read5.in");
}

static void
test_read6_special ()
{
  run_unsat_test ("read6.in");
}

static void
test_read7_special ()
{
  run_unsat_test ("read7.in");
}

static void
test_read8_special ()
{
  run_unsat_test ("read8.in");
}

static void
test_read9_special ()
{
  run_unsat_test ("read9.in");
}

static void
test_read10_special ()
{
  run_unsat_test ("read10.in");
}

static void
test_read11_special ()
{
  run_unsat_test ("read11.in");
}

static void
test_read12_special ()
{
  run_sat_test ("read12.in");
}

static void
test_read13_special ()
{
  run_sat_test ("read13.in");
}

static void
test_read14_special ()
{
  run_sat_test ("read14.in");
}

static void
test_read15_special ()
{
  run_sat_test ("read15.in");
}

static void
test_read16_special ()
{
  run_unsat_test ("read16.in");
}

static void
test_read17_special ()
{
  run_unsat_test ("read17.in");
}

static void
test_read18_special ()
{
  run_sat_test ("read18.in");
}

static void
test_write1_special ()
{
  run_unsat_test ("write1.in");
}

static void
test_write2_special ()
{
  run_unsat_test ("write2.in");
}

static void
test_write3_special ()
{
  run_unsat_test ("write3.in");
}

static void
test_write4_special ()
{
  run_unsat_test ("write4.in");
}

static void
test_write5_special ()
{
  run_sat_test ("write5.in");
}

static void
test_write6_special ()
{
  run_unsat_test ("write6.in");
}

static void
test_write7_special ()
{
  run_unsat_test ("write7.in");
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
}

void
finish_special_tests (void)
{
}
