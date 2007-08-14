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

void
run_special_tests (int argc, char **argv)
{
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
}

void
finish_special_tests (void)
{
}
