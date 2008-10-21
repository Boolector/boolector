#include "testmodelgen.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void
init_modelgen_tests (void)
{
}

static void
formula_modelgen_test (const char *fname, int rwl)
{
  char *btor_fname, *log_fname, *syscall_string;
  size_t len;
  int ret_val;

  assert (rwl >= 0);
  assert (rwl <= 3);

  len = strlen (fname);

  btor_fname = (char *) malloc (sizeof (char) * (len + 6));
  sprintf (btor_fname, "%s.btor", fname);

  log_fname = (char *) malloc (sizeof (char) * (len + 5));
  sprintf (log_fname, "%s.log", fname);

  syscall_string = (char *) malloc (sizeof (char)
                                    * (+len + 5 + len + 4
                                       + strlen ("boolector -rwl3 -m log/")
                                       + strlen (" -o log/") + 1));

  sprintf (syscall_string,
           "boolector -rwl%d -m log/%s -o log/%s",
           rwl,
           btor_fname,
           log_fname);

  system (syscall_string);
  free (syscall_string);

  syscall_string =
      (char *) malloc (sizeof (char)
                       * (len + 5 + len + 4 + strlen ("btorcheckmodel log/")
                          + strlen (" log/") + 1));

  sprintf (
      syscall_string, "btorcheckmodel log/%s log/%s", btor_fname, log_fname);
  ret_val = system (syscall_string);
  assert (ret_val == 0);

  free (syscall_string);
  free (log_fname);
  free (btor_fname);
}

static void
test_formula1_modelgen ()
{
  formula_modelgen_test ("modelgen1", 1);
}

static void
test_formula2_modelgen ()
{
  formula_modelgen_test ("modelgen2", 3);
}

static void
test_formula3_modelgen ()
{
  formula_modelgen_test ("modelgen3", 3);
}

static void
test_formula4_modelgen ()
{
  formula_modelgen_test ("modelgen4", 3);
}

static void
test_formula5_modelgen ()
{
  formula_modelgen_test ("modelgen5", 3);
}

static void
test_formula6_modelgen ()
{
  formula_modelgen_test ("modelgen6", 3);
}

static void
test_formula7_modelgen ()
{
  formula_modelgen_test ("modelgen7", 3);
}

static void
test_formula8_modelgen ()
{
  formula_modelgen_test ("modelgen8", 0);
}

static void
test_formula9_modelgen ()
{
  formula_modelgen_test ("modelgen9", 3);
}

static void
test_formula10_modelgen ()
{
  formula_modelgen_test ("modelgen10", 3);
}

static void
test_formula11_modelgen ()
{
  formula_modelgen_test ("modelgen11", 3);
}

static void
test_formula12_modelgen ()
{
  formula_modelgen_test ("modelgen12", 3);
}

static void
test_formula13_modelgen ()
{
  formula_modelgen_test ("modelgen13", 3);
}

static void
test_formula14_modelgen ()
{
  formula_modelgen_test ("modelgen14", 3);
}

static void
test_formula15_modelgen ()
{
  formula_modelgen_test ("modelgen15", 3);
}

static void
test_formula16_modelgen ()
{
  formula_modelgen_test ("modelgen16", 1);
}

static void
test_formula17_modelgen ()
{
  formula_modelgen_test ("modelgen17", 1);
}

static void
test_formula18_modelgen ()
{
  formula_modelgen_test ("modelgen18", 3);
}

static void
test_formula19_modelgen ()
{
  formula_modelgen_test ("modelgen19", 2);
}

void
run_modelgen_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (formula1_modelgen);
  BTOR_RUN_TEST (formula2_modelgen);
  BTOR_RUN_TEST (formula3_modelgen);
  BTOR_RUN_TEST (formula4_modelgen);
  BTOR_RUN_TEST (formula5_modelgen);
  BTOR_RUN_TEST (formula6_modelgen);
  BTOR_RUN_TEST (formula7_modelgen);
  BTOR_RUN_TEST (formula8_modelgen);
  BTOR_RUN_TEST (formula9_modelgen);
  BTOR_RUN_TEST (formula10_modelgen);
  BTOR_RUN_TEST (formula11_modelgen);
  BTOR_RUN_TEST (formula12_modelgen);
  BTOR_RUN_TEST (formula13_modelgen);
  BTOR_RUN_TEST (formula14_modelgen);
  BTOR_RUN_TEST (formula15_modelgen);
  BTOR_RUN_TEST (formula16_modelgen);
  BTOR_RUN_TEST (formula17_modelgen);
  BTOR_RUN_TEST (formula18_modelgen);
  BTOR_RUN_TEST (formula19_modelgen);
}

void
finish_modelgen_tests (void)
{
}
