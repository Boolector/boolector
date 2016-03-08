/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2016 Aina Niemetz
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int g_rwreads;

FILE *g_logfile = NULL;

static int g_skip_broken;

static int g_speed = BTOR_NORMAL_TEST_CASE;
static int g_num_tests;
static int g_num_skipped_tests;
static int g_compared;
static int g_compared_succ;

static struct
{
  const char *std;
  const char *green;
  const char *blue;
  const char *red;
  char nl[100];
} terminal;

/* By default a test is 'fast'.  Tests that are a little bit slower but can
 * still be run in a regression run within a minute are 'normal' and are
 * listed below in 'normaltests'.  Slow tests take considerable more time
 * and are listed in 'slowtests'.  As a rule of thumb a slow test takes
 * defintely more than 10 seconds to run.
 */

static const char *slowtests[] = {
    "smtaxiombvsmod7",
    "smtaxiombvsmod8",
    "smtaxiombvsdiv7",
    "smtaxiombvsdiv8",
    "smtaxiombvsrem7",
    "smtaxiombvsrem8",
    "factor4294967295_special",
    "inc_count8nondet",
    "binarysearch32s016",
    "fifo32ia04k05",
    "mulassoc6",
    "hd10",
    "hd14",
    "problem_130",
    "bv_to_ll_bitvec",
    "new_bitvec",
    "not_bitvec",
    "neg_bitvec",
    "slice_bitvec",
    "eq_bitvec",
    "ult_bitvec",
    "and_bitvec",
    "concat_bitvec",
    "add_bitvec",
    "sll_bitvec",
    "srl_bitvec",
    "mul_bitvec",
    "udiv_bitvec",
    "urem_bitvec",
    "uext_bitvec",
    "sext_bitvec",
    "perf_and_bitvec",
    "perf_eq_bitvec",
    "perf_ult_bitvec",
    "perf_add_bitvec",
    "perf_mul_bitvec",
    "perf_udiv_bitvec",
    "perf_urem_bitvec",
    "perf_sll_bitvec",
    "perf_srl_bitvec",
    "propinv_complete_add_bv",
    "propinv_complete_and_bv",
    "propinv_complete_eq_bv",
    "propinv_complete_ult_bv",
    "propinv_complete_sll_bv",
    "propinv_complete_srl_bv",
    "propinv_complete_mul_bv",
    "propinv_complete_udiv_bv",
    "propinv_complete_urem_bv",
    "propinv_complete_concat_bv",
    "propinv_complete_slice_bv",

    0, /* NOTE: DO NOT REMOVE AND KEEP AT SENTINEL */
};

/* Again these are the tests that are slightly faster than slow tests.  They
 * run in the order of 1 to 10 seconds each of them.  Fast tests definitely
 * take less than a second.
 */
static const char *normaltests[] = {
    "sll_shift",
    "srl_shift",
    "sra_shift",
    "rol_shift",
    "ror_shift",
    "sll_shift",
    "srl_shift",
    "sra_shift",
    "rol_shift",
    "ror_shift",
    "smtaxiombvsmod5",
    "smtaxiombvsmod6",
    "smtaxiombvsdiv5",
    "smtaxiombvsdiv6",
    "smtaxiombvsrem5",
    "smtaxiombvsrem6",
    "udiv8castdown6",
    "udiv8castdown7",
    "udiv16castdown8",
    "mulassoc6",
    "inc_lt8",
    "hd4",
    "hd9",
    "hd11",
    "headline1",
    "headline6",
    "headline7",
    "headline8",

    0, /* NOTE: DO NOT REMOVE AND KEEP AT SENTINEL */
};

/* These are performance tests that take a very long time.
 */

static const char *performancetests[] = {
    "perf_",

    0, /* NOTE: DO NOT REMOVE AND KEEP AT SENTINEL */
};

static const char *brokentests[] = {
    /* SMT2 files broken */
    "modelgensmt28",
    "modelgensmt210",
    "modelgensmt215",
    /* broken due to sort mix-up (needs to be fixed (ma))*/
    "modelgensmt25",
    "modelgensmt26",
    "modelgensmt27",
    /* currently broken due to dumper support for args/apply */
    "dumpbtor2",
    "dumpsmt1",
    "dumpsmt2",
    /* currently broken as we do not have reads/writes/aconds anymore */
    "read_exp",
    "write_exp",
    /* currently broken as we do not support lambda hashing yet */
    "lambda_param_write1",
    "lambda_param_write2",
    "lambda_param_acond",
    /* currently broken since we don't allow to mix lambdas with arrays */
    "regrbetacache2",

    0, /* NOTE: DO NOT REMOVE AND KEEP AT SENTINEL */
};

void
init_tests (BtorTestCaseSpeed speed, int skip_broken)
{
  g_skip_broken       = skip_broken;
  g_speed             = speed;
  g_num_tests         = 0;
  g_num_skipped_tests = 0;
  g_compared          = 0;
  g_compared_succ     = 0;

  if (isatty (1)) /* check for non bash terminals as well */
  {
    terminal.std   = "\e[0;39m";
    terminal.green = "\e[1;32m";
    terminal.blue  = "\e[1;34m";
    terminal.red   = "\e[1;31m";
    sprintf (terminal.nl, "\r%80s\r", "");
  }
  else
  {
    terminal.std   = "";
    terminal.green = "";
    terminal.blue  = "";
    terminal.red   = "";
    strcpy (terminal.nl, "\n");
  }
}

static void
nl (void)
{
  fputs (terminal.nl, stdout);
  fflush (stdout);
}

void
print_test_suite_name (const char *name)
{
  assert (name != NULL);
  printf ("Registered %s tests\n", name);
}

static int
cmp_file (const char *a, const char *b)
{
  FILE *f, *g;
  char *stack_a, *stack_b, *sa, *sb;
  int res, c, d, init_size = 100, size, nelems = 0;
  bool isperr_a, isperr_b;

  assert (a);
  assert (b);

  f = fopen (a, "r");
  if (!f) return 0;

  g = fopen (b, "r");
  if (!g)
  {
    fclose (f);
    return 0;
  }

  stack_a    = malloc (sizeof (char) * init_size);
  stack_b    = malloc (sizeof (char) * init_size);
  stack_a[0] = 0;
  stack_b[0] = 0;

  for (nelems = 0, size = init_size, c = getc (f); c != EOF; c = getc (f))
  {
    assert (nelems < size);
    stack_a[nelems] = c;
    nelems += 1;
    if (nelems == size)
    {
      stack_a = realloc (stack_a, sizeof (char) * 2 * size);
      size *= 2;
    }
  }
  stack_a[nelems] = 0;

  for (nelems = 0, size = init_size, d = getc (g); d != EOF; d = getc (g))
  {
    assert (nelems < size);
    stack_b[nelems] = d;
    nelems += 1;
    if (nelems == size)
    {
      stack_b = realloc (stack_b, sizeof (char) * 2 * size);
      size *= 2;
    }
  }
  stack_b[nelems] = 0;

  /* trim path */
  isperr_a = strncmp (stack_a, "boolector:", strlen ("boolector:")) == 0;
  isperr_b = strncmp (stack_b, "boolector:", strlen ("boolector:")) == 0;

  if (isperr_a != isperr_b) return 0;

  if (isperr_a)
  {
    sa = strstr (stack_a, "log");
    sb = strstr (stack_b, "log");
    if (!sa || !sb)
    {
      res = 0;
      goto DONE;
    }
  }
  else
  {
    sa = stack_a;
    sb = stack_b;
  }

  res = !strcmp (sa, sb);

DONE:
  free (stack_a);
  free (stack_b);

  fclose (f);
  fclose (g);

  return res;
}

static void
check_log (char *logfile_name, char *outfile_name)
{
  assert (logfile_name);
  assert (outfile_name);

  g_compared++;

  if (cmp_file (logfile_name, outfile_name))
  {
    nl ();
    g_compared_succ++;
  }
  else
  {
    printf ("  %s[ %sFAILED %s]%s\n",
            terminal.blue,
            terminal.red,
            terminal.blue,
            terminal.std);
  }
}

static int
match (const char *str, const char *pattern)
{
  return strstr (str, pattern) != NULL;
}

// currently unused (but maybe useful in the future)
#if 0
static int
find (const char *str, const char **testset, int testset_size)
{
  assert (testset_size > 0);

  int min_idx = 0, max_idx = testset_size - 1;
  int pivot = min_idx + (max_idx - min_idx) / 2;
  int cmp;

  while ((cmp = strcmp (str, testset[pivot])))
    {
      if (cmp < 0)
	max_idx = pivot - 1;
      else
	min_idx = pivot + 1;
      pivot = min_idx + (max_idx - min_idx) / 2;

      if (max_idx < min_idx)
	return 0;
    }

  return 1;
}
#endif

void
run_test_case (
    int argc, char **argv, void (*funcp) (void), char *name, int check_log_file)
{
  int i, count, skip, len;
  char *logfile_name, *outfile_name;
  const char **p;

  g_num_tests++;
  skip = 0;

  if (g_skip_broken)
    for (p = brokentests; !skip && *p; p++) skip = match (name, *p);

  if (g_speed < BTOR_NORMAL_TEST_CASE)
    for (p = normaltests; !skip && *p; p++) skip = match (name, *p);

  if (g_speed < BTOR_SLOW_TEST_CASE)
    for (p = slowtests; !skip && *p; p++) skip = match (name, *p);

  if (g_speed < BTOR_SLOW_TEST_CASE)
    for (p = performancetests; !skip && *p; p++) skip = match (name, *p);

  count     = 0;
  g_rwreads = 0;
  for (i = 1; i < argc; i++)
  {
    count += (argv[i][0] != '-');
    if (strcmp (argv[i], "-R") == 0 || strcmp (argv[i], "--bra") == 0)
      g_rwreads = 1;
  }

  if (!skip && count)
  {
    skip = 1;
    for (i = 1; skip && i < argc; i++)
      if (argv[i][0] != '-') skip = !match (name, argv[i]);
  }

  if (skip)
  {
    g_num_skipped_tests++;
    printf (" Skipping %s ", name);
  }
  else
  {
    printf (" Running %s ", name);

    fflush (stdout);
    fflush (stdout); /* for assertion failures */

    if (check_log_file)
    {
      len = 0;
      /* "log/" + name + ".log" or ".out" + \0 */
      len          = 4 + strlen (name) + 4 + 1;
      logfile_name = (char *) malloc (len + strlen (BTOR_LOG_DIR));
      outfile_name = (char *) malloc (len + strlen (BTOR_LOG_DIR));
      sprintf (logfile_name, "%s%s.log", BTOR_LOG_DIR, name);
      sprintf (outfile_name, "%s%s.out", BTOR_LOG_DIR, name);

      g_logfile = fopen (logfile_name, "w");
      assert (g_logfile);
    }

    funcp ();

    if (check_log_file)
    {
      fclose (g_logfile);
      check_log (logfile_name, outfile_name);
      free (logfile_name);
      free (outfile_name);
    }
  }

  nl ();
}

void
finish_tests (void)
{
  nl ();

  printf ("%sFinished %d tests:\n%s",
          (g_compared == g_compared_succ) ? terminal.green : terminal.red,
          g_num_tests,
          terminal.std);
  if (g_num_skipped_tests > 0)
    printf ("  %sNumber of tests skipped: %d%s\n",
            terminal.blue,
            g_num_skipped_tests,
            terminal.std);
  printf ("  %sNumber of tests succeeded: %d%s\n",
          terminal.green,
          g_num_tests - g_num_skipped_tests,
          terminal.std);

  printf ("  %sNumber of files successfully compared: %d/%d%s\n",
          (g_compared == g_compared_succ) ? terminal.green : terminal.red,
          g_compared_succ,
          g_compared,
          terminal.std);
}
