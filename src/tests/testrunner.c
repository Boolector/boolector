/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2018 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
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

#include "boolector.h"
#include "btorconfig.h"
#include "btorcore.h"
#include "btoropt.h"
#include "utils/btormem.h"

const char *btor_bin_dir     = BTOR_BIN_DIR;
const char *btor_log_dir     = BTOR_LOG_DIR;
const char *btor_contrib_dir = BTOR_CONTRIB_DIR;
const char *btor_test_dir    = BTOR_TEST_DIR;

int32_t g_rwreads;

FILE *g_logfile = NULL;

static bool g_skip_broken;

static int32_t g_speed = BTOR_NORMAL_TEST_CASE;
static int32_t g_num_tests;
static int32_t g_num_skipped_tests;
static int32_t g_compared;
static int32_t g_compared_succ;

static BtorMemMgr *g_mm = NULL;

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
init_tests (BtorTestCaseSpeed speed, bool skip_broken)
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

static int32_t
cmp_file (const char *a, const char *b)
{
  FILE *f, *g;
  char *sa, *sb;
  int32_t res, c;
  bool isperr_a, isperr_b;
  BtorCharStack stack_a, stack_b;

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

  BTOR_INIT_STACK (g_mm, stack_a);
  BTOR_INIT_STACK (g_mm, stack_b);

  for (c = getc (f); c != EOF; c = getc (f)) BTOR_PUSH_STACK (stack_a, c);
  BTOR_PUSH_STACK (stack_a, 0);

  for (c = getc (g); c != EOF; c = getc (g)) BTOR_PUSH_STACK (stack_b, c);
  BTOR_PUSH_STACK (stack_b, 0);

  /* trim path */
  isperr_a = strncmp (stack_a.start, "boolector:", strlen ("boolector:")) == 0;
  isperr_b = strncmp (stack_b.start, "boolector:", strlen ("boolector:")) == 0;

  if (isperr_a != isperr_b)
  {
    res = 0;
    goto DONE;
  }

  if (isperr_a)
  {
    sa = strstr (stack_a.start, "log");
    sb = strstr (stack_b.start, "log");
    if (!sa || !sb)
    {
      res = 0;
      goto DONE;
    }
  }
  else
  {
    sa = stack_a.start;
    sb = stack_b.start;
  }

  res = !strcmp (sa, sb);

DONE:
  BTOR_RELEASE_STACK (stack_a);
  BTOR_RELEASE_STACK (stack_b);
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

static bool
match (const char *str, const char *pattern)
{
  return strstr (str, pattern) != NULL;
}

// currently unused (but maybe useful in the future)
#if 0
static int32_t
find (const char *str, const char **testset, int32_t testset_size)
{
  assert (testset_size > 0);

  int32_t min_idx = 0, max_idx = testset_size - 1;
  int32_t pivot = min_idx + (max_idx - min_idx) / 2;
  int32_t cmp;

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
run_boolector (int32_t argc, char **argv)
{
  assert (g_mm);

  Btor *btor;
  FILE *infile = 0, *outfile = stdout;
  char *infile_name = 0;
  BtorOption opt;
  int32_t i, status = 0, res;
  uint32_t val;
  size_t prefix_len, len, j;
  char *arg_val, *err_msg = 0;
  const char *shrt, *lng;
  bool set_opt, is_shrt;
  bool dump_btor = false, dump_smt = false, print_model = false;
  char *print_model_format = "btor";
  BtorCharStack arg;

  btor = boolector_new ();
  BTOR_INIT_STACK (g_mm, arg);

  for (i = 1; i < argc; i++)
  {
    is_shrt = true;
    if (argv[i][0] != '-')
    {
      infile_name = argv[i];
      infile      = fopen (infile_name, "r");
    }
    else
    {
      for (j = 0, arg_val = 0, len = strlen (argv[i]); j < len; j++)
      {
        if (argv[i][j] == '-' && j < 2)
        {
          if (j) is_shrt = false;
          continue;
        }
        if (argv[i][j] == '=')
        {
          arg_val = argv[i] + j + 1;
          break;
        }
        BTOR_PUSH_STACK (arg, argv[i][j]);
      }
      BTOR_PUSH_STACK (arg, 0);
      if (!arg_val && i + 1 < argc && argv[i + 1][0] != '-')
      {
        i += 1;
        arg_val = argv[i];
      }
      for (opt = boolector_first_opt (btor), set_opt = false;
           boolector_has_opt (btor, opt);
           opt = boolector_next_opt (btor, opt))
      {
        shrt = boolector_get_opt_shrt (btor, opt);
        lng = boolector_get_opt_lng (btor, opt);
        if ((is_shrt && shrt && !strcmp (shrt, arg.start))
            || (!is_shrt && !strcmp (lng, arg.start)))
        {
          /* Attention: no no-xxx options supported! supported */
          val = arg_val ? (uint32_t) atoi (arg_val) : 1;
          boolector_set_opt (btor, opt, val);
          set_opt = true;
          if (opt == BTOR_OPT_MODEL_GEN) print_model = true;
          break;
        }
      }
      if (!set_opt)
      {
        /* Attention: currently only the options of btormain that are actually
         *            used in file testcases are handled here, extend if needed
         */
        if ((is_shrt && !strcmp (arg.start, "o"))
            || !strcmp (arg.start, "outfile"))
        {
          outfile = fopen (arg_val, "w");
          assert (outfile);
        }
        else if ((is_shrt && !strcmp (arg.start, "db"))
                 || !strcmp (arg.start, "dump-btor"))
        {
          dump_btor = true;
        }
        else if ((is_shrt && !strcmp (arg.start, "ds"))
                 || !strcmp (arg.start, "dump-smt"))
        {
          dump_smt = true;
        }
        else if ((is_shrt && !strcmp (arg.start, "d"))
                 || !strcmp (arg.start, "dec"))
        {
          boolector_set_opt (
              btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT, BTOR_OUTPUT_BASE_DEC);
        }
        else if (!strcmp (arg.start, "smt2-model"))
        {
          print_model        = true;
          print_model_format = "smt2";
        }
        else
        {
          /* Unsupported option. */
          assert (0);
        }
      }
      BTOR_RESET_STACK (arg);
    }
  }

  assert (infile);
  assert (outfile);
  res = boolector_parse (btor, infile, infile_name, outfile, &err_msg, &status);
  if (err_msg)
  {
    prefix_len = strlen (btor_test_dir);
    assert (strlen (err_msg) > prefix_len);
    fprintf (outfile, "%s\n", err_msg + prefix_len);
  }
  else
  {
    if (dump_btor)
    {
      boolector_simplify (btor);
      boolector_dump_btor (btor, outfile);
    }
    else if (dump_smt)
    {
      boolector_simplify (btor);
      boolector_dump_smt2 (btor, outfile);
    }
    else
    {
      if (res == BOOLECTOR_PARSE_UNKNOWN)
      {
        res = boolector_sat (btor);
        if (res == BOOLECTOR_SAT)
        {
          fprintf (outfile, "sat\n");
          if (print_model)
            boolector_print_model (btor, print_model_format, outfile);
        }
        else if (res == BOOLECTOR_UNSAT)
        {
          fprintf (outfile, "unsat\n");
        }
        else
        {
          assert (res == BOOLECTOR_UNKNOWN);
          fprintf (outfile, "unknown\n");
        }
      }
    }
  }
  fclose (outfile);
  fclose (infile);
  boolector_delete (btor);
  BTOR_RELEASE_STACK (arg);
}

void
run_test_case (int32_t argc,
               char **argv,
               void (*funcp) (void),
               char *name,
               bool check_log_file)
{
  bool skip;
  int32_t i, count, len, len_log;
  char *logfile_name, *outfile_name;
  const char **p;

  g_mm = btor_mem_mgr_new ();

  g_num_tests++;
  skip = false;

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
    skip = true;
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
      len     = 4 + strlen (name) + 4 + 1;
      len_log = len + 4 + strlen (btor_log_dir);
      BTOR_NEWN (g_mm, logfile_name, len_log);
      BTOR_NEWN (g_mm, outfile_name, len_log);
      sprintf (logfile_name, "%s%s.log", btor_log_dir, name);
      sprintf (outfile_name, "%s%s.out", btor_log_dir, name);

      g_logfile = fopen (logfile_name, "w");
      assert (g_logfile);
    }

    funcp ();

    if (check_log_file)
    {
      fclose (g_logfile);
      check_log (logfile_name, outfile_name);
      BTOR_DELETEN (g_mm, logfile_name, len_log);
      BTOR_DELETEN (g_mm, outfile_name, len_log);
    }
  }

  btor_mem_mgr_delete (g_mm);
  g_mm = 0;

  nl ();
}

int32_t
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

  return g_compared != g_compared_succ;
}
