#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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

/* By default a test is 'fast'.  Test that are a little bit slower
 * but still can be run in a regression run within a minute are 'normal' and
 * are listed below in 'normaltests'.  Slow tests take considerable more
 * time and are listed in 'slowtests', as rule of thumb a slow test
 * takes defintely more than 10 seconds to run.
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

void
init_tests (BtorTestCaseSpeed speed)
{
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
  int res, c, d;

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

  do
  {
    c   = getc (f);
    d   = getc (g);
    res = (c == d);
  } while (res && c != EOF);

  fclose (f);
  fclose (g);

  return res;
}

static void
check_log (char *name)
{
  char *path;
  char *log;
  char *out;
  size_t len;

  assert (name);

  len = strlen ("log/");
  len += strlen (name);
  len++;

  path = malloc (len);
  sprintf (path, "log/%s", name);

  len += 4; /* ".log" or ".out" */

  log = malloc (len);
  out = malloc (len);

  sprintf (log, "%s.log", path);
  sprintf (out, "%s.out", path);

  g_compared++;

  if (cmp_file (log, out))
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

  free (path);
  free (log);
  free (out);
}

static int
match (const char *str, const char *pattern)
{
  return strstr (str, pattern) != NULL;
}

void
run_test_case (
    int argc, char **argv, void (*funcp) (), char *name, int check_log_file)
{
  int skip = 0, count;
  const char **p;
  int i = 0;

  g_num_tests++;
  skip = 0;

  if (g_speed < BTOR_NORMAL_TEST_CASE)
    for (p = normaltests; !skip && *p; p++) skip = match (name, *p);

  if (g_speed < BTOR_SLOW_TEST_CASE)
    for (p = slowtests; !skip && *p; p++) skip = match (name, *p);

  count = 0;
  for (i = 1; i < argc; i++) count += (argv[i][0] != '-');

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
    fflush (stdout); /* for assertions failures */

    funcp ();

    if (check_log_file) check_log (name);
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
