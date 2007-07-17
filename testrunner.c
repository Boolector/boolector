#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int g_fast;
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

void
init_tests (int fast)
{
  g_fast              = fast;
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
  printf ("Running %s tests\n", name);
}

static void
check_log (char *file_name)
{
  char *call               = NULL;
  char *file_name_with_dir = NULL;
  size_t len               = 0;
  assert (file_name != NULL);
  file_name_with_dir = (char *) malloc (
      sizeof (char) * (strlen ("log/") + strlen (file_name) + 1));
  strcpy (file_name_with_dir, "log/");
  strcat (file_name_with_dir, file_name);
  len =
      7 + strlen (file_name_with_dir) + 5 + strlen (file_name_with_dir) + 4 + 1;
  call = (char *) malloc (sizeof (char) * len);
  strcpy (call, "cmp -s ");
  strcat (call, file_name_with_dir);
  strcat (call, ".log ");
  strcat (call, file_name_with_dir);
  strcat (call, ".out");
  printf ("  Checking %s", file_name);
  g_compared++;
  if (system (call) == 0)
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
  free (call);
  free (file_name_with_dir);
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
  int skip           = 0;
  int i              = 0;
  int found_slow     = 0;
  char *slow_tests[] = {"arithmetic", "overflow", "comp", "logic", "misc"};
  const int slow_tests_len =
      (int) (sizeof (slow_tests) / sizeof (slow_tests[0]));
  g_num_tests++;
  skip       = 0;
  found_slow = 0;
  if (g_fast)
  {
    for (i = 0; i < slow_tests_len; i++)
    {
      if (strstr (name, slow_tests[i]) != NULL)
      {
        skip = 1;
        break;
      }
    }
  }
  else
  {
    if (argc > 1)
    {
      skip = 1;
      for (i = 1; skip && i < argc; i++)
      {
        if (argv[i][0] == '-') continue;
        skip = !match (name, argv[i]);
      }
    }
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
    fflush (stderr); /* for assertions failures */

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
