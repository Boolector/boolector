#include "testparseerror.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

void
init_parseerror_tests (void)
{
}

static void
parseerror_test (const char *fname)
{
  char *btor_fname, *syscall_string;
  size_t len;
  int ret_val;

  len = strlen (fname);

  btor_fname = (char *) malloc (sizeof (char) * (len + 6));
  sprintf (btor_fname, "%s.btor", fname);
  syscall_string = (char *) malloc (
      sizeof (char)
      * (strlen ("boolector log/") + len + 6 + strlen (" > /dev/null") + 1));

  sprintf (syscall_string, "boolector log/%s > /dev/null", btor_fname);
  ret_val = system (syscall_string);
  assert (WEXITSTATUS (ret_val) == 1);

  free (syscall_string);
  free (btor_fname);
}

static void
test_parseerror1 ()
{
  parseerror_test ("parseerror1");
}

void
run_parseerror_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (parseerror1);
}

void
finish_parseerror_tests (void)
{
}
