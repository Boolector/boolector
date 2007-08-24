#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

#include "btormain.h"
#include "testrunner.h"
#include "testtestcases.h"

#include <stdio.h>

void
init_testcases_tests (void)
{
}

void
run_testcases_tests (int argc, char** argv)
{
  FILE* file;
  assert ((file = fopen ("testcases", "r")));
  fclose (file);
}

void
finish_testcases_tests (void)
{
}
