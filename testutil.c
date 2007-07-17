#include "testutil.h"
#include "btorutil.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

void
init_util_tests (void)
{
}

static void
test_is_power_of_2_util (void)
{
  assert (btor_is_power_of_2_util (1));
  assert (btor_is_power_of_2_util (2));
  assert (!btor_is_power_of_2_util (3));
  assert (btor_is_power_of_2_util (4));
  assert (!btor_is_power_of_2_util (5));
  assert (!btor_is_power_of_2_util (6));
  assert (!btor_is_power_of_2_util (7));
  assert (btor_is_power_of_2_util (8));
  assert (btor_is_power_of_2_util (16));
  assert (btor_is_power_of_2_util (32));
  assert (btor_is_power_of_2_util (64));
  assert (btor_is_power_of_2_util (128));
  assert (btor_is_power_of_2_util (256));
}

static void
test_log_2_util (void)
{
  assert (btor_log_2_util (1) == 0);
  assert (btor_log_2_util (2) == 1);
  assert (btor_log_2_util (4) == 2);
  assert (btor_log_2_util (8) == 3);
  assert (btor_log_2_util (16) == 4);
  assert (btor_log_2_util (32) == 5);
  assert (btor_log_2_util (64) == 6);
  assert (btor_log_2_util (128) == 7);
  assert (btor_log_2_util (256) == 8);
}

static void
test_pow_2_util (void)
{
  assert (btor_pow_2_util (0) == 1);
  assert (btor_pow_2_util (1) == 2);
  assert (btor_pow_2_util (2) == 4);
  assert (btor_pow_2_util (3) == 8);
  assert (btor_pow_2_util (4) == 16);
  assert (btor_pow_2_util (5) == 32);
  assert (btor_pow_2_util (6) == 64);
  assert (btor_pow_2_util (7) == 128);
  assert (btor_pow_2_util (8) == 256);
}

void
run_util_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (is_power_of_2_util);
  BTOR_RUN_TEST (log_2_util);
  BTOR_RUN_TEST (pow_2_util);
}

void
finish_util_tests (void)
{
}
