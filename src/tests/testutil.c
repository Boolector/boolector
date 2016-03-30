/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testutil.h"
#include "testrunner.h"
#include "utils/btorutil.h"

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

static void
test_next_power_of_2_util (void)
{
  assert (btor_next_power_of_2_util (1) == 1);
  assert (btor_next_power_of_2_util (2) == 2);
  assert (btor_next_power_of_2_util (3) == 4);
  assert (btor_next_power_of_2_util (4) == 4);
  assert (btor_next_power_of_2_util (5) == 8);
  assert (btor_next_power_of_2_util (6) == 8);
  assert (btor_next_power_of_2_util (7) == 8);
  assert (btor_next_power_of_2_util (8) == 8);
  assert (btor_next_power_of_2_util (9) == 16);
  assert (btor_next_power_of_2_util (10) == 16);
  assert (btor_next_power_of_2_util (11) == 16);
  assert (btor_next_power_of_2_util (12) == 16);
  assert (btor_next_power_of_2_util (13) == 16);
  assert (btor_next_power_of_2_util (14) == 16);
  assert (btor_next_power_of_2_util (15) == 16);
  assert (btor_next_power_of_2_util (16) == 16);
  assert (btor_next_power_of_2_util (520) == 1024);
  assert (btor_next_power_of_2_util (990) == 1024);
  assert (btor_next_power_of_2_util (4095) == 4096);
  assert (btor_next_power_of_2_util (22376) == 32768);
  assert (btor_next_power_of_2_util (111712) == 131072);
  assert (btor_next_power_of_2_util (1000000000) == 1073741824);
}

static void
test_num_digits_util (void)
{
  assert (btor_num_digits_util (0) == 1);
  assert (btor_num_digits_util (1) == 1);
  assert (btor_num_digits_util (5) == 1);
  assert (btor_num_digits_util (11) == 2);
  assert (btor_num_digits_util (99) == 2);
  assert (btor_num_digits_util (100) == 3);
  assert (btor_num_digits_util (1024) == 4);
  assert (btor_num_digits_util (10001) == 5);
  assert (btor_num_digits_util (100343) == 6);
  assert (btor_num_digits_util (2343443) == 7);
}

void
run_util_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (is_power_of_2_util);
  BTOR_RUN_TEST (log_2_util);
  BTOR_RUN_TEST (pow_2_util);
  BTOR_RUN_TEST (next_power_of_2_util);
  BTOR_RUN_TEST (num_digits_util);
}

void
finish_util_tests (void)
{
}
