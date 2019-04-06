/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
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
  assert (btor_util_is_power_of_2 (1));
  assert (btor_util_is_power_of_2 (2));
  assert (!btor_util_is_power_of_2 (3));
  assert (btor_util_is_power_of_2 (4));
  assert (!btor_util_is_power_of_2 (5));
  assert (!btor_util_is_power_of_2 (6));
  assert (!btor_util_is_power_of_2 (7));
  assert (btor_util_is_power_of_2 (8));
  assert (btor_util_is_power_of_2 (16));
  assert (btor_util_is_power_of_2 (32));
  assert (btor_util_is_power_of_2 (64));
  assert (btor_util_is_power_of_2 (128));
  assert (btor_util_is_power_of_2 (256));
}

static void
test_log_2_util (void)
{
  assert (btor_util_log_2 (1) == 0);
  assert (btor_util_log_2 (2) == 1);
  assert (btor_util_log_2 (4) == 2);
  assert (btor_util_log_2 (8) == 3);
  assert (btor_util_log_2 (16) == 4);
  assert (btor_util_log_2 (32) == 5);
  assert (btor_util_log_2 (64) == 6);
  assert (btor_util_log_2 (128) == 7);
  assert (btor_util_log_2 (256) == 8);
}

static void
test_pow_2_util (void)
{
  assert (btor_util_pow_2 (0) == 1);
  assert (btor_util_pow_2 (1) == 2);
  assert (btor_util_pow_2 (2) == 4);
  assert (btor_util_pow_2 (3) == 8);
  assert (btor_util_pow_2 (4) == 16);
  assert (btor_util_pow_2 (5) == 32);
  assert (btor_util_pow_2 (6) == 64);
  assert (btor_util_pow_2 (7) == 128);
  assert (btor_util_pow_2 (8) == 256);
}

static void
test_next_power_of_2_util (void)
{
  assert (btor_util_next_power_of_2 (1) == 1);
  assert (btor_util_next_power_of_2 (2) == 2);
  assert (btor_util_next_power_of_2 (3) == 4);
  assert (btor_util_next_power_of_2 (4) == 4);
  assert (btor_util_next_power_of_2 (5) == 8);
  assert (btor_util_next_power_of_2 (6) == 8);
  assert (btor_util_next_power_of_2 (7) == 8);
  assert (btor_util_next_power_of_2 (8) == 8);
  assert (btor_util_next_power_of_2 (9) == 16);
  assert (btor_util_next_power_of_2 (10) == 16);
  assert (btor_util_next_power_of_2 (11) == 16);
  assert (btor_util_next_power_of_2 (12) == 16);
  assert (btor_util_next_power_of_2 (13) == 16);
  assert (btor_util_next_power_of_2 (14) == 16);
  assert (btor_util_next_power_of_2 (15) == 16);
  assert (btor_util_next_power_of_2 (16) == 16);
  assert (btor_util_next_power_of_2 (520) == 1024);
  assert (btor_util_next_power_of_2 (990) == 1024);
  assert (btor_util_next_power_of_2 (4095) == 4096);
  assert (btor_util_next_power_of_2 (22376) == 32768);
  assert (btor_util_next_power_of_2 (111712) == 131072);
  assert (btor_util_next_power_of_2 (1000000000) == 1073741824);
}

static void
test_num_digits_util (void)
{
  assert (btor_util_num_digits (0) == 1);
  assert (btor_util_num_digits (1) == 1);
  assert (btor_util_num_digits (5) == 1);
  assert (btor_util_num_digits (11) == 2);
  assert (btor_util_num_digits (99) == 2);
  assert (btor_util_num_digits (100) == 3);
  assert (btor_util_num_digits (1024) == 4);
  assert (btor_util_num_digits (10001) == 5);
  assert (btor_util_num_digits (100343) == 6);
  assert (btor_util_num_digits (2343443) == 7);
}

void
run_util_tests (int32_t argc, char **argv)
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
