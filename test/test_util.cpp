/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/btorutil.h"
}

TEST (TestUtil, is_power_of_2)
{
  ASSERT_TRUE (btor_util_is_power_of_2 (1));
  ASSERT_TRUE (btor_util_is_power_of_2 (2));
  ASSERT_TRUE (!btor_util_is_power_of_2 (3));
  ASSERT_TRUE (btor_util_is_power_of_2 (4));
  ASSERT_TRUE (!btor_util_is_power_of_2 (5));
  ASSERT_TRUE (!btor_util_is_power_of_2 (6));
  ASSERT_TRUE (!btor_util_is_power_of_2 (7));
  ASSERT_TRUE (btor_util_is_power_of_2 (8));
  ASSERT_TRUE (btor_util_is_power_of_2 (16));
  ASSERT_TRUE (btor_util_is_power_of_2 (32));
  ASSERT_TRUE (btor_util_is_power_of_2 (64));
  ASSERT_TRUE (btor_util_is_power_of_2 (128));
  ASSERT_TRUE (btor_util_is_power_of_2 (256));
}

TEST (TestUtil, log_2)
{
  ASSERT_EQ (btor_util_log_2 (1), 0u);
  ASSERT_EQ (btor_util_log_2 (2), 1u);
  ASSERT_EQ (btor_util_log_2 (4), 2u);
  ASSERT_EQ (btor_util_log_2 (8), 3u);
  ASSERT_EQ (btor_util_log_2 (16), 4u);
  ASSERT_EQ (btor_util_log_2 (32), 5u);
  ASSERT_EQ (btor_util_log_2 (64), 6u);
  ASSERT_EQ (btor_util_log_2 (128), 7u);
  ASSERT_EQ (btor_util_log_2 (256), 8u);
}

TEST (TestUtil, pow_2)
{
  ASSERT_EQ (btor_util_pow_2 (0), 1);
  ASSERT_EQ (btor_util_pow_2 (1), 2);
  ASSERT_EQ (btor_util_pow_2 (2), 4);
  ASSERT_EQ (btor_util_pow_2 (3), 8);
  ASSERT_EQ (btor_util_pow_2 (4), 16);
  ASSERT_EQ (btor_util_pow_2 (5), 32);
  ASSERT_EQ (btor_util_pow_2 (6), 64);
  ASSERT_EQ (btor_util_pow_2 (7), 128);
  ASSERT_EQ (btor_util_pow_2 (8), 256);
}

TEST (TestUtil, next_power_of_2)
{
  ASSERT_EQ (btor_util_next_power_of_2 (1), 1);
  ASSERT_EQ (btor_util_next_power_of_2 (2), 2);
  ASSERT_EQ (btor_util_next_power_of_2 (3), 4);
  ASSERT_EQ (btor_util_next_power_of_2 (4), 4);
  ASSERT_EQ (btor_util_next_power_of_2 (5), 8);
  ASSERT_EQ (btor_util_next_power_of_2 (6), 8);
  ASSERT_EQ (btor_util_next_power_of_2 (7), 8);
  ASSERT_EQ (btor_util_next_power_of_2 (8), 8);
  ASSERT_EQ (btor_util_next_power_of_2 (9), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (10), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (11), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (12), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (13), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (14), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (15), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (16), 16);
  ASSERT_EQ (btor_util_next_power_of_2 (520), 1024);
  ASSERT_EQ (btor_util_next_power_of_2 (990), 1024);
  ASSERT_EQ (btor_util_next_power_of_2 (4095), 4096);
  ASSERT_EQ (btor_util_next_power_of_2 (22376), 32768);
  ASSERT_EQ (btor_util_next_power_of_2 (111712), 131072);
  ASSERT_EQ (btor_util_next_power_of_2 (1000000000), 1073741824);
}

TEST (TestUtil, num_digits)
{
  ASSERT_EQ (btor_util_num_digits (0), 1u);
  ASSERT_EQ (btor_util_num_digits (1), 1u);
  ASSERT_EQ (btor_util_num_digits (5), 1u);
  ASSERT_EQ (btor_util_num_digits (11), 2u);
  ASSERT_EQ (btor_util_num_digits (99), 2u);
  ASSERT_EQ (btor_util_num_digits (100), 3u);
  ASSERT_EQ (btor_util_num_digits (1024), 4u);
  ASSERT_EQ (btor_util_num_digits (10001), 5u);
  ASSERT_EQ (btor_util_num_digits (100343), 6u);
  ASSERT_EQ (btor_util_num_digits (2343443), 7u);
}
