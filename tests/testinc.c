/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2007-2012 Robert Daniel Brummayer, Armin Biere
 *  Copyright (C) 2012-2013 Aina Niemetz
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "testinc.h"
#include "btorcore.h"
#include "btorexit.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>

static Btor *g_btor = NULL;

static void
init_inc_test (void)
{
  g_btor                  = btor_new_btor ();
  g_btor->beta_reduce_all = g_rwreads;
}

static void
finish_inc_test (void)
{
  btor_delete_btor (g_btor);
}

static void
test_inc_true_false (void)
{
  BtorNode *ff;
  BtorNode *tt;
  int res;

  init_inc_test ();

  ff = btor_false_exp (g_btor);
  tt = btor_true_exp (g_btor);
  btor_enable_inc_usage (g_btor);
  btor_assume_exp (g_btor, tt);
  res = btor_sat_btor (g_btor);
  assert (res == BTOR_SAT);

  btor_assume_exp (g_btor, ff);
  res = btor_sat_btor (g_btor);
  assert (res == BTOR_UNSAT);
  assert (btor_failed_exp (g_btor, ff));

  btor_release_exp (g_btor, ff);
  btor_release_exp (g_btor, tt);
  finish_inc_test ();
}

static void
test_inc_counter (int w, int nondet)
{
  BtorNode *nonzero, *allzero, *one, *oracle;
  BtorNode *current, *next, *inc;
  char name[100];
  int i, res;

  assert (w > 0);

  init_inc_test ();

  btor_enable_inc_usage (g_btor);
  one     = btor_one_exp (g_btor, w);
  current = btor_zero_exp (g_btor, w);
  i       = 0;

  for (;;)
  {
    inc = btor_add_exp (g_btor, current, one);

    if (nondet)
    {
      sprintf (name, "oracle%d", i);
      if (i)
        oracle = btor_var_exp (g_btor, 1, name);
      else
        oracle = btor_true_exp (g_btor);
      next = btor_cond_exp (g_btor, oracle, inc, current);
      btor_release_exp (g_btor, oracle);
    }
    else
      next = btor_copy_exp (g_btor, inc);

    btor_release_exp (g_btor, inc);
    btor_release_exp (g_btor, current);
    current = next;

    nonzero = btor_redor_exp (g_btor, current);
    allzero = btor_not_exp (g_btor, nonzero);
    btor_release_exp (g_btor, nonzero);

    i++;

    btor_assume_exp (g_btor, allzero);
    btor_release_exp (g_btor, allzero);

    res = btor_sat_btor (g_btor);
    if (res == BTOR_SAT) break;

    assert (res == BTOR_UNSAT);
    assert (btor_failed_exp (g_btor, allzero));

    assert (i < (1 << w));
  }

  assert (i == (1 << w));

  btor_release_exp (g_btor, one);
  btor_release_exp (g_btor, current);

  finish_inc_test ();
}

static void
test_inc_count1 (void)
{
  test_inc_counter (1, 0);
}

static void
test_inc_count2 (void)
{
  test_inc_counter (2, 0);
}

static void
test_inc_count3 (void)
{
  test_inc_counter (3, 0);
}

static void
test_inc_count4 (void)
{
  test_inc_counter (4, 0);
}

static void
test_inc_count8 (void)
{
  test_inc_counter (8, 0);
}

static void
test_inc_count1nondet (void)
{
  test_inc_counter (1, 1);
}

static void
test_inc_count2nondet (void)
{
  test_inc_counter (2, 1);
}

static void
test_inc_count3nondet (void)
{
  test_inc_counter (3, 1);
}

static void
test_inc_count4nondet (void)
{
  test_inc_counter (4, 1);
}

static void
test_inc_count8nondet (void)
{
  test_inc_counter (8, 1);
}

static void
test_inc_lt (int w)
{
  BtorNode *prev, *next, *lt;
  char name[100];
  int i, res;

  assert (w > 0);

  init_inc_test ();
  btor_enable_inc_usage (g_btor);

  i    = 0;
  prev = 0;
  for (;;)
  {
    i++;

    sprintf (name, "%d", i);
    next = btor_var_exp (g_btor, w, name);

    if (prev)
    {
      lt = btor_ult_exp (g_btor, prev, next);
      btor_assert_exp (g_btor, lt);
      btor_release_exp (g_btor, lt);
      btor_release_exp (g_btor, prev);
    }

    prev = next;

    res = btor_sat_btor (g_btor);
    if (res == BTOR_UNSAT) break;

    assert (res == BTOR_SAT);
    assert (i <= (1 << w));
  }

  assert (i == (1 << w) + 1);

  btor_release_exp (g_btor, prev);

  finish_inc_test ();
}

static void
test_inc_lt1 (void)
{
  test_inc_lt (1);
}

static void
test_inc_lt2 (void)
{
  test_inc_lt (2);
}

static void
test_inc_lt3 (void)
{
  test_inc_lt (3);
}

static void
test_inc_lt4 (void)
{
  test_inc_lt (4);
}

static void
test_inc_lt8 (void)
{
  test_inc_lt (8);
}

static void
test_inc_assume_assert1 (void)
{
  int sat_result;
  BtorNode *array, *index1, *index2, *read1, *read2, *eq_index, *ne_read;

  init_inc_test ();
  btor_enable_inc_usage (g_btor);
  btor_set_rewrite_level_btor (g_btor, 0);

  array    = btor_array_exp (g_btor, 1, 1, "array1");
  index1   = btor_var_exp (g_btor, 1, "index1");
  index2   = btor_var_exp (g_btor, 1, "index2");
  read1    = btor_read_exp (g_btor, array, index1);
  read2    = btor_read_exp (g_btor, array, index2);
  eq_index = btor_eq_exp (g_btor, index1, index2);
  ne_read  = btor_ne_exp (g_btor, read1, read2);

  btor_assert_exp (g_btor, ne_read);
  sat_result = btor_sat_btor (g_btor);
  assert (sat_result == BTOR_SAT);

  btor_assume_exp (g_btor, eq_index);
  sat_result = btor_sat_btor (g_btor);
  assert (sat_result == BTOR_UNSAT);
  assert (btor_failed_exp (g_btor, eq_index));

  sat_result = btor_sat_btor (g_btor);
  assert (sat_result == BTOR_SAT);

  btor_release_exp (g_btor, array);
  btor_release_exp (g_btor, index1);
  btor_release_exp (g_btor, index2);
  btor_release_exp (g_btor, read1);
  btor_release_exp (g_btor, read2);
  btor_release_exp (g_btor, eq_index);
  btor_release_exp (g_btor, ne_read);

  finish_inc_test ();
}

static void
test_inc_lemmas_on_demand_1 ()
{
  int sat_result;
  BtorNode *array, *index1, *index2, *read1, *read2, *eq, *ne;

  init_inc_test ();
  btor_enable_inc_usage (g_btor);
  btor_set_rewrite_level_btor (g_btor, 0);

  array  = btor_array_exp (g_btor, 1, 1, "array1");
  index1 = btor_var_exp (g_btor, 1, "index1");
  index2 = btor_var_exp (g_btor, 1, "index2");
  read1  = btor_read_exp (g_btor, array, index1);
  read2  = btor_read_exp (g_btor, array, index2);
  eq     = btor_eq_exp (g_btor, index1, index2);
  ne     = btor_ne_exp (g_btor, read1, read2);

  btor_assert_exp (g_btor, eq);
  btor_assume_exp (g_btor, ne);
  sat_result = btor_sat_btor (g_btor);
  assert (sat_result == BTOR_UNSAT);
  assert (btor_failed_exp (g_btor, ne));

  sat_result = btor_sat_btor (g_btor);
  assert (sat_result == BTOR_SAT);

  btor_release_exp (g_btor, array);
  btor_release_exp (g_btor, index1);
  btor_release_exp (g_btor, index2);
  btor_release_exp (g_btor, read1);
  btor_release_exp (g_btor, read2);
  btor_release_exp (g_btor, eq);
  btor_release_exp (g_btor, ne);
  btor_delete_btor (g_btor);
}

void
init_inc_tests (void)
{
}

void
run_inc_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (inc_true_false);
  BTOR_RUN_TEST (inc_count1);
  BTOR_RUN_TEST (inc_count2);
  BTOR_RUN_TEST (inc_count3);
  BTOR_RUN_TEST (inc_count4);
  BTOR_RUN_TEST (inc_count8);
  BTOR_RUN_TEST (inc_count1nondet);
  BTOR_RUN_TEST (inc_count2nondet);
  BTOR_RUN_TEST (inc_count3nondet);
  BTOR_RUN_TEST (inc_count4nondet);
  BTOR_RUN_TEST (inc_count8nondet);
  BTOR_RUN_TEST (inc_lt1);
  BTOR_RUN_TEST (inc_lt2);
  BTOR_RUN_TEST (inc_lt3);
  BTOR_RUN_TEST (inc_lt4);
  BTOR_RUN_TEST (inc_lt8);
  BTOR_RUN_TEST (inc_assume_assert1);
  BTOR_RUN_TEST (inc_lemmas_on_demand_1);
}

void
finish_inc_tests (void)
{
}
