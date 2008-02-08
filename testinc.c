#include "testinc.h"
#include "boolector.h"
#include "btorexit.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <limits.h>

static void
test_inc_true_false (void)
{
  Btor* btor  = btor_new_btor ();
  BtorExp* ff = btor_false_exp (btor);
  BtorExp* tt = btor_true_exp (btor);
  int res;

  btor_add_assumption_exp (btor, tt);
  res = btor_sat_btor (btor, INT_MAX);
  assert (res == BTOR_SAT);

  btor_add_assumption_exp (btor, ff);
  res = btor_sat_btor (btor, INT_MAX);
  assert (res == BTOR_UNSAT);

  btor_release_exp (btor, ff);
  btor_release_exp (btor, tt);
  btor_delete_btor (btor);
}

static void
test_inc_counter (int w, int nondet)
{
  BtorExp *nonzero, *allzero, *one, *oracle;
  BtorExp *current, *next, *inc;
  Btor* btor;
  char name[100];
  int i, res;

  assert (w > 0);

  btor    = btor_new_btor ();
  one     = btor_one_exp (btor, w);
  current = btor_zeros_exp (btor, w);
  i       = 0;

  for (;;)
  {
    inc = btor_add_exp (btor, current, one);

    if (nondet)
    {
      sprintf (name, "oracle%d", i);
      if (i)
        oracle = btor_var_exp (btor, 1, name);
      else
        oracle = btor_true_exp (btor);
      next = btor_cond_exp (btor, oracle, inc, current);
      btor_release_exp (btor, oracle);
    }
    else
      next = btor_copy_exp (btor, inc);

    btor_release_exp (btor, inc);
    btor_release_exp (btor, current);
    current = next;

    nonzero = btor_redor_exp (btor, current);
    allzero = btor_not_exp (btor, nonzero);
    btor_release_exp (btor, nonzero);

    i++;

    btor_add_assumption_exp (btor, allzero);
    btor_release_exp (btor, allzero);

    res = btor_sat_btor (btor, INT_MAX);
    if (res == BTOR_SAT) break;

    assert (res == BTOR_UNSAT);
    assert (i < (1 << w));
  }

  assert (i == (1 << w));

  btor_release_exp (btor, one);
  btor_release_exp (btor, current);

  btor_delete_btor (btor);
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
  BtorExp *prev, *next, *lt;
  Btor* btor;
  char name[100];
  int i, res;

  assert (w > 0);

  btor = btor_new_btor ();

  i    = 0;
  prev = 0;
  for (;;)
  {
    i++;

    sprintf (name, "%d", i);
    next = btor_var_exp (btor, w, name);

    if (prev)
    {
      lt = btor_ult_exp (btor, prev, next);
      btor_add_constraint_exp (btor, lt);
      btor_release_exp (btor, lt);
      btor_release_exp (btor, prev);
    }

    prev = next;

    res = btor_sat_btor (btor, INT_MAX);
    if (res == BTOR_UNSAT) break;

    assert (res == BTOR_SAT);
    assert (i <= (1 << w));
  }

  assert (i == (1 << w) + 1);

  btor_release_exp (btor, prev);
  btor_delete_btor (btor);
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

void
init_inc_tests (void)
{
}

void
run_inc_tests (int argc, char** argv)
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
}

void
finish_inc_tests (void)
{
}
