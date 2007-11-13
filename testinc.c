#include "testinc.h"
#include "boolector.h"
#include "btorexit.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static void
test_inc_true_false (void)
{
  BtorExpMgr* mgr = btor_new_exp_mgr (2, 0, 0, 0);
  BtorExp* ff     = btor_false_exp (mgr);
  BtorExp* tt     = btor_true_exp (mgr);
  int res;

  btor_add_assumption_exp (mgr, tt);
  res = btor_sat_exp (mgr);
  assert (res == BTOR_SAT);

  btor_add_assumption_exp (mgr, ff);
  res = btor_sat_exp (mgr);
  assert (res == BTOR_UNSAT);

  btor_release_exp (mgr, ff);
  btor_release_exp (mgr, tt);
  btor_delete_exp_mgr (mgr);
}

static void
test_inc_counter (int w, int nondet)
{
  BtorExp *nonzero, *allzero, *one, *oracle;
  BtorExp *current, *next, *inc;
  BtorExpMgr* mgr;
  char name[100];
  int i, res;

  assert (w > 0);

  mgr     = btor_new_exp_mgr (2, 0, 0, 0);
  one     = btor_one_exp (mgr, w);
  current = btor_zeros_exp (mgr, w);
  i       = 0;

  for (;;)
  {
    inc = btor_add_exp (mgr, current, one);

    if (nondet)
    {
      sprintf (name, "oracle%d", i);
      if (i)
        oracle = btor_var_exp (mgr, 1, name);
      else
        oracle = btor_true_exp (mgr);
      next = btor_cond_exp (mgr, oracle, inc, current);
      btor_release_exp (mgr, oracle);
    }
    else
      next = btor_copy_exp (mgr, inc);

    btor_release_exp (mgr, inc);
    btor_release_exp (mgr, current);
    current = next;

    nonzero = btor_redor_exp (mgr, current);
    allzero = btor_not_exp (mgr, nonzero);
    btor_release_exp (mgr, nonzero);

    i++;

    btor_add_assumption_exp (mgr, allzero);
    btor_release_exp (mgr, allzero);

    res = btor_sat_exp (mgr);
    if (res == BTOR_SAT) break;

    assert (res == BTOR_UNSAT);
    assert (i < (1 << w));
  }

  assert (i == (1 << w));

  btor_release_exp (mgr, one);
  btor_release_exp (mgr, current);

  btor_delete_exp_mgr (mgr);
}

static void
test_inc_count1 (void)
{
  return test_inc_counter (1, 0);
}

static void
test_inc_count2 (void)
{
  return test_inc_counter (2, 0);
}

static void
test_inc_count3 (void)
{
  return test_inc_counter (3, 0);
}

static void
test_inc_count4 (void)
{
  return test_inc_counter (4, 0);
}

static void
test_inc_count8 (void)
{
  return test_inc_counter (8, 0);
}

static void
test_inc_count1nondet (void)
{
  return test_inc_counter (1, 1);
}

static void
test_inc_count2nondet (void)
{
  return test_inc_counter (2, 1);
}

static void
test_inc_count3nondet (void)
{
  return test_inc_counter (3, 1);
}

static void
test_inc_count4nondet (void)
{
  return test_inc_counter (4, 1);
}

static void
test_inc_count8nondet (void)
{
  return test_inc_counter (8, 1);
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
}

void
finish_inc_tests (void)
{
}
