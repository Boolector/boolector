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
test_inc_counter (int w)
{
  BtorExp *current, *next, *nonzero, *allzero, *one;
  BtorExpMgr* mgr;
  int i, res;

  assert (w > 0);

  mgr     = btor_new_exp_mgr (2, 0, 0, 0);
  one     = btor_one_exp (mgr, w);
  current = btor_zeros_exp (mgr, w);
  i       = 0;

  for (;;)
  {
    next = btor_add_exp (mgr, current, one);
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
  return test_inc_counter (1);
}

static void
test_inc_count2 (void)
{
  return test_inc_counter (2);
}

static void
test_inc_count3 (void)
{
  return test_inc_counter (3);
}

static void
test_inc_count4 (void)
{
  return test_inc_counter (4);
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
}

void
finish_inc_tests (void)
{
}
