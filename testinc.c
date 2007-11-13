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

void
init_inc_tests (void)
{
}

void
run_inc_tests (int argc, char** argv)
{
  BTOR_RUN_TEST (inc_true_false);
}

void
finish_inc_tests (void)
{
}
