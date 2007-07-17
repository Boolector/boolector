#include "testsat.h"
#include "btormem.h"
#include "btorsat.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *g_mm;

void
init_sat_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_new_delete_cnf_mgr (void)
{
  BtorCNFMgr *cmgr = btor_new_cnf_mgr (g_mm);
  btor_delete_cnf_mgr (cmgr);
}

static void
test_next_cnf_id_cnf_mgr (void)
{
  BtorCNFMgr *cmgr = btor_new_cnf_mgr (g_mm);
  assert (btor_next_cnf_id_cnf_mgr (cmgr) == 1);
  assert (btor_next_cnf_id_cnf_mgr (cmgr) == 2);
  assert (btor_next_cnf_id_cnf_mgr (cmgr) == 3);
  btor_delete_cnf_mgr (cmgr);
}

void
run_sat_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_cnf_mgr);
  BTOR_RUN_TEST (next_cnf_id_cnf_mgr);
}

void
finish_sat_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}
