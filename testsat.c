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
test_new_delete_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_new_sat_mgr (g_mm, 0);
  btor_delete_sat_mgr (smgr);
}

static void
test_next_cnf_id_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_new_sat_mgr (g_mm, 0);
  btor_init_sat (smgr);
  assert (btor_next_cnf_id_sat_mgr (smgr) == 1);
  assert (btor_next_cnf_id_sat_mgr (smgr) == 2);
  assert (btor_next_cnf_id_sat_mgr (smgr) == 3);
  btor_reset_sat (smgr);
  btor_delete_sat_mgr (smgr);
}

void
run_sat_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_sat_mgr);
  BTOR_RUN_TEST (next_cnf_id_sat_mgr);
}

void
finish_sat_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}
