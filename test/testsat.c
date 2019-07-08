/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testsat.h"
#include "btorcore.h"
#include "btorsat.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static Btor *g_btor;
static BtorMemMgr *g_mm;
static BtorMsg *g_msg;

void
init_sat_tests (void)
{
  g_btor = btor_new ();
  g_mm   = g_btor->mm;
  g_msg  = g_btor->msg;
}

static void
test_new_delete_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_sat_mgr_new (g_btor);
  btor_sat_mgr_delete (smgr);
}

static void
test_next_cnf_id_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_sat_mgr_new (g_btor);
  btor_sat_enable_solver (smgr);
  btor_sat_init (smgr);
  assert (btor_sat_mgr_next_cnf_id (smgr) == 2);
  assert (btor_sat_mgr_next_cnf_id (smgr) == 3);
  assert (btor_sat_mgr_next_cnf_id (smgr) == 4);
  btor_sat_reset (smgr);
  btor_sat_mgr_delete (smgr);
}

void
run_sat_tests (int32_t argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_sat_mgr);
  BTOR_RUN_TEST (next_cnf_id_sat_mgr);
}

void
finish_sat_tests (void)
{
  btor_delete (g_btor);
}
