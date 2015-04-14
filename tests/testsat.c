/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "testsat.h"
#include "btorsat.h"
#include "testrunner.h"
#include "utils/btormem.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

static BtorMemMgr *g_mm;
static BtorMsg *g_msg;
static int g_verbosity;

void
init_sat_tests (void)
{
  g_mm  = btor_new_mem_mgr ();
  g_msg = btor_new_btor_msg (g_mm, &g_verbosity);
}

static void
test_new_delete_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_new_sat_mgr (g_mm, g_msg);
  btor_delete_sat_mgr (smgr);
}

static void
test_next_cnf_id_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_new_sat_mgr (g_mm, g_msg);
  btor_init_sat (smgr);
  assert (btor_next_cnf_id_sat_mgr (smgr) == 2);
  assert (btor_next_cnf_id_sat_mgr (smgr) == 3);
  assert (btor_next_cnf_id_sat_mgr (smgr) == 4);
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
  btor_delete_btor_msg (g_msg);
  btor_delete_mem_mgr (g_mm);
}
