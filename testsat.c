/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2010  Robert Daniel Brummayer, Armin Biere
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
  BtorSATMgr *smgr = btor_new_sat_mgr (g_mm);
  btor_delete_sat_mgr (smgr);
}

static void
test_next_cnf_id_sat_mgr (void)
{
  BtorSATMgr *smgr = btor_new_sat_mgr (g_mm);
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
  btor_delete_mem_mgr (g_mm);
}
