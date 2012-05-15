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

#include "testaig.h"
#include "btoraig.h"
#include "btormem.h"
#include "btorsat.h"
#include "testrunner.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <stdio.h>

static BtorMemMgr *g_mm;

void
init_aig_tests (void)
{
  g_mm = btor_new_mem_mgr ();
}

static void
test_new_delete_aig_mgr (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  btor_delete_aig_mgr (amgr);
}

static void
test_false_aig (void)
{
  FILE *fout       = fopen ("log/false_aig.log", "w");
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  btor_dump_aig (amgr, 0, fout, BTOR_AIG_FALSE);
  btor_delete_aig_mgr (amgr);
  fclose (fout);
}

static void
test_true_aig (void)
{
  FILE *fout       = fopen ("log/true_aig.log", "w");
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  btor_dump_aig (amgr, 0, fout, BTOR_AIG_TRUE);
  btor_delete_aig_mgr (amgr);
  fclose (fout);
}

static void
test_var_aig (void)
{
  FILE *fout       = fopen ("log/var_aig.log", "w");
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  BtorAIG *var     = btor_var_aig (amgr);
  assert (BTOR_IS_VAR_AIG (var));
  btor_dump_aig (amgr, 0, fout, var);
  btor_release_aig (amgr, var);
  btor_delete_aig_mgr (amgr);
  fclose (fout);
}

static void
test_not_aig (void)
{
  FILE *fout       = fopen ("log/not_aig.log", "w");
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  BtorAIG *var     = btor_var_aig (amgr);
  BtorAIG *not     = btor_not_aig (amgr, var);
  btor_dump_aig (amgr, 0, fout, not);
  btor_release_aig (amgr, var);
  btor_release_aig (amgr, not);
  btor_delete_aig_mgr (amgr);
  fclose (fout);
}

static void
binary_commutative_aig_test (
    BtorAIG *(*func) (BtorAIGMgr *, BtorAIG *, BtorAIG *), char *log)
{
  FILE *fout       = fopen (log, "w");
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  BtorAIG *aig1    = btor_var_aig (amgr);
  BtorAIG *aig2    = btor_var_aig (amgr);
  BtorAIG *aig3    = func (amgr, aig1, aig2);
  BtorAIG *aig4    = func (amgr, aig1, aig2);
  BtorAIG *aig5    = func (amgr, aig2, aig1);
  assert (aig3 == aig4);
  assert (aig4 == aig5);
  btor_dump_aig (amgr, 0, fout, aig5);
  btor_release_aig (amgr, aig1);
  btor_release_aig (amgr, aig2);
  btor_release_aig (amgr, aig3);
  btor_release_aig (amgr, aig4);
  btor_release_aig (amgr, aig5);
  btor_delete_aig_mgr (amgr);
  fclose (fout);
}

static void
test_and_aig (void)
{
  binary_commutative_aig_test (btor_and_aig, "log/and_aig.log");
}

static void
test_or_aig (void)
{
  binary_commutative_aig_test (btor_or_aig, "log/or_aig.log");
}

static void
test_eq_aig (void)
{
  binary_commutative_aig_test (btor_eq_aig, "log/eq_aig.log");
}

static void
test_cond_aig (void)
{
  FILE *fout       = fopen ("log/cond_aig.log", "w");
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  BtorAIG *aig1    = btor_var_aig (amgr);
  BtorAIG *aig2    = btor_var_aig (amgr);
  BtorAIG *aig3    = btor_var_aig (amgr);
  BtorAIG *aig4    = btor_cond_aig (amgr, aig1, aig2, aig3);
  BtorAIG *aig5    = btor_cond_aig (amgr, aig1, aig2, aig3);
  assert (aig4 == aig5);
  btor_dump_aig (amgr, 0, fout, aig5);
  btor_release_aig (amgr, aig1);
  btor_release_aig (amgr, aig2);
  btor_release_aig (amgr, aig3);
  btor_release_aig (amgr, aig4);
  btor_release_aig (amgr, aig5);
  btor_delete_aig_mgr (amgr);
  fclose (fout);
}

static void
test_aig_to_sat (void)
{
  BtorAIGMgr *amgr = btor_new_aig_mgr (g_mm);
  BtorSATMgr *smgr = btor_get_sat_mgr_aig_mgr (amgr);
  BtorAIG *var1    = btor_var_aig (amgr);
  BtorAIG *var2    = btor_var_aig (amgr);
  BtorAIG *var3    = btor_var_aig (amgr);
  BtorAIG *var4    = btor_var_aig (amgr);
  BtorAIG *and1    = btor_and_aig (amgr, var1, var2);
  BtorAIG *and2    = btor_and_aig (amgr, var3, var4);
  BtorAIG *and3    = btor_or_aig (amgr, and1, and2);
  btor_init_sat (smgr);
  btor_aig_to_sat (amgr, and3);
  btor_reset_sat (smgr);
  btor_release_aig (amgr, var1);
  btor_release_aig (amgr, var2);
  btor_release_aig (amgr, var3);
  btor_release_aig (amgr, var4);
  btor_release_aig (amgr, and1);
  btor_release_aig (amgr, and2);
  btor_release_aig (amgr, and3);
  btor_delete_aig_mgr (amgr);
}

void
run_aig_tests (int argc, char **argv)
{
  BTOR_RUN_TEST (new_delete_aig_mgr);
  BTOR_RUN_TEST_CHECK_LOG (false_aig);
  BTOR_RUN_TEST_CHECK_LOG (true_aig);
  BTOR_RUN_TEST_CHECK_LOG (var_aig);
  BTOR_RUN_TEST_CHECK_LOG (not_aig);
  BTOR_RUN_TEST_CHECK_LOG (and_aig);
  BTOR_RUN_TEST_CHECK_LOG (or_aig);
  BTOR_RUN_TEST_CHECK_LOG (eq_aig);
  BTOR_RUN_TEST_CHECK_LOG (cond_aig);
  BTOR_RUN_TEST (aig_to_sat);
}

void
finish_aig_tests (void)
{
  btor_delete_mem_mgr (g_mm);
}
