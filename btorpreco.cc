/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010-2011 Armin Biere, FMV, JKU.
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

#ifdef BTOR_USE_PRECOSAT
#include "../precosat/precobnr.hh"
#include "../precosat/precosat.hh"
extern "C" {

#include "btorpreco.h"
#include "btorsat.h"

using namespace PrecoSat;

static int
btor_precosat_lsbsign_lit (int lit)
{
  return 2 * abs (lit) + (lit < 0);
}

const char*
btor_precosat_version (void)
{
  return precosat_version ();
}

void*
btor_precosat_init (BtorSATMgr* smgr)
{
  Solver* solver;

  btor_msg_sat (smgr, 1, "PrecoSAT Version %s\n", btor_precosat_version ());
  solver = new Solver;
  solver->set (btor_mem_mgr_sat (smgr),
               (Mem::NewFun) btor_malloc,
               (Mem::DeleteFun) btor_free,
               (Mem::ResizeFun) btor_realloc);
  solver->init ();
  solver->fxopts ();

  return solver;
}

int
btor_precosat_add (BtorSATMgr* smgr, int lit)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  solver->add (btor_precosat_lsbsign_lit (lit));
  return solver->getAddedOrigClauses ();
}

int
btor_precosat_sat (BtorSATMgr* smgr)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  int res;

  res = solver->solve ();
  if (res < 0)
    res = 20;
  else if (res > 0)
    res = 10;
  else
    assert (!res);
  return res;
}

int
btor_precosat_deref (BtorSATMgr* smgr, int lit)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  return solver->val (btor_precosat_lsbsign_lit (lit));
}

void
btor_precosat_reset (BtorSATMgr* smgr)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  solver->reset ();
  delete solver;
}

void
btor_precosat_set_output (BtorSATMgr* smgr, FILE* file)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  solver->set (file);
}

void
btor_precosat_set_prefix (BtorSATMgr* smgr, const char* newprfx)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  solver->setprfx (newprfx);
}

void
btor_precosat_enable_verbosity (BtorSATMgr* smgr)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  bool res;
  res = solver->set ("verbose", 1);
  assert (res);
}

int
btor_precosat_inc_max_var (BtorSATMgr* smgr)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  return solver->next ();
}

int
btor_precosat_variables (BtorSATMgr* smgr)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  return solver->getMaxVar ();
}

void
btor_precosat_stats (BtorSATMgr* smgr)
{
  Solver* solver = (Solver*) btor_get_solver_sat (smgr);
  solver->prstats ();
}
};
#endif
