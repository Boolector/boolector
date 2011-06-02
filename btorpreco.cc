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

static void *(*new_for_precosat) (void *, size_t);
static void (*delete_for_precosat) (void *, void *, size_t);
static void *(*resize_for_precosat) (void *, void *, size_t, size_t);

static int
btor_precosat_lsbsign_lit (int lit)
{
  return 2 * abs (lit) + (lit < 0);
}

const char *
btor_precosat_version (void)
{
  return precosat_version ();
}

void *
btor_precosat_init (BtorSATMgr *smgr)
{
  Solver *solver = new Solver;

  solver->set (btor_mem_mgr_sat (smgr),
               new_for_precosat,
               delete_for_precosat,
               resize_for_precosat);
  solver->init ();
  solver->fxopts ();

  return solver;
}

int
btor_precosat_add (void *ptr, int lit)
{
  Solver *solver = (Solver *) ptr;
  solver->add (btor_precosat_lsbsign_lit (lit));
  return solver->getAddedOrigClauses ();
}

int
btor_precosat_sat (void *ptr)
{
  Solver *solver = (Solver *) ptr;
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
btor_precosat_deref (void *ptr, int lit)
{
  Solver *solver = (Solver *) ptr;
  return solver->val (btor_precosat_lsbsign_lit (lit));
}

void
btor_precosat_reset (void *ptr)
{
  Solver *solver   = (Solver *) ptr;
  new_for_precosat = 0;
  solver->reset ();
  delete solver;
}

void
btor_precosat_set_output (void *ptr, FILE *file)
{
  Solver *solver = (Solver *) ptr;
  solver->set (file);
}

void
btor_precosat_set_prefix (void *ptr, const char *newprfx)
{
  Solver *solver = (Solver *) ptr;
  solver->setprfx (newprfx);
}

void
btor_precosat_enable_verbosity (void *ptr)
{
  Solver *solver = (Solver *) ptr;
  bool res;
  res = solver->set ("verbose", 1);
  assert (res);
}

int
btor_precosat_inc_max_var (void *ptr)
{
  Solver *solver = (Solver *) ptr;
  return solver->next ();
}

int
btor_precosat_variables (void *ptr)
{
  Solver *solver = (Solver *) ptr;
  return solver->getMaxVar ();
}

int
btor_precosat_added_original_clauses (void *ptr)
{
  Solver *solver = (Solver *) ptr;
  return solver->getAddedOrigClauses ();
}

void
btor_precosat_stats (void *ptr)
{
  Solver *solver = (Solver *) ptr;
  solver->prstats ();
}
};
#endif
