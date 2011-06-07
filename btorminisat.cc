/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011 Armin Biere, FMV, JKU.
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

#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS
#endif

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include "minisat/simp/SimpSolver.h"

extern "C" {

#include "btorminisat.h"
#include "btorsat.h"

#include <cassert>
#include <cstring>

using namespace Minisat;

class BtorMiniSAT : public SimpSolver
{
  vec<Lit> assumptions, clause;
  int szmap;
  unsigned char *map;
  Lit import (int lit)
  {
    assert (0 < abs (lit) && abs (lit) <= nVars ());
    return mkLit (Var (abs (lit) - 1), (lit < 0));
  }
  void reset ()
  {
    if (map) delete[] map, map = 0, szmap = 0;
  }
  void ana ()
  {
    map = new unsigned char[nVars ()];
    memset (map, 0, nVars ());
    for (int i = 0; i < conflict.size (); i++)
    {
      int tmp = var (conflict[i]);
      assert (0 <= tmp && tmp < nVars ());
      map[tmp] = 1;
    }
  }

 public:
  BtorMiniSAT () : szmap (0), map (0) {}
  ~BtorMiniSAT () { reset (); }
  int inc ()
  {
    int res = newVar ();
    assert (res == nVars ());
    return res + 1;
  }
  void assume (int lit) { assumptions.push (import (lit)); }
  void add (int lit)
  {
    if (lit)
      clause.push (import (lit));
    else
      addClause (clause), clause.clear ();
  }
  int sat ()
  {
    reset ();
    bool res = solve (assumptions);
    assumptions.clear ();
    return res ? 10 : 20;
  }
  int failed (int lit)
  {
    if (!map) ana ();
    int tmp = var (import (lit));
    assert (0 <= tmp && tmp < nVars ());
    return map[tmp];
  }
};

void *
btor_minisat_init (BtorSATMgr *)
{
  return new BtorMiniSAT ();
}

const char *
btor_minisat_version (void)
{
  return "unknown";
}

void
btor_minisat_add (BtorSATMgr *smgr, int)
{
}

int
btor_minisat_sat (BtorSATMgr *smgr)
{
}

int
btor_minisat_deref (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) btor_get_solver_sat (smgr);
  return 1;
}

void
btor_minisat_reset (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) btor_get_solver_sat (smgr);
  delete solver;
}

void
btor_minisat_set_output (BtorSATMgr *smgr, FILE *file)
{
  (void) smgr;
  (void) file;
}

void
btor_minisat_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  (void) smgr;
  (void) prefix;
}

void
btor_minisat_enable_verbosity (BtorSATMgr *smgr)
{
  (void) smgr;
}

int
btor_minisat_inc_max_var (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) btor_get_solver_sat (smgr);
  return solver->inc ();
}

int
btor_minisat_variables (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) btor_get_solver_sat (smgr);
  return solver->nVars ();
}

void
btor_minisat_stats (BtorSATMgr *smgr)
{
  (void) smgr;
}

void
btor_minisat_assume (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) btor_get_solver_sat (smgr);
  solver->assume (lit);
}

int
btor_minisat_failed (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) btor_get_solver_sat (smgr);
  return solver->failed (lit);
}

int
btor_minisat_fixed (BtorSATMgr *, int)
{
  return 0;
}

int
btor_minisat_changed (BtorSATMgr *)
{
  return 1;
}

int
btor_minisat_inconsistent (BtorSATMgr *)
{
  return 0;
}
};

#endif
