/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2014 Armin Biere.
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef BTOR_USE_MINISAT

#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS
#endif

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include "../minisat/minisat/simp/SimpSolver.h"

#include <cassert>
#include <cstdio>
#include <cstring>

extern "C" {

#include "btorminisat.h"
#include "btoropt.h"
#include "btorsat.h"

using namespace Minisat;

class BtorMiniSAT : public SimpSolver
{
  vec<Lit> assumptions, clause;
  int szfmap;
  signed char *fmap;
  bool nomodel;
  Lit import (int lit)
  {
    assert (0 < abs (lit) && abs (lit) <= nVars ());
    return mkLit (Var (abs (lit) - 1), (lit < 0));
  }
  void reset ()
  {
    if (fmap) delete[] fmap, fmap = 0, szfmap = 0;
  }
  void ana ()
  {
    fmap = new signed char[szfmap = nVars ()];
    memset (fmap, 0, szfmap);
    for (int i = 0; i < conflict.size (); i++)
    {
      int tmp = var (conflict[i]);
      assert (0 <= tmp && tmp < szfmap);
      fmap[tmp] = 1;
    }
  }

 public:
  BtorMiniSAT () : szfmap (0), fmap (0), nomodel (true) {}
  ~BtorMiniSAT () { reset (); }
  int inc ()
  {
    nomodel = true;
    int res = newVar ();
    assert (0 <= res && res == nVars () - 1);
    return res + 1;
  }
  void assume (int lit)
  {
    nomodel = true;
    assumptions.push (import (lit));
  }
  void add (int lit)
  {
    nomodel = true;
    if (lit)
      clause.push (import (lit));
    else
      addClause (clause), clause.clear ();
  }
  unsigned long long calls;
  int sat (bool simp)
  {
    calls++;
    reset ();
    lbool res = solveLimited (assumptions, simp);
    assumptions.clear ();
    nomodel = res != l_True;
    return res == l_Undef ? 0 : (res == l_True ? 10 : 20);
  }
  int failed (int lit)
  {
    if (!fmap) ana ();
    int tmp = var (import (lit));
    assert (0 <= tmp && tmp < nVars ());
    return fmap[tmp];
  }
  int fixed (int lit)
  {
    Var v   = var (import (lit));
    int idx = v, res;
    assert (0 <= idx && idx < nVars ());
    lbool val = assigns[idx];
    if (val == l_Undef || level (v))
      res = 0;
    else
      res = (val == l_True) ? 1 : -1;
    if (lit < 0) res = -res;
    return res;
  }
  int deref (int lit)
  {
    if (nomodel) return fixed (lit);
    lbool res = modelValue (import (lit));
    return (res == l_True) ? 1 : -1;
  }
};

void *
btor_minisat_init (BtorSATMgr *smgr)
{
  BtorMiniSAT *res = new BtorMiniSAT ();
  if (btor_get_opt (smgr->msg->btor, BTOR_OPT_VERBOSITY) >= 2)
    res->verbosity = btor_get_opt (smgr->msg->btor, BTOR_OPT_VERBOSITY) - 1;
  return res;
}

const char *
btor_minisat_version (void)
{
  return "unknown";
}

void
btor_minisat_add (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  solver->add (lit);
}

int
btor_minisat_sat (BtorSATMgr *smgr, int limit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  if (limit < 0)
    solver->budgetOff ();
  else
    solver->setConfBudget (limit);
  return solver->sat (!smgr->inc_required);
}

int
btor_minisat_deref (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  return solver->deref (lit);
}

int
btor_minisat_repr (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  return lit;
}

void
btor_minisat_reset (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  delete solver;
}

int
btor_minisat_inc_max_var (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  return solver->inc ();
}

int
btor_minisat_variables (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  return solver->nVars ();
}

void
btor_minisat_assume (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  solver->assume (lit);
}

int
btor_minisat_fixed (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  return solver->fixed (lit);
}

int
btor_minisat_failed (BtorSATMgr *smgr, int lit)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  return solver->failed (lit);
}

void
btor_minisat_set_output (BtorSATMgr *, FILE *)
{
}

void
btor_minisat_set_prefix (BtorSATMgr *, const char *)
{
}

void
btor_minisat_enable_verbosity (BtorSATMgr *smgr, int level)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  if (solver->verbosity >= 0)
    solver->verbosity = level;
  else
    solver->verbosity = 0;
}

void
btor_minisat_stats (BtorSATMgr *smgr)
{
  BtorMiniSAT *solver = (BtorMiniSAT *) BTOR_GET_SOLVER_SAT (smgr);
  printf (
      "[minisat] calls %llu\n"
      "[minisat] restarts %llu\n"
      "[minisat] conflicts %llu\n"
      "[minisat] decisions %llu\n"
      "[minisat] propagations %llu\n",
      (unsigned long long) solver->calls,
      (unsigned long long) solver->starts,
      (unsigned long long) solver->conflicts,
      (unsigned long long) solver->decisions,
      (unsigned long long) solver->propagations);
  fflush (stdout);
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
