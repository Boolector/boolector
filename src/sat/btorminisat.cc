/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2014 Armin Biere.
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
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

#include "btorabort.h"
#include "btorsat.h"
#include "sat/btorminisat.h"

using namespace Minisat;

/*------------------------------------------------------------------------*/

class BtorMiniSAT : public SimpSolver
{
  vec<Lit> assumptions, clause;
  int szfmap;
  signed char* fmap;
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

/*------------------------------------------------------------------------*/

static void*
init (BtorSATMgr* smgr)
{
  (void) smgr;
  BtorMiniSAT* res = new BtorMiniSAT ();
  return res;
}

static void
add (BtorSATMgr* smgr, int lit)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  solver->add (lit);
}

static int
sat (BtorSATMgr* smgr, int limit)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  if (limit < 0)
    solver->budgetOff ();
  else
    solver->setConfBudget (limit);
  return solver->sat (!smgr->inc_required);
}

static int
deref (BtorSATMgr* smgr, int lit)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  return solver->deref (lit);
}

static void
reset (BtorSATMgr* smgr)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  delete solver;
}

static int
inc_max_var (BtorSATMgr* smgr)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  return solver->inc ();
}

static void
assume (BtorSATMgr* smgr, int lit)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  solver->assume (lit);
}

static int
fixed (BtorSATMgr* smgr, int lit)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  return solver->fixed (lit);
}

static int
failed (BtorSATMgr* smgr, int lit)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
  return solver->failed (lit);
}

static void
enable_verbosity (BtorSATMgr* smgr, int level)
{
  (void) smgr;
  if (level >= 2) ((BtorMiniSAT*) smgr->solver)->verbosity = level - 1;
}

static void
stats (BtorSATMgr* smgr)
{
  BtorMiniSAT* solver = (BtorMiniSAT*) smgr;
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

/*------------------------------------------------------------------------*/

bool
btor_sat_enable_minisat (BtorSATMgr* smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_minisat'");

  smgr->name = "MiniSAT";

  BTOR_CLR (&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
  smgr->api.inc_max_var      = inc_max_var;
  smgr->api.init             = init;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = 0;
  smgr->api.set_prefix       = 0;
  smgr->api.stats            = stats;
  return true;
}
};
#endif
