/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef BTOR_USE_CMS

#include "cryptominisat5/cryptominisat.h"

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstring>
#include <vector>

extern "C" {

#include "btorabort.h"
#include "btorsat.h"
#include "btoropt.h"
#include "sat/btorcms.h"

using namespace CMSat;

/*------------------------------------------------------------------------*/

class BtorCMS : public SATSolver
{
  uint32_t size;
  std::vector<Lit> assumptions, clause;
  signed char* failed_map;
  int32_t* assigned_map;
  bool nomodel;

  Lit import (int32_t lit)
  {
    assert (0 < abs (lit) && ((uint32_t) abs (lit)) <= nVars ());
    return Lit (abs (lit) - 1, lit < 0);
  }

  void reset ()
  {
    if (failed_map) delete[] failed_map, failed_map = 0;
    if (assigned_map) delete[] assigned_map, assigned_map = 0;
    size = 0;
  }

  void analyze_failed ()
  {
    uint32_t nvars = nVars ();
    failed_map     = new signed char[nvars];
    memset (failed_map, 0, nvars);
    const std::vector<Lit>& conflict = get_conflict ();
    for (size_t i = 0; i < conflict.size (); i++)
    {
      uint32_t v = conflict[i].var ();
      assert (v < nvars);
      failed_map[v] = 1;
    }
  }

  void analyze_fixed ()
  {
    assert (!assigned_map);
    assert (!size);
    size         = nVars ();
    assigned_map = new int32_t[size];
    memset (assigned_map, 0, sizeof(int32_t) * size);
    const std::vector<Lit> assigned_lits = get_zero_assigned_lits ();
    for (size_t i = 0; i < assigned_lits.size (); i++)
    {
      Lit l      = assigned_lits[i];
      uint32_t v = l.var ();
      assert (v < size);
      assigned_map[v] = l.sign () ? -1 : 1;
    }
  }

 public:
  BtorCMS () : size (0), failed_map (0), assigned_map (0), nomodel (true) {}

  ~BtorCMS () { reset (); }

  int32_t inc ()
  {
    nomodel = true;
    new_var ();
    return nVars ();
  }

  void assume (int32_t lit)
  {
    nomodel = true;
    assumptions.push_back (import (lit));
  }

  void add (int32_t lit)
  {
    nomodel = true;
    if (lit)
      clause.push_back (import (lit));
    else
      add_clause (clause), clause.clear ();
  }

  int32_t sat ()
  {
    calls++;
    reset ();
    lbool res = solve (&assumptions);
    analyze_fixed ();
    conflicts += get_last_conflicts ();
    decisions += get_last_decisions ();
    propagations += get_last_propagations ();
    assumptions.clear ();
    nomodel = res != l_True;
    return res == l_Undef ? 0 : (res == l_True ? 10 : 20);
  }

  int32_t failed (int32_t lit)
  {
    if (!failed_map) analyze_failed ();
    Lit l      = import (lit);
    uint32_t v = l.var ();
    assert (v < nVars ());
    return failed_map[v];
  }

  int32_t fixed (int32_t lit)
  {
    Lit l      = import (lit);
    uint32_t v = l.var ();
    if (v >= size) return 0;
    return l.sign () ? -assigned_map[v] : assigned_map[v];
  }

  int32_t deref (int32_t lit)
  {
    if (nomodel) return fixed (lit);
    const std::vector<lbool>& model = get_model ();
    Lit l                           = import (lit);
    uint32_t v                      = l.var ();
    assert (v < model.size ());
    int32_t res = model[l.var ()] == l_True ? 1 : -1;
    return l.sign () ? -res : res;
  }

  uint64_t calls, conflicts, decisions, propagations;
};

/*------------------------------------------------------------------------*/

static void*
init (BtorSATMgr* smgr)
{
  (void) smgr;
  uint32_t nthreads;
  BtorCMS* res = new BtorCMS ();
  if ((nthreads = btor_opt_get(smgr->btor, BTOR_OPT_SAT_ENGINE_N_THREADS)) > 1)
    res->set_num_threads(nthreads);
  return res;
}

static void
add (BtorSATMgr* smgr, int32_t lit)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  solver->add (lit);
}

static int32_t
sat (BtorSATMgr* smgr, int32_t limit)
{
  (void) limit;
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  return solver->sat ();
}

static int32_t
deref (BtorSATMgr* smgr, int32_t lit)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  return solver->deref (lit);
}

static void
reset (BtorSATMgr* smgr)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  delete solver;
}

static int32_t
inc_max_var (BtorSATMgr* smgr)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  return solver->inc ();
}

static void
assume (BtorSATMgr* smgr, int32_t lit)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  solver->assume (lit);
}

static int32_t
fixed (BtorSATMgr* smgr, int32_t lit)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  return solver->fixed (lit);
}

static int32_t
failed (BtorSATMgr* smgr, int32_t lit)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  return solver->failed (lit);
}

static void
enable_verbosity (BtorSATMgr* smgr, int32_t level)
{
  (void) smgr;
  if (level >= 2) ((BtorCMS*) smgr->solver)->set_verbosity (level - 1);
}

static void
stats (BtorSATMgr* smgr)
{
  BtorCMS* solver = (BtorCMS*) smgr->solver;
  printf (
      "[cms] calls %llu\n"
      "[cms] conflicts %llu\n"
      "[cms] decisions %llu\n"
      "[cms] propagations %llu\n",
      (unsigned long long) solver->calls,
      (unsigned long long) solver->conflicts,
      (unsigned long long) solver->decisions,
      (unsigned long long) solver->propagations);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

bool
btor_sat_enable_cms (BtorSATMgr* smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_cms'");

  smgr->name = "CryptoMiniSat";

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
