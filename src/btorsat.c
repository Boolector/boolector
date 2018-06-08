/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2018 Mathias Preiner.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsat.h"

#include "sat/btorcadical.h"
#include "sat/btorlgl.h"
#include "sat/btorminisat.h"
#include "sat/btorpicosat.h"

#include "btorabort.h"
#include "btorcore.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/

#if !defined(BTOR_USE_LINGELING) && !defined(BTOR_USE_PICOSAT) \
    && !defined(BTOR_USE_MINISAT) && !defined(BTOR_USE_CADICAL)
#error "no SAT solver configured"
#endif

/*------------------------------------------------------------------------*/
/* wrapper functions for SAT solver API                                   */
/*------------------------------------------------------------------------*/

static inline void
add (BtorSATMgr *smgr, int32_t lit)
{
  assert (smgr->api.add);
  smgr->api.add (smgr, lit);
}

static inline void
assume (BtorSATMgr *smgr, int32_t lit)
{
  BTOR_ABORT (!smgr->api.assume,
              "SAT solver %s does not support 'assume' API call",
              smgr->name);
  smgr->api.assume (smgr, lit);
}

static inline void *
clone (BtorSATMgr *smgr, BtorMemMgr *mm)
{
  BTOR_ABORT (!smgr->api.clone,
              "SAT solver %s does not support 'clone' API call",
              smgr->name);
  return smgr->api.clone (smgr, mm);
}

static inline int32_t
deref (BtorSATMgr *smgr, int32_t lit)
{
  assert (smgr->api.deref);
  return smgr->api.deref (smgr, lit);
}

static inline void
enable_verbosity (BtorSATMgr *smgr, int32_t level)
{
  if (smgr->api.enable_verbosity) smgr->api.enable_verbosity (smgr, level);
}

static inline int32_t
failed (BtorSATMgr *smgr, int32_t lit)
{
  BTOR_ABORT (!smgr->api.failed,
              "SAT solver %s does not support 'failed' API call",
              smgr->name);
  return smgr->api.failed (smgr, lit);
}

static inline int32_t
fixed (BtorSATMgr *smgr, int32_t lit)
{
  if (smgr->api.fixed) return smgr->api.fixed (smgr, lit);
  return 0;
}

static inline int32_t
inc_max_var (BtorSATMgr *smgr)
{
  if (smgr->api.inc_max_var) return smgr->api.inc_max_var (smgr);
  return smgr->maxvar + 1;
}

static inline void *
init (BtorSATMgr *smgr)
{
  assert (smgr->api.init);
  return smgr->api.init (smgr);
}

static inline void
melt (BtorSATMgr *smgr, int32_t lit)
{
  if (smgr->api.melt) smgr->api.melt (smgr, lit);
  // TODO: else case warning?
}

static inline int32_t
repr (BtorSATMgr *smgr, int32_t lit)
{
  if (smgr->api.repr) return smgr->api.repr (smgr, lit);
  return lit;
}

static inline void
reset (BtorSATMgr *smgr)
{
  assert (smgr->api.reset);
  smgr->api.reset (smgr);
}

static inline int32_t
sat (BtorSATMgr *smgr, int32_t limit)
{
  assert (smgr->api.sat);
  return smgr->api.sat (smgr, limit);
}

static inline void
set_output (BtorSATMgr *smgr, FILE *output)
{
  if (smgr->api.set_output) smgr->api.set_output (smgr, output);
}

static inline void
set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  if (smgr->api.set_prefix) smgr->api.set_prefix (smgr, prefix);
}

static inline void
setterm (BtorSATMgr *smgr)
{
  if (smgr->api.setterm) smgr->api.setterm (smgr);
}

static inline void
stats (BtorSATMgr *smgr)
{
  if (smgr->api.stats) smgr->api.stats (smgr);
}

/*------------------------------------------------------------------------*/

BtorSATMgr *
btor_sat_mgr_new (Btor *btor)
{
  assert (btor);

  BtorSATMgr *smgr;

  BTOR_CNEW (btor->mm, smgr);
  smgr->btor   = btor;
  smgr->output = stdout;
  return smgr;
}

bool
btor_sat_mgr_has_clone_support (const BtorSATMgr *smgr)
{
  if (!smgr) return true;
  return smgr->api.clone != 0;
}

bool
btor_sat_mgr_has_incremental_support (const BtorSATMgr *smgr)
{
  if (!smgr) return false;
  return smgr->api.assume != 0 && smgr->api.failed != 0;
}

void
btor_sat_mgr_set_term (BtorSATMgr *smgr, int32_t (*fun) (void *), void *state)
{
  assert (smgr);
  smgr->term.fun   = fun;
  smgr->term.state = state;
}

// FIXME log output handling, in particular: sat manager name output
// (see lingeling_sat) should be unique, which is not the case for
// clones
BtorSATMgr *
btor_sat_mgr_clone (Btor *btor, BtorSATMgr *smgr)
{
  assert (btor);
  assert (smgr);

  BtorSATMgr *res;
  BtorMemMgr *mm;

  BTOR_ABORT (!btor_sat_mgr_has_clone_support (smgr),
              "SAT solver does not support cloning");

  mm = btor->mm;
  BTOR_NEW (mm, res);
  res->solver = clone (smgr, mm);
  res->btor   = btor;
  assert (mm->sat_allocated == smgr->btor->mm->sat_allocated);
  res->name = smgr->name;
  memcpy (&res->inc_required,
          &smgr->inc_required,
          (char *) smgr + sizeof (*smgr) - (char *) &smgr->inc_required);
  BTOR_CLR (&res->term);
  return res;
}

bool
btor_sat_is_initialized (BtorSATMgr *smgr)
{
  assert (smgr);
  return smgr->initialized;
}

int32_t
btor_sat_mgr_next_cnf_id (BtorSATMgr *smgr)
{
  int32_t result;
  assert (smgr);
  assert (smgr->initialized);
  result = inc_max_var (smgr);
  if (abs (result) > smgr->maxvar) smgr->maxvar = abs (result);
  BTOR_ABORT (result <= 0, "CNF id overflow");
  if (btor_opt_get (smgr->btor, BTOR_OPT_VERBOSITY) > 2 && !(result % 100000))
    BTOR_MSG (smgr->btor->msg, 2, "reached CNF id %d", result);
  return result;
}

void
btor_sat_mgr_release_cnf_id (BtorSATMgr *smgr, int32_t lit)
{
  assert (smgr);
  if (!smgr->initialized) return;
  assert (abs (lit) <= smgr->maxvar);
  if (abs (lit) == smgr->true_lit) return;
  melt (smgr, lit);
}

void
btor_sat_mgr_delete (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  /* if SAT is still initialized, then
   * reset_sat has not been called
   */
  if (smgr->initialized) btor_sat_reset (smgr);
  BTOR_DELETE (smgr->btor->mm, smgr);
}

/*------------------------------------------------------------------------*/

void
btor_sat_set_output (BtorSATMgr *smgr, FILE *output)
{
  char *prefix, *q;
  const char *p;

  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (output != NULL);
  (void) smgr;
  set_output (smgr, output);
  smgr->output = output;

  prefix = btor_mem_malloc (smgr->btor->mm, strlen (smgr->name) + 4);
  sprintf (prefix, "[%s] ", smgr->name);
  q = prefix + 1;
  for (p = smgr->name; *p; p++) *q++ = tolower ((int32_t) *p);
  set_prefix (smgr, prefix);
  btor_mem_free (smgr->btor->mm, prefix, strlen (smgr->name) + 4);
}

void
btor_sat_enable_solver (BtorSATMgr *smgr)
{
  assert (smgr);

  uint32_t opt;

  opt = btor_opt_get (smgr->btor, BTOR_OPT_SAT_ENGINE);
  switch (opt)
  {
#ifdef BTOR_USE_LINGELING
    case BTOR_SAT_ENGINE_LINGELING: btor_sat_enable_lingeling (smgr); break;
#endif
#ifdef BTOR_USE_PICOSAT
    case BTOR_SAT_ENGINE_PICOSAT: btor_sat_enable_picosat (smgr); break;
#endif
#ifdef BTOR_USE_MINISAT
    case BTOR_SAT_ENGINE_MINISAT: btor_sat_enable_minisat (smgr); break;
#endif
#ifdef BTOR_USE_CADICAL
    case BTOR_SAT_ENGINE_CADICAL: btor_sat_enable_cadical (smgr); break;
#endif
    default: BTOR_ABORT (1, "no sat solver configured");
  }

  BTOR_MSG (smgr->btor->msg,
            1,
            "%s allows %snon-incremental mode",
            smgr->name,
            smgr->api.assume ? "both incremental and " : "");
}

void
btor_sat_init (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (!smgr->initialized);
  BTOR_MSG (smgr->btor->msg, 1, "initialized %s", smgr->name);

  smgr->solver = init (smgr);
  enable_verbosity (smgr, btor_opt_get (smgr->btor, BTOR_OPT_VERBOSITY));
  smgr->initialized  = true;
  smgr->inc_required = true;
  smgr->sat_time     = 0;

  /* Set terminate callbacks if SAT solver supports it */
  if (smgr->term.fun && smgr->api.setterm)
  {
    setterm (smgr);
  }

  smgr->true_lit = btor_sat_mgr_next_cnf_id (smgr);
  btor_sat_add (smgr, smgr->true_lit);
  btor_sat_add (smgr, 0);
  btor_sat_set_output (smgr, stdout);
}

void
btor_sat_print_stats (BtorSATMgr *smgr)
{
  if (!smgr || !smgr->initialized) return;
  stats (smgr);
  BTOR_MSG (smgr->btor->msg,
            1,
            "%d SAT calls in %.1f seconds",
            smgr->satcalls,
            smgr->sat_time);
}

void
btor_sat_add (BtorSATMgr *smgr, int32_t lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (!smgr->satcalls || smgr->inc_required);
  if (!lit) smgr->clauses++;
  add (smgr, lit);
}

BtorSolverResult
btor_sat_check_sat (BtorSATMgr *smgr, int32_t limit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (!smgr->inc_required || btor_sat_mgr_has_incremental_support (smgr));

  double start = btor_util_time_stamp ();
  int32_t sat_res;
  BtorSolverResult res;
  BTOR_MSG (smgr->btor->msg,
            2,
            "calling SAT solver %s with limit %d",
            smgr->name,
            limit);
  assert (!smgr->satcalls || smgr->inc_required);
  smgr->satcalls++;
  setterm (smgr);
  sat_res = sat (smgr, limit);
  smgr->sat_time += btor_util_time_stamp () - start;
  switch (sat_res)
  {
    case 10: res = BTOR_RESULT_SAT; break;
    case 20: res = BTOR_RESULT_UNSAT; break;
    default: assert (sat_res == 0); res = BTOR_RESULT_UNKNOWN;
  }
  return res;
}

int32_t
btor_sat_deref (BtorSATMgr *smgr, int32_t lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return deref (smgr, lit);
}

int32_t
btor_sat_repr (BtorSATMgr *smgr, int32_t lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return repr (smgr, lit);
}

void
btor_sat_reset (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  BTOR_MSG (smgr->btor->msg, 2, "resetting %s", smgr->name);
  reset (smgr);
  smgr->solver      = 0;
  smgr->initialized = false;
}

int32_t
btor_sat_fixed (BtorSATMgr *smgr, int32_t lit)
{
  int32_t res;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  res = fixed (smgr, lit);
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_sat_assume (BtorSATMgr *smgr, int32_t lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (!smgr->satcalls || smgr->inc_required);
  assume (smgr, lit);
}

int32_t
btor_sat_failed (BtorSATMgr *smgr, int32_t lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return failed (smgr, lit);
}
