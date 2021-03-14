/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2020 Mathias Preiner.
 *  Copyright (C) 2013-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsat.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdlib.h>

#include "btorabort.h"
#include "btorconfig.h"
#include "btorcore.h"
#include "sat/btorcadical.h"
#include "sat/btorcms.h"
#include "sat/btorlgl.h"
#include "sat/btorminisat.h"
#include "sat/btorpicosat.h"
#include "utils/btorutil.h"

/*------------------------------------------------------------------------*/

#if !defined(BTOR_USE_LINGELING) && !defined(BTOR_USE_PICOSAT)  \
    && !defined(BTOR_USE_MINISAT) && !defined(BTOR_USE_CADICAL) \
    && !defined(BTOR_USE_CMS)
#error "no SAT solver configured"
#endif

static bool enable_dimacs_printer (BtorSATMgr *smgr);

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
clone (Btor *btor, BtorSATMgr *smgr)
{
  BTOR_ABORT (!smgr->api.clone,
              "SAT solver %s does not support 'clone' API call",
              smgr->name);
  return smgr->api.clone (btor, smgr);
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
  res->solver = clone (btor, smgr);
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
#ifdef BTOR_USE_CMS
    case BTOR_SAT_ENGINE_CMS: btor_sat_enable_cms (smgr); break;
#endif
    default: BTOR_ABORT (1, "no sat solver configured");
  }

  BTOR_MSG (smgr->btor->msg,
            1,
            "%s allows %snon-incremental mode",
            smgr->name,
            smgr->api.assume ? "both incremental and " : "");

  if (btor_opt_get (smgr->btor, BTOR_OPT_PRINT_DIMACS))
  {
    enable_dimacs_printer (smgr);
  }
}

static void
init_flags (BtorSATMgr *smgr)
{
  assert (smgr);
  smgr->initialized  = true;
  smgr->inc_required = true;
  smgr->sat_time     = 0;
}

void
btor_sat_init (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (!smgr->initialized);
  BTOR_MSG (smgr->btor->msg, 1, "initialized %s", smgr->name);

  init_flags (smgr);

  smgr->solver = init (smgr);
  enable_verbosity (smgr, btor_opt_get (smgr->btor, BTOR_OPT_VERBOSITY));

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

/*------------------------------------------------------------------------*/
/* DIMACS printer                                                         */
/*------------------------------------------------------------------------*/

static void *
dimacs_printer_init (BtorSATMgr *smgr)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BtorSATMgr *wrapped_smgr = printer->smgr;

  BTOR_INIT_STACK (smgr->btor->mm, printer->clauses);
  BTOR_INIT_STACK (smgr->btor->mm, printer->assumptions);
  printer->out = stdout;

  /* Note: We need to explicitly do the initialization steps for 'wrapped_smgr'
   * here instead of calling btor_sat_init on 'wrapped_smgr'. Otherwise, not all
   * information is recorded correctly. */
  BTOR_MSG (smgr->btor->msg, 1, "initialized %s", wrapped_smgr->name);
  init_flags (wrapped_smgr);
  wrapped_smgr->solver = wrapped_smgr->api.init (wrapped_smgr);

  return printer;
}

static void
dimacs_printer_add (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BTOR_PUSH_STACK (printer->clauses, lit);
  add (printer->smgr, lit);
}

static void
dimacs_printer_assume (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BTOR_PUSH_STACK (printer->assumptions, lit);
  assume (printer->smgr, lit);
}

static int32_t
dimacs_printer_deref (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  return deref (printer->smgr, lit);
}

static int32_t
dimacs_printer_repr (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  return repr (printer->smgr, lit);
}

static void
dimacs_printer_enable_verbosity (BtorSATMgr *smgr, int32_t level)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  return enable_verbosity (printer->smgr, level);
}

static int32_t
dimacs_printer_failed (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  return failed (printer->smgr, lit);
}

static int32_t
dimacs_printer_fixed (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  return fixed (printer->smgr, lit);
}

static void
dimacs_printer_reset (BtorSATMgr *smgr)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BtorSATMgr *wrapped_smgr = printer->smgr;

  reset (wrapped_smgr);

  BTOR_DELETE (smgr->btor->mm, wrapped_smgr);
  BTOR_RELEASE_STACK (printer->clauses);
  BTOR_RELEASE_STACK (printer->assumptions);
  BTOR_DELETE (smgr->btor->mm, printer);
  smgr->solver = 0;
}

static void
print_dimacs (BtorSATMgr *smgr)
{
  int32_t lit;
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;

  /* Print CNF in DIMACS format. */
  fprintf (printer->out, "c CNF dump %u start\n", smgr->satcalls);
  fprintf (printer->out, "c Boolector version %s\n", BTOR_GIT_ID);
  fprintf (printer->out, "p cnf %u %u\n", smgr->maxvar, smgr->clauses);

  /* Print clauses */
  for (size_t i = 0; i < BTOR_COUNT_STACK (printer->clauses); i++)
  {
    lit = BTOR_PEEK_STACK (printer->clauses, i);
    if (lit)
      printf ("%d ", lit);
    else
      printf ("%d\n", lit);
  }

  /* Print assumptions */
  if (!BTOR_EMPTY_STACK (printer->assumptions))
  {
    fprintf (printer->out, "c assumptions\n");
    for (size_t i = 0; i < BTOR_COUNT_STACK (printer->assumptions); i++)
    {
      lit = BTOR_PEEK_STACK (printer->assumptions, i);
      fprintf (printer->out, "%d\n", lit);
    }
  }
  fprintf (printer->out, "c CNF dump %u end\n", smgr->satcalls);
}

static int32_t
dimacs_printer_sat (BtorSATMgr *smgr, int32_t limit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BtorSATMgr *wrapped_smgr = printer->smgr;

  print_dimacs (smgr);

  wrapped_smgr->inc_required = smgr->inc_required;
  wrapped_smgr->satcalls     = smgr->satcalls;

  /* If incremental is disabled, we only print the CNF and return unknown. */
  return smgr->inc_required ? sat (wrapped_smgr, limit) : 0;
}

static void
dimacs_printer_set_output (BtorSATMgr *smgr, FILE *output)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  printer->out            = output;
  set_output (printer->smgr, output);
}

static void
dimacs_printer_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  set_prefix (printer->smgr, prefix);
}

static void
dimacs_printer_stats (BtorSATMgr *smgr)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  stats (printer->smgr);
}

static void
clone_int_stack (BtorMemMgr *mm, BtorIntStack *clone, BtorIntStack *stack)
{
  size_t size = BTOR_SIZE_STACK (*stack);
  size_t cnt  = BTOR_COUNT_STACK (*stack);

  BTOR_INIT_STACK (mm, *clone);
  if (size)
  {
    BTOR_CNEWN (mm, clone->start, size);
    clone->end = clone->start + size;
    clone->top = clone->start + cnt;
    memcpy (clone->start, stack->start, cnt * sizeof (int32_t));
  }
}

static void *
dimacs_printer_clone (Btor *btor, BtorSATMgr *smgr)
{
  BtorCnfPrinter *printer, *printer_clone;
  BtorMemMgr *mm;

  mm      = btor->mm;
  printer = (BtorCnfPrinter *) smgr->solver;

  BTOR_CNEW (mm, printer_clone);
  clone_int_stack (mm, &printer_clone->assumptions, &printer->assumptions);
  clone_int_stack (mm, &printer_clone->clauses, &printer->clauses);
  printer_clone->out  = printer->out;
  printer_clone->smgr = btor_sat_mgr_clone (btor, printer->smgr);

  return printer_clone;
}

static void
dimacs_printer_setterm (BtorSATMgr *smgr)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  setterm (printer->smgr);
}

static int32_t
dimacs_printer_inc_max_var (BtorSATMgr *smgr)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BtorSATMgr *wrapped_smgr   = printer->smgr;
  wrapped_smgr->inc_required = smgr->inc_required;
  wrapped_smgr->maxvar       = smgr->maxvar;
  return inc_max_var (wrapped_smgr);
}

static void
dimacs_printer_melt (BtorSATMgr *smgr, int32_t lit)
{
  BtorCnfPrinter *printer = (BtorCnfPrinter *) smgr->solver;
  BtorSATMgr *wrapped_smgr   = printer->smgr;
  wrapped_smgr->inc_required = smgr->inc_required;
  melt (wrapped_smgr, lit);
}

/*------------------------------------------------------------------------*/

/* The DIMACS printer is a SAT manager that wraps the currently configured SAT
 * mangager. It records the CNF sent to the SAT solver and forwards all API
 * calls to the wrapped SAT manager. The DIMACS printer assumes a SAT solver
 * was already enabled. */
static bool
enable_dimacs_printer (BtorSATMgr *smgr)
{
  assert (smgr);
  assert (smgr->name);

  BtorCnfPrinter *printer;

  /* Initialize printer and copy current SAT manager. */
  BTOR_CNEW (smgr->btor->mm, printer);
  BTOR_CNEW (smgr->btor->mm, printer->smgr);
  memcpy (printer->smgr, smgr, sizeof (BtorSATMgr));

  /* Clear API */
  memset (&smgr->api, 0, sizeof (smgr->api));

  smgr->solver               = printer;
  smgr->name                 = "DIMACS Printer";
  smgr->api.add              = dimacs_printer_add;
  smgr->api.deref            = dimacs_printer_deref;
  smgr->api.enable_verbosity = dimacs_printer_enable_verbosity;
  smgr->api.fixed            = dimacs_printer_fixed;
  smgr->api.inc_max_var      = dimacs_printer_inc_max_var;
  smgr->api.init             = dimacs_printer_init;
  smgr->api.melt             = dimacs_printer_melt;
  smgr->api.repr             = dimacs_printer_repr;
  smgr->api.reset            = dimacs_printer_reset;
  smgr->api.sat              = dimacs_printer_sat;
  smgr->api.set_output       = dimacs_printer_set_output;
  smgr->api.set_prefix       = dimacs_printer_set_prefix;
  smgr->api.stats            = dimacs_printer_stats;
  smgr->api.setterm          = dimacs_printer_setterm;

  /* These function are used in btor_sat_mgr_has_* testers and should only be
   * set if the underlying SAT solver also has support for it. */
  smgr->api.assume = printer->smgr->api.assume ? dimacs_printer_assume : 0;
  smgr->api.failed = printer->smgr->api.failed ? dimacs_printer_failed : 0;
  smgr->api.clone  = printer->smgr->api.clone ? dimacs_printer_clone : 0;

  return true;
}
