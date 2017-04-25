/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsat.h"

#ifdef BTOR_USE_PICOSAT
#include "picosat.h"
#endif
#ifdef BTOR_USE_LINGELING
#include "lglib.h"
#endif
#ifdef BTOR_USE_MINISAT
#include "btorminisat.h"
#endif
#include "btorabort.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/
// #define BTOR_PRINT_DIMACS_FOR_LINGELING // enable to print dimacs files
#ifdef BTOR_PRINT_DIMACS_FOR_LINGELING
#include <sys/types.h>  // for getpid
#include <unistd.h>     // for getpid
#endif
/*------------------------------------------------------------------------*/

#if defined(BTOR_USE_LINGELING)
#define btor_enable_default_sat(SMGR) btor_sat_enable_lingeling ((SMGR), 0, 0)
#elif defined(BTOR_USE_PICOSAT)
#define btor_enable_default_sat btor_sat_enable_picosat
#elif defined(BTOR_USE_MINISAT)
#define btor_enable_default_sat btor_sat_enable_minisat
#else
#error "no SAT solver configured"
#endif

/*------------------------------------------------------------------------*/

BtorSATMgr *
btor_sat_mgr_new (BtorMemMgr *mm, BtorMsg *msg)
{
  BtorSATMgr *smgr;

  assert (mm != NULL);

  BTOR_CNEW (mm, smgr);
  smgr->mm     = mm;
  smgr->msg    = msg;
  smgr->output = stdout;
  btor_enable_default_sat (smgr);
  BTOR_MSG (msg, 1, "enabled %s as default SAT solver", smgr->name);
  return smgr;
}

bool
btor_sat_mgr_has_clone_support (const BtorSATMgr *smgr)
{
  if (!smgr) return true;
  return smgr->api.clone != 0;
}

bool
btor_sat_mgr_has_term_support (const BtorSATMgr *smgr)
{
  if (!smgr) return false;
  return (!strcmp (smgr->name, "Lingeling"));
}

void
btor_sat_mgr_set_term (BtorSATMgr *smgr, int (*fun) (void *), void *state)
{
  assert (smgr);
  smgr->term.fun   = fun;
  smgr->term.state = state;
}

// FIXME log output handling, in particular: sat manager name output
// (see lingeling_sat) should be unique, which is not the case for
// clones
BtorSATMgr *
btor_sat_mgr_clone (BtorMemMgr *mm, BtorMsg *msg, BtorSATMgr *smgr)
{
  assert (smgr);
  assert (btor_sat_mgr_has_clone_support (smgr));
  assert (msg);
  assert (mm);

  BtorSATMgr *res;

  BTOR_ABORT (!btor_sat_mgr_has_clone_support (smgr),
              "SAT solver does not support cloning");
  BTOR_NEW (mm, res);
  res->solver = smgr->api.clone (smgr, mm);
  res->mm     = mm;
  res->msg    = msg;
  assert (res->mm->sat_allocated == smgr->mm->sat_allocated);
  res->name   = smgr->name;
  res->optstr = btor_mem_strdup (mm, smgr->optstr);
  memcpy (&res->inc_required,
          &smgr->inc_required,
          (char *) smgr + sizeof (*smgr) - (char *) &smgr->inc_required);
  return res;
}

bool
btor_sat_is_initialized (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  return smgr->initialized;
}

int
btor_sat_mgr_next_cnf_id (BtorSATMgr *smgr)
{
  int result;
  assert (smgr);
  assert (smgr->initialized);
  result = smgr->api.inc_max_var (smgr);
  if (abs (result) > smgr->maxvar) smgr->maxvar = abs (result);
  BTOR_ABORT (result <= 0, "CNF id overflow");
  if (btor_opt_get (smgr->msg->btor, BTOR_OPT_VERBOSITY) > 2
      && !(result % 100000))
    BTOR_MSG (smgr->msg, 2, "reached CNF id %d", result);
  return result;
}

void
btor_sat_mgr_release_cnf_id (BtorSATMgr *smgr, int lit)
{
  assert (smgr);
  if (!smgr->initialized) return;
  assert (abs (lit) <= smgr->maxvar);
  if (abs (lit) == smgr->true_lit) return;
  if (smgr->api.melt) smgr->api.melt (smgr, lit);
}

#if 0
int
btor_get_last_cnf_id_sat_mgr (BtorSATMgr * smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->api.variables (smgr);
}
#endif

void
btor_sat_mgr_delete (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  /* if SAT is still initialized, then
   * reset_sat has not been called
   */
  if (smgr->initialized) btor_sat_reset (smgr);
  if (smgr->optstr) btor_mem_freestr (smgr->mm, smgr->optstr);
  BTOR_DELETE (smgr->mm, smgr);
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
  smgr->api.set_output (smgr, output);
  smgr->output = output;

  prefix = btor_mem_malloc (smgr->mm, strlen (smgr->name) + 4);
  sprintf (prefix, "[%s] ", smgr->name);
  q = prefix + 1;
  for (p = smgr->name; *p; p++) *q++ = tolower ((int) *p);
  smgr->api.set_prefix (smgr, prefix);
  btor_mem_free (smgr->mm, prefix, strlen (smgr->name) + 4);
}

void
btor_sat_init (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (!smgr->initialized);
  BTOR_MSG (smgr->msg, 1, "initialized %s", smgr->name);

  smgr->solver = smgr->api.init (smgr);
  smgr->api.enable_verbosity (
      smgr, btor_opt_get (smgr->msg->btor, BTOR_OPT_VERBOSITY));
  smgr->initialized  = true;
  smgr->inc_required = true;
  smgr->sat_time     = 0;

  smgr->true_lit = btor_sat_mgr_next_cnf_id (smgr);
  btor_sat_add (smgr, smgr->true_lit);
  btor_sat_add (smgr, 0);
  btor_sat_set_output (smgr, stdout);
}

void
btor_sat_print_stats (BtorSATMgr *smgr)
{
  if (!smgr || !smgr->initialized) return;
  smgr->api.stats (smgr);
  BTOR_MSG (smgr->msg,
            1,
            "%d SAT calls in %.1f seconds",
            smgr->satcalls,
            smgr->sat_time);
}

void
btor_sat_add (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (!smgr->satcalls || smgr->inc_required);
  if (!lit) smgr->clauses++;
  (void) smgr->api.add (smgr, lit);
}

BtorSolverResult
btor_sat_sat (BtorSATMgr *smgr, int limit)
{
  double start = btor_util_time_stamp ();
  int sat_res;
  BtorSolverResult res;
  assert (smgr != NULL);
  assert (smgr->initialized);
  BTOR_MSG (
      smgr->msg, 2, "calling SAT solver %s with limit %d", smgr->name, limit);
  assert (!smgr->satcalls || smgr->inc_required);
  smgr->satcalls++;
  if (smgr->api.setterm) smgr->api.setterm (smgr);
  sat_res = smgr->api.sat (smgr, limit);
  smgr->sat_time += btor_util_time_stamp () - start;
  switch (sat_res)
  {
    case 10: res = BTOR_RESULT_SAT; break;
    case 20: res = BTOR_RESULT_UNSAT; break;
    default: assert (sat_res == 0); res = BTOR_RESULT_UNKNOWN;
  }
  return res;
}

int
btor_sat_deref (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.deref (smgr, lit);
}

int
btor_sat_repr (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.repr (smgr, lit);
}

void
btor_sat_reset (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  BTOR_MSG (smgr->msg, 2, "resetting %s", smgr->name);
  smgr->api.reset (smgr);
  smgr->solver = 0;
  if (smgr->optstr)
  {
    btor_mem_freestr (smgr->mm, smgr->optstr);
    smgr->optstr = 0;
  }
  smgr->initialized = false;
}

int
btor_sat_fixed (BtorSATMgr *smgr, int lit)
{
  int res;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  res = smgr->api.fixed (smgr, lit);
  return res;
}

/*------------------------------------------------------------------------*/

void
btor_sat_assume (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (!smgr->satcalls || smgr->inc_required);
  smgr->api.assume (smgr, lit);
}

int
btor_sat_failed (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.failed (smgr, lit);
}

#if 0
int
btor_sat_inconsistent (BtorSATMgr * smgr)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  return smgr->api.inconsistent (smgr);
}

int
btor_sat_changed (BtorSATMgr * smgr)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  return smgr->api.changed (smgr);
}
#endif

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_PICOSAT
/*------------------------------------------------------------------------*/
static void *
picosat_init (BtorSATMgr *smgr)
{
  PicoSAT *res;

  BTOR_MSG (smgr->msg, 1, "PicoSAT Version %s", picosat_version ());

  res = picosat_minit (smgr->mm,
                       (picosat_malloc) btor_mem_sat_malloc,
                       (picosat_realloc) btor_mem_sat_realloc,
                       (picosat_free) btor_mem_sat_free);

  picosat_set_global_default_phase (res, 0);

  return res;
}

static void
picosat_add (BtorSATMgr *smgr, int lit)
{
  (void) picosat_add (smgr->solver, lit);
}

static int
picosat_sat (BtorSATMgr *smgr, int limit)
{
  return picosat_sat (smgr->solver, limit);
}

#if 0
static int
picosat_changed (BtorSATMgr * smgr)
{
  return picosat_changed (smgr->solver);
}
#endif

static int
picosat_deref (BtorSATMgr *smgr, int lit)
{
  return picosat_deref (smgr->solver, lit);
}

static int
picosat_repr (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  return lit;
}

static void
picosat_reset (BtorSATMgr *smgr)
{
  picosat_reset (smgr->solver);
  smgr->solver = 0;
}

static void
picosat_set_output (BtorSATMgr *smgr, FILE *output)
{
  picosat_set_output (smgr->solver, output);
}

static void
picosat_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  picosat_set_prefix (smgr->solver, prefix);
}

static void
picosat_enable_verbosity (BtorSATMgr *smgr, int level)
{
  if (level >= 2) picosat_set_verbosity (smgr->solver, level - 1);
}

static int
picosat_inc_max_var (BtorSATMgr *smgr)
{
  return picosat_inc_max_var (smgr->solver);
}

#if 0
static int
picosat_variables (BtorSATMgr * smgr)
{
  return picosat_variables (smgr->solver);
}
#endif

static void
picosat_stats (BtorSATMgr *smgr)
{
  picosat_stats (smgr->solver);
}

static int
picosat_fixed (BtorSATMgr *smgr, int lit)
{
  int res;
  res = picosat_deref_toplevel (smgr->solver, lit);
  return res;
}

/*------------------------------------------------------------------------*/

static void
picosat_assume (BtorSATMgr *smgr, int lit)
{
  (void) picosat_assume (smgr->solver, lit);
}

static int
picosat_failed (BtorSATMgr *smgr, int lit)
{
  return picosat_failed_assumption (smgr->solver, lit);
}

#if 0
static int
picosat_inconsistent (BtorSATMgr * smgr)
{
  return picosat_inconsistent (smgr->solver);
}
#endif

/*------------------------------------------------------------------------*/

bool
btor_sat_enable_picosat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_picosat'");

  smgr->name   = "PicoSAT";
  smgr->optstr = 0;

  BTOR_CLR (&smgr->api);
  smgr->api.add    = picosat_add;
  smgr->api.assume = picosat_assume;
#if 0
  smgr->api.changed = picosat_changed;
#endif
  smgr->api.deref            = picosat_deref;
  smgr->api.enable_verbosity = picosat_enable_verbosity;
  smgr->api.failed           = picosat_failed;
  smgr->api.fixed            = picosat_fixed;
  smgr->api.inc_max_var      = picosat_inc_max_var;
#if 0
  smgr->api.inconsistent = picosat_inconsistent;
#endif
  smgr->api.init       = picosat_init;
  smgr->api.melt       = 0;
  smgr->api.repr       = picosat_repr;
  smgr->api.reset      = picosat_reset;
  smgr->api.sat        = picosat_sat;
  smgr->api.set_output = picosat_set_output;
  smgr->api.set_prefix = picosat_set_prefix;
  smgr->api.stats      = picosat_stats;
#if 0
  smgr->api.variables = picosat_variables;
#endif

  BTOR_MSG (
      smgr->msg, 1, "PicoSAT allows both incremental and non-incremental mode");

  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_LINGELING
/*------------------------------------------------------------------------*/
static bool
passdown_lingeling_options (BtorSATMgr *smgr,
                            const char *optstr,
                            LGL *external_lgl)
{
  char *str, *p, *next, *eq, *opt, *val;
  LGL *lgl = external_lgl ? external_lgl : 0;
  int len, valid;
  bool res;

  assert (optstr);
  len = strlen (optstr);

  BTOR_NEWN (smgr->mm, str, len + 1);
  strcpy (str, optstr);

  res = true;

  for (p = str; *p; p = next)
  {
    if (*p == ',')
      next = p + 1;
    else
    {
      opt = p;
      while (*p != ',' && *p) p++;

      if (*p)
      {
        assert (*p == ',');
        *p   = 0;
        next = p + 1;
      }
      else
        next = p;

      val = eq = 0;

      if (!isalpha ((int) *opt))
        valid = 0;
      else
      {
        for (p = opt + 1; isalnum ((int) *p); p++)
          ;

        if (*p == '=')
        {
          *(eq = p++) = 0;
          val         = p;
          if (*p == '-') p++;
          if (isdigit ((int) *p))
          {
            while (isdigit ((int) *p)) p++;

            valid = !*p;
          }
          else
            valid = 0;
        }
        else
          valid = 0;
      }

      if (valid)
      {
        if (!lgl)
        {
          assert (!external_lgl);
          lgl = lglinit ();
        }

        if (lglhasopt (lgl, opt))
        {
          if (external_lgl && val)
          {
            assert (lgl == external_lgl);
            BTOR_MSG (
                smgr->msg, 2, "setting Lingeling option --%s=%s", opt, val);
            lglsetopt (lgl, opt, atoi (val));
          }
        }
        else
          valid = 0;
      }

      if (!valid) res = false;
      if (valid || external_lgl) continue;

      if (eq) *eq = '=';
      BTOR_MSG (smgr->msg,
                1,
                "*** can not pass down to Lingeling invalid option '%s'",
                optstr);
    }
  }

  BTOR_DELETEN (smgr->mm, str, len + 1);
  if (lgl && !external_lgl) lglrelease (lgl);

  return res;
}

#define BTOR_LGL_SIMP_DELAY 10000
#define BTOR_LGL_MIN_BLIMIT 50000
#define BTOR_LGL_MAX_BLIMIT 200000

static void *
lingeling_init (BtorSATMgr *smgr)
{
  BtorLGL *res;

  if (btor_opt_get (smgr->msg->btor, BTOR_OPT_VERBOSITY) >= 1)
  {
    lglbnr ("Lingeling", "[lingeling] ", stdout);
    fflush (stdout);
  }

  BTOR_CNEW (smgr->mm, res);
  res->lgl = lglminit (smgr->mm,
                       (lglalloc) btor_mem_sat_malloc,
                       (lglrealloc) btor_mem_sat_realloc,
                       (lgldealloc) btor_mem_sat_free);

  if (smgr->optstr) passdown_lingeling_options (smgr, smgr->optstr, res->lgl);

  res->blimit = BTOR_LGL_MIN_BLIMIT;

  return res;
}

static void
lingeling_add (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  lgladd (blgl->lgl, lit);
}

static int
lingeling_sat (BtorSATMgr *smgr, int limit)
{
  BtorLGL *blgl = smgr->solver;
  LGL *lgl      = blgl->lgl, *clone;
  const char *str;
  int res, bfres;
  char name[80];

  assert (smgr->satcalls >= 1);

  lglsetopt (lgl, "simplify", 1);

#ifdef BTOR_PRINT_DIMACS_FOR_LINGELING
  {
    static int count = 0;
    char name[80];
    FILE *file;
    sprintf (name, "/tmp/btor_lingeling_sat_%05d_%08d.cnf", getpid (), count++);
    file = fopen (name, "w");
    lglprint (lgl, file);
    fclose (file);
    BTOR_MSG (smgr->msg, 0, "wrote %s", name);
  }
#endif

  if (smgr->inc_required
      && (smgr->satcalls == 1 || (smgr->satcalls & (smgr->satcalls - 1))))
    lglsetopt (lgl, "simpdelay", BTOR_LGL_SIMP_DELAY);
  else
    lglsetopt (lgl, "simpdelay", 0);

  if (smgr->inc_required)
  {
    lglsetopt (lgl, "flipping", 0);
    lglsetopt (lgl, "locs", 0);
  }
  else
  {
    lglsetopt (lgl, "clim", -1);
    res = lglsat (lgl);
    return res;
  }

  if (!smgr->fork || (0 <= limit && limit < blgl->blimit))
  {
    if (limit < INT_MAX) lglsetopt (lgl, "clim", limit);
    res = lglsat (lgl);
  }
  else
  {
    BTOR_MSG (smgr->msg, 2, "blimit = %d", blgl->blimit);
    lglsetopt (lgl, "clim", blgl->blimit);
    if (!(res = lglsat (lgl)))
    {
      blgl->blimit *= 2;
      if (blgl->blimit > BTOR_LGL_MAX_BLIMIT)
        blgl->blimit = BTOR_LGL_MAX_BLIMIT;

      blgl->nforked++;
      clone = lglclone (lgl);
      lglfixate (clone);
      lglmeltall (clone);
      str = "clone";
      lglsetopt (clone, "clim", limit);
      /* callbacks are not cloned in Lingeling */
      if (smgr->term.fun) lglseterm (clone, smgr->term.fun, smgr->term.state);
      sprintf (name, "[%s lgl%s%d] ", smgr->msg->prefix, str, blgl->nforked);
      lglsetprefix (clone, name);
      lglsetout (clone, smgr->output);

#ifndef NDEBUG
      res =
#else
      (void)
#endif
          lglsat (clone);
      if (btor_opt_get (smgr->msg->btor, BTOR_OPT_VERBOSITY) > 0)
        lglstats (clone);
      bfres = lglunclone (lgl, clone);
      lglrelease (clone);
      assert (!res || bfres == res);
      res = bfres;
    }
    else
    {
      blgl->blimit = 9 * (blgl->blimit / 10);
      if (blgl->blimit < BTOR_LGL_MIN_BLIMIT)
        blgl->blimit = BTOR_LGL_MIN_BLIMIT;
    }
  }
  return res;
}

#if 0
static int
lingeling_changed (BtorSATMgr * smgr)
{
  BtorLGL * blgl = smgr->solver;
  return lglchanged (blgl->lgl);
}
#endif

static int
lingeling_deref (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglderef (blgl->lgl, lit);
}

static int
lingeling_repr (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglrepr (blgl->lgl, lit);
}

static void
lingeling_reset (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  lglrelease (blgl->lgl);
  BTOR_DELETE (smgr->mm, blgl);
}

static void
lingeling_set_output (BtorSATMgr *smgr, FILE *output)
{
  BtorLGL *blgl = smgr->solver;
  lglsetout (blgl->lgl, output);
}

static void
lingeling_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  BtorLGL *blgl = smgr->solver;
  lglsetprefix (blgl->lgl, prefix);
}

static void
lingeling_enable_verbosity (BtorSATMgr *smgr, int level)
{
  BtorLGL *blgl = smgr->solver;
  if (level <= 0)
    lglsetopt (blgl->lgl, "verb", -1);
  else if (level >= 2)
    lglsetopt (blgl->lgl, "verb", level - 1);
}

static int
lingeling_inc_max_var (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  int res       = lglincvar (blgl->lgl);
  if (smgr->inc_required) lglfreeze (blgl->lgl, res);
  return res;
}

#if 0
static int
lingeling_variables (BtorSATMgr * smgr)
{
  BtorLGL * blgl = smgr->solver;
  return lglmaxvar (blgl->lgl);
}
#endif

static void
lingeling_stats (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  lglstats (blgl->lgl);
  BTOR_MSG (smgr->msg, 1, "%d forked", blgl->nforked);
}

/*------------------------------------------------------------------------*/

static void
lingeling_assume (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  lglassume (blgl->lgl, lit);
}

static void
lingeling_melt (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  if (smgr->inc_required) lglmelt (blgl->lgl, lit);
}

static int
lingeling_failed (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglfailed (blgl->lgl, lit);
}

static int
lingeling_fixed (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglfixed (blgl->lgl, lit);
}

#if 0
static int
lingeling_inconsistent (BtorSATMgr * smgr)
{
  BtorLGL * blgl = smgr->solver;
  return lglinconsistent (blgl->lgl);
}
#endif

static void *
lingeling_clone (BtorSATMgr *smgr, BtorMemMgr *mm)
{
  assert (smgr);

  BtorLGL *res, *blgl;

  blgl = smgr->solver;

  /* not initialized yet */
  if (!blgl) return 0;

  BTOR_CNEW (mm, res);
  res->nforked = blgl->nforked;
  res->blimit  = blgl->blimit;
  res->lgl     = lglmclone (blgl->lgl,
                        mm,
                        (lglalloc) btor_mem_sat_malloc,
                        (lglrealloc) btor_mem_sat_realloc,
                        (lgldealloc) btor_mem_sat_free);
  return res;
}

static void
lingeling_setterm (BtorSATMgr *smgr)
{
  assert (smgr);

  BtorLGL *blgl;
  blgl = smgr->solver;
  lglseterm (blgl->lgl, smgr->term.fun, smgr->term.state);
}

/*------------------------------------------------------------------------*/

bool
btor_sat_enable_lingeling (BtorSATMgr *smgr, const char *optstr, bool fork)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_lingeling'");

  smgr->optstr = btor_mem_strdup (smgr->mm, optstr);
  if (smgr->optstr && !passdown_lingeling_options (smgr, optstr, 0))
    return false;

  smgr->name = "Lingeling";
  smgr->fork = fork;

  BTOR_CLR (&smgr->api);
  smgr->api.add    = lingeling_add;
  smgr->api.assume = lingeling_assume;
#if 0
  smgr->api.changed = lingeling_changed;
#endif
  smgr->api.deref            = lingeling_deref;
  smgr->api.enable_verbosity = lingeling_enable_verbosity;
  smgr->api.failed           = lingeling_failed;
  smgr->api.fixed            = lingeling_fixed;
  smgr->api.inc_max_var      = lingeling_inc_max_var;
#if 0
  smgr->api.inconsistent = lingeling_inconsistent;
#endif
  smgr->api.init       = lingeling_init;
  smgr->api.melt       = lingeling_melt;
  smgr->api.repr       = lingeling_repr;
  smgr->api.reset      = lingeling_reset;
  smgr->api.sat        = lingeling_sat;
  smgr->api.set_output = lingeling_set_output;
  smgr->api.set_prefix = lingeling_set_prefix;
  smgr->api.stats      = lingeling_stats;
#if 0
  smgr->api.variables = lingeling_variables;
#endif
  smgr->api.clone   = lingeling_clone;
  smgr->api.setterm = lingeling_setterm;

  BTOR_MSG (smgr->msg,
            1,
            "Lingeling allows both incremental and non-incremental mode");
  if (smgr->optstr)
    BTOR_MSG (
        smgr->msg, 1, "Configured options for Lingeling: %s", smgr->optstr);

  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_MINISAT
/*------------------------------------------------------------------------*/
bool
btor_sat_enable_minisat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_minisat'");

  smgr->name   = "MiniSAT";
  smgr->optstr = 0;

  BTOR_CLR (&smgr->api);
  smgr->api.add    = btor_minisat_add;
  smgr->api.assume = btor_minisat_assume;
#if 0
  smgr->api.changed = btor_minisat_changed;
#endif
  smgr->api.deref            = btor_minisat_deref;
  smgr->api.enable_verbosity = btor_minisat_enable_verbosity;
  smgr->api.failed           = btor_minisat_failed;
  smgr->api.fixed            = btor_minisat_fixed;
  smgr->api.inc_max_var      = btor_minisat_inc_max_var;
#if 0
  smgr->api.inconsistent = btor_minisat_inconsistent;
#endif
  smgr->api.init       = btor_minisat_init;
  smgr->api.repr       = btor_minisat_repr;
  smgr->api.reset      = btor_minisat_reset;
  smgr->api.sat        = btor_minisat_sat;
  smgr->api.set_output = btor_minisat_set_output;
  smgr->api.set_prefix = btor_minisat_set_prefix;
  smgr->api.stats      = btor_minisat_stats;
#if 0
  smgr->api.variables = btor_minisat_variables;
#endif

  BTOR_MSG (
      smgr->msg, 1, "MiniSAT allows both incremental and non-incremental mode");

  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
