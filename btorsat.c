/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifdef BTOR_USE_PICOSAT
#include "picosat.h"
#endif

#ifdef BTOR_USE_LINGELING
#include "lglib.h"
#endif

#ifdef BTOR_USE_MINISAT
#include "btorminisat.h"
#endif

#include "btorexit.h"
#include "btorsat.h"
#include "btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/

#define BTOR_ABORT_SAT(cond, msg)                   \
  do                                                \
  {                                                 \
    if (cond)                                       \
    {                                               \
      printf ("[btorsat] %s: %s\n", __func__, msg); \
      fflush (stdout);                              \
      exit (BTOR_ERR_EXIT);                         \
    }                                               \
  } while (0)

/*------------------------------------------------------------------------*/

#if defined(BTOR_USE_LINGELING)
static BtorLGL *btor_clone_lingeling (BtorLGL *, BtorMemMgr *);

int btor_enable_lingeling_sat (BtorSATMgr *, const char *optstr, int nofork);

#define btor_enable_default_sat(SMGR)         \
  do                                          \
  {                                           \
    btor_enable_lingeling_sat ((SMGR), 0, 0); \
  } while (0)

#elif defined(BTOR_USE_PICOSAT)
void btor_enable_picosat_sat (BtorSATMgr *);
#define btor_enable_default_sat btor_enable_picosat_sat
#elif defined(BTOR_USE_MINISAT)
void btor_enable_minisat_sat (BtorSATMgr *);
#define btor_enable_default_sat btor_enable_minisat_sat
#else
#error "no SAT solver configured"
#endif

/*------------------------------------------------------------------------*/

BtorSATMgr *
btor_new_sat_mgr (BtorMemMgr *mm, BtorMsg *msg)
{
  BtorSATMgr *smgr;

  assert (mm != NULL);

  BTOR_CNEW (mm, smgr);
  smgr->mm     = mm;
  smgr->msg    = msg;
  smgr->output = stdout;
  btor_enable_default_sat (smgr);

  return smgr;
}

int
btor_has_clone_support_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr);
  return (!strcmp (smgr->name, "Lingeling"));
}

// FIXME log output handling, in particular: sat manager name output
// (see btor_lingeling_sat) should be unique, which is not the case for
// clones
BtorSATMgr *
btor_clone_sat_mgr (BtorMemMgr *mm, BtorMsg *msg, BtorSATMgr *smgr)
{
  assert (smgr);
  assert (btor_has_clone_support_sat_mgr (smgr));
  assert (msg);
  assert (mm);

  BtorSATMgr *res;

  BTOR_NEW (mm, res);
  res->solver = btor_clone_lingeling (smgr->solver, mm);
  res->mm     = mm;
  res->msg    = msg;
  assert (res->mm->sat_allocated == smgr->mm->sat_allocated);
  res->name   = smgr->name;
  res->optstr = btor_strdup (mm, smgr->optstr);
  memcpy (&res->inc_required,
          &smgr->inc_required,
          (char *) smgr + sizeof (*smgr) - (char *) &smgr->inc_required);
  return res;
}

int
btor_is_initialized_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  return smgr->initialized;
}

int
btor_next_cnf_id_sat_mgr (BtorSATMgr *smgr)
{
  int result;
  assert (smgr);
  assert (smgr->initialized);
  result = smgr->api.inc_max_var (smgr);
  if (abs (result) > smgr->maxvar) smgr->maxvar = abs (result);
  BTOR_ABORT_SAT (result <= 0, "CNF id overflow");
  if (*smgr->msg->verbosity > 2 && !(result % 100000))
    BTOR_MSG (smgr->msg, 2, "reached CNF id %d", result);
  return result;
}

void
btor_release_cnf_id_sat_mgr (BtorSATMgr *smgr, int lit)
{
  assert (smgr);
  if (!smgr->initialized) return;
  assert (abs (lit) <= smgr->maxvar);
  if (abs (lit) == smgr->true_lit) return;
  if (smgr->api.melt) smgr->api.melt (smgr, lit);
}

int
btor_get_last_cnf_id_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  (void) smgr;
  return smgr->api.variables (smgr);
}

void
btor_delete_sat_mgr (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  /* if SAT is still initialized, then
   * reset_sat has not been called
   */
  if (smgr->initialized) btor_reset_sat (smgr);
  if (smgr->optstr) btor_freestr (smgr->mm, smgr->optstr);
  BTOR_DELETE (smgr->mm, smgr);
}

/*------------------------------------------------------------------------*/

void
btor_set_output_sat (BtorSATMgr *smgr, FILE *output)
{
  char *prefix, *q;
  const char *p;

  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (output != NULL);
  (void) smgr;
  smgr->api.set_output (smgr, output);
  smgr->output = output;

  prefix = btor_malloc (smgr->mm, strlen (smgr->name) + 4);
  sprintf (prefix, "[%s] ", smgr->name);
  q = prefix + 1;
  for (p = smgr->name; *p; p++) *q++ = tolower (*p);
  smgr->api.set_prefix (smgr, prefix);
  btor_free (smgr->mm, prefix, strlen (smgr->name) + 4);
}

void
btor_init_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (!smgr->initialized);

  smgr->solver                         = smgr->api.init (smgr);
  smgr->initialized                    = 1;
  smgr->inc_required                   = 1;
  smgr->sat_time                       = 0;
  smgr->used_that_inc_was_not_required = 0;
  smgr->true_lit                       = btor_next_cnf_id_sat_mgr (smgr);
  btor_add_sat (smgr, smgr->true_lit);
  btor_add_sat (smgr, 0);
  btor_set_output_sat (smgr, stdout);
}

void
btor_print_stats_sat (BtorSATMgr *smgr)
{
  if (!smgr || !smgr->initialized) return;
  smgr->api.stats (smgr);
  BTOR_MSG (smgr->msg,
            0,
            "%d SAT calls in %.1f seconds",
            smgr->satcalls,
            smgr->sat_time);
}

void
btor_add_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (!smgr->satcalls || smgr->inc_required);
  if (!lit) smgr->clauses++;
  (void) smgr->api.add (smgr, lit);
}

int
btor_sat_sat (BtorSATMgr *smgr, int limit)
{
  double start = btor_time_stamp ();
  int res;
  assert (smgr != NULL);
  assert (smgr->initialized);
  BTOR_MSG (
      smgr->msg, 2, "calling SAT solver %s with limit %d", smgr->name, limit);
  assert (!smgr->satcalls || smgr->inc_required);
  smgr->satcalls++;
  res = smgr->api.sat (smgr, limit);
  smgr->sat_time += btor_time_stamp () - start;
  return res;
}

int
btor_deref_sat (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.deref (smgr, lit);
}

int
btor_repr_sat (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.repr (smgr, lit);
}

void
btor_reset_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  BTOR_MSG (smgr->msg, 2, "resetting %s", smgr->name);
  smgr->api.reset (smgr);
  smgr->solver = 0;
  if (smgr->optstr)
  {
    btor_freestr (smgr->mm, smgr->optstr);
    smgr->optstr = 0;
  }
  smgr->initialized = 0;
}

int
btor_fixed_sat (BtorSATMgr *smgr, int lit)
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
btor_assume_sat (BtorSATMgr *smgr, int lit)
{
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  assert (!smgr->satcalls || smgr->inc_required);
  smgr->api.assume (smgr, lit);
}

int
btor_failed_sat (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  assert (abs (lit) <= smgr->maxvar);
  return smgr->api.failed (smgr, lit);
}

int
btor_inconsistent_sat (BtorSATMgr *smgr)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  return smgr->api.inconsistent (smgr);
}

int
btor_changed_sat (BtorSATMgr *smgr)
{
  (void) smgr;
  assert (smgr != NULL);
  assert (smgr->initialized);
  return smgr->api.changed (smgr);
}

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_PICOSAT

static void *
btor_picosat_init (BtorSATMgr *smgr)
{
  PicoSAT *res;

  BTOR_MSG (smgr->msg, 1, "PicoSAT Version %s", picosat_version ());

  res = picosat_minit (smgr->mm,
                       (picosat_malloc) btor_sat_malloc,
                       (picosat_realloc) btor_sat_realloc,
                       (picosat_free) btor_sat_free);

  picosat_set_global_default_phase (res, 0);

  return res;
}

static void
btor_picosat_add (BtorSATMgr *smgr, int lit)
{
  (void) picosat_add (smgr->solver, lit);
}

static int
btor_picosat_sat (BtorSATMgr *smgr, int limit)
{
  return picosat_sat (smgr->solver, limit);
}

static int
btor_picosat_changed (BtorSATMgr *smgr)
{
  return picosat_changed (smgr->solver);
}

static int
btor_picosat_deref (BtorSATMgr *smgr, int lit)
{
  return picosat_deref (smgr->solver, lit);
}

static int
btor_picosat_repr (BtorSATMgr *smgr, int lit)
{
  (void) smgr;
  return lit;
}

static void
btor_picosat_reset (BtorSATMgr *smgr)
{
  picosat_reset (smgr->solver);
  smgr->solver = 0;
}

static void
btor_picosat_set_output (BtorSATMgr *smgr, FILE *output)
{
  picosat_set_output (smgr->solver, output);
}

static void
btor_picosat_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  picosat_set_prefix (smgr->solver, prefix);
}

static void
btor_picosat_enable_verbosity (BtorSATMgr *smgr, int level)
{
  picosat_set_verbosity (smgr->solver, level >= 1);
}

static int
btor_picosat_inc_max_var (BtorSATMgr *smgr)
{
  return picosat_inc_max_var (smgr->solver);
}

static int
btor_picosat_variables (BtorSATMgr *smgr)
{
  return picosat_variables (smgr->solver);
}

static void
btor_picosat_stats (BtorSATMgr *smgr)
{
  picosat_stats (smgr->solver);
}

static int
btor_picosat_fixed (BtorSATMgr *smgr, int lit)
{
  int res;
  res = picosat_deref_toplevel (smgr->solver, lit);
  return res;
}

/*------------------------------------------------------------------------*/

static void
btor_picosat_assume (BtorSATMgr *smgr, int lit)
{
  (void) picosat_assume (smgr->solver, lit);
}

static int
btor_picosat_failed (BtorSATMgr *smgr, int lit)
{
  return picosat_failed_assumption (smgr->solver, lit);
}

static int
btor_picosat_inconsistent (BtorSATMgr *smgr)
{
  return picosat_inconsistent (smgr->solver);
}

/*------------------------------------------------------------------------*/

void
btor_enable_picosat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before 'btor_enable_picosat_sat'");

  smgr->name   = "PicoSAT";
  smgr->optstr = 0;

  smgr->api.add              = btor_picosat_add;
  smgr->api.assume           = btor_picosat_assume;
  smgr->api.changed          = btor_picosat_changed;
  smgr->api.deref            = btor_picosat_deref;
  smgr->api.enable_verbosity = btor_picosat_enable_verbosity;
  smgr->api.failed           = btor_picosat_failed;
  smgr->api.fixed            = btor_picosat_fixed;
  smgr->api.inc_max_var      = btor_picosat_inc_max_var;
  smgr->api.inconsistent     = btor_picosat_inconsistent;
  smgr->api.init             = btor_picosat_init;
  smgr->api.melt             = 0;
  smgr->api.repr             = btor_picosat_repr;
  smgr->api.reset            = btor_picosat_reset;
  smgr->api.sat              = btor_picosat_sat;
  smgr->api.set_output       = btor_picosat_set_output;
  smgr->api.set_prefix       = btor_picosat_set_prefix;
  smgr->api.stats            = btor_picosat_stats;
  smgr->api.variables        = btor_picosat_variables;

  BTOR_MSG (
      smgr->msg, 1, "PicoSAT allows both incremental and non-incremental mode");
}

#endif
/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_LINGELING

static BtorLGL *
btor_clone_lingeling (BtorLGL *solver, BtorMemMgr *mm)
{
  assert (mm);

  BtorLGL *res;

  if (!solver) return 0;

  assert (solver->lgl);

  BTOR_CNEW (mm, res);
  res->nforked = solver->nforked;
  res->blimit  = solver->blimit;
  res->lgl     = lglmclone (solver->lgl,
                        mm,
                        (lglalloc) btor_sat_malloc,
                        (lglrealloc) btor_sat_realloc,
                        (lgldealloc) btor_sat_free);
  return res;
}

static int
btor_passdown_lingeling_options (BtorSATMgr *smgr,
                                 const char *optstr,
                                 LGL *external_lgl)
{
  char *str, *p, *next, *eq, *opt, *val;
  LGL *lgl = external_lgl ? external_lgl : 0;
  int len, valid, res = 1;

  assert (optstr);
  len = strlen (optstr);

  BTOR_NEWN (smgr->mm, str, len + 1);
  strcpy (str, optstr);

  res = 1;

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

      if (!isalpha (*opt))
        valid = 0;
      else
      {
        for (p = opt + 1; isalnum (*p); p++)
          ;

        if (*p == '=')
        {
          *(eq = p++) = 0;
          val         = p;
          if (*p == '-') p++;
          if (isdigit (*p))
          {
            while (isdigit (*p)) p++;

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

      if (!valid) res = 0;
      if (valid || external_lgl) continue;

      if (eq) *eq = '=';
      BTOR_MSG (smgr->msg,
                0,
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
btor_lingeling_init (BtorSATMgr *smgr)
{
  BtorLGL *res;

  if (*smgr->msg->verbosity >= 1)
  {
    lglbnr ("Lingeling", "[lingeling] ", stdout);
    fflush (stdout);
  }

  BTOR_CNEW (smgr->mm, res);
  res->lgl = lglminit (smgr->mm,
                       (lglalloc) btor_sat_malloc,
                       (lglrealloc) btor_sat_realloc,
                       (lgldealloc) btor_sat_free);
  if (*smgr->msg->verbosity <= 0) lglsetopt (res->lgl, "verbose", -1);
  res->blimit = BTOR_LGL_MIN_BLIMIT;
  assert (res);
  if (smgr->optstr)
    btor_passdown_lingeling_options (smgr, smgr->optstr, res->lgl);
  return res;
}

static void
btor_lingeling_add (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  lgladd (blgl->lgl, lit);
}

static int
btor_lingeling_sat (BtorSATMgr *smgr, int limit)
{
  BtorLGL *blgl = smgr->solver;
  LGL *lgl      = blgl->lgl, *clone;
  const char *str;
  int res, bfres;
  char name[80];

  assert (smgr->satcalls >= 1);

  lglsetopt (lgl, "simplify", 1);

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

  if (smgr->nofork || (0 <= limit && limit < blgl->blimit))
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
      sprintf (name, "[lgl%s%d] ", str, blgl->nforked);
      lglsetprefix (clone, name);
      lglsetout (clone, smgr->output);

#ifndef NDEBUG
      res =
#else
      (void)
#endif
          lglsat (clone);
      if (*smgr->msg->verbosity > 0) lglstats (clone);
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

static int
btor_lingeling_changed (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  return lglchanged (blgl->lgl);
}

static int
btor_lingeling_deref (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglderef (blgl->lgl, lit);
}

static int
btor_lingeling_repr (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglrepr (blgl->lgl, lit);
}

static void
btor_lingeling_reset (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  lglrelease (blgl->lgl);
  BTOR_DELETE (smgr->mm, blgl);
}

static void
btor_lingeling_set_output (BtorSATMgr *smgr, FILE *output)
{
  BtorLGL *blgl = smgr->solver;
  lglsetout (blgl->lgl, output);
}

static void
btor_lingeling_set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  BtorLGL *blgl = smgr->solver;
  lglsetprefix (blgl->lgl, prefix);
}

static void
btor_lingeling_enable_verbosity (BtorSATMgr *smgr, int level)
{
  BtorLGL *blgl = smgr->solver;
  lglsetopt (blgl->lgl, "verbose", level - 1);
}

static int
btor_lingeling_inc_max_var (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  int res       = lglincvar (blgl->lgl);
  if (smgr->inc_required)
    lglfreeze (blgl->lgl, res);
  else
    smgr->used_that_inc_was_not_required = 1;
  return res;
}

static int
btor_lingeling_variables (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  return lglmaxvar (blgl->lgl);
}

static void
btor_lingeling_stats (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  lglstats (blgl->lgl);
  BTOR_MSG (smgr->msg, 1, "%d forked", blgl->nforked);
}

/*------------------------------------------------------------------------*/

static void
btor_lingeling_assume (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  lglassume (blgl->lgl, lit);
}

static void
btor_lingeling_melt (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  if (smgr->inc_required)
  {
    assert (!smgr->used_that_inc_was_not_required);
    lglmelt (blgl->lgl, lit);
  }
}

static int
btor_lingeling_failed (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglfailed (blgl->lgl, lit);
}

static int
btor_lingeling_fixed (BtorSATMgr *smgr, int lit)
{
  BtorLGL *blgl = smgr->solver;
  return lglfixed (blgl->lgl, lit);
}

static int
btor_lingeling_inconsistent (BtorSATMgr *smgr)
{
  BtorLGL *blgl = smgr->solver;
  return lglinconsistent (blgl->lgl);
}

/*------------------------------------------------------------------------*/

int
btor_enable_lingeling_sat (BtorSATMgr *smgr, const char *optstr, int nofork)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before 'btor_enable_lingeling_sat'");

  smgr->optstr = btor_strdup (smgr->mm, optstr);
  if (smgr->optstr && !btor_passdown_lingeling_options (smgr, optstr, 0))
    return 0;

  smgr->name   = "Lingeling";
  smgr->nofork = nofork;

  smgr->api.add              = btor_lingeling_add;
  smgr->api.assume           = btor_lingeling_assume;
  smgr->api.changed          = btor_lingeling_changed;
  smgr->api.deref            = btor_lingeling_deref;
  smgr->api.enable_verbosity = btor_lingeling_enable_verbosity;
  smgr->api.failed           = btor_lingeling_failed;
  smgr->api.fixed            = btor_lingeling_fixed;
  smgr->api.inc_max_var      = btor_lingeling_inc_max_var;
  smgr->api.inconsistent     = btor_lingeling_inconsistent;
  smgr->api.init             = btor_lingeling_init;
  smgr->api.melt             = btor_lingeling_melt;
  smgr->api.repr             = btor_lingeling_repr;
  smgr->api.reset            = btor_lingeling_reset;
  smgr->api.sat              = btor_lingeling_sat;
  smgr->api.set_output       = btor_lingeling_set_output;
  smgr->api.set_prefix       = btor_lingeling_set_prefix;
  smgr->api.stats            = btor_lingeling_stats;
  smgr->api.variables        = btor_lingeling_variables;

  BTOR_MSG (smgr->msg,
            1,
            "Lingeling allows both incremental and non-incremental mode");

  return 1;
}
#endif

/*------------------------------------------------------------------------*/

#ifdef BTOR_USE_MINISAT

/*------------------------------------------------------------------------*/

void
btor_enable_minisat_sat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT_SAT (smgr->initialized,
                  "'btor_init_sat' called before 'btor_enable_minisat_sat'");

  smgr->name   = "MiniSAT";
  smgr->optstr = 0;

  smgr->api.add              = btor_minisat_add;
  smgr->api.assume           = btor_minisat_assume;
  smgr->api.changed          = btor_minisat_changed;
  smgr->api.deref            = btor_minisat_deref;
  smgr->api.enable_verbosity = btor_minisat_enable_verbosity;
  smgr->api.failed           = btor_minisat_failed;
  smgr->api.fixed            = btor_minisat_fixed;
  smgr->api.inc_max_var      = btor_minisat_inc_max_var;
  smgr->api.inconsistent     = btor_minisat_inconsistent;
  smgr->api.init             = btor_minisat_init;
  smgr->api.melt             = 0;
  smgr->api.repr             = btor_minisat_repr;
  smgr->api.reset            = btor_minisat_reset;
  smgr->api.sat              = btor_minisat_sat;
  smgr->api.set_output       = btor_minisat_set_output;
  smgr->api.set_prefix       = btor_minisat_set_prefix;
  smgr->api.stats            = btor_minisat_stats;
  smgr->api.variables        = btor_minisat_variables;

  BTOR_MSG (
      smgr->msg, 1, "MiniSAT allows both incremental and non-incremental mode");
}

#endif

int
btor_set_sat_solver (BtorSATMgr *smgr,
                     const char *solver,
                     const char *optstr,
                     int nofork)
{
  assert (smgr);
  assert (solver);
#ifndef BTOR_USE_LINGELING
  (void) optstr;
  (void) nofork;
#endif

  if (!strcasecmp (solver, "lingeling"))
#ifdef BTOR_USE_LINGELING
  {
    btor_enable_lingeling_sat (smgr, optstr, nofork);
    return 1;
  }
#else
    return 0;
#endif

  if (!strcasecmp (solver, "minisat"))
#ifdef BTOR_USE_MINISAT
  {
    btor_enable_minisat_sat (smgr);
    return 1;
  }
#else
    return 0;
#endif

  if (!strcasecmp (solver, "picosat"))
#ifdef BTOR_USE_PICOSAT
  {
    btor_enable_picosat_sat (smgr);
    return 1;
  }
#else
    return 0;
#endif

  return 0;
}

/*------------------------------------------------------------------------*/
