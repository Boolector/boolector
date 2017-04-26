/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "sat/btorsatlgl.h"

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_LINGELING
/*------------------------------------------------------------------------*/

#include <ctype.h>
#include <limits.h>
#include "btorabort.h"
#include "btorcore.h"

#define BTOR_LGL_SIMP_DELAY 10000
#define BTOR_LGL_MIN_BLIMIT 50000
#define BTOR_LGL_MAX_BLIMIT 200000

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

  BTOR_NEWN (smgr->btor->mm, str, len + 1);
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
            BTOR_MSG (smgr->btor->msg,
                      2,
                      "setting Lingeling option --%s=%s",
                      opt,
                      val);
            lglsetopt (lgl, opt, atoi (val));
          }
        }
        else
          valid = 0;
      }

      if (!valid) res = false;
      if (valid || external_lgl) continue;

      if (eq) *eq = '=';
      BTOR_MSG (smgr->btor->msg,
                1,
                "*** can not pass down to Lingeling invalid option '%s'",
                optstr);
    }
  }

  BTOR_DELETEN (smgr->btor->mm, str, len + 1);
  if (lgl && !external_lgl) lglrelease (lgl);

  return res;
}

/*------------------------------------------------------------------------*/

static void *
lingeling_init (BtorSATMgr *smgr)
{
  BtorLGL *res;

  if (btor_opt_get (smgr->btor, BTOR_OPT_VERBOSITY) >= 1)
  {
    lglbnr ("Lingeling", "[lingeling] ", stdout);
    fflush (stdout);
  }

  BTOR_CNEW (smgr->btor->mm, res);
  res->lgl = lglminit (smgr->btor->mm,
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
    BTOR_MSG (smgr->btor->msg, 0, "wrote %s", name);
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
    BTOR_MSG (smgr->btor->msg, 2, "blimit = %d", blgl->blimit);
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
      sprintf (
          name, "[%s lgl%s%d] ", smgr->btor->msg->prefix, str, blgl->nforked);
      lglsetprefix (clone, name);
      lglsetout (clone, smgr->output);

#ifndef NDEBUG
      res =
#else
      (void)
#endif
          lglsat (clone);
      if (btor_opt_get (smgr->btor, BTOR_OPT_VERBOSITY) > 0) lglstats (clone);
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
  BTOR_DELETE (smgr->btor->mm, blgl);
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
  BTOR_MSG (smgr->btor->msg, 1, "%d forked", blgl->nforked);
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

  smgr->optstr = btor_mem_strdup (smgr->btor->mm, optstr);
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

  BTOR_MSG (smgr->btor->msg,
            1,
            "Lingeling allows both incremental and non-incremental mode");
  if (smgr->optstr)
    BTOR_MSG (smgr->btor->msg,
              1,
              "Configured options for Lingeling: %s",
              smgr->optstr);

  return true;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
