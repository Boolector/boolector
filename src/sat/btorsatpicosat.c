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

#include "sat/btorsatpicosat.h"

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_PICOSAT
/*------------------------------------------------------------------------*/

#include "picosat.h"

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
