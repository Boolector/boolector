/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "sat/btorpicosat.h"
#include "btorabort.h"

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_PICOSAT
/*------------------------------------------------------------------------*/

#include "btorcore.h"
#include "picosat.h"

static void *
init (BtorSATMgr *smgr)
{
  PicoSAT *res;

  BTOR_MSG (smgr->btor->msg, 1, "PicoSAT Version %s", picosat_version ());

  res = picosat_minit (smgr->btor->mm,
                       (picosat_malloc) btor_mem_sat_malloc,
                       (picosat_realloc) btor_mem_sat_realloc,
                       (picosat_free) btor_mem_sat_free);

  picosat_set_global_default_phase (res, 0);

  return res;
}

static void
add (BtorSATMgr *smgr, int32_t lit)
{
  (void) picosat_add (smgr->solver, lit);
}

static int32_t
sat (BtorSATMgr *smgr, int32_t limit)
{
  return picosat_sat (smgr->solver, limit);
}

static int32_t
deref (BtorSATMgr *smgr, int32_t lit)
{
  return picosat_deref (smgr->solver, lit);
}

static void
reset (BtorSATMgr *smgr)
{
  picosat_reset (smgr->solver);
  smgr->solver = 0;
}

static void
set_output (BtorSATMgr *smgr, FILE *output)
{
  picosat_set_output (smgr->solver, output);
}

static void
set_prefix (BtorSATMgr *smgr, const char *prefix)
{
  picosat_set_prefix (smgr->solver, prefix);
}

static void
enable_verbosity (BtorSATMgr *smgr, int32_t level)
{
  if (level >= 2) picosat_set_verbosity (smgr->solver, level - 1);
}

static int32_t
inc_max_var (BtorSATMgr *smgr)
{
  return picosat_inc_max_var (smgr->solver);
}

static void
stats (BtorSATMgr *smgr)
{
  picosat_stats (smgr->solver);
}

static int32_t
fixed (BtorSATMgr *smgr, int32_t lit)
{
  return picosat_deref_toplevel (smgr->solver, lit);
}

/*------------------------------------------------------------------------*/

static void
assume (BtorSATMgr *smgr, int32_t lit)
{
  (void) picosat_assume (smgr->solver, lit);
}

static int32_t
failed (BtorSATMgr *smgr, int32_t lit)
{
  return picosat_failed_assumption (smgr->solver, lit);
}

/*------------------------------------------------------------------------*/

bool
btor_sat_enable_picosat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_picosat'");

  smgr->name = "PicoSAT";

  BTOR_CLR (&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
  smgr->api.inc_max_var      = inc_max_var;
  smgr->api.init             = init;
  smgr->api.melt             = 0;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = set_output;
  smgr->api.set_prefix       = set_prefix;
  smgr->api.stats            = stats;
  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
