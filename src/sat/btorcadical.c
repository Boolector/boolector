/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "sat/btorcadical.h"
#include "btorabort.h"

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_CADICAL
/*------------------------------------------------------------------------*/

#include "btorcore.h"
#include "ccadical.h"

static void *
init (BtorSATMgr *smgr)
{
  (void) smgr;
  CCaDiCaL *slv = ccadical_init ();
  if (smgr->inc_required
      && btor_opt_get (smgr->btor, BTOR_OPT_SAT_ENGINE_CADICAL_FREEZE))
  {
    ccadical_set_option (slv, "checkfrozen", 1);
  }
  return slv;
}

static void
add (BtorSATMgr *smgr, int32_t lit)
{
  ccadical_add (smgr->solver, lit);
}

static void
assume (BtorSATMgr *smgr, int32_t lit)
{
  ccadical_assume (smgr->solver, lit);
}

static int32_t
deref (BtorSATMgr *smgr, int32_t lit)
{
  int32_t val;
  val = ccadical_deref (smgr->solver, lit);
  if (val > 0)
    return 1;
  if (val < 0)
    return -1;
  return 0;
}

static void
enable_verbosity (BtorSATMgr *smgr, int32_t level)
{
  if (level <= 1)
    ccadical_set_option (smgr->solver, "quiet", 1);
  else if (level >= 2)
    ccadical_set_option (smgr->solver, "verbose", level - 2);
}

static int32_t
failed (BtorSATMgr *smgr, int32_t lit)
{
  return ccadical_failed (smgr->solver, lit);
}

static void
reset (BtorSATMgr *smgr)
{
  ccadical_reset (smgr->solver);
  smgr->solver = 0;
}

static int32_t
sat (BtorSATMgr *smgr, int32_t limit)
{
  (void) limit;
  return ccadical_sat (smgr->solver);
}

static void
setterm (BtorSATMgr *smgr)
{
  /* for CaDiCaL, state is the first argument (unlike, e.g., Lingeling) */
  ccadical_set_terminate (smgr->solver, smgr->term.state, smgr->term.fun);
}

/*------------------------------------------------------------------------*/
/* incremental API                                                        */
/*------------------------------------------------------------------------*/

static int32_t
inc_max_var (BtorSATMgr *smgr)
{
  int32_t var = smgr->maxvar + 1;
  if (smgr->inc_required)
  {
    ccadical_freeze (smgr->solver, var);
  }
  return var;
}

static void
melt (BtorSATMgr *smgr, int32_t lit)
{
  if (smgr->inc_required) ccadical_melt (smgr->solver, lit);
}

/*------------------------------------------------------------------------*/

bool
btor_sat_enable_cadical (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_cadical'");

  smgr->name = "CaDiCaL";

  BTOR_CLR (&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = failed;
  smgr->api.fixed            = 0;
  smgr->api.inc_max_var      = 0;
  smgr->api.init             = init;
  smgr->api.melt             = 0;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = 0;
  smgr->api.set_prefix       = 0;
  smgr->api.stats            = 0;
  smgr->api.setterm          = setterm;

  if (btor_opt_get (smgr->btor, BTOR_OPT_SAT_ENGINE_CADICAL_FREEZE))
  {
    smgr->api.inc_max_var = inc_max_var;
    smgr->api.melt        = melt;
  }
  else
  {
    smgr->have_restore = true;
  }

  return true;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
