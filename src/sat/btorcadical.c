/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
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
  return ccadical_init ();
}

static void
add (BtorSATMgr *smgr, int32_t lit)
{
  ccadical_add (smgr->solver, lit);
}

static int32_t
sat (BtorSATMgr *smgr, int32_t limit)
{
  (void) limit;
  return ccadical_sat (smgr->solver);
}

static int32_t
deref (BtorSATMgr *smgr, int32_t lit)
{
  return ccadical_deref (smgr->solver, lit);
}

static void
reset (BtorSATMgr *smgr)
{
  ccadical_reset (smgr->solver);
  smgr->solver = 0;
}

static void
enable_verbosity (BtorSATMgr *smgr, int32_t level)
{
  if (level <= 1)
    ccadical_set_option (smgr->solver, "quiet", 1);
  else if (level >= 2)
    ccadical_set_option (smgr->solver, "verbose", level - 2);
}

/*------------------------------------------------------------------------*/
/* incremental API                                                        */
/*------------------------------------------------------------------------*/

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
  smgr->api.assume           = 0;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = 0;
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
  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
