/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Andrew V. Jones
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "sat/btorkissat.h"

#include "btorabort.h"

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "btorcore.h"
#include "kissat/kissat.h"

static void *
init (BtorSATMgr *smgr)
{
  kissat *res;

  BTOR_MSG (smgr->btor->msg, 1, "Kissat Version %s", kissat_version ());

  res = kissat_init ();

  return res;
}

static void
add (BtorSATMgr *smgr, int32_t lit)
{
  (void) kissat_add (smgr->solver, lit);
}

static int32_t
sat (BtorSATMgr *smgr, int32_t limit)
{
  (void) limit;
  return kissat_solve (smgr->solver);
}

static int32_t
deref (BtorSATMgr *smgr, int32_t lit)
{
  return kissat_value (smgr->solver, lit);
}

static void
reset (BtorSATMgr *smgr)
{
  kissat_release (smgr->solver);
  smgr->solver = 0;
}

bool
btor_sat_enable_kissat (BtorSATMgr *smgr)
{
  assert (smgr != NULL);

  BTOR_ABORT (smgr->initialized,
              "'btor_sat_init' called before 'btor_sat_enable_kissat'");

  smgr->name = "Kissat";

  BTOR_CLR (&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = 0;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = 0;
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
