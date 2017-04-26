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

#include "sat/btorsatminisat.h"

/*------------------------------------------------------------------------*/
#ifdef BTOR_USE_MINISAT
/*------------------------------------------------------------------------*/

#include "btorminisat.h"

bool
btor_sat_enable_minisat (BtorSATMgr* smgr)
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
