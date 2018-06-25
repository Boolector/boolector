/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2014 Armin Biere.
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolectormc.h"
#include "btormc.h"

#include "btorabort.h"
#include "btornode.h"

/*------------------------------------------------------------------------*/

#define BTOR_MC_ABORT_IF_STATE(MC)               \
  do                                             \
  {                                              \
    BTOR_ABORT ((MC)->state != BTOR_NO_MC_STATE, \
                "model checker was run before"); \
  } while (0)

#define BTOR_MC_CHECK_OWNS_NODE_ARG(NODE)                             \
  do                                                                  \
  {                                                                   \
    BTOR_ABORT_ARG_NULL (NODE);                                       \
    BTOR_ABORT (boolector_get_btor (NODE) != mc->btor,                \
                "node '" #NODE                                        \
                "' does not belong to 'Btor' of this model checker"); \
  } while (0)

/*------------------------------------------------------------------------*/

BtorMC *
boolector_mc_new (void)
{
  return btor_mc_new ();
}

void
boolector_mc_delete (BtorMC *mc)
{
  BTOR_ABORT_ARG_NULL (mc);
  btor_mc_delete (mc);
}

/*------------------------------------------------------------------------*/

void
boolector_mc_set_opt (BtorMC *mc, BtorMCOption opt, uint32_t val)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  BTOR_ABORT (val < btor_mc_get_opt_min (mc, opt)
                  || val > btor_mc_get_opt_max (mc, opt),
              "invalid option value '%u' for option '%s'",
              val,
              btor_mc_get_opt_lng (mc, opt));
  BTOR_ABORT (
      val && opt == BTOR_MC_OPT_TRACE_GEN && mc->state != BTOR_NO_MC_STATE,
      "trace generation can not be enabled if model checker was "
      "run before");
  btor_mc_set_opt (mc, opt, val);
}

uint32_t
boolector_mc_get_opt (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt (mc, opt);
}

uint32_t
boolector_mc_get_opt_min (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt_min (mc, opt);
}

uint32_t
boolector_mc_get_opt_max (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt_max (mc, opt);
}

uint32_t
boolector_mc_get_opt_dflt (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt_dflt (mc, opt);
}

const char *
boolector_mc_get_opt_lng (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt_lng (mc, opt);
}

const char *
boolector_mc_get_opt_shrt (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt_shrt (mc, opt);
}

const char *
boolector_mc_get_opt_desc (BtorMC *mc, BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (!btor_mc_is_valid_opt (mc, opt), "invalid option");
  return btor_mc_get_opt_desc (mc, opt);
}

bool
boolector_mc_is_valid_opt (BtorMC *mc, const BtorMCOption opt)
{
  BTOR_ABORT_ARG_NULL (mc);
  return btor_mc_is_valid_opt (mc, opt);
}

/*------------------------------------------------------------------------*/

Btor *
boolector_mc_get_btor (BtorMC *mc)
{
  BTOR_ABORT_ARG_NULL (mc);
  return btor_mc_get_btor (mc);
}

/*------------------------------------------------------------------------*/

BoolectorNode *
boolector_mc_state (BtorMC *mc, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (sort);
  BTOR_ABORT (mc->state != BTOR_NO_MC_STATE,
              "may not be called after checking");
  BTOR_ABORT (!boolector_is_bitvec_sort (mc->btor, sort)
                  && !boolector_is_array_sort (mc->btor, sort),
              "invalid state sort");
  return btor_mc_state (mc, sort, symbol);
}

BoolectorNode *
boolector_mc_input (BtorMC *mc, BoolectorSort sort, const char *symbol)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (sort);
  BTOR_ABORT (mc->state != BTOR_NO_MC_STATE,
              "may not be called after checking");
  return btor_mc_input (mc, sort, symbol);
}

/*------------------------------------------------------------------------*/

void
boolector_mc_init (BtorMC *mc, BoolectorNode *state, BoolectorNode *init)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (state);
  BTOR_MC_CHECK_OWNS_NODE_ARG (init);
  btor_mc_init (mc, state, init);
}

void
boolector_mc_next (BtorMC *mc, BoolectorNode *state, BoolectorNode *next)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (state);
  BTOR_MC_CHECK_OWNS_NODE_ARG (next);
  btor_mc_next (mc, state, next);
}

/*------------------------------------------------------------------------*/

uint32_t
boolector_mc_bad (BtorMC *mc, BoolectorNode *bad)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (bad);
  return btor_mc_bad (mc, bad);
}

uint32_t
boolector_mc_constraint (BtorMC *mc, BoolectorNode *constraint)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_MC_ABORT_IF_STATE (mc);
  BTOR_MC_CHECK_OWNS_NODE_ARG (constraint);
  return btor_mc_constraint (mc, constraint);
}

/*------------------------------------------------------------------------*/

void
boolector_mc_dump (BtorMC *mc, FILE *file)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (file);
  btor_mc_dump (mc, file);
}

/*------------------------------------------------------------------------*/

int32_t
boolector_mc_bmc (BtorMC *mc, int32_t mink, int32_t maxk)
{
  BTOR_ABORT_ARG_NULL (mc);
  return btor_mc_bmc (mc, mink, maxk);
}

/*------------------------------------------------------------------------*/

char *
boolector_mc_assignment (BtorMC *mc, BoolectorNode *node, int32_t time)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (mc->state == BTOR_NO_MC_STATE,
              "model checker was not run before");
  BTOR_ABORT (mc->state == BTOR_UNSAT_MC_STATE,
              "model checking status is UNSAT");
  BTOR_ABORT (!btor_mc_get_opt (mc, BTOR_MC_OPT_TRACE_GEN),
              "'btor_mc_enable_trace_gen' was not called before");
  BTOR_ABORT_ARG_NULL (node);
  BTOR_ABORT_REFS_NOT_POS ((BtorNode *) node);
  BTOR_MC_CHECK_OWNS_NODE_ARG (node);
  BTOR_ABORT (0 > time, "negative 'time' argument");
  BTOR_ABORT ((size_t) time >= BTOR_COUNT_STACK (mc->frames),
              "'time' exceeds previously returned bound");

  return btor_mc_assignment (mc, node, time);
}

void
boolector_mc_free_assignment (BtorMC *mc, char *assignment)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (assignment);
  btor_mc_free_assignment (mc, assignment);
}

/*------------------------------------------------------------------------*/

int32_t
boolector_mc_reached_bad_at_bound (BtorMC *mc, int32_t badidx)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT (mc->state == BTOR_NO_MC_STATE,
              "model checker was not run before");
  BTOR_ABORT (btor_mc_get_opt (mc, BTOR_MC_OPT_STOP_FIRST),
              "stopping at first reached property must be disabled");
  BTOR_ABORT (badidx < 0, "negative bad state property index");
  BTOR_ABORT ((size_t) badidx >= BTOR_COUNT_STACK (mc->bad),
              "bad state property index too large");
  return btor_mc_reached_bad_at_bound (mc, badidx);
}

void
boolector_mc_set_reached_at_bound_call_back (BtorMC *mc,
                                             void *state,
                                             BtorMCReachedAtBound fun)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (state);
  BTOR_ABORT_ARG_NULL (fun);
  btor_mc_set_reached_at_bound_call_back (mc, state, fun);
}

/*------------------------------------------------------------------------*/

void
boolector_mc_set_starting_bound_call_back (BtorMC *mc,
                                           void *state,
                                           BtorMCStartingBound fun)
{
  BTOR_ABORT_ARG_NULL (mc);
  BTOR_ABORT_ARG_NULL (state);
  BTOR_ABORT_ARG_NULL (fun);
  btor_mc_set_starting_bound_call_back (mc, state, fun);
}

/*------------------------------------------------------------------------*/
