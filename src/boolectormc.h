/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#ifndef boolectormc_h_INCLUDED
#define boolectormc_h_INCLUDED

/*------------------------------------------------------------------------*/

#include "boolector.h"

/*------------------------------------------------------------------------*/

typedef struct BtorMC BtorMC;

/*------------------------------------------------------------------------*/

/* Create new model checker instance. */
BtorMC *boolector_mc_new (void);

/* Delete model checker instance. */
void boolector_mc_delete (BtorMC *mc);

/*------------------------------------------------------------------------*/

enum BtorMCOption
{
  /* Print statistics for frame Boolector instance. */
  BTOR_MC_OPT_BTOR_STATS,
  /* Set the minimum bound for BMC */
  BTOR_MC_OPT_MIN_K,
  /* Set the maximum bound for BMC */
  BTOR_MC_OPT_MAX_K,
  /* Enable (val: 1) or disable (val: 0) stopping a the first reached bad
   * state property (default: 1). Disabling this option will result in the
   * model checker to run until all properties have been reached (or proven
   * not to be reachable) or the maximum bound is reached.  */
  BTOR_MC_OPT_STOP_FIRST,
  /* Enable (val: 1) or disable (val: 0) trace generation.
   * In order to be able to obtain the trace after model checking you
   * need to enable this option before calling 'boolector_mc_bmc'. */
  BTOR_MC_OPT_TRACE_GEN,
  /* Enable (val: 1) or disable (val: 0) to print states in every step if
   * BTOR_MC_OPT_TRACE_GEN is enabled. */
  BTOR_MC_OPT_TRACE_GEN_FULL,
  /* Set the level of verbosity. */
  BTOR_MC_OPT_VERBOSITY,
  /* This MUST be the last entry! */
  BTOR_MC_OPT_NUM_OPTS,
};
typedef enum BtorMCOption BtorMCOption;

/* Set model checker option. */
void boolector_mc_set_opt (BtorMC *mc, BtorMCOption opt, uint32_t val);
/* Get current value of model checker option. */
uint32_t boolector_mc_get_opt (BtorMC *mc, BtorMCOption opt);
/* Get min value of model checker option. */
uint32_t boolector_mc_get_opt_min (BtorMC *mc, BtorMCOption opt);
/* Get max value of model checker option.  */
uint32_t boolector_mc_get_opt_max (BtorMC *mc, BtorMCOption opt);
/* Get default value of model checker option. */
uint32_t boolector_mc_get_opt_dflt (BtorMC *mc, BtorMCOption opt);
/* Get long name of model checker option. */
const char *boolector_mc_get_opt_lng (BtorMC *mc, BtorMCOption opt);
/* Get short name of model checker option. */
const char *boolector_mc_get_opt_shrt (BtorMC *mc, BtorMCOption opt);
/* Get description of model checker option. */
const char *boolector_mc_get_opt_desc (BtorMC *mc, BtorMCOption opt);
/* Check if given option is a valid model checker option. */
bool boolector_mc_is_valid_opt (BtorMC *mc, const BtorMCOption opt);

/*------------------------------------------------------------------------*/

/* Get model checker's Boolector instance. */
Btor *boolector_mc_get_btor (BtorMC *mc);

/*------------------------------------------------------------------------*/

/* Initialize state 'node' with constant 'init'. */
void boolector_mc_init (BtorMC *mc, BoolectorNode *state, BoolectorNode *init);

/* Create input. */
BoolectorNode *boolector_mc_input (BtorMC *mc,
                                   BoolectorSort sort,
                                   const char *symbol);
/* Create state. */
BoolectorNode *boolector_mc_state (BtorMC *mc,
                                   BoolectorSort sort,
                                   const char *symbol);

/* Define 'next' state of 'state'. */
void boolector_mc_next (BtorMC *, BoolectorNode *state, BoolectorNode *next);

/* Define safety property 'bad'. */
int32_t boolector_mc_bad (BtorMC *mc, BoolectorNode *bad);
/* Define invariant 'constraint'. */
int32_t boolector_mc_constraint (BtorMC *mc, BoolectorNode *constraint);

/*------------------------------------------------------------------------*/

void boolector_mc_dump (BtorMC *mc, FILE *file);

/*------------------------------------------------------------------------*/

#define BTOR_MC_BOUND_NONE -1
#define BTOR_MC_BOUND_DEFAULT 20

int32_t boolector_mc_bmc (BtorMC *, int32_t mink, int32_t maxk);

/*------------------------------------------------------------------------*/

/* Assumes that 'boolector_mc_set_opt (mc, BTOR_MC_OPT_TRACE_GEN, 1)'
 * was called before calling 'boolector_mc_bmc' which returned a 'k' with
 * '0 <= time <= k'.
 */
char *boolector_mc_assignment (BtorMC *mc, BoolectorNode *node, int32_t time);

/* The caller of 'boolector_mc_assignment' has to release the returned
 * assignment with this 'boolector_mc_free_assignment' again.
 */
void boolector_mc_free_assignment (BtorMC *mc, char *assignment);

// TODO: api for array models

/*------------------------------------------------------------------------*/
/* Return the 'k' at which a previous model checking run proved that the bad
 * state property with index 'badidx' was reached or a negative number if
 * it was not reached.  This does not make much sense if the model checker
 * stops at the first reached property.  So if this function is used
 * it is an error if the user did not request to continue after the first
 * property was reached.
 */
int32_t boolector_mc_reached_bad_at_bound (BtorMC *mc, int32_t badidx);

/* Alternatively the user can provide a call back function which is called
 * the first time a bad state property is reached.  The same comment as in
 * the previous function applies, e.g. the user might want to call
 * 'boolector_mc_set_opt (mc, BTOR_MC_OPT_STOP_FIRST, 0)' before
 * calling the model checker.
 */
typedef void (*BtorMCReachedAtBound) (void *, int32_t badidx, int32_t k);

void boolector_mc_set_reached_at_bound_call_back (BtorMC *mc,
                                                  void *state,
                                                  BtorMCReachedAtBound fun);

/*------------------------------------------------------------------------*/

typedef void (*BtorMCStartingBound) (void *, int32_t k);

void boolector_mc_set_starting_bound_call_back (BtorMC *mc,
                                                void *state,
                                                BtorMCStartingBound fun);

/*------------------------------------------------------------------------*/

#endif
