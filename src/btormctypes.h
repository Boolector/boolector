/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMCTYPES_H_INCLUDED
#define BTORMCTYPES_H_INCLUDED

#include <stdint.h>

/*------------------------------------------------------------------------*/

typedef struct BtorMC BtorMC;

/*------------------------------------------------------------------------*/

/* Boolector model checker options. */

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

/*------------------------------------------------------------------------*/

/**
 * Call back function, called at the first time a bad state property is
 * reached.  This does not make much sense if the model checker stops at the
 * first reached property. Hence, if this function is used, it is an error if
 * the user did not request to continue after the first property was reached.
 * To do so, set 'boolector_mc_set_opt (mc, BTOR_MC_OPT_STOP_FIRST, 0)' before
 * calling the model checker.
 */
typedef void (*BtorMCReachedAtBound) (void *, int32_t badidx, int32_t k);

typedef void (*BtorMCStartingBound) (void *, int32_t k);

/*------------------------------------------------------------------------*/
#endif
