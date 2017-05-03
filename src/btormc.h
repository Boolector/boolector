/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#ifndef btormc_h_INCLUDED
#define btormc_h_INCLUDED

/*------------------------------------------------------------------------*/

#include "boolector.h"

/*------------------------------------------------------------------------*/

typedef struct BtorMC BtorMC;

/*------------------------------------------------------------------------*/

BtorMC *boolector_mc_new (void);
void boolector_mc_delete (BtorMC *);

void boolector_mc_set_verbosity (BtorMC *, uint32_t verbosity);

/* Default is to stop at the first reached bad state property.  Given a zero
 * argument 'stop == 0' to this function will result in the model checker to
 * run until all properties have been reached (or proven not to be
 * reachable) or the maximum bound is reached.
 */
void boolector_mc_set_stop_at_first_reached_property (BtorMC *, bool stop);

/* In order to be able to obtain the trace after model checking you
 * need to request trace generation (before calling 'boolector_mc_bmc').
 */
void boolector_mc_enable_trace_gen (BtorMC *);

/*------------------------------------------------------------------------*/

Btor *boolector_mc_btor (BtorMC *);

/*------------------------------------------------------------------------*/

void boolector_mc_init (BtorMC *, BoolectorNode *latch, BoolectorNode *init);

/*------------------------------------------------------------------------*/
/* model checking API */

BoolectorNode *boolector_input (BtorMC *, uint32_t width, const char *);
BoolectorNode *boolector_latch (BtorMC *, uint32_t width, const char *);

void boolector_next (BtorMC *, BoolectorNode *latch, BoolectorNode *next);

int32_t boolector_bad (BtorMC *, BoolectorNode *bad);

int32_t boolector_constraint (BtorMC *, BoolectorNode *constraint);

/*------------------------------------------------------------------------*/

void boolector_mc_dump (BtorMC *, FILE *);

/*------------------------------------------------------------------------*/

int32_t boolector_mc_bmc (BtorMC *, int32_t mink, int32_t maxk);

/*------------------------------------------------------------------------*/

/* Return the 'k' at which a previous model checking run proved that the bad
 * state property with index 'badidx' was reached or a negative number if
 * it was not reached.  This does not make much sense if the model checker
 * stops at the first reached property.  So if this function is used
 * it is an error if the user did not request to continue after the first
 * property was reached.
 */
int32_t boolector_mc_reached_bad_at_bound (BtorMC *, int32_t badidx);

/* Alternatively the user can provide a call back function which is called
 * the first time a bad state property is reached.  The same comment as in
 * the previous function applies, e.g. the user might want to call
 * 'boolector_mc_set_stop_at_first_reached_property (btormc, 0)' before
 * calling the model checker.
 */
typedef void (*BtorMCReachedAtBound) (void *, int32_t badidx, int32_t k);

void boolector_mc_set_reached_at_bound_call_back (BtorMC *,
                                                  void *state,
                                                  BtorMCReachedAtBound fun);

/*------------------------------------------------------------------------*/

typedef void (*BtorMCStartingBound) (void *, int32_t k);

void boolector_mc_set_starting_bound_call_back (BtorMC *,
                                                void *state,
                                                BtorMCStartingBound fun);

/*------------------------------------------------------------------------*/

/* Assumes that 'boolector_mc_enable_trace_gen' was called and then
 * 'boolector_mc_bmc' which returned a 'k' with '0 <= time <= k'.
 */
char *boolector_mc_assignment (BtorMC *,
                               BoolectorNode *input_or_latch,
                               int32_t time);

/* The caller of 'boolector_mc_assignment' has to release the returned
 * assignment with this 'boolector_mc_free_assignment' again.
 */
void boolector_mc_free_assignment (BtorMC *, char *);

/*------------------------------------------------------------------------*/
#endif
