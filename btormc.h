/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
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

BtorMC *boolector_new_mc (void);
void boolector_delete_mc (BtorMC *);

void boolector_set_verbosity_mc (BtorMC *, int verbosity);

/* In order to be able to obtain the trace afte model checking you
 * need to request trace generation (before calling 'boolector_bmc').
 */
void boolector_enable_trace_gen (BtorMC *);

/*------------------------------------------------------------------------*/

Btor *boolector_btor_mc (BtorMC *);

/*------------------------------------------------------------------------*/

BoolectorNode *boolector_input (BtorMC *, int width, const char *);
BoolectorNode *boolector_latch (BtorMC *, int width, const char *);

void boolector_next (BtorMC *, BoolectorNode *latch, BoolectorNode *next);

void boolector_init (BtorMC *, BoolectorNode *latch, BoolectorNode *init);

int boolector_bad (BtorMC *, BoolectorNode *bad);

int boolector_constraint (BtorMC *, BoolectorNode *constraint);

/*------------------------------------------------------------------------*/

void boolector_dump_btormc (BtorMC *, FILE *);

/*------------------------------------------------------------------------*/

int boolector_bmc (BtorMC *, int mink, int maxk);

/* Assumes that 'boolector_enable_trace_gen' was called and then
 * 'boolector_bmc' which returned a 'k' with '0 <= time <= k'.
 */
char *boolector_mc_assignment (BtorMC *,
                               BoolectorNode *input_or_latch,
                               int time);

/* The caller of 'boolector_mc_assignment' has to release the returned
 * assignment with this 'boolector_free_mc_assignment' again.
 */
void boolector_free_mc_assignment (BtorMC *, char *);

/*------------------------------------------------------------------------*/
#endif
