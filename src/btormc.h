/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2013 Armin Biere.
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/

#ifndef BTORMC_H_INCLUDED
#define BTORMC_H_INCLUDED

#include "btormctypes.h"
#include "utils/boolectornodemap.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"

#include <stdio.h>

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

/*------------------------------------------------------------------------*/

struct BtorMCOpt
{
  bool isflag;      /* flag? */
  const char *shrt; /* short option identifier (may be 0) */
  const char *lng;  /* long option identifier */
  const char *desc; /* description */
  uint32_t val;     /* value */
  uint32_t dflt;    /* default value */
  uint32_t min;     /* min value */
  uint32_t max;     /* max value */
};
typedef struct BtorMCOpt BtorMCOpt;

/*------------------------------------------------------------------------*/

struct BtorMCInput
{
  int32_t id;
  BoolectorNode *node;
};
typedef struct BtorMCInput BtorMCInput;

struct BtorMCstate
{
  int32_t id;
  BoolectorNode *node, *next, *init;
};
typedef struct BtorMCstate BtorMCstate;

enum BtorMCState
{
  BTOR_NO_MC_STATE    = 0,
  BTOR_SAT_MC_STATE   = 10,
  BTOR_UNSAT_MC_STATE = 20,
};
typedef enum BtorMCState BtorMCState;

struct BtorMCFrame
{
  int32_t time;
  BoolectorNodeMap *model2const;
  BoolectorNodePtrStack inputs, init, states, next, bad;
};
typedef struct BtorMCFrame BtorMCFrame;

BTOR_DECLARE_STACK (BtorMCFrame, BtorMCFrame);

/*------------------------------------------------------------------------*/

struct BtorMC
{
  BtorMemMgr *mm;
  BtorMCOpt *options;
  BtorMCState state;
  int32_t initialized, nextstates;
  Btor *btor, *forward;
  BtorMCFrameStack frames;
  BtorPtrHashTable *inputs;
  BtorPtrHashTable *states;
  BoolectorNodePtrStack bad;
  BoolectorNodePtrStack constraints;
  BtorIntStack reached;
  uint32_t num_reached;
  struct
  {
    struct
    {
      void *state;
      BtorMCReachedAtBound fun;
    } reached_at_bound;
    struct
    {
      void *state;
      BtorMCStartingBound fun;
    } starting_bound;
  } call_backs;
};

/*------------------------------------------------------------------------*/

/* Create new model checker instance. */
BtorMC *btor_mc_new (void);

/* Delete model checker instance. */
void btor_mc_delete (BtorMC *mc);

/* Set model checker option. */
void btor_mc_set_opt (BtorMC *mc, BtorMCOption opt, uint32_t val);
/* Get current value of model checker option. */
uint32_t btor_mc_get_opt (BtorMC *mc, BtorMCOption opt);
/* Get min value of model checker option. */
uint32_t btor_mc_get_opt_min (BtorMC *mc, BtorMCOption opt);
/* Get max value of model checker option.  */
uint32_t btor_mc_get_opt_max (BtorMC *mc, BtorMCOption opt);
/* Get default value of model checker option. */
uint32_t btor_mc_get_opt_dflt (BtorMC *mc, BtorMCOption opt);
/* Get long name of model checker option. */
const char *btor_mc_get_opt_lng (BtorMC *mc, BtorMCOption opt);
/* Get short name of model checker option. */
const char *btor_mc_get_opt_shrt (BtorMC *mc, BtorMCOption opt);
/* Get description of model checker option. */
const char *btor_mc_get_opt_desc (BtorMC *mc, BtorMCOption opt);
/* Check if given option is a valid model checker option. */
bool btor_mc_is_valid_opt (BtorMC *mc, const BtorMCOption opt);

/* Get model checker's Boolector instance. */
Btor *btor_mc_get_btor (BtorMC *mc);

/*------------------------------------------------------------------------*/

/* Create input. */
BoolectorNode *btor_mc_input (BtorMC *mc,
                              BoolectorSort sort,
                              const char *symbol);
/* Create state. */
BoolectorNode *btor_mc_state (BtorMC *mc,
                              BoolectorSort sort,
                              const char *symbol);

/*------------------------------------------------------------------------*/

/* Initialize state 'node' with constant 'init'. */
void btor_mc_init (BtorMC *, BoolectorNode *node, BoolectorNode *init);

/* Define 'next' state of 'node'. */
void btor_mc_next (BtorMC *, BoolectorNode *node, BoolectorNode *next);

/*------------------------------------------------------------------------*/

/* Define safety property 'bad'. */
uint32_t btor_mc_bad (BtorMC *, BoolectorNode *bad);

/* Define invariant 'constraint'. */
uint32_t btor_mc_constraint (BtorMC *, BoolectorNode *constraint);

/*------------------------------------------------------------------------*/

void btor_mc_dump (BtorMC *, FILE *);

/*------------------------------------------------------------------------*/

int32_t btor_mc_bmc (BtorMC *, int32_t mink, int32_t maxk);

/*------------------------------------------------------------------------*/

/* Assumes that 'btor_mc_set_opt (mc, BTOR_MC_OPT_TRACE_GEN, 1)'
 * was called before calling 'btor_mc_bmc' which returned a 'k' with
 * '0 <= time <= k'.
 */
char *btor_mc_assignment (BtorMC *mc, BoolectorNode *node, int32_t time);

/* The caller of 'btor_mc_assignment' has to release the returned
 * assignment with this 'btor_mc_free_assignment' again.
 */
void btor_mc_free_assignment (BtorMC *mc, char *assignment);

/*------------------------------------------------------------------------*/

/* Return the 'k' at which a previous model checking run proved that the bad
 * state property with index 'badidx' was reached or a negative number if
 * it was not reached.  This does not make much sense if the model checker
 * stops at the first reached property.  So if this function is used
 * it is an error if the user did not request to continue after the first
 * property was reached.
 */
int32_t btor_mc_reached_bad_at_bound (BtorMC *mc, int32_t badidx);

/* Alternatively the user can provide a call back function which is called
 * the first time a bad state property is reached.  The same comment as in
 * the previous function applies, e.g. the user might want to call
 * 'btor_mc_set_opt (mc, BTOR_MC_OPT_STOP_FIRST, 0)' before
 * calling the model checker.
 */
void btor_mc_set_reached_at_bound_call_back (BtorMC *mc,
                                             void *state,
                                             BtorMCReachedAtBound fun);

/*------------------------------------------------------------------------*/

void btor_mc_set_starting_bound_call_back (BtorMC *mc,
                                           void *state,
                                           BtorMCStartingBound fun);

/*------------------------------------------------------------------------*/

#endif
