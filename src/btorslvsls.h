/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLVSLS_H_INCLUDED
#define BTORSLVSLS_H_INCLUDED

#include "utils/btornodemap.h"
#ifndef NDEBUG
#include "btorbv.h"
#endif

#include "btorslv.h"
#include "utils/btorhashint.h"
#include "utils/btorstack.h"

enum BtorSLSMoveKind
{
  BTOR_SLS_MOVE_FLIP = 0,
  BTOR_SLS_MOVE_INC,
  BTOR_SLS_MOVE_DEC,
  BTOR_SLS_MOVE_NOT,
  BTOR_SLS_MOVE_FLIP_RANGE,
  BTOR_SLS_MOVE_FLIP_SEGMENT,
  BTOR_SLS_MOVE_DONE,
  BTOR_SLS_MOVE_RAND,
  BTOR_SLS_MOVE_RAND_WALK,
  BTOR_SLS_MOVE_PROP,
};
typedef enum BtorSLSMoveKind BtorSLSMoveKind;

struct BtorSLSMove
{
  BtorIntHashTable *cans;
  double sc;
};
typedef struct BtorSLSMove BtorSLSMove;

struct BtorSLSConstrData
{
  int64_t weight;
  int64_t selected;
};
typedef struct BtorSLSConstrData BtorSLSConstrData;

BTOR_DECLARE_STACK (BtorSLSMovePtr, BtorSLSMove *);

/*------------------------------------------------------------------------*/

#define BTOR_SLS_SOLVER(btor) ((BtorSLSSolver *) (btor)->slv)

struct BtorSLSSolver
{
  BTOR_SOLVER_STRUCT;

  BtorIntHashTable *roots;   /* must be map (for common propsls funs)
                                but does not maintain anything */
  BtorIntHashTable *weights; /* also maintains assertion weights */
  BtorIntHashTable *score;   /* sls score */

  uint32_t nflips; /* limit, disabled if 0 */
  bool terminate;

  BtorSLSMovePtrStack moves; /* record moves for prob rand walk */
  uint32_t npropmoves;       /* record #no moves for prop moves */
  uint32_t nslsmoves;        /* record #no moves for sls moves */
  double sum_score;          /* record sum of all scores for prob rand walk */

  /* prop moves only */
  uint32_t prop_flip_cond_const_prob;
  int32_t prop_flip_cond_const_prob_delta;
  uint32_t prop_nflip_cond_const;

  /* the following maintain data for the next move (i.e. either the move
   * with the maximum score of all tried moves, or a random walk, or a
   * randomized move). */
  BtorIntHashTable *max_cans; /* list of (can, neigh) */
  double max_score;
  BtorSLSMoveKind max_move; /* move kind (for stats) */
  int32_t max_gw;           /* is groupwise move? (for stats) */

  /* statistics */
  struct
  {
    uint32_t restarts;
    uint32_t moves;
    uint32_t flips;
    uint32_t props;
    uint32_t move_flip;
    uint32_t move_inc;
    uint32_t move_dec;
    uint32_t move_not;
    uint32_t move_range;
    uint32_t move_seg;
    uint32_t move_rand;
    uint32_t move_rand_walk;
    uint32_t move_prop;
    uint32_t move_prop_rec_conf;
    uint32_t move_prop_non_rec_conf;
    uint32_t move_gw_flip;
    uint32_t move_gw_inc;
    uint32_t move_gw_dec;
    uint32_t move_gw_not;
    uint32_t move_gw_range;
    uint32_t move_gw_seg;
    uint32_t move_gw_rand;
    uint32_t move_gw_rand_walk;
    uint64_t updates;
  } stats;

  struct
  {
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BtorSLSSolver BtorSLSSolver;

BtorSolver *btor_new_sls_solver (Btor *btor);

#endif
