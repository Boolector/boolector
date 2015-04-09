/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLS_H_INCLUDED
#define BTORSLS_H_INCLUDED

#include "btormap.h"

int btor_sat_aux_btor_sls (Btor *btor);
void btor_generate_model_sls (Btor *btor, int model_for_all_nodes, int reset);

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
};
typedef enum BtorSLSMoveKind BtorSLSMoveKind;

struct BtorSLSMove
{
  BtorPtrHashTable *cans;
  double sc;
};
typedef struct BtorSLSMove BtorSLSMove;

BTOR_DECLARE_STACK (BtorSLSMovePtr, BtorSLSMove *);

struct BtorSLSSolver
{
  Btor *btor;

  BtorPtrHashTable *roots; /* also maintains assertion weights */
  BtorPtrHashTable *score;

  BtorSLSMovePtrStack moves; /* record moves for prob rand walk */
  double sum_score;          /* record sum of all scores for prob rand walk */

  /* the following maintain data for the next move (i.e. either the move
   * with the maximum score of all tried moves, or a random walk, or a
   * randomized move). */
  BtorPtrHashTable *max_cans; /* list of (can, neigh) */
  double max_score;
  BtorSLSMoveKind max_move; /* move kind (for stats) */
  int max_gw;               /* is groupwise move? (for stats) */

  /* statistics */
  struct
  {
    int restarts;
    int moves;
    int flips;
    int move_flip;
    int move_inc;
    int move_dec;
    int move_not;
    int move_range;
    int move_seg;
    int move_rand;
    int move_rand_walk;
    int move_gw_flip;
    int move_gw_inc;
    int move_gw_dec;
    int move_gw_not;
    int move_gw_range;
    int move_gw_seg;
    int move_gw_rand;
    int move_gw_rand_walk;
  } stats;
};
typedef struct BtorSLSSolver BtorSLSSolver;

BtorSLSSolver *btor_new_sls_solver (Btor *btor);

BtorSLSSolver *btor_clone_sls_solver (Btor *clone,
                                      BtorSLSSolver *slv,
                                      BtorNodeMap *exp_map);

void btor_delete_sls_solver (Btor *btor, BtorSLSSolver *slv);
void btor_print_stats_sls_solver (Btor *btor, BtorSLSSolver *slv);

#endif
