/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPROP_H_INCLUDED
#define BTORPROP_H_INCLUDED

#include "btorbitvec.h"
#include "btorslv.h"
#include "btortypes.h"
#include "utils/btorhashint.h"

struct BtorPropSolver
{
  BTOR_SOLVER_STRUCT;

  // BtorPtrHashTable *roots;    /* maintains n times selected */
  BtorIntHashTable *roots;
  BtorPtrHashTable *score;

  struct
  {
    uint32_t restarts;
    uint32_t moves;
    uint32_t move_prop_rec_conf;
    uint32_t move_prop_non_rec_conf;
    uint64_t props;
    uint64_t updates;

#ifndef NDEBUG
    uint32_t inv_add;
    uint32_t inv_and;
    uint32_t inv_eq;
    uint32_t inv_ult;
    uint32_t inv_sll;
    uint32_t inv_srl;
    uint32_t inv_mul;
    uint32_t inv_udiv;
    uint32_t inv_urem;
    uint32_t inv_concat;
    uint32_t inv_slice;

    uint32_t cons_add;
    uint32_t cons_and;
    uint32_t cons_eq;
    uint32_t cons_ult;
    uint32_t cons_sll;
    uint32_t cons_srl;
    uint32_t cons_mul;
    uint32_t cons_udiv;
    uint32_t cons_urem;
    uint32_t cons_concat;
    uint32_t cons_slice;
#endif
  } stats;

  struct
  {
    double sat;
    double sat_total;
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BtorPropSolver BtorPropSolver;

#define BTOR_PROP_SOLVER(btor) ((BtorPropSolver *) (btor)->slv)

BtorSolver *btor_new_prop_solver (Btor *btor);

/*------------------------------------------------------------------------*/

uint64_t btor_select_move_prop (Btor *btor,
                                BtorNode *root,
                                BtorNode **input,
                                BtorBitVector **assignment);

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
BtorBitVector *inv_add_bv (Btor *btor,
                           BtorNode *add_exp,
                           BtorBitVector *bvadd,
                           BtorBitVector *bve,
                           int eidx);

BtorBitVector *inv_and_bv (Btor *btor,
                           BtorNode *and_exp,
                           BtorBitVector *bvand,
                           BtorBitVector *bve,
                           int eidx);

BtorBitVector *inv_eq_bv (Btor *btor,
                          BtorNode *eq_exp,
                          BtorBitVector *bveq,
                          BtorBitVector *bve,
                          int eidx);

BtorBitVector *inv_ult_bv (Btor *btor,
                           BtorNode *ult_exp,
                           BtorBitVector *bvult,
                           BtorBitVector *bve,
                           int eidx);

BtorBitVector *inv_sll_bv (Btor *btor,
                           BtorNode *sll_exp,
                           BtorBitVector *bvsll,
                           BtorBitVector *bve,
                           int eidx);

BtorBitVector *inv_srl_bv (Btor *btor,
                           BtorNode *srl_exp,
                           BtorBitVector *bvsrl,
                           BtorBitVector *bve,
                           int eidx);

BtorBitVector *inv_mul_bv (Btor *btor,
                           BtorNode *mul_exp,
                           BtorBitVector *bvmul,
                           BtorBitVector *bve,
                           int eidx);

BtorBitVector *inv_udiv_bv (Btor *btor,
                            BtorNode *div_exp,
                            BtorBitVector *bvdiv,
                            BtorBitVector *bve,
                            int eidx);

BtorBitVector *inv_urem_bv (Btor *btor,
                            BtorNode *urem_exp,
                            BtorBitVector *bvurem,
                            BtorBitVector *bve,
                            int eidx);

BtorBitVector *inv_concat_bv (Btor *btor,
                              BtorNode *conc_exp,
                              BtorBitVector *bvconc,
                              BtorBitVector *bve,
                              int eidx);

BtorBitVector *inv_slice_bv (Btor *btor,
                             BtorNode *slice_exp,
                             BtorBitVector *bvslice,
                             BtorBitVector *bve);

int sat_prop_solver_aux (Btor *btor);
#endif

#endif
