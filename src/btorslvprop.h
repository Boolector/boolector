/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
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

struct BtorPropSolver
{
  BTOR_SOLVER_STRUCT;

  BtorPtrHashTable *roots; /* maintains n times selected */
  BtorPtrHashTable *score;

  struct
  {
    uint32_t restarts;
    uint32_t moves;
    uint32_t move_prop_rec_conf;
    uint32_t move_prop_non_rec_conf;
  } stats;

  struct
  {
    double sat;
  } time;
};

typedef struct BtorPropSolver BtorPropSolver;

#define BTOR_PROP_SOLVER(btor) ((BtorPropSolver *) (btor)->slv)

BtorSolver *btor_new_prop_solver (Btor *btor);

/*------------------------------------------------------------------------*/

void btor_select_move_prop (Btor *btor,
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
