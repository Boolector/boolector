/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPROPUTILS_H_INCLUDED
#define BTORPROPUTILS_H_INCLUDED

#include "btorslvprop.h"
#include "btorslvsls.h"

#include "btorbv.h"
#include "btorlog.h"
#include "btormodel.h"
#include "btornode.h"
#include "btortypes.h"
#include "utils/btorhashint.h"

/*------------------------------------------------------------------------*/

#define BTOR_PROPUTILS_PROB_FLIP_COND_CONST_DELTA 100

/*------------------------------------------------------------------------*/

uint64_t btor_proputils_select_move_prop (Btor* btor,
                                          BtorNode* root,
                                          BtorNode** input,
                                          BtorBitVector** assignment);

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
BtorBitVector* inv_add_bv (Btor* btor,
                           BtorNode* add_exp,
                           BtorBitVector* bvadd,
                           BtorBitVector* bve,
                           int32_t eidx);

BtorBitVector* inv_and_bv (Btor* btor,
                           BtorNode* and_exp,
                           BtorBitVector* bvand,
                           BtorBitVector* bve,
                           int32_t eidx);

BtorBitVector* inv_eq_bv (Btor* btor,
                          BtorNode* eq_exp,
                          BtorBitVector* bveq,
                          BtorBitVector* bve,
                          int32_t eidx);

BtorBitVector* inv_ult_bv (Btor* btor,
                           BtorNode* ult_exp,
                           BtorBitVector* bvult,
                           BtorBitVector* bve,
                           int32_t eidx);

BtorBitVector* inv_sll_bv (Btor* btor,
                           BtorNode* sll_exp,
                           BtorBitVector* bvsll,
                           BtorBitVector* bve,
                           int32_t eidx);

BtorBitVector* inv_srl_bv (Btor* btor,
                           BtorNode* srl_exp,
                           BtorBitVector* bvsrl,
                           BtorBitVector* bve,
                           int32_t eidx);

BtorBitVector* inv_mul_bv (Btor* btor,
                           BtorNode* mul_exp,
                           BtorBitVector* bvmul,
                           BtorBitVector* bve,
                           int32_t eidx);

BtorBitVector* inv_udiv_bv (Btor* btor,
                            BtorNode* div_exp,
                            BtorBitVector* bvdiv,
                            BtorBitVector* bve,
                            int32_t eidx);

BtorBitVector* inv_urem_bv (Btor* btor,
                            BtorNode* urem_exp,
                            BtorBitVector* bvurem,
                            BtorBitVector* bve,
                            int32_t eidx);

BtorBitVector* inv_concat_bv (Btor* btor,
                              BtorNode* conc_exp,
                              BtorBitVector* bvconc,
                              BtorBitVector* bve,
                              int32_t eidx);

BtorBitVector* inv_slice_bv (Btor* btor,
                             BtorNode* slice_exp,
                             BtorBitVector* bvslice,
                             BtorBitVector* bve,
                             int32_t eidx);

BtorBitVector* inv_cond_bv (Btor* btor,
                            BtorNode* cond_exp,
                            BtorBitVector* bvcond,
                            BtorBitVector* bve,
                            int32_t eidx);

int32_t sat_prop_solver_aux (Btor* btor);
#endif

/*------------------------------------------------------------------------*/

#endif
