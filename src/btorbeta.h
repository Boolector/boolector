/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBETA_H_INCLUDED
#define BTORBETA_H_INCLUDED

#include "btorexp.h"
#include "btortypes.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

BtorNode* btor_beta_reduce_full (Btor* btor,
                                 BtorNode* exp,
                                 BtorPtrHashTable* cache);

BtorNode* btor_beta_reduce_merge (Btor* btor,
                                  BtorNode* exp,
                                  BtorPtrHashTable* merge_lambdas);

BtorNode* btor_beta_reduce_partial (Btor* btor,
                                    BtorNode* exp,
                                    BtorPtrHashTable* conds);

BtorNode* btor_beta_reduce_partial_collect (Btor* btor,
                                            BtorNode* exp,
                                            BtorPtrHashTable* cond_sel_if,
                                            BtorPtrHashTable* cond_sel_else);

BtorNode* btor_beta_reduce_partial_collect_new (Btor* btor,
                                                BtorNode* exp,
                                                BtorNodePtrStack* exps,
                                                BtorIntHashTable* cache);

BtorNode* btor_beta_reduce_bounded (Btor* btor, BtorNode* exp, int32_t bound);

void btor_beta_assign_param (Btor* btor, BtorNode* lambda, BtorNode* arg);

void btor_beta_assign_args (Btor* btor, BtorNode* fun, BtorNode* args);

void btor_beta_unassign_params (Btor* btor, BtorNode* lambda);

#endif
