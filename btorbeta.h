/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBETA_H_INCLUDED
#define BTORBETA_H_INCLUDED

#include "btorcore.h"

BtorNode* btor_beta_reduce_full (Btor* btor, BtorNode* exp);

BtorNode* btor_beta_reduce_full_cached (Btor* btor,
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

BtorNode* btor_beta_reduce_bounded (Btor* btor, BtorNode* exp, int bound);

BtorNode* btor_param_cur_assignment (BtorNode* exp);

BtorNode* btor_apply_and_reduce (Btor* btor,
                                 int argc,
                                 BtorNode** args,
                                 BtorNode* fun);

void btor_assign_param (Btor* btor, BtorNode* lambda, BtorNode* arg);

void btor_assign_args (Btor* btor, BtorNode* fun, BtorNode* args);

void btor_unassign_params (Btor* btor, BtorNode* lambda);

#endif
