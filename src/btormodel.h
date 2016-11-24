/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMODEL_H_INCLUDED
#define BTORMODEL_H_INCLUDED

#include "btorbitvec.h"
#include "btorcore.h"
#include "btorexp.h"
#include "utils/btorhashint.h"

/*------------------------------------------------------------------------*/

BtorBitVector* btor_recursively_compute_assignment (Btor* btor,
                                                    BtorIntHashTable* bv_model,
                                                    BtorIntHashTable* fun_model,
                                                    BtorNode* exp);

void btor_generate_model (Btor* btor,
                          BtorIntHashTable* bv_model,
                          BtorIntHashTable* fun_model,
                          bool model_for_all_nodes);

/*------------------------------------------------------------------------*/

void btor_delete_model (Btor* btor);
void btor_delete_bv_model (Btor* btor, BtorIntHashTable** bv_model);

/*------------------------------------------------------------------------*/

void btor_init_bv_model (Btor* btor, BtorIntHashTable** bv_model);
void btor_init_fun_model (Btor* btor, BtorIntHashTable** fun_model);

/*------------------------------------------------------------------------*/

BtorIntHashTable* btor_clone_bv_model (Btor* btor,
                                       BtorIntHashTable* bv_model,
                                       bool inc_ref_cnt);
BtorIntHashTable* btor_clone_fun_model (Btor* btor,
                                        BtorIntHashTable* fun_model,
                                        bool inc_ref_cnt);

/*------------------------------------------------------------------------*/

const BtorBitVector* btor_get_bv_model (Btor* btor, BtorNode* exp);
const BtorBitVector* btor_get_bv_model_aux (Btor* btor,
                                            BtorIntHashTable* bv_model,
                                            BtorIntHashTable* fun_model,
                                            BtorNode* exp);

const BtorPtrHashTable* btor_get_fun_model (Btor* btor, BtorNode* exp);
const BtorPtrHashTable* btor_get_fun_model_aux (Btor* btor,
                                                BtorIntHashTable* bv_model,
                                                BtorIntHashTable* fun_model,
                                                BtorNode* exp);

/*------------------------------------------------------------------------*/

void btor_add_to_bv_model (Btor* btor,
                           BtorIntHashTable* bv_model,
                           BtorNode* exp,
                           const BtorBitVector* assignment);
void btor_remove_from_bv_model (Btor* btor,
                                BtorIntHashTable* bv_model,
                                BtorNode* exp);

/*------------------------------------------------------------------------*/

#if 0
BtorNode * btor_generate_lambda_model_from_fun_model (
			   Btor * btor,
			   BtorNode * exp,
			   const BtorIntHashTable * model);
#endif

#endif
