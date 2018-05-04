/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMODEL_H_INCLUDED
#define BTORMODEL_H_INCLUDED

#include "btorbv.h"
#include "btorcore.h"
#include "btornode.h"
#include "utils/btorhashint.h"

/*------------------------------------------------------------------------*/

BtorBitVector* btor_model_recursively_compute_assignment (
    Btor* btor,
    BtorIntHashTable* bv_model,
    BtorIntHashTable* fun_model,
    BtorNode* exp);

void btor_model_generate (Btor* btor,
                          BtorIntHashTable* bv_model,
                          BtorIntHashTable* fun_model,
                          bool model_for_all_nodes);

/*------------------------------------------------------------------------*/

void btor_model_delete (Btor* btor);
void btor_model_delete_bv (Btor* btor, BtorIntHashTable** bv_model);

/*------------------------------------------------------------------------*/

void btor_model_init_bv (Btor* btor, BtorIntHashTable** bv_model);
void btor_model_init_fun (Btor* btor, BtorIntHashTable** fun_model);

/*------------------------------------------------------------------------*/

BtorIntHashTable* btor_model_clone_bv (Btor* btor,
                                       BtorIntHashTable* bv_model,
                                       bool inc_ref_cnt);
BtorIntHashTable* btor_model_clone_fun (Btor* btor,
                                        BtorIntHashTable* fun_model,
                                        bool inc_ref_cnt);

/*------------------------------------------------------------------------*/

const BtorBitVector* btor_model_get_bv (Btor* btor, BtorNode* exp);
const BtorBitVector* btor_model_get_bv_aux (Btor* btor,
                                            BtorIntHashTable* bv_model,
                                            BtorIntHashTable* fun_model,
                                            BtorNode* exp);

const BtorPtrHashTable* btor_model_get_fun (Btor* btor, BtorNode* exp);
const BtorPtrHashTable* btor_model_get_fun_aux (Btor* btor,
                                                BtorIntHashTable* bv_model,
                                                BtorIntHashTable* fun_model,
                                                BtorNode* exp);

/*------------------------------------------------------------------------*/

void btor_model_add_to_bv (Btor* btor,
                           BtorIntHashTable* bv_model,
                           BtorNode* exp,
                           const BtorBitVector* assignment);
void btor_model_remove_from_bv (Btor* btor,
                                BtorIntHashTable* bv_model,
                                BtorNode* exp);

/*------------------------------------------------------------------------*/

#endif
