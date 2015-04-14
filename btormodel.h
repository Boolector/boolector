/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
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
#include "utils/btorhash.h"

void btor_generate_model (Btor* btor, int model_for_all_reads);
void btor_generate_model_aux (Btor* btor,
                              BtorPtrHashTable* bv_model,
                              BtorPtrHashTable* fun_model,
                              int model_for_all_nodes);

void btor_init_bv_model (Btor* btor, BtorPtrHashTable** bv_model);
void btor_init_fun_model (Btor* btor, BtorPtrHashTable** fun_model);

void btor_delete_model (Btor* btor);
void btor_delete_bv_model (Btor* btor, BtorPtrHashTable** bv_model);

const BitVector* btor_get_bv_model (Btor* btor, BtorNode* exp);
const BitVector* btor_get_bv_model_aux (Btor* btor,
                                        BtorPtrHashTable** bv_model,
                                        BtorPtrHashTable** fun_model,
                                        BtorNode* exp);

const BtorPtrHashTable* btor_get_fun_model (Btor* btor, BtorNode* exp);
const BtorPtrHashTable* btor_get_fun_model_aux (Btor* btor,
                                                BtorPtrHashTable** bv_model,
                                                BtorPtrHashTable** fun_model,
                                                BtorNode* exp);

void btor_add_to_bv_model (Btor* btor,
                           BtorPtrHashTable* bv_model,
                           BtorNode* exp,
                           BitVector* assignment);

BtorNode* btor_generate_lambda_model_from_fun_model (
    Btor* btor, BtorNode* exp, const BtorPtrHashTable* model);

BitVector* btor_recursively_compute_assignment (Btor* btor,
                                                BtorPtrHashTable* bv_model,
                                                BtorPtrHashTable* fun_model,
                                                BtorNode* exp);
#endif
