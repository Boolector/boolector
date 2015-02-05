/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2014 Aina Niemetz.
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
#include "btorhash.h"

void btor_generate_model (Btor* btor, int model_for_all_reads);
void btor_delete_model (Btor* btor);
void btor_update_model (Btor* btor,
                        BtorNode* exp,
                        BitVector* assignment,
                        int model_for_all_nodes);

const BitVector* btor_get_bv_model (Btor* btor, BtorNode* exp);
const BtorPtrHashTable* btor_get_fun_model (Btor* btor, BtorNode* exp);

BtorNode* btor_generate_lambda_model_from_fun_model (
    Btor* btor, BtorNode* exp, const BtorPtrHashTable* model);

#endif
