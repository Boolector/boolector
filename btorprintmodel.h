/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2014-2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPRINTMODEL_H_INCLUDED
#define BTORPRINTMODEL_H_INCLUDED

#include "btorcore.h"
#include "btorexp.h"

const char* btor_get_bv_model_str (Btor* btor, BtorNode* exp);
const char* btor_get_bv_model_str_aux (Btor* btor,
                                       BtorPtrHashTable** bv_model,
                                       BtorPtrHashTable** fun_model,
                                       BtorNode* exp);

void btor_get_fun_model_str (
    Btor* btor, BtorNode* exp, char*** args, char*** values, int* size);
void btor_get_fun_model_str_aux (Btor* btor,
                                 BtorPtrHashTable** fun_model,
                                 BtorNode* exp,
                                 char*** args,
                                 char*** values,
                                 int* size);

void btor_print_model (Btor* btor, char* format, FILE* file);
void btor_print_value (
    Btor* btor, BtorNode* exp, char* exp_str, char* format, FILE* file);

#endif
