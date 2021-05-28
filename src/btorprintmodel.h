/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPRINTMODEL_H_INCLUDED
#define BTORPRINTMODEL_H_INCLUDED

#include "btornode.h"
#include "btortypes.h"

void btor_print_model (Btor* btor, const char* format, FILE* file);
void btor_print_node_model (Btor* btor,
                            BtorNode* input,
                            BtorNode* value,
                            const char* format,
                            FILE* file);
void btor_print_fun_model (
    Btor* btor, BtorNode* node, const char* format, uint32_t base, FILE* file);
void btor_print_bv_model (
    Btor* btor, BtorNode* node, const char* format, uint32_t base, FILE* file);
void btor_print_model_aufbv (Btor* btor, const char* format, FILE* file);

void btor_print_value_smt2 (Btor* btor,
                            BtorNode* exp,
                            char* symbol_str,
                            FILE* file);

#endif
