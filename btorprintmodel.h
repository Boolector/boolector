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

#ifndef BTORPRINTMODEL_H_INCLUDED
#define BTORPRINTMODEL_H_INCLUDED

#include "btorcore.h"
#include "btorexp.h"

const char *btor_get_bv_model_str (Btor *, BtorNode *);
void btor_get_fun_model_str (Btor *, BtorNode *, char ***, char ***, int *);

void btor_print_model (Btor *btor, char *format, FILE *file);
void btor_print_value (
    Btor *btor, BtorNode *exp, char *exp_str, char *format, FILE *file);

#endif
