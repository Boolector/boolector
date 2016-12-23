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

#ifndef BTORPRINTMODEL_H_INCLUDED
#define BTORPRINTMODEL_H_INCLUDED

#include "btorcore.h"
#include "btorexp.h"

void btor_print_model (Btor* btor, char* format, FILE* file);

void btor_print_value (
    Btor* btor, BtorNode* exp, char* symbol_str, char* format, FILE* file);

#endif
