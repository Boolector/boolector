/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
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

void btor_generate_model (Btor *);
void btor_delete_model (Btor *);

// TODO: these functions may be obsolete in the future
int btor_has_bv_model (Btor *, BtorNode *);
int btor_has_array_model (Btor *, BtorNode *);

const char *btor_get_bv_model_str (Btor *, BtorNode *);
void btor_get_array_model_str (Btor *, BtorNode *, char ***, char ***, int *);

#endif
