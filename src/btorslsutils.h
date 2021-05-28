/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLSUTILS_H_INCLUDED
#define BTORSLSUTILS_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashint.h"

double btor_slsutils_compute_score_node (Btor *btor,
                                         BtorIntHashTable *bv_model,
                                         BtorIntHashTable *fun_model,
                                         BtorIntHashTable *score,
                                         BtorNode *exp);

void btor_slsutils_compute_sls_scores (Btor *btor,
                                       BtorIntHashTable *bv_model,
                                       BtorIntHashTable *fun_model,
                                       BtorIntHashTable *score);
#endif
