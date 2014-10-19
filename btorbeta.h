/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORBETA_H_INCLUDED
#define BTORBETA_H_INCLUDED

#include "btorcore.h"

BtorNode *btor_beta_reduce_full (Btor *, BtorNode *);

BtorNode *btor_beta_reduce_merge (Btor *, BtorNode *);

BtorNode *btor_beta_reduce_partial (
    Btor *, BtorNode *, int *, BtorPtrHashTable *, BtorPtrHashTable *);

BtorNode *btor_beta_reduce_partial_collect (Btor *,
                                            BtorNode *,
                                            BtorPtrHashTable *,
                                            BtorPtrHashTable *);

BtorNode *btor_beta_reduce_bounded (Btor *, BtorNode *, int);

BtorNode *btor_param_cur_assignment (BtorNode *);

BtorNode *btor_apply_and_reduce (Btor *, int, BtorNode **, BtorNode *);

void btor_assign_param (Btor *, BtorNode *, BtorNode *);

void btor_assign_args (Btor *, BtorNode *, BtorNode *);

void btor_unassign_params (Btor *, BtorNode *);

#endif
