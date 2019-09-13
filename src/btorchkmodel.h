/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORCHKMODEL_H_INCLUDED
#define BTORCHKMODEL_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashptr.h"

typedef struct BtorCheckModelContext BtorCheckModelContext;

BtorCheckModelContext *btor_check_model_init (Btor *btor);

void btor_check_model_delete (BtorCheckModelContext *ctx);

void btor_check_model (BtorCheckModelContext *ctx);

#endif
