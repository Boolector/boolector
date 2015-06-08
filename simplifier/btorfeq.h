/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORFEQ_H_INCLUDED
#define BTORFEQ_H_INCLUDED

#include "btortypes.h"

BtorNode* btor_rewrite_function_inequality (Btor* btor, BtorNode* feq);

void btor_rewrite_function_inequalities (Btor* btor);

#endif
