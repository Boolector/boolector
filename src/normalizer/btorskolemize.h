/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSKOLEMIZE_H_INCLUDED
#define BTORSKOLEMIZE_H_INCLUDED

#include "btortypes.h"

void btor_skolemize (Btor* btor);

BtorNode* btor_skolemize_node (Btor* btor, BtorNode* root);

#endif
