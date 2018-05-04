/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORDER_H_INCLUDED
#define BTORDER_H_INCLUDED

#include "btortypes.h"

BtorNode* btor_der_node (Btor* btor, BtorNode* root);

BtorNode* btor_cer_node (Btor* btor, BtorNode* root);

#endif
