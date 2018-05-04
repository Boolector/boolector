/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORNORMQUANT_H_INCLUDED
#define BTORNORMQUANT_H_INCLUDED

#include "btortypes.h"
#include "utils/btorhashint.h"

BtorNode* btor_normalize_quantifiers_node (Btor* btor, BtorNode* root);

BtorNode* btor_normalize_quantifiers (Btor* btor);

#if 0
/* negates 'root' and inverts all quantifiers under 'root'. */
BtorNode * btor_invert_quantifiers (Btor * btor, BtorNode * root,
				    BtorIntHashTable * node_map);
#endif

#endif
