/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSYNTHFUN_H_INCLUDED
#define BTORSYNTHFUN_H_INCLUDED

#include <stdint.h>
#include "btorexp.h"
#include "btortypes.h"
#include "utils/btorhashint.h"
#include "utils/btorhashptr.h"

BtorNode* btor_synthesize_term (Btor* btor,
                                BtorNode* params[],
                                uint32_t nparams,
                                BtorBitVectorTuple* value_in[],
                                BtorBitVector* value_out[],
                                uint32_t nvalues,
                                BtorIntHashTable* value_in_map,
                                BtorNode* constraints[],
                                uint32_t nconstraints,
                                BtorNode* consts[],
                                uint32_t nconsts,
                                uint32_t max_checks,
                                uint32_t max_level,
                                BtorNode* prev_synth);
#endif
