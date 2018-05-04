/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORDUMPSMT_H_INCLUDED
#define BTORDUMPSMT_H_INCLUDED

#include <stdio.h>
#include "btorbv.h"
#include "btorcore.h"

void btor_dumpsmt_dump_node (Btor* btor,
                             FILE* file,
                             BtorNode* node,
                             uint32_t depth);

void btor_dumpsmt_dump (Btor* btor, FILE* file);

void btor_dumpsmt_dump_const_value (Btor* btor,
                                    const BtorBitVector* bits,
                                    uint32_t base,
                                    FILE* file);

void btor_dumpsmt_dump_sort_node (BtorNode* exp, FILE* file);
void btor_dumpsmt_dump_sort (BtorSort* sort, FILE* file);
#endif
