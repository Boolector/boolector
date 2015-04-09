/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz.
 *  Copyright (C) 2012-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORDUMPSMT_H_INCLUDED
#define BTORDUMPSMT_H_INCLUDED

#include <stdio.h>
#include "btorcore.h"

void btor_dump_smt1_nodes (Btor* btor,
                           FILE* file,
                           BtorNode** roots,
                           int nroots);

void btor_dump_smt1 (Btor* btor, FILE* file);

void btor_dump_smt2_nodes (Btor* btor,
                           FILE* file,
                           BtorNode** roots,
                           int nroots);

void btor_dump_smt2_node (Btor* btor,
                          FILE* file,
                          BtorNode* node,
                          unsigned depth);

void btor_dump_smt2 (Btor* btor, FILE* file);

void btor_dump_const_value_smt (
    Btor* btor, const char* bits, int base, int version, FILE* file);

void btor_dump_sort_smt_node (BtorNode* exp, int version, FILE* file);
void btor_dump_sort_smt (BtorSort* sort, int version, FILE* file);
#endif
