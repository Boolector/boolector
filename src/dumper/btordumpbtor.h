/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORDUMPBTOR_H_INCLUDED
#define BTORDUMPBTOR_H_INCLUDED

#include <stdbool.h>
#include <stdio.h>
#include "btortypes.h"

typedef struct BtorDumpContext BtorDumpContext;

BtorDumpContext *btor_new_dump_context (Btor *);
void btor_delete_dump_context (BtorDumpContext *);

void btor_add_input_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_latch_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_next_to_dump_context (BtorDumpContext *, BtorNode *, BtorNode *);
void btor_add_init_to_dump_context (BtorDumpContext *, BtorNode *, BtorNode *);
void btor_add_bad_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_output_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_constraint_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_root_to_dump_context (BtorDumpContext *, BtorNode *);

void btor_dump_btor_bdc (BtorDumpContext *, FILE *file);
void btor_dump_btor_node (Btor *, FILE *, BtorNode *);
void btor_dump_btor_nodes (Btor *, FILE *, BtorNode **, int);
void btor_dump_btor (Btor *, FILE *, int);

/* FIXME: right now we cannot dump UF in BTOR as the format does not support UF
 *        yet */
bool btor_can_be_dumped (Btor *);

#endif
