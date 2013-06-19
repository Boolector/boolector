/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "boolector.h"

typedef struct BtorDumpContext BtorDumpContext;

BtorDumpContext *btor_new_dump_context (Btor *);
void btor_delete_dump_context (BtorDumpContext *);

void btor_add_input_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_latch_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_next_to_dump_context (BtorDumpContext *, BtorNode *, BtorNode *);
void btor_add_init_to_dump_context (BtorDumpContext *, BtorNode *, BtorNode *);
void btor_add_bad_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_root_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_add_constraint_to_dump_context (BtorDumpContext *, BtorNode *);

void btor_dump_btor (BtorDumpContext *, FILE *file);
