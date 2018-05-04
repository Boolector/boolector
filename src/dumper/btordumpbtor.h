/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013 Armin Biere.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2016-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORDUMPBTOR_H_INCLUDED
#define BTORDUMPBTOR_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "btortypes.h"

typedef struct BtorDumpContext BtorDumpContext;

BtorDumpContext *btor_dumpbtor_new_dump_context (Btor *);
void btor_dumpbtor_delete_dump_context (BtorDumpContext *);

void btor_dumpbtor_add_input_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_dumpbtor_add_state_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_dumpbtor_add_next_to_dump_context (BtorDumpContext *,
                                             BtorNode *,
                                             BtorNode *);
void btor_dumpbtor_add_init_to_dump_context (BtorDumpContext *,
                                             BtorNode *,
                                             BtorNode *);
void btor_dumpbtor_add_bad_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_dumpbtor_add_output_to_dump_context (BtorDumpContext *, BtorNode *);
void btor_dumpbtor_add_constraint_to_dump_context (BtorDumpContext *,
                                                   BtorNode *);
void btor_dumpbtor_add_root_to_dump_context (BtorDumpContext *, BtorNode *);

void btor_dumpbtor_dump_bdc (BtorDumpContext *, FILE *file);
void btor_dumpbtor_dump_node (Btor *, FILE *, BtorNode *);
void btor_dumpbtor_dump_nodes (Btor *, FILE *, BtorNode **, uint32_t);
void btor_dumpbtor_dump (Btor *, FILE *, uint32_t);

/* FIXME: right now we cannot dump UF in BTOR as the format does not support UF
 *        yet */
bool btor_dumpbtor_can_be_dumped (Btor *);

#endif
