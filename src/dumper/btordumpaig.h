/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BTORDUMPAIG_H_INCLUDED
#define BTORDUMPAIG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "btoraig.h"
#include "btortypes.h"

/* Dumps AIG in AIGER format to file. */
void btor_dumpaig_dump_aig (BtorAIGMgr* amgr,
                            bool is_binary,
                            FILE* output,
                            BtorAIG* aig);

/* Dumps sequential AIGER model to file. */
void btor_dumpaig_dump_seq (BtorAIGMgr* amgr,
                            bool is_binary,
                            FILE* output,
                            int32_t naigs,
                            BtorAIG** aigs,
                            int32_t nregs,
                            BtorAIG** regs,
                            BtorAIG** nexts,
                            BtorPtrHashTable* back_annotation);

/* Dumps AIGs in AIGER format to file. */
void btor_dumpaig_dump (Btor* btor,
                        bool is_binary,
                        FILE* output,
                        bool merge_roots);
#endif
