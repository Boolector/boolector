/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPARTGEN_H_INCLUDED
#define BTORPARTGEN_H_INCLUDED

#define BTOR_PART_GEN_MAX_TUPLE_SIZE 3

#include <stdbool.h>
#include <stdint.h>

struct BtorPartitionGenerator
{
  uint32_t n;
  int32_t cnt_1;
  int32_t cnt_2;
  int32_t cnt_3;
  uint32_t size;
  uint32_t tuple[BTOR_PART_GEN_MAX_TUPLE_SIZE];
  bool permutate;
  uint32_t perm_idx;
  uint32_t perm_cnt;
};

typedef struct BtorPartitionGenerator BtorPartitionGenerator;

void btor_init_part_gen (BtorPartitionGenerator* pg,
                         uint32_t n,
                         uint32_t size,
                         bool permutate);

uint32_t* btor_next_part_gen (BtorPartitionGenerator* pg);

bool btor_has_next_part_gen (BtorPartitionGenerator* pg);

#endif
