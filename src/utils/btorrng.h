/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORRNG_H_INCLUDED
#define BTORRNG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

struct BtorRNG
{
  uint32_t z, w;
};
typedef struct BtorRNG BtorRNG;

void btor_init_rng (BtorRNG* rng, uint32_t seed);

uint32_t btor_rand_rng (BtorRNG* rng);
uint32_t btor_pick_rand_rng (BtorRNG* rng, uint32_t from, uint32_t to);
double btor_pick_rand_dbl_rng (BtorRNG* rng, double from, double to);

bool btor_pick_with_prob_rng (BtorRNG* rng, uint32_t prob);

#endif
