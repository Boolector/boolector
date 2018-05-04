/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
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

void btor_rng_init (BtorRNG* rng, uint32_t seed);

uint32_t btor_rng_rand (BtorRNG* rng);
uint32_t btor_rng_pick_rand (BtorRNG* rng, uint32_t from, uint32_t to);
double btor_rng_pick_rand_dbl (BtorRNG* rng, double from, double to);

bool btor_rng_pick_with_prob (BtorRNG* rng, uint32_t prob);

#endif
