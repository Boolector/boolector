/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORRNG_H_INCLUDED
#define BTORRNG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#ifdef BTOR_USE_GMP
#include <gmp.h>
#endif

struct BtorRNG
{
  uint32_t z, w;
#ifdef BTOR_USE_GMP
  bool is_init;
  gmp_randstate_t gmp_state;
#endif
};
typedef struct BtorRNG BtorRNG;

void btor_rng_init (BtorRNG* rng, uint32_t seed);
void btor_rng_clone (BtorRNG* rng, BtorRNG* clone);
void btor_rng_delete (BtorRNG* rng);

uint32_t btor_rng_rand (BtorRNG* rng);
uint32_t btor_rng_pick_rand (BtorRNG* rng, uint32_t from, uint32_t to);
double btor_rng_pick_rand_dbl (BtorRNG* rng, double from, double to);

bool btor_rng_pick_with_prob (BtorRNG* rng, uint32_t prob);

#endif
