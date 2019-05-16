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

/**
 * Initialize RNG with given seed. If compiled with GMP, this additionally
 * initializes the state of the GMP RNG, thus calling this function is in
 * that case mandatory.
 */
void btor_rng_init (BtorRNG* rng, uint32_t seed);

/**
 * Initialize given RNG clone when cloning.
 * This does nothing when not compiled with GMP but must be called when cloning
 * objects that maintain an RNG struct (and thus memcpy the state of this object
 * to the cloned object when cloning) when compiled with GMP.
 */
void btor_rng_clone (BtorRNG* rng, BtorRNG* clone);

/**
 * Delete allocated data members of the given RNG.
 * This does nothing when not compiled with GMP but must be called to free
 * allocated GMP data members when compiled with GMP.
 */
void btor_rng_delete (BtorRNG* rng);

/* Pick a random unsigned 32 bit integer. */
uint32_t btor_rng_rand (BtorRNG* rng);
/* Pick a random unsigned 32 bit integer between given bounds (inclusive). */
uint32_t btor_rng_pick_rand (BtorRNG* rng, uint32_t from, uint32_t to);
/* Pick a random double between given bounds (inclusive). */
double btor_rng_pick_rand_dbl (BtorRNG* rng, double from, double to);

/* Pick true with given probability (1000 = 100%). */
bool btor_rng_pick_with_prob (BtorRNG* rng, uint32_t prob);

#endif
