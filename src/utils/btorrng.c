/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorrng.h"
#include "btoropt.h"

#include <assert.h>
#include <limits.h>
#ifndef NDEBUG
#include <float.h>
#endif

#ifdef BTOR_USE_GMP
#include <gmp.h>
#endif

void
btor_rng_init (BtorRNG* rng, uint32_t seed)
{
  assert (rng);

  rng->w = seed;
  rng->z = ~rng->w;
  rng->w <<= 1;
  rng->z <<= 1;
  rng->w += 1;
  rng->z += 1;
  rng->w *= 2019164533u;
  rng->z *= 1000632769u;

#ifdef BTOR_USE_GMP
  if (rng->is_init)
  {
    assert (rng->gmp_state);
    gmp_randclear (*((gmp_randstate_t*) rng->gmp_state));
  }
  else
  {
    rng->mm        = btor_mem_mgr_new ();
    rng->gmp_state = btor_mem_malloc (rng->mm, sizeof (gmp_randstate_t));
  }
  rng->is_init = true;
  gmp_randinit_mt (*((gmp_randstate_t*) rng->gmp_state));
  gmp_randseed_ui (*((gmp_randstate_t*) rng->gmp_state), btor_rng_rand (rng));
#endif
}

void
btor_rng_clone (BtorRNG* rng, BtorRNG* clone)
{
  (void) rng;
  (void) clone;
#ifdef BTOR_USE_GMP
  assert (rng->gmp_state);
  clone->mm        = btor_mem_mgr_new ();
  clone->gmp_state = btor_mem_malloc (clone->mm, sizeof (gmp_randstate_t));
  gmp_randinit_set (*((gmp_randstate_t*) clone->gmp_state),
                    *((gmp_randstate_t*) rng->gmp_state));
#endif
}

void
btor_rng_delete (BtorRNG* rng)
{
  (void) rng;
#ifdef BTOR_USE_GMP
  assert (rng->gmp_state);
  gmp_randclear (*((gmp_randstate_t*) rng->gmp_state));
  btor_mem_free (rng->mm, rng->gmp_state, sizeof (gmp_randstate_t));
  btor_mem_mgr_delete (rng->mm);
  rng->gmp_state = 0;
  rng->is_init = false;
#endif
}

uint32_t
btor_rng_rand (BtorRNG* rng)
{
  assert (rng);
  rng->z = 36969 * (rng->z & 65535) + (rng->z >> 16);
  rng->w = 18000 * (rng->w & 65535) + (rng->w >> 16);
  return (rng->z << 16) + rng->w; /* 32-bit result */
}

uint32_t
btor_rng_pick_rand (BtorRNG* rng, uint32_t from, uint32_t to)
{
  assert (rng);
  assert (from <= to);

  uint32_t res;

  from = from == UINT32_MAX ? UINT32_MAX - 1 : from;
  to   = to == UINT32_MAX ? UINT32_MAX - 1 : to;
  res  = btor_rng_rand (rng);
  res %= to - from + 1;
  res += from;
  return res;
}

double
btor_rng_pick_rand_dbl (BtorRNG* rng, double from, double to)
{
  assert (rng);
  assert (from <= to && to < DBL_MAX);

  double res;

  res = (double) btor_rng_rand (rng) / UINT32_MAX;
  res = from + res * (to - from);
  return res;
}

bool
btor_rng_pick_with_prob (BtorRNG* rng, uint32_t prob)
{
  assert (rng);
  assert (prob <= BTOR_PROB_MAX);

  uint32_t r;

  r = btor_rng_pick_rand (rng, 0, BTOR_PROB_MAX - 1);
  return r < prob;
}
