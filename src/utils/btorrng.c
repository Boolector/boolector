/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *
 *  All rights reserved.
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

void
btor_init_rng (BtorRNG* rng, uint32_t seed)
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
}

uint32_t
btor_rand_rng (BtorRNG* rng)
{
  assert (rng);
  rng->z = 36969 * (rng->z & 65535) + (rng->z >> 16);
  rng->w = 18000 * (rng->w & 65535) + (rng->w >> 16);
  return (rng->z << 16) + rng->w; /* 32-bit result */
}

uint32_t
btor_pick_rand_rng (BtorRNG* rng, uint32_t from, uint32_t to)
{
  assert (rng);
  assert (from <= to);

  uint32_t res;

  from = from == UINT_MAX ? UINT_MAX - 1 : from;
  to   = to == UINT_MAX ? UINT_MAX - 1 : to;
  res  = btor_rand_rng (rng);
  res %= to - from + 1;
  res += from;
  return res;
}

double
btor_pick_rand_dbl_rng (BtorRNG* rng, double from, double to)
{
  assert (rng);
  assert (from <= to && to < DBL_MAX);

  double res;

  res = (double) btor_rand_rng (rng) / UINT_MAX;
  res = from + res * (to - from);
  return res;
}

bool
btor_pick_with_prob_rng (BtorRNG* rng, uint32_t prob)
{
  assert (rng);
  assert (prob <= BTOR_PROB_MAX);

  uint32_t r;

  r = btor_pick_rand_rng (rng, 0, BTOR_PROB_MAX);
  return r < prob;
}
