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

struct BtorRNG
{
  unsigned z, w;
};
typedef struct BtorRNG BtorRNG;

void btor_init_rng (BtorRNG* rng, unsigned seed);
unsigned btor_rand_rng (BtorRNG* rng);
unsigned btor_pick_rand_rng (BtorRNG* rng, unsigned from, unsigned to);
double btor_pick_rand_dbl_rng (BtorRNG* rng, double from, double to);

#endif
