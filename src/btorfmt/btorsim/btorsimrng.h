/**
 *  BtorFMT: A tool package for the BTOR format.
 *
 *  Copyright (c) 2015-2018 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of the BtorFMT package.
 *  See LICENSE.txt for more information on using this software.
 */

#ifndef BTORFMTRNG_H_INCLUDED
#define BTORFMTRNG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

struct BtorSimRNG
{
  uint32_t z, w;
};
typedef struct BtorSimRNG BtorSimRNG;

void btorsim_rng_init (BtorSimRNG* rng, uint32_t seed);

uint32_t btorsim_rng_rand (BtorSimRNG* rng);
uint32_t btorsim_rng_pick_rand (BtorSimRNG* rng, uint32_t from, uint32_t to);

#endif
