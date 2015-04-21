/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>

/*------------------------------------------------------------------------*/

int
btor_is_power_of_2_util (int x)
{
  assert (x > 0);
  return (x & (x - 1)) == 0;
}

int
btor_log_2_util (int x)
{
  int result = 0;
  assert (x > 0);
  assert (btor_is_power_of_2_util (x));
  while (x > 1)
  {
    x >>= 1;
    result++;
  }
  assert (result >= 0);
  return result;
}

int
btor_pow_2_util (int x)
{
  int result = 1;
  assert (x >= 0);
  while (x > 0)
  {
    assert (result <= INT_MAX / 2);
    result <<= 1;
    x--;
  }
  assert (result > 0);
  return result;
}

int
btor_next_power_of_2_util (int x)
{
  int i;
  assert (x > 0);
  x--;
  for (i = 1; i < (int) sizeof (int) * 8; i *= 2) x = x | (x >> i);
  return x + 1;
}

int
btor_num_digits_util (int x)
{
  int result;
  assert (x >= 0);

  result = 0;
  do
  {
    x /= 10;
    result++;
  } while (x > 0);
  return result;
}

/*------------------------------------------------------------------------*/

#ifdef BTOR_HAVE_GETRUSAGE

#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

double
btor_time_stamp (void)
{
  double res = -1;
  struct rusage u;
  res = 0;
  if (!getrusage (RUSAGE_SELF, &u))
  {
    res += u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
    res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  }
  return res;
}
#endif

/*------------------------------------------------------------------------*/

#define BTOR_HAVE_STAT

#ifdef BTOR_HAVE_STAT
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
int
btor_file_exists (const char* path)
{
  struct stat buf;
  return !stat (path, &buf);
}
#else
int
btor_file_exists (const char* path)
{
  (void) path;
  return -1;
}
#endif

/*------------------------------------------------------------------------*/

void
btor_init_rng (BtorRNG* rng, unsigned seed)
{
  assert (rng);

  rng->w = (unsigned) seed;
  rng->z = ~rng->w;
  rng->w <<= 1;
  rng->z <<= 1;
  rng->w += 1;
  rng->z += 1;
  rng->w *= 2019164533u;
  rng->z *= 1000632769u;
}

unsigned
btor_rand_rng (BtorRNG* rng)
{
  assert (rng);
  rng->z = 36969 * (rng->z & 65535) + (rng->z >> 16);
  rng->w = 18000 * (rng->w & 65535) + (rng->w >> 16);
  return (rng->z << 16) + rng->w; /* 32-bit result */
}

unsigned
btor_pick_rand_rng (BtorRNG* rng, unsigned from, unsigned to)
{
  assert (rng);
  assert (from <= to && to < UINT_MAX);

  unsigned res;

  res = btor_rand_rng (rng);
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
