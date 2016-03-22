/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#ifndef NDEBUG
#include <float.h>
#endif

/*------------------------------------------------------------------------*/

bool
btor_is_power_of_2_util (uint32_t x)
{
  assert (x > 0);
  return (x & (x - 1)) == 0;
}

uint32_t
btor_log_2_util (uint32_t x)
{
  uint32_t result = 0;
  assert (x > 0);
  assert (btor_is_power_of_2_util (x));
  while (x > 1)
  {
    x >>= 1;
    result++;
  }
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
