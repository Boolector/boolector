/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010 Armin Biere, FMV, JKU.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "btorutil.h"

#include <assert.h>
#include <limits.h>

/*------------------------------------------------------------------------*/
/* BEGIN OF DECLARATIONS                                                  */
/*------------------------------------------------------------------------*/
/*------------------------------------------------------------------------*/
/* END OF DECLARATIONS                                                    */
/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
/* BEGIN OF IMPLEMENTATION                                                */
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
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
