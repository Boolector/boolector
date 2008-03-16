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
  while (x > 1)
  {
    if ((x & 1) != 0) return 0;
    x >>= 1;
  }
  return 1;
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

/*------------------------------------------------------------------------*/
/* END OF IMPLEMENTATION                                                  */
/*------------------------------------------------------------------------*/
