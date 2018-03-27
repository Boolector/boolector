#include <stdio.h>
#include <stdlib.h>
#include "boolector.h"
#include "btoropt.h"
#include "utils/btorutil.h"

/* We verify that the following algorithm is equal to (x & (x - 1)) == 0
 * we assume x > 0

int is_power_of_2 (int x)
{
  assert (x > 0);
  while (x > 1)
    {
      if ((x & 1) != 0)
        return 0;
      x >>= 1;
    }
  return 1;
}

*/

int
main (int argc, char **argv)
{
  int num_bits, i;
  Btor *btor;
  BoolectorNode *var, *var_shift, *zero, *one, *onelog, *formula;
  BoolectorNode *result1, *result2, *and, *temp, *sgt, *eq, *ne;
  BoolectorSort s0, s1;
  if (argc != 2)
  {
    printf ("Usage: ./ispowerof2 <num-bits>\n");
    return 1;
  }
  num_bits = atoi (argv[1]);
  if (num_bits <= 1)
  {
    printf ("Number of bits must be greater than one\n");
    return 1;
  }
  if (!btor_util_is_power_of_2 (num_bits))
  {
    printf ("Number of bits must be a power of two\n");
    return 1;
  }
  btor = boolector_new ();
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);
  s0        = boolector_bitvec_sort (btor, num_bits);
  s1        = boolector_bitvec_sort (btor, btor_util_log_2 (num_bits));
  var       = boolector_var (btor, s0, "var");
  var_shift = boolector_copy (btor, var);
  zero      = boolector_zero (btor, s0);
  one       = boolector_one (btor, s0);
  onelog    = boolector_one (btor, s1);
  result1   = boolector_true (btor);
  for (i = 0; i < num_bits - 2; i++)
  {
    /* x > 1 ? */
    sgt = boolector_sgt (btor, var_shift, one);

    /* x % 2 != 1 ? */
    and = boolector_and (btor, var_shift, one);
    ne  = boolector_ne (btor, and, one);
    boolector_release (btor, and);

    and = boolector_and (btor, result1, ne);
    boolector_release (btor, ne);

    temp = boolector_cond (btor, sgt, and, result1);
    boolector_release (btor, result1);
    result1 = temp;

    boolector_release (btor, sgt);
    boolector_release (btor, and);

    /* x >>= 1; */
    temp = boolector_srl (btor, var_shift, onelog);
    boolector_release (btor, var_shift);
    var_shift = temp;
  }

  /* (x & (x - 1)) == 0 */
  temp    = boolector_sub (btor, var, one);
  result2 = boolector_and (btor, var, temp);
  boolector_release (btor, temp);
  temp = boolector_eq (btor, result2, zero);
  boolector_release (btor, result2);
  result2 = temp;

  sgt     = boolector_sgt (btor, var, zero);
  eq      = boolector_eq (btor, result1, result2);
  formula = boolector_implies (btor, sgt, eq);
  temp    = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;

  boolector_dump_btor_node (btor, stdout, formula);

  /* clean up */
  boolector_release (btor, sgt);
  boolector_release (btor, eq);
  boolector_release (btor, result1);
  boolector_release (btor, result2);
  boolector_release (btor, formula);
  boolector_release (btor, var);
  boolector_release (btor, var_shift);
  boolector_release (btor, zero);
  boolector_release (btor, one);
  boolector_release (btor, onelog);
  boolector_release_sort (btor, s0);
  boolector_release_sort (btor, s1);
  boolector_delete (btor);
  return 0;
}
