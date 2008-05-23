#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

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
  BtorExp *var, *var_shift, *zero, *one, *onelog, *formula;
  BtorExp *result1, *result2, *and, *temp, *sgt, *eq, *ne;
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
  if (!btor_is_power_of_2_util (num_bits))
  {
    printf ("Number of bits must be a power of two\n");
    return 1;
  }
  btor = btor_new_btor ();
  btor_set_rewrite_level_btor (btor, 0);
  var       = btor_var_exp (btor, num_bits, "var");
  var_shift = btor_copy_exp (btor, var);
  zero      = btor_zero_exp (btor, num_bits);
  one       = btor_one_exp (btor, num_bits);
  onelog    = btor_one_exp (btor, btor_log_2_util (num_bits));
  result1   = btor_true_exp (btor);
  for (i = 0; i < num_bits - 2; i++)
  {
    /* x > 1 ? */
    sgt = btor_sgt_exp (btor, var_shift, one);

    /* x % 2 != 1 ? */
    and = btor_and_exp (btor, var_shift, one);
    ne  = btor_ne_exp (btor, and, one);
    btor_release_exp (btor, and);

    and = btor_and_exp (btor, result1, ne);
    btor_release_exp (btor, ne);

    temp = btor_cond_exp (btor, sgt, and, result1);
    btor_release_exp (btor, result1);
    result1 = temp;

    btor_release_exp (btor, sgt);
    btor_release_exp (btor, and);

    /* x >>= 1; */
    temp = btor_srl_exp (btor, var_shift, onelog);
    btor_release_exp (btor, var_shift);
    var_shift = temp;
  }

  /* (x & (x - 1)) == 0 */
  temp    = btor_sub_exp (btor, var, one);
  result2 = btor_and_exp (btor, var, temp);
  btor_release_exp (btor, temp);
  temp = btor_eq_exp (btor, result2, zero);
  btor_release_exp (btor, result2);
  result2 = temp;

  sgt     = btor_sgt_exp (btor, var, zero);
  eq      = btor_eq_exp (btor, result1, result2);
  formula = btor_implies_exp (btor, sgt, eq);
  temp    = btor_not_exp (btor, formula);
  btor_release_exp (btor, formula);
  formula = temp;

  btor_dump_exp (btor, stdout, formula);

  /* clean up */
  btor_release_exp (btor, sgt);
  btor_release_exp (btor, eq);
  btor_release_exp (btor, result1);
  btor_release_exp (btor, result2);
  btor_release_exp (btor, formula);
  btor_release_exp (btor, var);
  btor_release_exp (btor, var_shift);
  btor_release_exp (btor, zero);
  btor_release_exp (btor, one);
  btor_release_exp (btor, onelog);
  btor_delete_btor (btor);
  return 0;
}
