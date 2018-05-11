#include "boolector.h"
#include "btoropt.h"
#include "maxand.h"
#include "utils/btorutil.h"

#include <stdio.h>
#include <stdlib.h>

int
main (int argc, char **argv)
{
  int num_bits;
  Btor *btor;
  BoolectorNode *formula, *zero_num_bits_m_1, *tmp, *a, *b, *c, *d, *m;
  BoolectorNode *result, *one, *x_and_y, *premisse;
  BoolectorNode *a_ulte_x, *x_ulte_b, *c_ulte_y, *y_ulte_d, *x, *y, *concl;
  BoolectorSort sort_1, sort_zero, sort_var;

  if (argc != 2)
  {
    printf ("Usage: ./maxand <num-bits>\n");
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

  btor      = boolector_new ();
  sort_1    = boolector_bitvec_sort (btor, 1);
  sort_zero = boolector_bitvec_sort (btor, num_bits - 1);
  sort_var  = boolector_bitvec_sort (btor, num_bits);
  boolector_set_opt (btor, BTOR_OPT_REWRITE_LEVEL, 0);

  one               = boolector_one (btor, sort_1);
  zero_num_bits_m_1 = boolector_zero (btor, sort_zero);
  m                 = boolector_concat (btor, one, zero_num_bits_m_1);
  a                 = boolector_var (btor, sort_var, "a");
  b                 = boolector_var (btor, sort_var, "b");
  c                 = boolector_var (btor, sort_var, "c");
  d                 = boolector_var (btor, sort_var, "d");
  x                 = boolector_var (btor, sort_var, "x");
  y                 = boolector_var (btor, sort_var, "y");

  x_and_y = boolector_and (btor, x, y);

  a_ulte_x = boolector_ulte (btor, a, x);
  x_ulte_b = boolector_ulte (btor, x, b);
  c_ulte_y = boolector_ulte (btor, c, y);
  y_ulte_d = boolector_ulte (btor, y, d);
  premisse = boolector_and (btor, a_ulte_x, x_ulte_b);
  tmp      = boolector_and (btor, premisse, c_ulte_y);
  boolector_release (btor, premisse);
  premisse = tmp;
  tmp      = boolector_and (btor, premisse, y_ulte_d);
  boolector_release (btor, premisse);
  premisse = tmp;

  result = btor_maxand (btor, a, b, c, d, m, num_bits);

  /* conclusion: result is indeed the maximum of x & y */
  concl   = boolector_ugte (btor, result, x_and_y);
  formula = boolector_implies (btor, premisse, concl);
  /* we negate the formula and show that it is UNSAT */
  tmp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = tmp;
  boolector_dump_btor_node (btor, stdout, formula);

  /* clean up */
  boolector_release (btor, result);
  boolector_release (btor, premisse);
  boolector_release (btor, concl);
  boolector_release (btor, formula);
  boolector_release (btor, x_and_y);
  boolector_release (btor, a_ulte_x);
  boolector_release (btor, x_ulte_b);
  boolector_release (btor, c_ulte_y);
  boolector_release (btor, y_ulte_d);
  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, x);
  boolector_release (btor, y);
  boolector_release (btor, zero_num_bits_m_1);
  boolector_release (btor, one);
  boolector_release_sort (btor, sort_1);
  boolector_release_sort (btor, sort_zero);
  boolector_release_sort (btor, sort_var);
  boolector_delete (btor);
  return 0;
}
