#include "boolector.h"
#include "btoropt.h"
#include "maxand.h"
#include "maxor.h"
#include "maxxor.h"
#include "minand.h"
#include "minor.h"
#include "minxor.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

int
main (int argc, char **argv)
{
  Btor *btor;
  BoolectorNode *one, *zero_num_bits_m_1, *a, *b, *c, *d, *m, *formula, *tmp;
  BoolectorNode *not_a, *not_b, *not_c, *not_d;
  BoolectorNode *min_and, *max_and, *min_or, *max_or;
  BoolectorNode *min_and_1, *min_and_2, * or, *min_xor, *max_xor, *eq;
  BoolectorNode *premisse, *a_ulte_b, *c_ulte_d, *max_and_1, *max_and_2, *zero;
  BoolectorSort sort_one, sort_nbits1, sort_nbits;
  int theorem_number, num_bits;

  if (argc != 3)
  {
    printf ("Usage: ./theorems <theorem-number> <num-bits>\n");
    printf ("Theorems:\n");
    printf ("1: minAND(a,b,c,d) = ~maxOR(~b,~a,~d,~c)\n");
    printf ("2: maxAND(a,b,c,d) = ~minOR(~b,~a,~d,~c)\n");
    printf ("3: minXOR(a,b,c,d) = minAND(a,b,~d,~c) | minAND(~b,~a,c,d)\n");
    printf (
        "4: maxXOR(a,b,c,d) = maxOR(0, maxAND(a,b,~d,~c), 0, "
        "maxAND(~b,~a,c,d)\n");
    return 1;
  }

  theorem_number = atoi (argv[1]);
  if (theorem_number < 1 || theorem_number > 4)
  {
    printf ("Theorem number must be in [1,4]\n");
    return 1;
  }

  num_bits = atoi (argv[2]);
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

  sort_one    = boolector_bitvec_sort (btor, 1);
  sort_nbits1 = boolector_bitvec_sort (btor, num_bits - 1);
  sort_nbits  = boolector_bitvec_sort (btor, num_bits);

  one               = boolector_one (btor, sort_one);
  zero_num_bits_m_1 = boolector_zero (btor, sort_nbits1);
  m                 = boolector_concat (btor, one, zero_num_bits_m_1);
  a                 = boolector_var (btor, sort_nbits, "a");
  b                 = boolector_var (btor, sort_nbits, "b");
  c                 = boolector_var (btor, sort_nbits, "c");
  d                 = boolector_var (btor, sort_nbits, "d");

  switch (theorem_number)
  {
    case 1:
      min_and = btor_minand (btor, a, b, c, d, m, num_bits);
      not_a   = boolector_not (btor, a);
      not_b   = boolector_not (btor, b);
      not_c   = boolector_not (btor, c);
      not_d   = boolector_not (btor, d);
      max_or  = btor_maxor (btor, not_b, not_a, not_d, not_c, m, num_bits);
      tmp     = boolector_not (btor, max_or);
      boolector_release (btor, max_or);
      max_or = tmp;
      eq     = boolector_eq (btor, min_and, max_or);
      boolector_release (btor, min_and);
      boolector_release (btor, max_or);
      boolector_release (btor, not_a);
      boolector_release (btor, not_b);
      boolector_release (btor, not_c);
      boolector_release (btor, not_d);
      break;
    case 2:
      max_and = btor_maxand (btor, a, b, c, d, m, num_bits);
      not_a   = boolector_not (btor, a);
      not_b   = boolector_not (btor, b);
      not_c   = boolector_not (btor, c);
      not_d   = boolector_not (btor, d);
      min_or  = btor_minor (btor, not_b, not_a, not_d, not_c, m, num_bits);
      tmp     = boolector_not (btor, min_or);
      boolector_release (btor, min_or);
      min_or = tmp;
      eq     = boolector_eq (btor, max_and, min_or);
      boolector_release (btor, max_and);
      boolector_release (btor, min_or);
      boolector_release (btor, not_a);
      boolector_release (btor, not_b);
      boolector_release (btor, not_c);
      boolector_release (btor, not_d);
      break;
    case 3:
      not_a     = boolector_not (btor, a);
      not_b     = boolector_not (btor, b);
      not_c     = boolector_not (btor, c);
      not_d     = boolector_not (btor, d);
      min_xor   = btor_minxor (btor, a, b, c, d, m, num_bits);
      min_and_1 = btor_minand (btor, a, b, not_d, not_c, m, num_bits);
      min_and_2 = btor_minand (btor, not_b, not_a, c, d, m, num_bits);
      or        = boolector_or (btor, min_and_1, min_and_2);
      eq        = boolector_eq (btor, min_xor, or);
      boolector_release (btor, min_xor);
      boolector_release (btor, min_and_1);
      boolector_release (btor, min_and_2);
      boolector_release (btor, or);
      boolector_release (btor, not_a);
      boolector_release (btor, not_b);
      boolector_release (btor, not_c);
      boolector_release (btor, not_d);
      break;
    default:
      assert (theorem_number == 4);
      max_xor   = btor_maxxor (btor, a, b, c, d, m, num_bits);
      not_a     = boolector_not (btor, a);
      not_b     = boolector_not (btor, b);
      not_c     = boolector_not (btor, c);
      not_d     = boolector_not (btor, d);
      max_and_1 = btor_maxand (btor, a, b, not_d, not_c, m, num_bits);
      max_and_2 = btor_maxand (btor, not_b, not_a, c, d, m, num_bits);
      zero      = boolector_zero (btor, sort_nbits);
      max_or = btor_maxor (btor, zero, max_and_1, zero, max_and_2, m, num_bits);
      eq     = boolector_eq (btor, max_xor, max_or);
      boolector_release (btor, max_and_1);
      boolector_release (btor, max_and_2);
      boolector_release (btor, max_xor);
      boolector_release (btor, max_or);
      boolector_release (btor, zero);
      boolector_release (btor, not_a);
      boolector_release (btor, not_b);
      boolector_release (btor, not_c);
      boolector_release (btor, not_d);
  }

  a_ulte_b = boolector_ulte (btor, a, b);
  c_ulte_d = boolector_ulte (btor, c, d);
  premisse = boolector_and (btor, a_ulte_b, c_ulte_d);
  formula  = boolector_implies (btor, premisse, eq);
  /* we negate the formula and show that it is UNSAT */
  tmp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = tmp;
  boolector_dump_btor_node (btor, stdout, formula);

  boolector_release (btor, a_ulte_b);
  boolector_release (btor, c_ulte_d);
  boolector_release (btor, eq);
  boolector_release (btor, premisse);
  boolector_release (btor, formula);
  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, zero_num_bits_m_1);
  boolector_release (btor, one);
  boolector_release_sort (btor, sort_one);
  boolector_release_sort (btor, sort_nbits1);
  boolector_release_sort (btor, sort_nbits);
  boolector_delete (btor);
  return 0;
}
