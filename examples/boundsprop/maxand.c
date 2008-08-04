#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

/* maxAND algorithm from hacker's delight, page 61 */

int
main (int argc, char **argv)
{
  int num_bits, i;
  Btor *btor;
  BtorExp *formula, *temp_1, *temp_2, *m, *zero, *zero_num_bits_m_1;
  BtorExp *one, *tmp, *a, *b, *c, *d, *not_b, *not_d, *not_m, *m_minus_1;
  BtorExp *b_and_not_d, *b_and_not_d_and_m, *b_and_not_d_and_m_ne_zero;
  BtorExp *b_and_not_m, *not_b_and_d, *not_b_and_d_and_m, *d_and_not_m;
  BtorExp *not_b_and_d_and_m_ne_zero, *temp_1_ugte_a, *temp_2_ugte_c;
  BtorExp *result, *cond_if, *cond_else_1, *cond_else_2;
  BtorExp *one_log_bits, *b_and_d, *one_full_bits;

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
  if (!btor_is_power_of_2_util (num_bits))
  {
    printf ("Number of bits must be a power of two\n");
    return 1;
  }

  btor = boolector_new ();
  boolector_set_rewrite_level (btor, 0);

  one               = boolector_one (btor, 1);
  one_log_bits      = boolector_one (btor, btor_log_2_util (num_bits));
  one_full_bits     = boolector_one (btor, num_bits);
  zero_num_bits_m_1 = boolector_zero (btor, num_bits - 1);
  zero              = boolector_zero (btor, num_bits);
  m                 = boolector_concat (btor, one, zero_num_bits_m_1);
  a                 = boolector_var (btor, num_bits, "a");
  b                 = boolector_var (btor, num_bits, "b");
  c                 = boolector_var (btor, num_bits, "c");
  d                 = boolector_var (btor, num_bits, "d");

  /* needed later for conclusion */
  b_and_d = boolector_and (btor, b, d);

  for (i = 0; i < num_bits; i++)
  {
    not_m     = boolector_not (btor, m);
    m_minus_1 = boolector_sub (btor, m, one_full_bits);

    not_d                     = boolector_not (btor, d);
    b_and_not_d               = boolector_and (btor, b, not_d);
    b_and_not_d_and_m         = boolector_and (btor, b_and_not_d, m);
    b_and_not_d_and_m_ne_zero = boolector_ne (btor, b_and_not_d_and_m, zero);

    b_and_not_m   = boolector_and (btor, b, not_m);
    temp_1        = boolector_or (btor, b_and_not_m, m_minus_1);
    temp_1_ugte_a = boolector_ugte (btor, temp_1, a);

    not_b                     = boolector_not (btor, b);
    not_b_and_d               = boolector_and (btor, not_b, d);
    not_b_and_d_and_m         = boolector_and (btor, not_b_and_d, m);
    not_b_and_d_and_m_ne_zero = boolector_ne (btor, not_b_and_d_and_m, zero);

    d_and_not_m   = boolector_and (btor, d, not_m);
    temp_2        = boolector_or (btor, d_and_not_m, not_m);
    temp_2_ugte_c = boolector_ugte (btor, temp_2, c);

    /* update b */
    cond_if = boolector_cond (btor, temp_1_ugte_a, temp_1, b);
    tmp     = boolector_cond (btor, b_and_not_d_and_m_ne_zero, cond_if, b);
    boolector_release (btor, b);
    b = tmp;

    /* update d */
    cond_else_1 = boolector_cond (btor, temp_2_ugte_c, temp_2, d);
    cond_else_2 =
        boolector_cond (btor, not_b_and_d_and_m_ne_zero, cond_else_1, d);
    tmp = boolector_cond (btor, b_and_not_d_and_m_ne_zero, d, cond_else_2);
    boolector_release (btor, d);
    d = tmp;

    /* update m */
    tmp = boolector_srl (btor, m, one_log_bits);
    boolector_release (btor, m);
    m = tmp;

    boolector_release (btor, not_b);
    boolector_release (btor, not_d);
    boolector_release (btor, not_m);
    boolector_release (btor, m_minus_1);
    boolector_release (btor, b_and_not_d);
    boolector_release (btor, b_and_not_d_and_m);
    boolector_release (btor, b_and_not_d_and_m_ne_zero);
    boolector_release (btor, not_b_and_d);
    boolector_release (btor, not_b_and_d_and_m);
    boolector_release (btor, not_b_and_d_and_m_ne_zero);
    boolector_release (btor, b_and_not_m);
    boolector_release (btor, d_and_not_m);
    boolector_release (btor, temp_1);
    boolector_release (btor, temp_2);
    boolector_release (btor, temp_1_ugte_a);
    boolector_release (btor, temp_2_ugte_c);
    boolector_release (btor, cond_if);
    boolector_release (btor, cond_else_1);
    boolector_release (btor, cond_else_2);
  }
  result = boolector_and (btor, b, d);

  /* conclusion: result is indeed the maximum of b & d */
  formula = boolector_ugte (btor, result, b_and_d);
  /* we negate the formula and show that it is UNSAT */
  tmp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = tmp;
  boolector_dump_btor (btor, stdout, formula);

  /* clean up */
  boolector_release (btor, result);
  boolector_release (btor, formula);
  boolector_release (btor, b_and_d);
  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, zero);
  boolector_release (btor, zero_num_bits_m_1);
  boolector_release (btor, one);
  boolector_release (btor, one_log_bits);
  boolector_release (btor, one_full_bits);
  boolector_delete (btor);
  return 0;
}
