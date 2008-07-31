#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

/* minOR algorithm from hacker's delight, page 59 */

int
main (int argc, char **argv)
{
  int num_bits, i;
  Btor *btor;
  BtorExp *formula, *temp_1, *temp_2, *m, *zero, *zero_num_bits_m_1;
  BtorExp *one, *tmp, *a, *b, *c, *d, *not_a, *not_c, *neg_m;
  BtorExp *not_a_and_c, *not_a_and_c_and_m, *a_or_m, *temp_1_ulte_b;
  BtorExp *a_and_not_c, *a_and_not_c_and_m, *c_or_m, *temp_2_ulte_d;
  BtorExp *not_a_and_c_and_m_ne_zero, *a_and_not_c_and_m_ne_zero, *result;
  BtorExp *cond_if, *cond_else_1, *cond_else_2, *one_log_bits, *a_or_c;

  if (argc != 2)
  {
    printf ("Usage: ./minor <num-bits>\n");
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
  zero_num_bits_m_1 = boolector_zero (btor, num_bits - 1);
  zero              = boolector_zero (btor, num_bits);
  m                 = boolector_concat (btor, one, zero_num_bits_m_1);
  a                 = boolector_var (btor, num_bits, "a");
  b                 = boolector_var (btor, num_bits, "b");
  c                 = boolector_var (btor, num_bits, "c");
  d                 = boolector_var (btor, num_bits, "d");

  /* needed later for conclusion */
  a_or_c = boolector_or (btor, a, c);

  for (i = 0; i < num_bits; i++)
  {
    neg_m = boolector_neg (btor, m);

    not_a                     = boolector_not (btor, a);
    not_a_and_c               = boolector_and (btor, not_a, c);
    not_a_and_c_and_m         = boolector_and (btor, not_a_and_c, m);
    not_a_and_c_and_m_ne_zero = boolector_ne (btor, not_a_and_c_and_m, zero);

    a_or_m        = boolector_or (btor, a, m);
    temp_1        = boolector_and (btor, a_or_m, neg_m);
    temp_1_ulte_b = boolector_ulte (btor, temp_1, b);

    not_c                     = boolector_not (btor, c);
    a_and_not_c               = boolector_and (btor, a, not_c);
    a_and_not_c_and_m         = boolector_and (btor, a_and_not_c, m);
    a_and_not_c_and_m_ne_zero = boolector_ne (btor, a_and_not_c_and_m, zero);

    c_or_m        = boolector_or (btor, c, m);
    temp_2        = boolector_and (btor, c_or_m, neg_m);
    temp_2_ulte_d = boolector_ulte (btor, temp_2, d);

    /* update a */
    cond_if = boolector_cond (btor, temp_1_ulte_b, temp_1, a);
    tmp     = boolector_cond (btor, not_a_and_c_and_m_ne_zero, cond_if, a);
    boolector_release (btor, a);
    a = tmp;

    /* update c */
    cond_else_1 = boolector_cond (btor, temp_2_ulte_d, temp_2, c);
    cond_else_2 =
        boolector_cond (btor, a_and_not_c_and_m_ne_zero, cond_else_1, c);
    tmp = boolector_cond (btor, not_a_and_c_and_m_ne_zero, c, cond_else_2);
    boolector_release (btor, c);
    c = tmp;

    /* update m */
    tmp = boolector_srl (btor, m, one_log_bits);
    boolector_release (btor, m);
    m = tmp;

    boolector_release (btor, not_a);
    boolector_release (btor, not_c);
    boolector_release (btor, neg_m);
    boolector_release (btor, not_a_and_c);
    boolector_release (btor, a_and_not_c);
    boolector_release (btor, not_a_and_c_and_m);
    boolector_release (btor, a_and_not_c_and_m);
    boolector_release (btor, not_a_and_c_and_m_ne_zero);
    boolector_release (btor, a_and_not_c_and_m_ne_zero);
    boolector_release (btor, a_or_m);
    boolector_release (btor, c_or_m);
    boolector_release (btor, temp_1);
    boolector_release (btor, temp_2);
    boolector_release (btor, temp_1_ulte_b);
    boolector_release (btor, temp_2_ulte_d);
    boolector_release (btor, cond_if);
    boolector_release (btor, cond_else_1);
    boolector_release (btor, cond_else_2);
  }
  result = boolector_or (btor, a, c);

  /* conclusion: result is indeed the minimum of a | c */
  formula = boolector_ulte (btor, result, a_or_c);
  /* we negate the formula and show that it is UNSAT */
  tmp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = tmp;
  boolector_dump_btor (btor, stdout, formula);

  /* clean up */
  boolector_release (btor, result);
  boolector_release (btor, formula);
  boolector_release (btor, a_or_c);
  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, zero);
  boolector_release (btor, zero_num_bits_m_1);
  boolector_release (btor, one);
  boolector_release (btor, one_log_bits);
  boolector_delete (btor);
  return 0;
}
