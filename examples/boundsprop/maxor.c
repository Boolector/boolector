#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

/* maxOR algorithm from hacker's delight, page 60 */

int
main (int argc, char **argv)
{
  int num_bits, i;
  Btor *btor;
  BtorExp *formula, *temp_1, *temp_2, *m, *zero, *zero_num_bits_m_1;
  BtorExp *one, *tmp, *a, *b, *c, *d, *m_minus_1, *b_minus_m;
  BtorExp *d_minus_m, *one_log_bits, *b_or_d, *b_and_d;
  BtorExp *b_and_d_and_m, *temp_1_ugte_a, *temp_2_ugte_c;
  BtorExp *b_and_d_and_m_ne_zero, *cond_1, *cond_2, *result;
  BtorExp *and_break, *cond_3, *cond_4, *_break;

  if (argc != 2)
  {
    printf ("Usage: ./maxor <num-bits>\n");
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

  /* as soon _break becomes 1, we do not change the values
   * of b and d anymore */
  _break = boolector_false (btor);

  /* needed later for conclusion */
  b_or_d = boolector_or (btor, b, d);

  for (i = 0; i < num_bits; i++)
  {
    b_and_d               = boolector_and (btor, b, d);
    b_and_d_and_m         = boolector_and (btor, b_and_d, m);
    b_and_d_and_m_ne_zero = boolector_ne (btor, b_and_d_and_m, zero);

    m_minus_1 = boolector_dec (btor, m);

    b_minus_m     = boolector_sub (btor, b, m);
    temp_1        = boolector_or (btor, b_minus_m, m_minus_1);
    temp_1_ugte_a = boolector_ugte (btor, temp_1, a);

    d_minus_m     = boolector_sub (btor, d, m);
    temp_2        = boolector_or (btor, d_minus_m, m_minus_1);
    temp_2_ugte_c = boolector_ugte (btor, temp_2, c);

    /* update b */
    cond_1 = boolector_cond (btor, temp_1_ugte_a, temp_1, b);
    cond_2 = boolector_cond (btor, b_and_d_and_m_ne_zero, cond_1, b);
    tmp    = boolector_cond (btor, _break, b, cond_2);
    boolector_release (btor, b);
    b = tmp;

    /* update _break */
    and_break = boolector_and (btor, b_and_d_and_m_ne_zero, temp_1_ugte_a);
    tmp       = boolector_or (btor, _break, and_break);
    boolector_release (btor, _break);
    _break = tmp;

    /* update d */
    cond_3 = boolector_cond (btor, temp_2_ugte_c, temp_2, d);
    cond_4 = boolector_cond (btor, b_and_d_and_m_ne_zero, cond_3, d);
    tmp    = boolector_cond (btor, _break, d, cond_4);
    boolector_release (btor, d);
    d = tmp;

    /* update m */
    tmp = boolector_srl (btor, m, one_log_bits);
    boolector_release (btor, m);
    m = tmp;

    boolector_release (btor, and_break);
    boolector_release (btor, b_and_d);
    boolector_release (btor, b_and_d_and_m);
    boolector_release (btor, b_and_d_and_m_ne_zero);
    boolector_release (btor, cond_1);
    boolector_release (btor, cond_2);
    boolector_release (btor, cond_3);
    boolector_release (btor, cond_4);
    boolector_release (btor, m_minus_1);
    boolector_release (btor, b_minus_m);
    boolector_release (btor, d_minus_m);
    boolector_release (btor, temp_1);
    boolector_release (btor, temp_2);
    boolector_release (btor, temp_1_ugte_a);
    boolector_release (btor, temp_2_ugte_c);
  }

  result = boolector_or (btor, b, d);

  /* conclusion: result is indeed the maximum of b | d */
  formula = boolector_ugte (btor, result, b_or_d);
  /* we negate the formula and show that it is UNSAT */
  tmp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = tmp;
  boolector_dump_btor (btor, stdout, formula);

  /* clean up */
  boolector_release (btor, _break);
  boolector_release (btor, result);
  boolector_release (btor, formula);
  boolector_release (btor, b_or_d);
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
