#include "minxor.h"
#include "boolector.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/* minXOR algorithm from hacker's delight, page 62 */

BoolectorNode *
btor_minxor (Btor *btor,
             BoolectorNode *a_in,
             BoolectorNode *b_in,
             BoolectorNode *c_in,
             BoolectorNode *d_in,
             BoolectorNode *m_in,
             int num_bits)
{
  BoolectorNode *temp_1, *temp_2, *m, *zero;
  BoolectorNode *tmp, *a, *b, *c, *d, *not_a, *not_c, *neg_m;
  BoolectorNode *not_a_and_c, *not_a_and_c_and_m, *a_or_m, *temp_1_ulte_b;
  BoolectorNode *a_and_not_c, *a_and_not_c_and_m, *c_or_m, *temp_2_ulte_d;
  BoolectorNode *not_a_and_c_and_m_ne_zero, *a_and_not_c_and_m_ne_zero, *result;
  BoolectorNode *cond_if, *cond_else_1, *cond_else_2, *one_log_bits;
  BoolectorSort sort, sort_log;
  int i;

  assert (btor != NULL);
  assert (a_in != NULL);
  assert (b_in != NULL);
  assert (c_in != NULL);
  assert (d_in != NULL);
  assert (m_in != NULL);
  assert (num_bits > 0);
  assert (btor_util_is_power_of_2 (num_bits));

  a = boolector_copy (btor, a_in);
  b = boolector_copy (btor, b_in);
  c = boolector_copy (btor, c_in);
  d = boolector_copy (btor, d_in);
  m = boolector_copy (btor, m_in);

  sort     = boolector_bitvec_sort (btor, num_bits);
  sort_log = boolector_bitvec_sort (btor, btor_util_log_2 (num_bits));

  one_log_bits = boolector_one (btor, sort_log);
  zero         = boolector_zero (btor, sort);

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
  result = boolector_xor (btor, a, c);

  boolector_release (btor, zero);
  boolector_release (btor, one_log_bits);
  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release_sort (btor, sort_log);
  boolector_release_sort (btor, sort);

  return result;
}
