#include "minand.h"
#include "boolector.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/* minAND algorithm from hacker's delight, page 61 */

BoolectorNode *
btor_minand (Btor *btor,
             BoolectorNode *a_in,
             BoolectorNode *b_in,
             BoolectorNode *c_in,
             BoolectorNode *d_in,
             BoolectorNode *m_in,
             int num_bits)
{
  BoolectorNode *temp_1, *temp_2, *m, *zero;
  BoolectorNode *tmp, *a, *b, *c, *d, *neg_m, *not_a, *not_c;
  BoolectorNode *one_log_bits, *a_or_m, *c_or_m;
  BoolectorNode *temp_1_ulte_b, *temp_2_ulte_d, *not_a_and_not_c;
  BoolectorNode *not_a_and_not_c_and_m, *not_a_and_not_c_and_m_ne_zero;
  BoolectorNode *cond_1, *cond_2, *result, *and_break, *cond_3, *cond_4;
  BoolectorNode *_break;
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

  /* as soon _break becomes 1, we do not change the values
   * of a and c anymore */
  _break = boolector_false (btor);

  for (i = 0; i < num_bits; i++)
  {
    not_a = boolector_not (btor, a);
    not_c = boolector_not (btor, c);
    neg_m = boolector_neg (btor, m);

    not_a_and_not_c       = boolector_and (btor, not_a, not_c);
    not_a_and_not_c_and_m = boolector_and (btor, not_a_and_not_c, m);
    not_a_and_not_c_and_m_ne_zero =
        boolector_ne (btor, not_a_and_not_c_and_m, zero);

    a_or_m        = boolector_or (btor, a, m);
    temp_1        = boolector_and (btor, a_or_m, neg_m);
    temp_1_ulte_b = boolector_ulte (btor, temp_1, b);

    c_or_m        = boolector_or (btor, c, m);
    temp_2        = boolector_and (btor, c_or_m, neg_m);
    temp_2_ulte_d = boolector_ulte (btor, temp_2, d);

    /* update a */
    cond_1 = boolector_cond (btor, temp_1_ulte_b, temp_1, a);
    cond_2 = boolector_cond (btor, not_a_and_not_c_and_m_ne_zero, cond_1, a);
    tmp    = boolector_cond (btor, _break, a, cond_2);
    boolector_release (btor, a);
    a = tmp;

    /* update _break */
    and_break =
        boolector_and (btor, not_a_and_not_c_and_m_ne_zero, temp_1_ulte_b);
    tmp = boolector_or (btor, _break, and_break);
    boolector_release (btor, _break);
    _break = tmp;
    boolector_release (btor, and_break);

    /* update c */
    cond_3 = boolector_cond (btor, temp_2_ulte_d, temp_2, c);
    cond_4 = boolector_cond (btor, not_a_and_not_c_and_m_ne_zero, cond_3, c);
    tmp    = boolector_cond (btor, _break, c, cond_4);
    boolector_release (btor, c);
    c = tmp;

    /* update _break */
    and_break =
        boolector_and (btor, not_a_and_not_c_and_m_ne_zero, temp_2_ulte_d);
    tmp = boolector_or (btor, _break, and_break);
    boolector_release (btor, _break);
    _break = tmp;
    boolector_release (btor, and_break);

    /* update m */
    tmp = boolector_srl (btor, m, one_log_bits);
    boolector_release (btor, m);
    m = tmp;

    boolector_release (btor, not_a);
    boolector_release (btor, not_c);
    boolector_release (btor, not_a_and_not_c);
    boolector_release (btor, not_a_and_not_c_and_m);
    boolector_release (btor, not_a_and_not_c_and_m_ne_zero);
    boolector_release (btor, a_or_m);
    boolector_release (btor, c_or_m);
    boolector_release (btor, cond_1);
    boolector_release (btor, cond_2);
    boolector_release (btor, cond_3);
    boolector_release (btor, cond_4);
    boolector_release (btor, neg_m);
    boolector_release (btor, temp_1);
    boolector_release (btor, temp_2);
    boolector_release (btor, temp_1_ulte_b);
    boolector_release (btor, temp_2_ulte_d);
  }

  result = boolector_and (btor, a, c);

  boolector_release (btor, _break);
  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, one_log_bits);
  boolector_release (btor, zero);
  boolector_release_sort (btor, sort_log);
  boolector_release_sort (btor, sort);

  return result;
}
