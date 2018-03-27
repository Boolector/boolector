#include "maxxor.h"
#include "boolector.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/* maxXOR algorithm from hacker's delight, page 62 */

BoolectorNode *
btor_maxxor (Btor *btor,
             BoolectorNode *a_in,
             BoolectorNode *b_in,
             BoolectorNode *c_in,
             BoolectorNode *d_in,
             BoolectorNode *m_in,
             int num_bits)
{
  BoolectorNode *temp_1, *temp_2, *m, *zero;
  BoolectorNode *tmp, *a, *b, *c, *d, *m_minus_1, *b_minus_m;
  BoolectorNode *d_minus_m, *one_log_bits, *b_and_d;
  BoolectorNode *b_and_d_and_m, *temp_1_ugte_a, *temp_2_ugte_c;
  BoolectorNode *b_and_d_and_m_ne_zero, *cond_1, *cond_2, *result, *cond_3;
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
    tmp    = boolector_cond (btor, b_and_d_and_m_ne_zero, cond_1, b);
    boolector_release (btor, b);
    b = tmp;

    /* update d */
    cond_2 = boolector_cond (btor, temp_2_ugte_c, temp_2, d);
    cond_3 = boolector_cond (btor, temp_1_ugte_a, d, cond_2);
    tmp    = boolector_cond (btor, b_and_d_and_m_ne_zero, cond_3, d);
    boolector_release (btor, d);
    d = tmp;

    /* update m */
    tmp = boolector_srl (btor, m, one_log_bits);
    boolector_release (btor, m);
    m = tmp;

    boolector_release (btor, b_and_d);
    boolector_release (btor, b_and_d_and_m);
    boolector_release (btor, b_and_d_and_m_ne_zero);
    boolector_release (btor, cond_1);
    boolector_release (btor, cond_2);
    boolector_release (btor, cond_3);
    boolector_release (btor, m_minus_1);
    boolector_release (btor, b_minus_m);
    boolector_release (btor, d_minus_m);
    boolector_release (btor, temp_1);
    boolector_release (btor, temp_2);
    boolector_release (btor, temp_1_ugte_a);
    boolector_release (btor, temp_2_ugte_c);
  }

  result = boolector_xor (btor, b, d);

  boolector_release (btor, a);
  boolector_release (btor, b);
  boolector_release (btor, c);
  boolector_release (btor, d);
  boolector_release (btor, m);
  boolector_release (btor, zero);
  boolector_release (btor, one_log_bits);
  boolector_release_sort (btor, sort_log);
  boolector_release_sort (btor, sort);

  return result;
}
