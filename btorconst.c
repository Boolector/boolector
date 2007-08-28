#include "btorconst.h"
#include "btorutil.h"

#include <assert.h>
#include <limits.h>
#include <string.h>

static const char *digit2const_table[10] = {
    "",
    "1",
    "10",
    "11",
    "100",
    "101",
    "110",
    "111",
    "1000",
    "1001",
};

#ifndef NDEBUG

static int
valid_const (const char *c)
{
  const char *p;
  char ch;
  for (p = c; (ch = *p); p++)
    if (ch != '0' && ch != '1') return 0;
  return 1;
}

#endif

char *
btor_int_to_bin (BtorMemMgr *mm, int x, int len)
{
  char *result = NULL;
  int i        = 0;
  assert (mm != NULL);
  assert (x >= 0);
  assert (len > 0);
  result = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  for (i = len - 1; i >= 0; i--)
  {
    result[i] = x % 2 ? '1' : '0';
    x >>= 1;
  }
  result[len] = '\0';
  return result;
}

char *
btor_copy_const (BtorMemMgr *mm, const char *c)
{
  char *result = NULL;
  assert (mm != NULL);
  assert (c != NULL);
  assert (valid_const (c));
  result = (char *) btor_malloc (mm, sizeof (char) * (strlen (c) + 1));
  strcpy (result, c);
  return result;
}

void
btor_delete_const (BtorMemMgr *mm, char *c)
{
  assert (valid_const (c));
  btor_freestr (mm, c);
}

char *
btor_slice_const (BtorMemMgr *mm, const char *a, int upper, int lower)
{
  const char *p, *eoa;
  char *res, *q;
  int len, delta;

  assert (valid_const (a));

  len = strlen (a);

  assert (0 <= lower);
  assert (upper <= len);

  delta = upper - lower + 1;

  res = btor_malloc (mm, delta + 1);

  p   = a + len - upper;
  q   = res;
  eoa = a + len - lower + 1;

  while (p < eoa) *q++ = *p++;

  *q = 0;

  assert (strlen (res) == (size_t) delta);

  return res;
}

static const char *
strip_zeroes (const char *a)
{
  while (*a == '0') a++;

  return a;
}

char *
btor_add_unbounded_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *res, *r, c, x, y, s, *tmp;
  int alen, blen, rlen;
  const char *p, *q;

  assert (valid_const (a));
  assert (valid_const (b));

  a = strip_zeroes (a);
  b = strip_zeroes (b);

  if (!*a) return btor_strdup (mm, b);

  if (!*b) return btor_strdup (mm, a);

  alen = strlen (a);
  blen = strlen (b);
  rlen = (alen < blen) ? blen : alen;
  rlen++;

  res = btor_malloc (mm, rlen + 1);

  p = a + alen;
  q = b + blen;

  c = '0';

  r  = res + rlen;
  *r = 0;

  while (res < r)
  {
    x    = (a < p) ? *--p : '0';
    y    = (b < q) ? *--q : '0';
    s    = x ^ y ^ c;
    c    = (x & y) | (x & c) | (y & c);
    *--r = s;
  }

  p = strip_zeroes (res);
  if ((p != res))
  {
    tmp = btor_copy_const (mm, p);
    btor_delete_const (mm, res);
    res = tmp;
  }

  return res;
}

char *
btor_mult_unbounded_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *res, *r, c, x, y, s, m;
  int alen, blen, rlen, i;
  const char *p;

  assert (valid_const (a));
  assert (valid_const (b));

  a = strip_zeroes (a);

  if (!*a) return btor_strdup (mm, "");

  if (a[0] == '1' && !a[1]) return btor_strdup (mm, b);

  b = strip_zeroes (b);

  if (!*b) return btor_strdup (mm, "");

  if (b[0] == '1' && !b[1]) return btor_strdup (mm, a);

  alen      = strlen (a);
  blen      = strlen (b);
  rlen      = alen + blen;
  res       = btor_malloc (mm, rlen + 1);
  res[rlen] = 0;

  for (r = res; r < res + blen; r++) *r = '0';

  for (p = a; p < a + alen; p++) *r++ = *p;

  assert (r == res + rlen);

  for (i = 0; i < alen; i++)
  {
    m = res[rlen - 1];
    c = '0';

    if (m == '1')
    {
      p = b + blen;
      r = res + blen;

      while (res < r)
      {
        x  = *--p;
        y  = *--r;
        s  = x ^ y ^ c;
        c  = (x & y) | (x & c) | (y & c);
        *r = s;
      }
    }

    memmove (res + 1, res, rlen - 1);
    res[0] = c;
  }

  return res;
}

int
btor_cmp_const (const char *a, const char *b)
{
  const char *p, *q, *s;
  int l, k, delta;

  assert (valid_const (a));
  assert (valid_const (b));

  a = strip_zeroes (a);
  b = strip_zeroes (b);

  l = strlen (a);
  k = strlen (b);

  delta = (l - k);

  if (delta < 0)
  {
    p = a;
    s = b - delta;

    for (q = b; q < s; q++)
      if (*q == '1') return -1;
  }
  else
  {
    s = a + delta;
    q = b;

    for (p = a; p < s; p++)
      if (*p == '1') return 1;
  }

  assert (strlen (p) == strlen (q));

  return strcmp (p, q);
}

char *
btor_sub_unbounded_const (BtorMemMgr *mem, const char *a, const char *b)
{
  char *res, *tmp, *r, c, x, y, s;
  int alen, blen, rlen;
  const char *p, *q;

  assert (valid_const (a));
  assert (valid_const (b));
  assert (btor_cmp_const (b, a) <= 0);

  a = strip_zeroes (a);
  b = strip_zeroes (b);
  if (!*b) return btor_strdup (mem, a);

  alen = strlen (a);
  blen = strlen (b);

  assert (alen >= blen);
  rlen = alen;

  res = btor_malloc (mem, rlen + 1);

  p = a + alen;
  q = b + blen;

  c  = '0';
  r  = res + rlen;
  *r = 0;

  while (res < r)
  {
    assert (a < p);
    x = *--p;

    y = (b < q) ? *--q : '0';

    s = x ^ y ^ c;
    c = ((1 ^ x) & c) | ((1 ^ x) & y) | (y & c);

    *--r = s;
  }

  assert (c == '0');

#ifndef NDEBUG
  {
    tmp = btor_add_unbounded_const (mem, res, b);
    assert (!btor_cmp_const (tmp, a));
    btor_freestr (mem, tmp);
  }
#endif

  tmp = btor_strdup (mem, strip_zeroes (res));
  btor_freestr (mem, res);
  res = tmp;

  return res;
}

char *
btor_not_const (BtorMemMgr *mm, const char *a)
{
  char *result = NULL;
  int len      = 0;
  int i        = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (strlen (a) > 0);
  assert (valid_const (a));
  len    = (int) strlen (a);
  result = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  for (i = len - 1; i >= 0; i--) result[i] = a[i] ^ 1;
  result[len] = '\0';
  return result;
}

char *
btor_and_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  int len      = 0;
  int i        = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  len    = (int) strlen (a);
  result = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  for (i = len - 1; i >= 0; i--) result[i] = a[i] & b[i];
  result[len] = '\0';
  return result;
}

char *
btor_eq_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  int len      = 0;
  int i        = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  len       = (int) strlen (a);
  result    = (char *) btor_malloc (mm, sizeof (char) * 2);
  result[0] = '1';
  for (i = len - 1; i >= 0; i--)
  {
    if (a[i] != b[i])
    {
      result[0] = '0';
      break;
    }
  }
  result[1] = '\0';
  return result;
}

char *
btor_add_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  char carry   = '0';
  int len      = 0;
  int i        = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  len    = (int) strlen (a);
  result = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  for (i = len - 1; i >= 0; i--)
  {
    result[i] = a[i] ^ b[i] ^ carry;
    carry     = (a[i] & b[i]) | (a[i] & carry) | (b[i] & carry);
  }
  result[len] = '\0';
  return result;
}

char *
btor_neg_const (BtorMemMgr *mm, const char *a)
{
  char *result = NULL;
  char *not_a  = NULL;
  char *one    = NULL;
  int len      = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (strlen (a) > 0);
  assert (valid_const (a));
  len    = (int) strlen (a);
  not_a  = btor_not_const (mm, a);
  one    = btor_int_to_bin (mm, 1, len);
  result = btor_add_const (mm, not_a, one);
  btor_delete_const (mm, not_a);
  btor_delete_const (mm, one);
  return result;
}

char *
btor_sub_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  char *neg_b  = NULL;
  int len      = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  len    = (int) strlen (a);
  neg_b  = btor_neg_const (mm, b);
  result = btor_add_const (mm, a, neg_b);
  btor_delete_const (mm, neg_b);
  return result;
}

static char *
sll_n_bits (BtorMemMgr *mm, const char *a, int n)
{
  char *result = NULL;
  int len      = 0;
  int i        = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (valid_const (a));
  assert (n >= 0);
  assert (n < (int) strlen (a));
  len = (int) strlen (a);
  if (len == 0) return btor_strdup (mm, a);
  result = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  for (i = 0; i < len - n; i++) result[i] = a[i + n];
  for (i = len - n; i < len; i++) result[i] = '0';
  result[len] = '\0';
  return result;
}

char *
btor_umul_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  char *and    = NULL;
  char *add    = NULL;
  char *shift  = NULL;
  int i        = 0;
  int j        = 0;
  int len      = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  len    = (int) strlen (a);
  result = btor_int_to_bin (mm, 0, len);
  for (i = len - 1; i >= 0; i--)
  {
    and = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
    for (j = 0; j < len; j++) and[j] = a[j] & b[i];
    and[len] = '\0';
    shift    = sll_n_bits (mm, and, len - 1 - i);
    add      = btor_add_const (mm, result, shift);
    btor_delete_const (mm, result);
    btor_delete_const (mm, and);
    btor_delete_const (mm, shift);
    result = add;
  }
  return result;
}

static char *
srl_n_bits (BtorMemMgr *mm, const char *a, int n)
{
  char *result = NULL;
  int len      = 0;
  int i        = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (valid_const (a));
  assert (n >= 0);
  assert (n < (int) strlen (a));
  len = (int) strlen (a);
  if (len == 0) return btor_strdup (mm, a);
  result = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  for (i = 0; i < n; i++) result[i] = '0';
  for (i = n; i < len; i++) result[i] = a[i - n];
  result[len] = '\0';
  return result;
}

static void
udiv_umod_const (BtorMemMgr *mm,
                 const char *a,
                 const char *b,
                 char **quotient,
                 char **remainder)
{
  char *b_i          = NULL;
  char *temp         = NULL;
  char *sub          = NULL;
  char *remainder_2n = NULL;
  int len            = 0;
  int len_2n         = 0;
  int i              = 0;
  int gte            = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (quotient != NULL);
  assert (remainder != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  len = (int) strlen (a);
  assert (len <= INT_MAX / 2);
  len_2n           = len << 1;
  *quotient        = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  (*quotient)[len] = '\0';
  b_i              = (char *) btor_malloc (mm, sizeof (char) * (len_2n + 1));
  b_i[len_2n]      = '\0';
  remainder_2n     = (char *) btor_malloc (mm, sizeof (char) * (len_2n + 1));
  remainder_2n[len_2n] = '\0';
  for (i = 0; i < len; i++)
  {
    b_i[i]          = b[i];
    remainder_2n[i] = '0';
  }
  for (i = len; i < len_2n; i++)
  {
    b_i[i]          = '0';
    remainder_2n[i] = a[i - len];
  }
  for (i = len - 1; i >= 0; i--)
  {
    temp = srl_n_bits (mm, b_i, 1);
    btor_delete_const (mm, b_i);
    b_i                      = temp;
    gte                      = btor_cmp_const (remainder_2n, b_i) >= 0;
    (*quotient)[len - 1 - i] = (char) (48 ^ gte);
    if (gte)
    {
      sub = btor_sub_const (mm, remainder_2n, b_i);
      btor_delete_const (mm, remainder_2n);
      remainder_2n = sub;
    }
  }
  btor_delete_const (mm, b_i);
  *remainder        = (char *) btor_malloc (mm, sizeof (char) * (len + 1));
  (*remainder)[len] = '\0';
  for (i = len; i < len_2n; i++) (*remainder)[i - len] = remainder_2n[i];
  btor_delete_const (mm, remainder_2n);
}

char *
btor_udiv_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *quotient  = NULL;
  char *remainder = NULL;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  udiv_umod_const (mm, a, b, &quotient, &remainder);
  btor_delete_const (mm, remainder);
  return quotient;
}

char *
btor_umod_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *quotient  = NULL;
  char *remainder = NULL;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  udiv_umod_const (mm, a, b, &quotient, &remainder);
  btor_delete_const (mm, quotient);
  return remainder;
}

char *
btor_sll_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  char *temp   = NULL;
  int i        = 0;
  int len      = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) > 1);
  assert (btor_is_power_of_2_util (strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  len = strlen (b);
  if (b[len - 1] == '1')
    result = sll_n_bits (mm, a, 1);
  else
    result = btor_copy_const (mm, a);
  for (i = len - 2; i >= 0; i--)
  {
    temp = result;
    if (b[i] == '1')
      result = sll_n_bits (mm, temp, btor_pow_2_util (len - i - 1));
    else
      result = btor_copy_const (mm, temp);
    btor_delete_const (mm, temp);
  }
  return result;
}

char *
btor_srl_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  char *temp   = NULL;
  int i        = 0;
  int len      = 0;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) > 1);
  assert (btor_is_power_of_2_util (strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  len = strlen (b);
  if (b[len - 1] == '1')
    result = srl_n_bits (mm, a, 1);
  else
    result = btor_copy_const (mm, a);
  for (i = len - 2; i >= 0; i--)
  {
    temp = result;
    if (b[i] == '1')
      result = srl_n_bits (mm, temp, btor_pow_2_util (len - i - 1));
    else
      result = btor_copy_const (mm, temp);
    btor_delete_const (mm, temp);
  }
  return result;
}

char *
btor_ult_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert (strlen (a) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  result = (char *) btor_malloc (mm, sizeof (char) * 2);
  if (strcmp (a, b) == -1)
    result[0] = '1';
  else
    result[0] = '0';
  result[1] = '\0';
  return result;
}

char *
btor_concat_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result = NULL;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) > 0);
  assert (strlen (b) > 0);
  assert (valid_const (a));
  assert (valid_const (b));
  result =
      (char *) btor_malloc (mm, sizeof (char) * (strlen (a) + strlen (b) + 1));
  strcpy (result, a);
  strcat (result, b);
  return result;
}

char *
btor_udiv_unbounded_const (BtorMemMgr *mem,
                           const char *dividend,
                           const char *divisor,
                           char **rest_ptr)
{
  char *quotient, *rest, *extended_divisor, *tmp;
  int delta, plen, qlen;
  const char *p, *q;

  assert (valid_const (dividend));
  assert (valid_const (divisor));

  dividend = strip_zeroes (dividend);
  divisor  = strip_zeroes (divisor);

  for (p = dividend; *p && *p == '0'; p++)
    ;

  for (q = divisor; *q && *q == '0'; q++)
    ;

  assert (*q); /* in any case even if 'dividend == 0' */

  if (!*p || btor_cmp_const (p, q) < 0)
  {
    if (rest_ptr) *rest_ptr = btor_strdup (mem, q);

    return btor_strdup (mem, "");
  }

  plen  = strlen (p);
  qlen  = strlen (q);
  delta = plen - qlen;
  assert (delta >= 0);

  extended_divisor = btor_malloc (mem, plen + 1);
  memset (extended_divisor, '0', delta);
  strcpy (extended_divisor + delta, divisor);

  udiv_umod_const (mem, dividend, extended_divisor, &quotient, &rest);

  btor_delete_const (mem, extended_divisor);

  tmp = btor_strdup (mem, strip_zeroes (quotient));
  btor_delete_const (mem, quotient);
  quotient = tmp;

  tmp = btor_strdup (mem, strip_zeroes (rest));
  btor_delete_const (mem, rest);
  rest = tmp;

  assert (btor_cmp_const (rest, divisor) < 0);
#ifndef NDEBUG
  {
    char *tmp1 = btor_mult_unbounded_const (mem, quotient, divisor);
    char *tmp2 = btor_add_unbounded_const (mem, tmp1, rest);
    assert (!btor_cmp_const (dividend, tmp2));
    btor_freestr (mem, tmp1);
    btor_freestr (mem, tmp2);
  }
#endif
  if (rest_ptr)
    *rest_ptr = rest;
  else
    btor_delete_const (mem, rest);

  return quotient;
}

char *
btor_const_to_hex (BtorMemMgr *mem, const char *c)
{
  int clen = strlen (c), rlen = (clen + 3) / 4, i, j, tmp;
  char *res, ch;

  if (rlen)
  {
    res = btor_malloc (mem, rlen + 1);

    i = clen - 1;
    j = rlen;

    res[j--] = 0;

    while (i >= 0)
    {
      tmp = (c[i--] == '1');
      if (i >= 0)
      {
        tmp |= (c[i--] == '1') << 1;
        if (i >= 0)
        {
          tmp |= (c[i--] == '1') << 2;
          if (i >= 0) tmp |= (c[i--] == '1') << 3;
        }
      }

      if (tmp < 10)
        ch = '0' + tmp;
      else
        ch = 'a' + (tmp - 10);

      res[j--] = ch;
    }
  }
  else
    res = btor_strdup (mem, "0");

  return res;
}

char *
btor_uext_const (BtorMemMgr *mem, const char *c, int len)
{
  char *res, *q;
  const char *p;
  int rlen;

  assert (len >= 1);

  rlen = strlen (c) + len;

  BTOR_NEWN (mem, res, rlen + 1);

  for (q = res; len; len--, q++) *q = '0';

  for (p = c; *p; p++, q++) *q = *p;

  assert (res + rlen == q);
  *q = 0;

  return res;
}

char *
btor_hex_to_const_n (BtorMemMgr *mem, const char *str, int hlen)
{
  const char *p, *end;
  char *tmp, *res, *q;
  int len;

  len = 4 * hlen;
  BTOR_NEWN (mem, tmp, len + 1);
  q = tmp;

  end = str + hlen;
  for (p = str; p < end; p++) switch (*p)
    {
      case '0':
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        break;
      case '1':
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        break;
      case '2':
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        break;
      case '3':
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        break;
      case '4':
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        break;
      case '5':
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        break;
      case '6':
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        break;
      case '7':
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        break;
      case '8':
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        break;
      case '9':
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        break;
      case 'A':
      case 'a':
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        break;
      case 'B':
      case 'b':
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        break;
      case 'C':
      case 'c':
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        break;
      case 'D':
      case 'd':
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        break;
      case 'E':
      case 'e':
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        break;
      case 'F':
      case 'f':
      default:
        assert (*p == 'f' || *p == 'F');
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        break;
    }

  assert (tmp + len == q);
  *q++ = 0;

  res = btor_strdup (mem, strip_zeroes (tmp));
  btor_freestr (mem, tmp);

  return res;
}

char *
btor_hex_to_const (BtorMemMgr *mem, const char *str)
{
  return btor_hex_to_const_n (mem, str, strlen (str));
}

static const char *
digit2const (char ch)
{
  assert ('0' <= ch);
  assert (ch <= '9');
  return digit2const_table[ch - '0'];
}

char *
btor_decimal_to_const_n (BtorMemMgr *mem, const char *str, int len)
{
  const char *end, *p;
  char *res, *tmp;

  res = btor_strdup (mem, "");

  end = str + len;
  for (p = str; p < end; p++)
  {
    tmp = btor_mult_unbounded_const (mem, res, "1010"); /* *10 */
    btor_delete_const (mem, res);
    res = tmp;

    tmp = btor_add_unbounded_const (mem, res, digit2const (*p));
    btor_delete_const (mem, res);
    res = tmp;
  }

  assert (strip_zeroes (res) == res);

  return res;
}

char *
btor_decimal_to_const (BtorMemMgr *mem, const char *str)
{
  return btor_decimal_to_const_n (mem, str, strlen (str));
}
