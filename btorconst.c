#include "btorconst.h"
#include "btormem.h"
#include "btorstack.h"
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
is_valid_const (const char *c)
{
  const char *p;
  char ch;

  assert (c != NULL);

  for (p = c; (ch = *p); p++)
    if (ch != '0' && ch != '1') return 0;
  return 1;
}

static int
is_valid_const_3vl (const char *c)
{
  const char *p;
  char ch;

  assert (c != NULL);

  for (p = c; (ch = *p); p++)
    if (ch != '0' && ch != '1' && ch != 'x') return 0;
  return 1;
}

#endif

static const char *
digit2const (char ch)
{
  assert ('0' <= ch);
  assert (ch <= '9');

  return digit2const_table[ch - '0'];
}

static const char *
strip_zeroes (const char *a)
{
  assert (a != NULL);
  assert (is_valid_const (a));

  while (*a == '0') a++;

  return a;
}

#define MSB_INT ((int) (sizeof (int) * 8 - 1))

char *
btor_zero_const (BtorMemMgr *mm, int len)
{
  char *res;
  int i;

  assert (len > 0);

  BTOR_NEWN (mm, res, len + 1);
  for (i = 0; i < len; i++) res[i] = '0';
  res[i] = '\0';

  return res;
}

char *
btor_one_const (BtorMemMgr *mm, int len)
{
  char *res;
  int i;

  assert (mm != NULL);
  assert (len > 0);

  BTOR_NEWN (mm, res, len + 1);
  for (i = 0; i < len - 1; i++) res[i] = '0';
  res[i++] = '1';
  res[i]   = '\0';

  return res;
}

char *
btor_ones_const (BtorMemMgr *mm, int len)
{
  char *res;
  int i;

  assert (mm != NULL);
  assert (len > 0);

  BTOR_NEWN (mm, res, len + 1);
  for (i = 0; i < len; i++) res[i] = '1';
  res[i] = '\0';

  return res;
}

char *
btor_int_to_const (BtorMemMgr *mm, int x, int len)
{
  char msb, *result;
  int i;

  assert (mm != NULL);
  assert (len > 0);

  BTOR_NEWN (mm, result, len + 1);

  msb = (x & (1 << MSB_INT)) ? '1' : '0';
  for (i = len - 1; i >= MSB_INT; i--) result[len - 1 - i] = msb;

  while (i >= 0)
  {
    result[len - 1 - i] = (x & (1 << i)) ? '1' : '0';
    i--;
  }

  result[len] = '\0';

  return result;
}

#define MSB_UNSIGNED ((int) (sizeof (unsigned) * 8 - 1))

char *
btor_unsigned_to_const (BtorMemMgr *mm, unsigned x, int len)
{
  char *result;
  int i;

  assert (mm != NULL);
  assert (len > 0);

  BTOR_NEWN (mm, result, len + 1);

  for (i = len - 1; i > MSB_UNSIGNED; i--) result[len - 1 - i] = '0';

  while (i >= 0)
  {
    result[len - 1 - i] = (x & (1u << i)) ? '1' : '0';
    i--;
  }

  result[len] = '\0';

  return result;
}

char *
btor_decimal_to_const_n (BtorMemMgr *mem, const char *str, int len)
{
  const char *end, *p;
  char *res, *tmp;

  assert (mem != NULL);
  assert (str != NULL);
  assert (len >= 0);

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
  assert (mem != NULL);
  assert (str != NULL);

  return btor_decimal_to_const_n (mem, str, (int) strlen (str));
}

char *
btor_hex_to_const_n (BtorMemMgr *mem, const char *str, int hlen)
{
  const char *p, *end;
  char *tmp, *res, *q;
  int len;

  assert (mem != NULL);
  assert (str != NULL);
  assert (hlen >= 0);

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
  assert (mem != NULL);
  assert (str != NULL);

  return btor_hex_to_const_n (mem, str, (int) strlen (str));
}

char *
btor_ground_const_3vl (BtorMemMgr *mm, const char *c)
{
  char *res, *q;
  const char *p;
  char ch;

  assert (mm != NULL);
  assert (c != NULL);
  assert ((int) strlen (c) > 0);
  assert (is_valid_const_3vl (c));

  BTOR_NEWN (mm, res, (int) strlen (c) + 1);

  q = res;
  for (p = c; (ch = *p); p++) *q++ = (ch == '1') ? '1' : '0'; /* 'x' -> '0' */

  *q = 0;

  return res;
}

int
btor_is_zero_const (const char *str)
{
  const char *p;

  assert (str != NULL);
  assert ((int) strlen (str) > 0);
  assert (is_valid_const (str));

  for (p = str; *p; p++)
    if (*p != '0') return 0;
  return 1;
}

int
btor_is_one_const (const char *str)
{
  int len, i;

  assert (str != NULL);
  assert ((int) strlen (str) > 0);
  assert (is_valid_const (str));

  len = (int) strlen (str);
  if (str[len - 1] != '1') return 0;
  for (i = 0; i < len - 1; i++)
    if (str[i] != '0') return 0;
  return 1;
}

int
btor_is_ones_const (const char *str)
{
  const char *p;

  assert (str != NULL);
  assert ((int) strlen (str) > 0);
  assert (is_valid_const (str));

  for (p = str; *p; p++)
    if (*p != '1') return 0;
  return 1;
}

BtorSpecialConst
btor_is_special_const (const char *str)
{
  char c;
  const char *p;

  assert (str != NULL);
  assert ((int) strlen (str) > 0);
  assert (is_valid_const (str));

  c = *str;
  p = str + 1;

  while (*p)
  {
    if (*p != c)
    {
      p++;
      if (c == '0' && !*p)
        return BTOR_SPECIAL_CONST_ONE;
      else
        return BTOR_SPECIAL_CONST_NONE;
    }
    else
      p++;
  }

  if (c == '0') return BTOR_SPECIAL_CONST_ZERO;

  assert (c == '1');
  /* bit-width == 1 ? */
  if (p == str + 1)
  {
    assert ((int) strlen (str) == 1);
    return BTOR_SPECIAL_CONST_ONE_ONES;
  }
  return BTOR_SPECIAL_CONST_ONES;
}

char *
btor_copy_const (BtorMemMgr *mm, const char *c)
{
  assert (mm != NULL);
  assert (c != NULL);
  assert (is_valid_const_3vl (c));

  return btor_strdup (mm, c);
}

void
btor_delete_const (BtorMemMgr *mm, char *c)
{
  assert (mm != NULL);
  assert (c != NULL);
  assert (is_valid_const_3vl (c));

  btor_freestr (mm, c);
}

char *
btor_slice_const (BtorMemMgr *mm, const char *a, int upper, int lower)
{
  const char *p, *eoa;
  char *res, *q;
  int len, delta;

  assert (mm != NULL);
  assert (a != NULL);
  assert (is_valid_const (a));
  assert (upper < (int) strlen (a));
  assert (upper >= lower);
  assert (lower >= 0);

  len   = (int) strlen (a);
  delta = upper - lower + 1;

  BTOR_NEWN (mm, res, delta + 1);

  p   = a + len - 1 - upper;
  q   = res;
  eoa = a + len - 1 - lower;

  while (p <= eoa) *q++ = *p++;

  *q = 0;

  assert ((int) strlen (res) == delta);

  return res;
}

char *
btor_add_unbounded_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *res, *r, c, x, y, s, *tmp;
  int alen, blen, rlen;
  const char *p, *q;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  a = strip_zeroes (a);
  b = strip_zeroes (b);

  if (!*a) return btor_strdup (mm, b);

  if (!*b) return btor_strdup (mm, a);

  alen = (int) strlen (a);
  blen = (int) strlen (b);
  rlen = (alen < blen) ? blen : alen;
  rlen++;

  BTOR_NEWN (mm, res, rlen + 1);

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

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  a = strip_zeroes (a);

  if (!*a) return btor_strdup (mm, "");

  if (a[0] == '1' && !a[1]) return btor_strdup (mm, b);

  b = strip_zeroes (b);

  if (!*b) return btor_strdup (mm, "");

  if (b[0] == '1' && !b[1]) return btor_strdup (mm, a);

  alen = (int) strlen (a);
  blen = (int) strlen (b);
  rlen = alen + blen;
  BTOR_NEWN (mm, res, rlen + 1);
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

  assert (a != NULL);
  assert (b != NULL);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  a = strip_zeroes (a);
  b = strip_zeroes (b);

  l = (int) strlen (a);
  k = (int) strlen (b);

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

  assert (mem != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (is_valid_const (a));
  assert (is_valid_const (b));
  assert (btor_cmp_const (b, a) <= 0);

  a = strip_zeroes (a);
  b = strip_zeroes (b);
  if (!*b) return btor_strdup (mem, a);

  alen = (int) strlen (a);
  blen = (int) strlen (b);

  assert (alen >= blen);
  rlen = alen;

  BTOR_NEWN (mem, res, rlen + 1);

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

static void
invert_const (BtorMemMgr *mm, char *a)
{
  int len, i;
  assert (mm != NULL);
  assert (a != NULL);
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  (void) mm;

  len = (int) strlen (a);
  for (i = 0; i < len; i++)
    if (a[i] != 'x') a[i] = (char) (1 ^ a[i]);
}

void
btor_invert_const (BtorMemMgr *mm, char *a)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  invert_const (mm, a);
}

char *
btor_not_const (BtorMemMgr *mm, const char *a)
{
  char *result;
  int len, i;

  assert (mm != NULL);
  assert (a != NULL);
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));

  len = (int) strlen (a);
  BTOR_NEWN (mm, result, len + 1);
  for (i = len - 1; i >= 0; i--) result[i] = a[i] ^ 1;
  result[len] = '\0';
  return result;
}

static char *
and_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result;
  int len, i;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  len = (int) strlen (a);
  BTOR_NEWN (mm, result, len + 1);
  for (i = len - 1; i >= 0; i--)
  {
    if (a[i] == '0' || b[i] == '0')
      result[i] = '0';
    else if (a[i] == 'x' || b[i] == 'x')
      result[i] = 'x';
    else
      result[i] = a[i] & b[i];
  }
  result[len] = '\0';
  return result;
}

char *
btor_and_const (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  return and_const (mm, a, b);
}

static char *
eq_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result;
  int len, i, has_x;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  len = (int) strlen (a);
  BTOR_NEWN (mm, result, 2);
  result[0] = '1';
  has_x     = 0;

  for (i = len - 1; i >= 0; i--)
  {
    if (a[i] == 'x' || b[i] == 'x')
      has_x = 1;
    else if (a[i] != b[i])
    {
      result[0] = '0';
      break;
    }
  }
  result[1] = '\0';

  if (result[0] == '1' && has_x) result[0] = 'x';

  return result;
}

char *
btor_eq_const (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  return eq_const (mm, a, b);
}

static char *
add_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char carry, p0, p1, p2, *result;
  int len, i;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  carry = '0';
  len   = (int) strlen (a);
  BTOR_NEWN (mm, result, len + 1);
  for (i = len - 1; i >= 0; i--)
  {
    if (a[i] == 'x' || b[i] == 'x' || carry == 'x')
      result[i] = 'x';
    else
      result[i] = a[i] ^ b[i] ^ carry;

    if (a[i] == '0' || b[i] == '0')
      p0 = '0';
    else if (a[i] == 'x' || b[i] == 'x')
      p0 = 'x';
    else
      p0 = a[i] & b[i];

    if (a[i] == '0' || carry == '0')
      p1 = '0';
    else if (a[i] == 'x' || carry == 'x')
      p1 = 'x';
    else
      p1 = a[i] & carry;

    if (b[i] == '0' || carry == '0')
      p2 = '0';
    else if (b[i] == 'x' || carry == 'x')
      p2 = 'x';
    else
      p2 = b[i] & carry;

    if (p0 == '1' || p1 == '1' || p2 == '1')
      carry = '1';
    else if (p0 == 'x' || p1 == 'x' || p2 == 'x')
      carry = 'x';
    else
      carry = p0 | p1 | p2;
  }
  result[len] = '\0';
  return result;
}

char *
btor_add_const (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));
  return add_const (mm, a, b);
}

char *
btor_neg_const (BtorMemMgr *mm, const char *a)
{
  char *result, *not_a, *one;
  int len;

  assert (mm != NULL);
  assert (a != NULL);
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));

  len    = (int) strlen (a);
  not_a  = btor_not_const (mm, a);
  one    = btor_int_to_const (mm, 1, len);
  result = btor_add_const (mm, not_a, one);
  btor_delete_const (mm, not_a);
  btor_delete_const (mm, one);
  return result;
}

char *
btor_sub_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result, *neg_b;
  int len;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  len    = (int) strlen (a);
  neg_b  = btor_neg_const (mm, b);
  result = btor_add_const (mm, a, neg_b);
  btor_delete_const (mm, neg_b);
  return result;
}

static char *
sll_n_bits (BtorMemMgr *mm, const char *a, int n)
{
  char *result;
  int len, i;

  assert (mm != NULL);
  assert (a != NULL);
  assert (is_valid_const_3vl (a));
  assert (n >= 0);
  assert (n < (int) strlen (a));

  len = (int) strlen (a);
  if (len == 0) return btor_strdup (mm, a);
  BTOR_NEWN (mm, result, len + 1);
  for (i = 0; i < len - n; i++) result[i] = a[i + n];
  for (i = len - n; i < len; i++) result[i] = '0';
  result[len] = '\0';
  return result;
}

static char *
mul_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result, *and, *add, *shift;
  int i, j, len;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  len    = (int) strlen (a);
  result = btor_int_to_const (mm, 0, len);
  for (i = len - 1; i >= 0; i--)
  {
    BTOR_NEWN (mm, and, len + 1);
    for (j = 0; j < len; j++)
    {
      if (a[j] == '0' || b[i] == '0')
        and[j] = '0';
      else if (a[j] == 'x' || b[i] == 'x')
        and[j] = 'x';
      else
        and[j] = a[j] & b[i];
    }
    and[len] = '\0';
    shift    = sll_n_bits (mm, and, len - 1 - i);
    add      = add_const (mm, result, shift);
    btor_delete_const (mm, result);
    btor_delete_const (mm, and);
    btor_delete_const (mm, shift);
    result = add;
  }
  return result;
}

char *
btor_mul_const (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));
  return mul_const (mm, a, b);
}

static char *
srl_n_bits (BtorMemMgr *mm, const char *a, int n)
{
  char *result;
  int len, i;

  assert (mm != NULL);
  assert (a != NULL);
  assert (is_valid_const_3vl (a));
  assert (n >= 0);
  assert (n < (int) strlen (a));

  len = (int) strlen (a);
  if (len == 0) return btor_strdup (mm, a);
  BTOR_NEWN (mm, result, len + 1);
  for (i = 0; i < n; i++) result[i] = '0';
  for (i = n; i < len; i++) result[i] = a[i - n];
  result[len] = '\0';
  return result;
}

static void
udiv_urem_const (BtorMemMgr *mm,
                 const char *a,
                 const char *b,
                 char **quotient,
                 char **remainder)
{
  char *b_i, *temp, *sub, *remainder_2n;
  int len, len_2n, i, gte;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (quotient != NULL);
  assert (remainder != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  len = (int) strlen (a);
  assert (len <= INT_MAX / 2);

  len_2n = len << 1;
  BTOR_NEWN (mm, *quotient, len + 1);
  (*quotient)[len] = '\0';
  BTOR_NEWN (mm, b_i, len_2n + 1);
  b_i[len_2n] = '\0';
  BTOR_NEWN (mm, remainder_2n, len_2n + 1);
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
  BTOR_NEWN (mm, *remainder, len + 1);
  (*remainder)[len] = '\0';
  for (i = len; i < len_2n; i++) (*remainder)[i - len] = remainder_2n[i];
  btor_delete_const (mm, remainder_2n);
}

char *
btor_udiv_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *quotient, *remainder;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  udiv_urem_const (mm, a, b, &quotient, &remainder);
  btor_delete_const (mm, remainder);
  return quotient;
}

char *
btor_urem_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *quotient, *remainder;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  udiv_urem_const (mm, a, b, &quotient, &remainder);
  btor_delete_const (mm, quotient);
  return remainder;
}

static char *
sll_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result, *temp;
  int i, len;
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 1);
  assert (btor_is_power_of_2_util ((int) strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  assert (is_valid_const_3vl (a));
  assert (is_valid_const (b));

  len = (int) strlen (b);
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
btor_sll_const (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 1);
  assert (btor_is_power_of_2_util ((int) strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  return sll_const (mm, a, b);
}

static char *
srl_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result, *temp;
  int i, len;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 1);
  assert (btor_is_power_of_2_util ((int) strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  assert (is_valid_const_3vl (a));
  assert (is_valid_const (b));

  len = (int) strlen (b);
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
btor_srl_const (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 1);
  assert (btor_is_power_of_2_util ((int) strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  return srl_const (mm, a, b);
}

char *
btor_ult_const (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  BTOR_NEWN (mm, result, 2);
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
  char *result;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 0);
  assert ((int) strlen (b) > 0);
  assert (is_valid_const (a));
  assert (is_valid_const (b));

  BTOR_NEWN (mm, result, (int) strlen (a) + (int) strlen (b) + 1);
  strcpy (result, a);
  strcat (result, b);
  return result;
}

char *
btor_udiv_unbounded_const (BtorMemMgr *mem,
                           const char *dividend,
                           const char *divisor,
                           char **rem_ptr)
{
  char *quotient, *rest, *extended_divisor, *tmp;
  int delta, plen, qlen;
  const char *p, *q;

  assert (mem != NULL);
  assert (dividend != NULL);
  assert (divisor != NULL);
  assert (is_valid_const (dividend));
  assert (is_valid_const (divisor));

  dividend = strip_zeroes (dividend);
  divisor  = strip_zeroes (divisor);

  for (p = dividend; *p && *p == '0'; p++)
    ;

  for (q = divisor; *q && *q == '0'; q++)
    ;

  assert (*q); /* in any case even if 'dividend == 0' */

  if (!*p || btor_cmp_const (p, q) < 0)
  {
    if (rem_ptr) *rem_ptr = btor_strdup (mem, p); /* copy divident */

    return btor_strdup (mem, "");
  }

  plen  = (int) strlen (p);
  qlen  = (int) strlen (q);
  delta = plen - qlen;
  assert (delta >= 0);

  BTOR_NEWN (mem, extended_divisor, plen + 1);
  memset (extended_divisor, '0', delta);
  strcpy (extended_divisor + delta, divisor);

  udiv_urem_const (mem, dividend, extended_divisor, &quotient, &rest);

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
  if (rem_ptr)
    *rem_ptr = rest;
  else
    btor_delete_const (mem, rest);

  return quotient;
}

char *
btor_uext_const (BtorMemMgr *mem, const char *c, int len)
{
  char *res, *q;
  const char *p;
  int rlen;

  assert (mem != NULL);
  assert (c != NULL);
  assert (len >= 1);
  assert (is_valid_const (c));

  rlen = (int) strlen (c) + len;

  BTOR_NEWN (mem, res, rlen + 1);

  for (q = res; len; len--, q++) *q = '0';

  for (p = c; *p; p++, q++) *q = *p;

  assert (res + rlen == q);
  *q = 0;

  return res;
}

char *
btor_inverse_const (BtorMemMgr *mm, const char *c)
{
  char *a, *b, *y, *ly, *r, *q, *yq, *res, *ty;
  int len = strlen (c);

  assert (mm != NULL);
  assert (c != NULL);
  assert (len > 0);
  assert (c[len - 1] == '1'); /* odd */
  assert (is_valid_const (c));

  BTOR_NEWN (mm, a, len + 2);
  a[0] = '1';
  memset (a + 1, '0', len);
  a[len + 1] = 0;

  BTOR_NEWN (mm, b, len + 2);
  b[0] = '0';
  memcpy (b + 1, c, len);
  b[len + 1] = 0;

  y  = btor_unsigned_to_const (mm, 1, len + 1);
  ly = btor_unsigned_to_const (mm, 0, len + 1);

  while (!btor_is_zero_const (b))
  {
    udiv_urem_const (mm, a, b, &q, &r);

    btor_delete_const (mm, a);

    a = b;
    b = r;

    ty = y;
    yq = btor_mul_const (mm, y, q);
    btor_delete_const (mm, q);

    y = btor_sub_const (mm, ly, yq);
    btor_delete_const (mm, yq);

    btor_delete_const (mm, ly);
    ly = ty;
  }

  res = btor_slice_const (mm, ly, len - 1, 0);

#ifndef NDEBUG
  assert (strlen (res) == strlen (c));
  ty = btor_mul_const (mm, c, res);
  assert (btor_is_one_const (ty));
  btor_delete_const (mm, ty);
#endif

  btor_delete_const (mm, ly);
  btor_delete_const (mm, y);
  btor_delete_const (mm, b);
  btor_delete_const (mm, a);

  return res;
}

char *
btor_const_to_hex (BtorMemMgr *mem, const char *c)
{
  int clen, rlen, i, j, tmp;
  char *res, ch;

  assert (mem != NULL);
  assert (c != NULL);
  assert (is_valid_const (c));

  clen = (int) strlen (c);
  rlen = (clen + 3) / 4;

  if (rlen)
  {
    BTOR_NEWN (mem, res, rlen + 1);

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
btor_const_to_decimal (BtorMemMgr *mem, const char *c)
{
  char *res, *q, *tmp, *rem, ch;
  BtorCharStack stack;
  const char *p;
  int len;
  BTOR_INIT_STACK (stack);

  assert (mem != NULL);
  assert (c != NULL);
  assert (is_valid_const (c));

  res = btor_copy_const (mem, c);
  while (*res)
  {
    tmp = btor_udiv_unbounded_const (mem, res, "1010", &rem); /* / 10 */
    assert ((int) strlen (rem) <= 4);
    ch = 0;
    for (p = strip_zeroes (rem); *p; p++)
    {
      ch <<= 1;
      if (*p == '1') ch++;
    }
    assert (ch < 10);
    ch += '0';
    BTOR_PUSH_STACK (mem, stack, ch);
    btor_delete_const (mem, rem);
    btor_delete_const (mem, res);
    res = tmp;
  }
  btor_delete_const (mem, res);

  if (BTOR_EMPTY_STACK (stack)) BTOR_PUSH_STACK (mem, stack, '0');

  len = BTOR_COUNT_STACK (stack);
  BTOR_NEWN (mem, res, len + 1);
  q = res;
  p = stack.top;
  while (p > stack.start) *q++ = *--p;
  assert (res + len == q);
  *q = 0;
  assert (len == (int) strlen (res));
  BTOR_RELEASE_STACK (mem, stack);
  return res;
}

char *
btor_x_const_3vl (BtorMemMgr *mm, int len)
{
  char *res;
  int i;

  assert (mm != NULL);
  assert (len > 0);

  BTOR_NEWN (mm, res, len + 1);
  for (i = 0; i < len; i++) res[i] = 'x';
  res[i] = '\0';

  return res;
}

void
btor_invert_const_3vl (BtorMemMgr *mm, char *a)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  invert_const (mm, a);
}

char *
btor_and_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));
  return and_const (mm, a, b);
}

char *
btor_eq_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));
  return eq_const (mm, a, b);
}

static void
ult_const_0_x_or_x_1_case (
    const char *a, const char *b, int len, int i, char *result)
{
  assert (a != NULL);
  assert (b != NULL);
  assert (len == (int) strlen (a));
  assert (i >= 0);
  assert (i < len);
  assert (result != NULL);
  assert ((int) strlen (result) == 1);
  assert ((a[i] == '0' && b[i] == 'x') || (a[i] == 'x' && b[i] == '1'));

  result[0] = 'x';

  for (i = i + 1; i < len; i++)
  {
    if (a[i] == '0' && b[i] == 'x') continue;

    if (a[i] == 'x' && b[i] == '1') continue;

    if (a[i] == '0' && b[i] == '1')
    {
      result[0] = '1';
      break;
    }

    if (a[i] == b[i] && a[i] != 'x' && b[i] != 'x')
      continue;
    else
      break;
  }
}

static void
ult_const_1_x_or_x_0_case (
    const char *a, const char *b, int len, int i, char *result)
{
  assert (a != NULL);
  assert (b != NULL);
  assert (len == (int) strlen (a));
  assert (i >= 0);
  assert (i < len);
  assert (result != NULL);
  assert ((int) strlen (result) == 1);
  assert ((a[i] == '1' && b[i] == 'x') || (a[i] == 'x' && b[i] == '0'));

  result[0] = '0';

  for (i = i + 1; i < len; i++)
  {
    if (a[i] == '0')
    {
      if (b[i] == '0')
        continue;
      else
      {
        result[0] = 'x';
        break;
      }
    }

    if (a[i] == '1')
    {
      if (b[i] == '0')
        break;
      else
        continue;
    }

    if (a[i] == 'x')
    {
      if (b[i] == '0')
        continue;
      else
      {
        result[0] = 'x';
        break;
      }
    }
  }
}

char *
btor_ult_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  char *result;
  int i, len;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  len = (int) strlen (a);
  BTOR_NEWN (mm, result, 2);
  result[0] = '0';
  result[1] = '\0';

  for (i = 0; i < len; i++)
  {
    if (a[i] == '0')
    {
      if (b[i] == 'x')
      {
        ult_const_0_x_or_x_1_case (a, b, len, i, result);
        break;
      }
      else if (b[i] == '1')
      {
        result[0] = '1';
        break;
      }
      else
        continue;
    }

    if (a[i] == '1')
    {
      if (b[i] == 'x')
      {
        ult_const_1_x_or_x_0_case (a, b, len, i, result);
        break;
      }
      else if (b[i] == '0')
      {
        result[0] = '0';
        break;
      }
      else
        continue;
    }

    if (a[i] == 'x')
    {
      if (b[i] == '1')
      {
        ult_const_0_x_or_x_1_case (a, b, len, i, result);
        break;
      }
      else if (b[i] == '0')
      {
        ult_const_1_x_or_x_0_case (a, b, len, i, result);
        break;
      }
      else
      {
        result[0] = 'x';
        break;
      }
    }

    assert (a[i] == b[i] && a[i] != 'x' && b[i] != 'x');
  }

  return result;
}

char *
btor_add_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));
  return add_const (mm, a, b);
}

static int
compute_min_shift (BtorMemMgr *mm, const char *b)
{
  int len, i, result;
  assert (mm != NULL);
  assert (b != NULL);

  len    = (int) strlen (b);
  result = 0;

  for (i = 0; i < len; i++)
  {
    if (b[i] == '1')
    {
      result += btor_pow_2_util (len - i - 1);
      assert (result > 0);
    }
  }
  return result;
}

char *
btor_sll_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  int min_shift;
  char *result, *temp;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 1);
  assert (btor_is_power_of_2_util ((int) strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  if (is_valid_const (b))
    result = sll_const (mm, a, b);
  else
  {
    temp      = btor_x_const_3vl (mm, (int) strlen (a));
    min_shift = compute_min_shift (mm, b);
    result    = sll_n_bits (mm, temp, min_shift);
    btor_delete_const (mm, temp);
  }
  return result;
}

char *
btor_srl_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  int min_shift;
  char *result, *temp;

  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert ((int) strlen (a) > 1);
  assert (btor_is_power_of_2_util ((int) strlen (a)));
  assert (btor_log_2_util ((int) strlen (a)) == (int) strlen (b));
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));

  if (is_valid_const (b))
    result = srl_const (mm, a, b);
  else
  {
    temp      = btor_x_const_3vl (mm, (int) strlen (a));
    min_shift = compute_min_shift (mm, b);
    result    = srl_n_bits (mm, temp, min_shift);
    btor_delete_const (mm, temp);
  }
  return result;
}

char *
btor_mul_const_3vl (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm != NULL);
  assert (a != NULL);
  assert (b != NULL);
  assert (strlen (a) == strlen (b));
  assert ((int) strlen (a) > 0);
  assert (is_valid_const_3vl (a));
  assert (is_valid_const_3vl (b));
  return mul_const (mm, a, b);
}
