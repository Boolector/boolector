/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2016 Armin Biere.
 *  Copyright (C) 2015-2016 Aina Niemetz.
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorutil.h"

#include <assert.h>
#include <limits.h>
#ifndef NDEBUG
#include <float.h>
#endif
#include <sys/time.h>
#include <time.h>

/*------------------------------------------------------------------------*/

bool
btor_is_power_of_2_util (uint32_t x)
{
  assert (x > 0);
  return (x & (x - 1)) == 0;
}

uint32_t
btor_log_2_util (uint32_t x)
{
  uint32_t result = 0;
  assert (x > 0);
  assert (btor_is_power_of_2_util (x));
  while (x > 1)
  {
    x >>= 1;
    result++;
  }
  return result;
}

int
btor_pow_2_util (int x)
{
  int result = 1;
  assert (x >= 0);
  while (x > 0)
  {
    assert (result <= INT_MAX / 2);
    result <<= 1;
    x--;
  }
  assert (result > 0);
  return result;
}

int
btor_next_power_of_2_util (int x)
{
  int i;
  assert (x > 0);
  x--;
  for (i = 1; i < (int) sizeof (int) * 8; i *= 2) x = x | (x >> i);
  return x + 1;
}

int
btor_num_digits_util (int x)
{
  int result;
  assert (x >= 0);

  result = 0;
  do
  {
    x /= 10;
    result++;
  } while (x > 0);
  return result;
}

/*------------------------------------------------------------------------*/

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
  assert (a);

  while (*a == '0') a++;

  return a;
}

#ifndef NDEBUG

static int
is_bin_str (const char *c)
{
  const char *p;
  char ch;

  assert (c != NULL);

  for (p = c; (ch = *p); p++)
    if (ch != '0' && ch != '1') return 0;
  return 1;
}

#endif

static char *
add_unbounded_bin_str (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (is_bin_str (a));
  assert (is_bin_str (b));

  char *res, *r, c, x, y, s, *tmp;
  int alen, blen, rlen;
  const char *p, *q;

  a = strip_zeroes (a);
  b = strip_zeroes (b);

  if (!*a) return btor_strdup (mm, b);

  if (!*b) return btor_strdup (mm, a);

  alen = strlen (a);
  blen = strlen (b);
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
    tmp = btor_strdup (mm, p);
    btor_freestr (mm, res);
    res = tmp;
  }

  return res;
}
static char *
mult_unbounded_bin_str (BtorMemMgr *mm, const char *a, const char *b)
{
  assert (mm);
  assert (a);
  assert (b);
  assert (is_bin_str (a));
  assert (is_bin_str (b));

  char *res, *r, c, x, y, s, m;
  int alen, blen, rlen, i;
  const char *p;

  a = strip_zeroes (a);

  if (!*a) return btor_strdup (mm, "");

  if (a[0] == '1' && !a[1]) return btor_strdup (mm, b);

  b = strip_zeroes (b);

  if (!*b) return btor_strdup (mm, "");

  if (b[0] == '1' && !b[1]) return btor_strdup (mm, a);

  alen = strlen (a);
  blen = strlen (b);
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

      while (res < r && b < p)
      {
        assert (b < p);
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

char *
btor_dec_to_bin_str_n_util (BtorMemMgr *mm, const char *str, uint32_t len)
{
  assert (mm);
  assert (str);

  const char *end, *p;
  char *res, *tmp;

  res = btor_strdup (mm, "");

  end = str + len;
  for (p = str; p < end; p++)
  {
    tmp = mult_unbounded_bin_str (mm, res, "1010"); /* *10 */
    btor_freestr (mm, res);
    res = tmp;

    tmp = add_unbounded_bin_str (mm, res, digit2const (*p));
    btor_freestr (mm, res);
    res = tmp;
  }

  assert (strip_zeroes (res) == res);

  return res;
}

char *
btor_dec_to_bin_str_util (BtorMemMgr *mm, const char *str)
{
  assert (mm);
  assert (str);

  return btor_dec_to_bin_str_n_util (mm, str, strlen (str));
}

char *
btor_hex_to_bin_str_n_util (BtorMemMgr *mm, const char *str, uint32_t len)
{
  assert (mm);
  assert (str);

  const char *p, *end;
  char *tmp, *res, *q;
  uint32_t blen;

  blen = 4 * len;
  BTOR_NEWN (mm, tmp, blen + 1);
  q = tmp;

  end = str + len;
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

  assert (tmp + blen == q);
  *q++ = 0;

  res = btor_strdup (mm, strip_zeroes (tmp));
  btor_freestr (mm, tmp);

  return res;
}

char *
btor_hex_to_bin_str_util (BtorMemMgr *mm, const char *str)
{
  assert (mm);
  assert (str);

  return btor_hex_to_bin_str_n_util (mm, str, strlen (str));
}

/*------------------------------------------------------------------------*/

#ifdef BTOR_HAVE_GETRUSAGE

#include <sys/resource.h>
#include <unistd.h>

double
btor_time_stamp (void)
{
  double res = 0;
  struct rusage u;
  if (!getrusage (RUSAGE_SELF, &u))
  {
    res += u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
    res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  }
  return res;
}
#endif

double
btor_process_time_thread (void)
{
  struct timespec ts;
  double res = 0;
  if (!clock_gettime (CLOCK_THREAD_CPUTIME_ID, &ts))
    res += (double) ts.tv_sec + (double) ts.tv_nsec / 1000000000;
  return res;
}

double
btor_current_time (void)
{
  double res = 0;
  struct timeval tv;
  if (!gettimeofday (&tv, 0))
  {
    res = 1e-6 * tv.tv_usec;
    res += tv.tv_sec;
  }
  return res;
}

/*------------------------------------------------------------------------*/

#define BTOR_HAVE_STAT

#ifdef BTOR_HAVE_STAT
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
int
btor_file_exists (const char *path)
{
  struct stat buf;
  return !stat (path, &buf);
}
#else
int
btor_file_exists (const char *path)
{
  (void) path;
  return -1;
}
#endif

/*------------------------------------------------------------------------*/
