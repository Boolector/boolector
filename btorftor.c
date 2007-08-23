#include "btorftor.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorstack.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>

typedef BtorExp *(*Parser) (BtorFtor *, int len);
typedef BtorExp *(*Unary) (BtorExpMgr *, BtorExp *);
typedef BtorExp *(*Binary) (BtorExpMgr *, BtorExp *, BtorExp *);
typedef BtorExp *(*Shift) (BtorExpMgr *, BtorExp *, BtorExp *);
typedef BtorExp *(*Extend) (BtorExpMgr *, BtorExp *, int);

#define SIZE_PARSERS 128

struct BtorFtor
{
  BtorMemMgr *mm;
  BtorExpMgr *btor;

  FILE *file;
  int lineno;
  int saved;
  const char *name;
  char *error;

  BtorExpPtrStack exps;
  BtorExpPtrStack roots;
  BtorExpPtrStack vars;
  BtorExpPtrStack arrays;
  BtorExpPtrStack regs;
  BtorExpPtrStack next;

  BtorCharStack op;
  BtorCharStack bits;
  BtorCharStack constant;
  BtorCharStack varname;

  Parser *parsers;
  const char **ops;

  int idx;

  int verbosity;
};

static unsigned primes[4] = {111130391, 22237357, 33355519, 444476887};

#define PRIMES ((sizeof primes) / sizeof primes[0])

static void
print_verbose_msg (char *msg)
{
  assert (msg != NULL);
  fprintf (stderr, "[btorftor] %s", msg);
  fflush (stderr);
}

static unsigned
hash_op (const char *str, unsigned salt)
{
  unsigned i, res;
  const char *p;

  assert (salt < PRIMES);

  res = 0;
  i   = salt;
  for (p = str; *p; p++)
  {
    res += primes[i++] * (unsigned) *p;
    if (i == PRIMES) i = 0;
  }

  res &= SIZE_PARSERS - 1;

  return res;
}

static const char *
parse_error (BtorFtor *ftor, const char *fmt, ...)
{
  const char *p;
  size_t bytes;
  va_list ap;
  char *tmp;

  if (!ftor->error)
  {
    bytes = strlen (ftor->name) + 20; /* care for ':: \0' and lineno */

    va_start (ap, fmt);
    for (p = fmt; *p; p++)
    {
      if (*p == '%')
      {
        p++;
        assert (*p);
        if (*p == 'd' || *p == 'u')
          bytes += 12;
        else
        {
          assert (*p == 's');
          bytes += strlen (va_arg (ap, const char *));
        }
      }
      else
        bytes++;
    }
    va_end (ap);

    tmp = btor_malloc (ftor->mm, bytes);
    sprintf (tmp, "%s:%d: ", ftor->name, ftor->lineno);
    assert (strlen (tmp) + 1 < bytes);
    va_start (ap, fmt);
    vsprintf (tmp + strlen (tmp), fmt, ap);
    va_end (ap);
    ftor->error = btor_strdup (ftor->mm, tmp);
    btor_free (ftor->mm, tmp, bytes);
  }

  return ftor->error;
}

static int
nextch (BtorFtor *ftor)
{
  int ch;

  if (ftor->saved)
  {
    ch          = ftor->saved;
    ftor->saved = 0;
  }
  else
    ch = getc (ftor->file);

  if (ch == '\n') ftor->lineno++;

  return ch;
}

static void
savech (BtorFtor *ftor, int ch)
{
  assert (ch);
  assert (!ftor->saved);

  ftor->saved = ch;

  if (ch == '\n')
  {
    assert (ftor->lineno > 1);
    ftor->lineno--;
  }
}

static const char *
parse_non_negative_int (BtorFtor *ftor, int *res_ptr)
{
  int res, ch;

  ch = nextch (ftor);
  if (!isdigit (ch)) return parse_error (ftor, "expected digit");

  if (ch == '0')
  {
    res = 0;
    ch  = nextch (ftor);
    if (isdigit (ch)) return parse_error (ftor, "digit after '0'");
  }
  else
  {
    res = ch - '0';

    while (isdigit (ch = nextch (ftor))) res = 10 * res + (ch - '0');
  }

  savech (ftor, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_positive_int (BtorFtor *ftor, int *res_ptr)
{
  int res, ch;

  ch = nextch (ftor);
  if (!isdigit (ch)) return parse_error (ftor, "expected digit");

  if (ch == '0') return parse_error (ftor, "expected non zero digit");

  res = ch - '0';

  while (isdigit (ch = nextch (ftor))) res = 10 * res + (ch - '0');

  savech (ftor, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_non_zero_int (BtorFtor *ftor, int *res_ptr)
{
  int res, sign, ch;

  ch = nextch (ftor);

  if (ch == '-')
  {
    sign = -1;
    ch   = nextch (ftor);

    if (!isdigit (ch) || ch == '0')
      return parse_error (ftor, "expected non zero digit after '-'");
  }
  else
  {
    sign = 1;
    if (!isdigit (ch) || ch == '0')
      return parse_error (ftor, "expected non zero digit or '-'");
  }

  res = ch - '0';

  while (isdigit (ch = nextch (ftor))) res = 10 * res + (ch - '0');

  savech (ftor, ch);

  res *= sign;
  *res_ptr = res;

  return 0;
}

static BtorExp *
parse_exp (BtorFtor *ftor, int expected_len)
{
  int lit, idx, len_res;
  BtorExp *res;

  lit = 0;
  if (parse_non_zero_int (ftor, &lit)) return 0;

  idx = abs (lit);

  if (!idx)
  {
    (void) parse_error (ftor, "invalid index '0'");
    return 0;
  }

  if (idx >= BTOR_COUNT_STACK (ftor->exps) || !(res = ftor->exps.start[idx]))
  {
    (void) parse_error (ftor, "literal '%d' undefined", lit);
    return 0;
  }

  if (expected_len)
  {
    len_res = btor_get_exp_len (ftor->btor, res);
    if (expected_len != len_res)
    {
      (void) parse_error (ftor,
                          "literal '%d' has length '%d' but expected '%d'",
                          lit,
                          len_res,
                          expected_len);
      return 0;
    }
  }

  if (lit < 0)
    res = btor_not_exp (ftor->btor, res);
  else
    res = btor_copy_exp (ftor->btor, res);

  return res;
}

static const char *
parse_space (BtorFtor *ftor)
{
  int ch;

  ch = nextch (ftor);
  if (ch != ' ' && ch != '\t')
    return parse_error (ftor, "expected space or tab");

SKIP:
  ch = nextch (ftor);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (!ch) return parse_error (ftor, "unexpected character");

  savech (ftor, ch);

  return 0;
}

static BtorExp *
parse_var (BtorFtor *ftor, int len)
{
  const char *name;
  char buffer[20];
  BtorExp *res;
  int ch;

  while ((ch = nextch (ftor)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  UNEXPECTED_EOF:
  {
    (void) parse_error (ftor, "unexpected EOF");
    return 0;
  }

    if (ch == '\n')
    {
      sprintf (buffer, "%d", ftor->idx);
      name = buffer;
    }
    else
    {
      assert (BTOR_EMPTY_STACK (ftor->varname));

      BTOR_PUSH_STACK (ftor->mm, ftor->varname, ch);

      while (!isspace (ch = nextch (ftor)))
      {
        if (ch == EOF) goto UNEXPECTED_EOF;

        BTOR_PUSH_STACK (ftor->mm, ftor->varname, ch);
      }

      BTOR_PUSH_STACK (ftor->mm, ftor->varname, 0);
      BTOR_RESET_STACK (ftor->varname);
      name = ftor->varname.start;
    }

  savech (ftor, ch);

  res = btor_var_exp (ftor->btor, len, name);
  BTOR_PUSH_STACK (ftor->mm, ftor->vars, res);

  return res;
}

static BtorExp *
parse_array (BtorFtor *ftor, int len)
{
  char buffer[20];
  BtorExp *res;
  int idx_len;

  if (parse_space (ftor)) return 0;

  if (parse_positive_int (ftor, &idx_len)) return 0;

  sprintf (buffer, "%d", ftor->idx);
  res = btor_array_exp (ftor->btor, len, idx_len);
  BTOR_PUSH_STACK (ftor->mm, ftor->arrays, res);

  return res;
}

static BtorExp *
parse_const (BtorFtor *ftor, int len)
{
  BtorExp *res;
  int ch, clen;

  if (parse_space (ftor)) return 0;

  assert (BTOR_EMPTY_STACK (ftor->bits));
  while (!isspace (ch = nextch (ftor)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) parse_error (ftor, "expected '0' or '1'");
      return 0;
    }

    BTOR_PUSH_STACK (ftor->mm, ftor->bits, ch);
  }

  savech (ftor, ch);
  clen = BTOR_COUNT_STACK (ftor->bits);
  BTOR_PUSH_STACK (ftor->mm, ftor->bits, 0);
  BTOR_RESET_STACK (ftor->bits);

  if (clen != len)
  {
    (void) parse_error (ftor,
                        "constant '%s' has %d bits but expected %d",
                        ftor->bits.start,
                        clen,
                        len);
    return 0;
  }

  res = btor_const_exp (ftor->btor, ftor->bits.start);

  return res;
}

static void
push_bit (BtorFtor *ftor, int bit)
{
  assert (bit == 0 || bit == 1);
  BTOR_PUSH_STACK (ftor->mm, ftor->constant, '0' + bit);
}

static void
push_four_bits (BtorFtor *ftor, int a, int b, int c, int d)
{
  push_bit (ftor, a);
  push_bit (ftor, b);
  push_bit (ftor, c);
  push_bit (ftor, d);
}

static BtorExp *
parse_consth (BtorFtor *ftor, int len)
{
  int ch, clen, skip;
  BtorExp *res;
  char *p;

  if (parse_space (ftor)) return 0;

  assert (BTOR_EMPTY_STACK (ftor->constant));
  while (!isspace (ch = nextch (ftor)) && ch != EOF && ch != ';')
  {
    switch (ch)
    {
      case '0': push_four_bits (ftor, 0, 0, 0, 0); break;
      case '1': push_four_bits (ftor, 0, 0, 0, 1); break;
      case '2': push_four_bits (ftor, 0, 0, 1, 0); break;
      case '3': push_four_bits (ftor, 0, 0, 1, 1); break;
      case '4': push_four_bits (ftor, 0, 1, 0, 0); break;
      case '5': push_four_bits (ftor, 0, 1, 0, 1); break;
      case '6': push_four_bits (ftor, 0, 1, 1, 0); break;
      case '7': push_four_bits (ftor, 0, 1, 1, 1); break;
      case '8': push_four_bits (ftor, 1, 0, 0, 0); break;
      case '9': push_four_bits (ftor, 1, 0, 0, 1); break;
      case 'A':
      case 'a': push_four_bits (ftor, 1, 0, 1, 0); break;
      case 'B':
      case 'b': push_four_bits (ftor, 1, 0, 1, 1); break;
      case 'C':
      case 'c': push_four_bits (ftor, 1, 1, 0, 0); break;
      case 'D':
      case 'd': push_four_bits (ftor, 1, 1, 0, 1); break;
      case 'E':
      case 'e': push_four_bits (ftor, 1, 1, 1, 0); break;
      case 'F':
      case 'f': push_four_bits (ftor, 1, 1, 1, 1); break;
      default:
        (void) parse_error (ftor, "expected hexidecimal digit");
        return 0;
    }
  }

  savech (ftor, ch);
  clen = BTOR_COUNT_STACK (ftor->constant);
  BTOR_PUSH_STACK (ftor->mm, ftor->constant, 0);
  BTOR_RESET_STACK (ftor->constant);

  if (clen >= len)
  {
    if (clen >= len + 4)
    {
    EXCEEDS_WIDTH:
      (void) parse_error (
          ftor, "constant '%s' exceeds width", ftor->constant.start);
      return 0;
    }

    for (skip = 0; clen > len; clen--, skip++)
      if (ftor->constant.start[skip] != '0') goto EXCEEDS_WIDTH;

    assert (skip <= 3);
    res = btor_const_exp (ftor->btor, ftor->constant.start + skip);
  }
  else
  {
    assert (BTOR_EMPTY_STACK (ftor->bits));

    while (clen++ < len) BTOR_PUSH_STACK (ftor->mm, ftor->bits, '0');

    for (p = ftor->constant.start; (ch = *p); p++)
      BTOR_PUSH_STACK (ftor->mm, ftor->bits, ch);

    BTOR_PUSH_STACK (ftor->mm, ftor->bits, 0);
    BTOR_RESET_STACK (ftor->bits);

    res = btor_const_exp (ftor->btor, ftor->bits.start);
  }

  assert (btor_get_exp_len (ftor->btor, res) == len);

  return res;
}

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

static BtorExp *
parse_constd (BtorFtor *ftor, int len)
{
  const char *p, *msb;
  char *c, ch, *tmp;
  BtorExp *res;
  int pad;

  if (parse_space (ftor)) return 0;

  ch = nextch (ftor);
  if (!isdigit (ch))
  {
    (void) parse_error (ftor, "expected digit");
    return 0;
  }

  if (ch == '0')
  {
    ch = nextch (ftor);

    if (isdigit (ch))
    {
      (void) parse_error (ftor, "digit after '0'");
      return 0;
    }

    c = btor_strdup (ftor->mm, "");
  }
  else
  {
    c = btor_strdup (ftor->mm, digit2const (ch));

    while (isdigit (ch = nextch (ftor)))
    {
      tmp = btor_mult_unbounded_const (ftor->mm, c, "1010"); /* *10 */
      btor_delete_const (ftor->mm, c);
      c = tmp;

      tmp = btor_add_unbounded_const (ftor->mm, c, digit2const (ch));
      btor_delete_const (ftor->mm, c);
      c = tmp;
    }
  }

  savech (ftor, ch);

  for (msb = c; *msb == '0'; msb++)
    ;

  pad = len - strlen (msb);
  if (pad < 0)
  {
    (void) parse_error (ftor, "constant exceeds bit width");
    btor_freestr (ftor->mm, c);
    return 0;
  }

  assert (BTOR_EMPTY_STACK (ftor->bits));

  while (pad--) BTOR_PUSH_STACK (ftor->mm, ftor->bits, '0');

  for (p = msb; *p; p++) BTOR_PUSH_STACK (ftor->mm, ftor->bits, *p);

  BTOR_PUSH_STACK (ftor->mm, ftor->bits, 0);
  BTOR_RESET_STACK (ftor->bits);

  btor_freestr (ftor->mm, c);

  assert (strlen (ftor->bits.start) == (size_t) len);
  res = btor_const_exp (ftor->btor, ftor->bits.start);

  return res;
}

static BtorExp *
parse_root (BtorFtor *ftor, int len)
{
  BtorExp *res;

  if (parse_space (ftor)) return 0;

  if (!(res = parse_exp (ftor, len))) return 0;

  BTOR_PUSH_STACK (ftor->mm, ftor->roots, res);

  return res;
}

static BtorExp *
parse_unary (BtorFtor *ftor, int len, Unary f)
{
  BtorExp *tmp, *res;

  assert (len);
  if (parse_space (ftor)) return 0;

  if (!(tmp = parse_exp (ftor, len))) return 0;

  res = f (ftor->btor, tmp);
  btor_release_exp (ftor->btor, tmp);
  assert (btor_get_exp_len (ftor->btor, res) == len);

  return res;
}

static BtorExp *
parse_not (BtorFtor *ftor, int len)
{
  return parse_unary (ftor, len, btor_not_exp);
}

static BtorExp *
parse_neg (BtorFtor *ftor, int len)
{
  return parse_unary (ftor, len, btor_neg_exp);
}

static BtorExp *
parse_redunary_and_nego (BtorFtor *ftor, int len, Unary f)
{
  BtorExp *tmp, *res;

  (void) len;
  assert (len == 1);

  if (parse_space (ftor)) return 0;

  if (!(tmp = parse_exp (ftor, 0))) return 0;

  res = f (ftor->btor, tmp);
  btor_release_exp (ftor->btor, tmp);
  assert (btor_get_exp_len (ftor->btor, res) == 1);

  return res;
}

static BtorExp *
parse_redand (BtorFtor *ftor, int len)
{
  return parse_redunary_and_nego (ftor, len, btor_redand_exp);
}

static BtorExp *
parse_redor (BtorFtor *ftor, int len)
{
  return parse_redunary_and_nego (ftor, len, btor_redor_exp);
}

static BtorExp *
parse_redxor (BtorFtor *ftor, int len)
{
  return parse_redunary_and_nego (ftor, len, btor_redxor_exp);
}

static BtorExp *
parse_nego (BtorFtor *ftor, int len)
{
  return parse_redunary_and_nego (ftor, len, btor_nego_exp);
}

static BtorExp *
parse_binary (BtorFtor *ftor, int len, Binary f)
{
  BtorExp *l, *r, *res;

  assert (len);

  if (parse_space (ftor)) return 0;

  if (!(l = parse_exp (ftor, len))) return 0;

  if (parse_space (ftor))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, l);
    return 0;
  }

  if (!(r = parse_exp (ftor, len))) goto RELEASE_L_AND_RETURN_ERROR;

  res = f (ftor->btor, l, r);
  btor_release_exp (ftor->btor, r);
  btor_release_exp (ftor->btor, l);
  assert (btor_get_exp_len (ftor->btor, res) == len);

  return res;
}

static BtorExp *
parse_add (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_add_exp);
}

static BtorExp *
parse_and (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_and_exp);
}

static BtorExp *
parse_smod (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_smod_exp);
}

static BtorExp *
parse_smul (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_smul_exp);
}

static BtorExp *
parse_sub (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_sub_exp);
}

static BtorExp *
parse_udiv (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_udiv_exp);
}

static BtorExp *
parse_umod (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_umod_exp);
}

static BtorExp *
parse_umul (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_umul_exp);
}

static BtorExp *
parse_xor (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_xor_exp);
}

static BtorExp *
parse_xnor (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_xnor_exp);
}

static BtorExp *
parse_or (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_or_exp);
}

static BtorExp *
parse_sdiv (BtorFtor *ftor, int len)
{
  return parse_binary (ftor, len, btor_sdiv_exp);
}

static BtorExp *
parse_compare_and_overflow (BtorFtor *ftor, int len, Binary f)
{
  BtorExp *l, *r, *res;
  int llen, rlen;

  if (len != 1)
  {
    (void) parse_error (ftor, "operator returns %d bits", len);
    return 0;
  }

  if (parse_space (ftor)) return 0;

  if (!(l = parse_exp (ftor, 0))) return 0;

  if (parse_space (ftor))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, l);
    return 0;
  }

  if (!(r = parse_exp (ftor, 0))) goto RELEASE_L_AND_RETURN_ERROR;

  llen = btor_get_exp_len (ftor->btor, l);
  rlen = btor_get_exp_len (ftor->btor, r);

  if (llen != rlen)
  {
    (void) parse_error (
        ftor, "operands have different bit width %d and %d", llen, rlen);

    btor_release_exp (ftor->btor, r);
    btor_release_exp (ftor->btor, l);
    return 0;
  }

  res = f (ftor->btor, l, r);
  btor_release_exp (ftor->btor, r);
  btor_release_exp (ftor->btor, l);
  assert (btor_get_exp_len (ftor->btor, res) == 1);

  return res;
}

static BtorExp *
parse_eq (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_eq_exp);
}

static BtorExp *
parse_ne (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_ne_exp);
}

static BtorExp *
parse_sgt (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_sgt_exp);
}

static BtorExp *
parse_sgte (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_sgte_exp);
}

static BtorExp *
parse_slt (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_slt_exp);
}

static BtorExp *
parse_slte (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_slte_exp);
}

static BtorExp *
parse_ugt (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_ugt_exp);
}

static BtorExp *
parse_ugte (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_ugte_exp);
}

static BtorExp *
parse_ult (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_ult_exp);
}

static BtorExp *
parse_ulte (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_ulte_exp);
}

static BtorExp *
parse_saddo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_saddo_exp);
}

static BtorExp *
parse_ssubo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_ssubo_exp);
}

static BtorExp *
parse_smulo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_smulo_exp);
}

static BtorExp *
parse_sdivo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_sdivo_exp);
}

static BtorExp *
parse_uaddo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_uaddo_exp);
}

static BtorExp *
parse_usubo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_usubo_exp);
}

static BtorExp *
parse_umulo (BtorFtor *ftor, int len)
{
  return parse_compare_and_overflow (ftor, len, btor_umulo_exp);
}

static BtorExp *
parse_concat (BtorFtor *ftor, int len)
{
  BtorExp *l, *r, *res;
  int llen, rlen;

  if (parse_space (ftor)) return 0;

  if (!(l = parse_exp (ftor, 0))) return 0;

  if (parse_space (ftor))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, l);
    return 0;
  }

  if (!(r = parse_exp (ftor, 0))) goto RELEASE_L_AND_RETURN_ERROR;

  llen = btor_get_exp_len (ftor->btor, l);
  rlen = btor_get_exp_len (ftor->btor, r);

  if (llen + rlen != len)
  {
    (void) parse_error (
        ftor, "operands widths %d and %d do not add up to %d", llen, rlen, len);

    btor_release_exp (ftor->btor, r);
    btor_release_exp (ftor->btor, l);
    return 0;
  }

  res = btor_concat_exp (ftor->btor, l, r);
  btor_release_exp (ftor->btor, r);
  btor_release_exp (ftor->btor, l);
  assert (btor_get_exp_len (ftor->btor, res) == len);

  return res;
}

static BtorExp *
parse_shift (BtorFtor *ftor, int len, Shift f)
{
  BtorExp *l, *r, *res;
  int rlen;

  for (rlen = 1; rlen <= 30 && len != (1 << rlen); rlen++)
    ;

  if (len != (1 << rlen))
  {
    (void) parse_error (ftor, "length %d is not a power of two", len);
    return 0;
  }

  if (parse_space (ftor)) return 0;

  if (!(l = parse_exp (ftor, len))) return 0;

  if (parse_space (ftor))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, l);
    return 0;
  }

  if (!(r = parse_exp (ftor, rlen))) goto RELEASE_L_AND_RETURN_ERROR;

  res = f (ftor->btor, l, r);
  btor_release_exp (ftor->btor, r);
  btor_release_exp (ftor->btor, l);
  assert (btor_get_exp_len (ftor->btor, res) == len);

  return res;
}

static BtorExp *
parse_rol (BtorFtor *ftor, int len)
{
  return parse_shift (ftor, len, btor_rol_exp);
}

static BtorExp *
parse_ror (BtorFtor *ftor, int len)
{
  return parse_shift (ftor, len, btor_ror_exp);
}

static BtorExp *
parse_sll (BtorFtor *ftor, int len)
{
  return parse_shift (ftor, len, btor_sll_exp);
}

static BtorExp *
parse_sra (BtorFtor *ftor, int len)
{
  return parse_shift (ftor, len, btor_sra_exp);
}

static BtorExp *
parse_srl (BtorFtor *ftor, int len)
{
  return parse_shift (ftor, len, btor_srl_exp);
}

static BtorExp *
parse_cond (BtorFtor *ftor, int len)
{
  BtorExp *c, *t, *e, *res;

  if (parse_space (ftor)) return 0;

  if (!(c = parse_exp (ftor, 1))) return 0;

  if (parse_space (ftor))
  {
  RELEASE_C_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, c);
    return 0;
  }

  if (!(t = parse_exp (ftor, len))) goto RELEASE_C_AND_RETURN_ERROR;

  if (parse_space (ftor))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp (ftor, len))) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  res = btor_cond_exp (ftor->btor, c, t, e);
  btor_release_exp (ftor->btor, e);
  btor_release_exp (ftor->btor, t);
  btor_release_exp (ftor->btor, c);

  return res;
}

static BtorExp *
parse_slice (BtorFtor *ftor, int len)
{
  int arglen, upper, lower, delta;
  BtorExp *res, *arg;

  if (parse_space (ftor)) return 0;

  if (!(arg = parse_exp (ftor, 0))) return 0;

  if (parse_space (ftor))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, arg);
    return 0;
  }

  arglen = btor_get_exp_len (ftor->btor, arg);

  if (parse_non_negative_int (ftor, &upper)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper > arglen)
  {
    (void) parse_error (
        ftor, "upper index '%d' exceeds argument width '%d", upper, arglen);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  if (parse_space (ftor)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (parse_non_negative_int (ftor, &lower)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper < lower)
  {
    (void) parse_error (
        ftor, "upper index '%d' smaller than lower index '%d'", upper, lower);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  delta = upper - lower + 1;
  if (delta != len)
  {
    (void) parse_error (
        ftor, "slice width '%d' not equal to expected width '%d'", delta, len);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = btor_slice_exp (ftor->btor, arg, upper, lower);
  btor_release_exp (ftor->btor, arg);

  return res;
}

static BtorExp *
parse_read (BtorFtor *ftor, int len)
{
  BtorExp *array, *idx, *res;
  int idxlen;

  if (parse_space (ftor)) return 0;

  if (!(array = parse_exp (ftor, len))) return 0;

  if (!btor_is_array_exp (ftor->btor, array))
  {
    (void) parse_error (ftor, "expected array as first argument");
  RELEASE_ARRAY_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, array);
    return 0;
  }

  if (parse_space (ftor)) goto RELEASE_ARRAY_AND_RETURN_ERROR;

  idxlen = btor_get_index_exp_len (ftor->btor, array);
  if (!(idx = parse_exp (ftor, idxlen))) goto RELEASE_ARRAY_AND_RETURN_ERROR;

  res = btor_read_exp (ftor->btor, array, idx);
  btor_release_exp (ftor->btor, idx);
  btor_release_exp (ftor->btor, array);

  return res;
}

static BtorExp *
parse_ext (BtorFtor *ftor, int len, Extend f)
{
  BtorExp *res, *arg;
  int alen, elen;

  if (parse_space (ftor)) return 0;

  if (!(arg = parse_exp (ftor, 0))) return 0;

  alen = btor_get_exp_len (ftor->btor, arg);

  if (parse_space (ftor))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    btor_release_exp (ftor->btor, arg);
    return 0;
  }

  if (parse_non_negative_int (ftor, &elen)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (alen + elen != len)
  {
    (void) parse_error (ftor,
                        "argument length of %d plus %d does not match %d",
                        alen,
                        elen,
                        len);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = f (ftor->btor, arg, elen);
  assert (btor_get_exp_len (ftor->btor, res) == len);
  btor_release_exp (ftor->btor, arg);

  return res;
}

static BtorExp *
parse_sext (BtorFtor *ftor, int len)
{
  return parse_ext (ftor, len, btor_sext_exp);
}

static BtorExp *
parse_uext (BtorFtor *ftor, int len)
{
  return parse_ext (ftor, len, btor_uext_exp);
}

#if 0
static BtorExp *
parse_not_implemented (BtorFtor * ftor, int len)
{
  (void) parse_error (ftor, "parser for '%s' not implemented", ftor->op.start);
  return 0;
}
#endif

static void
new_parser (BtorFtor *ftor, Parser parser, const char *op)
{
  unsigned p, d;

  p = hash_op (op, 0);
  assert (p < SIZE_PARSERS);

  if (ftor->ops[p])
  {
    d = hash_op (op, 1);
    if (!(d & 1)) d++;

    do
    {
      p += d;
      if (p >= SIZE_PARSERS) p -= SIZE_PARSERS;
      assert (p < SIZE_PARSERS);
    } while (ftor->ops[p]);
  }

  ftor->ops[p]     = op;
  ftor->parsers[p] = parser;
}

static Parser
find_parser (BtorFtor *ftor, const char *op)
{
  const char *str;
  unsigned p, d;

  p = hash_op (op, 0);
  if ((str = ftor->ops[p]) && strcasecmp (str, op))
  {
    d = hash_op (op, 1);
    if (!(d & 1)) d++;

    do
    {
      p += d;
      if (p >= SIZE_PARSERS) p -= SIZE_PARSERS;
    } while ((str = ftor->ops[p]) && strcasecmp (str, op));
  }

  return str ? ftor->parsers[p] : 0;
}

BtorFtor *
btor_new_ftor (BtorExpMgr *btor, int verbosity)
{
  BtorMemMgr *mm = btor_get_mem_mgr_exp_mgr (btor);
  BtorFtor *res;

  assert (verbosity >= 0);

  res = btor_malloc (mm, sizeof *res);
  memset (res, 0, sizeof *res);

  res->mm   = mm;
  res->btor = btor;

  BTOR_NEWN (mm, res->parsers, SIZE_PARSERS);
  BTOR_NEWN (mm, res->ops, SIZE_PARSERS);
  BTOR_CLRN (res->ops, SIZE_PARSERS);

  new_parser (res, parse_add, "add");
  new_parser (res, parse_and, "and");
  new_parser (res, parse_array, "array");
  new_parser (res, parse_concat, "concat");
  new_parser (res, parse_cond, "cond");
  new_parser (res, parse_const, "const");
  new_parser (res, parse_consth, "consth");
  new_parser (res, parse_constd, "constd");
  new_parser (res, parse_read, "read");
  new_parser (res, parse_eq, "eq");
  new_parser (res, parse_ne, "ne");
  new_parser (res, parse_neg, "neg");
  new_parser (res, parse_not, "not");
  new_parser (res, parse_or, "or");
  new_parser (res, parse_redand, "redand");
  new_parser (res, parse_redor, "redor");
  new_parser (res, parse_redxor, "redxor");
  new_parser (res, parse_rol, "rol");
  new_parser (res, parse_root, "root"); /* only in parser */
  new_parser (res, parse_ror, "ror");
  new_parser (res, parse_nego, "nego");
  new_parser (res, parse_saddo, "saddo");
  new_parser (res, parse_ssubo, "ssubo");
  new_parser (res, parse_sdiv, "sdiv");
  new_parser (res, parse_sdivo, "sdivo");
  new_parser (res, parse_sext, "sext");
  new_parser (res, parse_sgt, "sgt");
  new_parser (res, parse_sgte, "sgte");
  new_parser (res, parse_slice, "slice");
  new_parser (res, parse_sll, "sll");
  new_parser (res, parse_slt, "slt");
  new_parser (res, parse_slte, "slte");
  new_parser (res, parse_smod, "smod");
  new_parser (res, parse_smul, "smul");
  new_parser (res, parse_smulo, "smulo");
  new_parser (res, parse_sra, "sra");
  new_parser (res, parse_srl, "srl");
  new_parser (res, parse_sub, "sub");
  new_parser (res, parse_uaddo, "uaddo");
  new_parser (res, parse_usubo, "usubo");
  new_parser (res, parse_udiv, "udiv");
  new_parser (res, parse_uext, "uext");
  new_parser (res, parse_ugt, "ugt");
  new_parser (res, parse_ugte, "ugte");
  new_parser (res, parse_ult, "ult");
  new_parser (res, parse_ulte, "ulte");
  new_parser (res, parse_umod, "umod");
  new_parser (res, parse_umul, "umul");
  new_parser (res, parse_umulo, "umulo");
  new_parser (res, parse_var, "var");
  new_parser (res, parse_xor, "xor");
  new_parser (res, parse_xnor, "xnor");

  res->verbosity = verbosity;

  return res;
}

void
btor_delete_ftor (BtorFtor *ftor)
{
  BtorExp *e;
  int i;

  for (i = 0; i < BTOR_COUNT_STACK (ftor->exps); i++)
    if ((e = ftor->exps.start[i]))
      btor_release_exp (ftor->btor, ftor->exps.start[i]);

  BTOR_RELEASE_STACK (ftor->mm, ftor->exps);
  BTOR_RELEASE_STACK (ftor->mm, ftor->vars);
  BTOR_RELEASE_STACK (ftor->mm, ftor->arrays);
  BTOR_RELEASE_STACK (ftor->mm, ftor->roots);

  BTOR_RELEASE_STACK (ftor->mm, ftor->op);
  BTOR_RELEASE_STACK (ftor->mm, ftor->bits);
  BTOR_RELEASE_STACK (ftor->mm, ftor->constant);
  BTOR_RELEASE_STACK (ftor->mm, ftor->varname);

  BTOR_DELETEN (ftor->mm, ftor->parsers, SIZE_PARSERS);
  BTOR_DELETEN (ftor->mm, ftor->ops, SIZE_PARSERS);

  btor_freestr (ftor->mm, ftor->error);

  btor_free (ftor->mm, ftor, sizeof *ftor);
}

const char *
btor_parse_ftor (BtorFtor *ftor,
                 FILE *file,
                 const char *name,
                 BtorFtorResult *res)
{
  Parser parser;
  int ch, len;
  BtorExp *e;

  assert (name);
  assert (file);

  if (ftor->verbosity > 0) print_verbose_msg ("parsing input\n");

  ftor->file   = file;
  ftor->name   = name;
  ftor->lineno = 1;

  memset (res, 0, sizeof *res);

NEXT:
  assert (!ftor->error);
  ch = nextch (ftor);
  if (isspace (ch)) /* also skip empty lines */
    goto NEXT;

  if (ch == EOF)
  {
  DONE:
    if (res)
    {
      res->vars  = ftor->vars.start;
      res->nvars = BTOR_COUNT_STACK (ftor->vars);

      res->arrays  = ftor->arrays.start;
      res->narrays = BTOR_COUNT_STACK (ftor->arrays);

      res->roots  = ftor->roots.start;
      res->nroots = BTOR_COUNT_STACK (ftor->roots);
    }

    return 0;
  }

  if (ch == ';') /* skip comments */
  {
  COMMENTS:
    while ((ch = nextch (ftor)) != '\n')
      if (ch == EOF) goto DONE;

    goto NEXT;
  }

  if (!isdigit (ch)) return parse_error (ftor, "expected ';' or digit");

  savech (ftor, ch);

  if (parse_positive_int (ftor, &ftor->idx)) return ftor->error;

  while (BTOR_COUNT_STACK (ftor->exps) <= ftor->idx)
    BTOR_PUSH_STACK (ftor->mm, ftor->exps, 0);

  if (ftor->exps.start[ftor->idx])
    return parse_error (ftor, "'%d' defined twice", ftor->idx);

  if (parse_space (ftor)) return ftor->error;

  assert (BTOR_EMPTY_STACK (ftor->op));
  while (!isspace (ch = nextch (ftor)) && ch != EOF)
    BTOR_PUSH_STACK (ftor->mm, ftor->op, ch);

  BTOR_PUSH_STACK (ftor->mm, ftor->op, 0);
  BTOR_RESET_STACK (ftor->op);
  savech (ftor, ch);

  if (parse_space (ftor)) return ftor->error;

  if (parse_positive_int (ftor, &len)) return ftor->error;

  if (!(parser = find_parser (ftor, ftor->op.start)))
    return parse_error (ftor, "invalid operator '%s'", ftor->op);

  if (!(e = parser (ftor, len)))
  {
    assert (ftor->error);
    return ftor->error;
  }

  assert (btor_get_exp_len (ftor->btor, e) == len);
  ftor->exps.start[ftor->idx] = e;

SKIP:
  ch = nextch (ftor);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (ch == ';') goto COMMENTS; /* ... and force new line */

  if (ch != '\n') return parse_error (ftor, "expected new line");

  goto NEXT;
}
