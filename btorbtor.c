#include "btorbtor.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorparse.h"
#include "btorstack.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>

typedef struct BtorBTORParser BtorBTORParser;

typedef BtorExp *(*BtorOpParser) (BtorBTORParser *, int len);
typedef BtorExp *(*Unary) (BtorExpMgr *, BtorExp *);
typedef BtorExp *(*Binary) (BtorExpMgr *, BtorExp *, BtorExp *);
typedef BtorExp *(*Shift) (BtorExpMgr *, BtorExp *, BtorExp *);
typedef BtorExp *(*Extend) (BtorExpMgr *, BtorExp *, int);

#define SIZE_PARSERS 128

struct BtorBTORParser
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
  BtorExpPtrStack regs;
  BtorExpPtrStack next;

  BtorCharStack op;
  BtorCharStack bits;
  BtorCharStack constant;
  BtorCharStack varname;

  BtorOpParser *parsers;
  const char **ops;

  int idx;

  int verbosity;
};

static unsigned primes[4] = {111130391, 22237357, 33355519, 444476887};

#define PRIMES ((sizeof primes) / sizeof primes[0])

static void
print_verbose_msg (char *fmt, ...)
{
  va_list ap;
  fprintf (stderr, "[btorbtor] ");
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
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
parse_error (BtorBTORParser *parser, const char *fmt, ...)
{
  const char *p;
  size_t bytes;
  va_list ap;
  char *tmp;

  if (!parser->error)
  {
    bytes = strlen (parser->name) + 20; /* care for ':: \0' and lineno */

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

    tmp = btor_malloc (parser->mm, bytes);
    sprintf (tmp, "%s:%d: ", parser->name, parser->lineno);
    assert (strlen (tmp) + 1 < bytes);
    va_start (ap, fmt);
    vsprintf (tmp + strlen (tmp), fmt, ap);
    va_end (ap);
    parser->error = btor_strdup (parser->mm, tmp);
    btor_free (parser->mm, tmp, bytes);
  }

  return parser->error;
}

static int
nextch (BtorBTORParser *parser)
{
  int ch;

  if (parser->saved)
  {
    ch            = parser->saved;
    parser->saved = 0;
  }
  else
    ch = getc (parser->file);

  if (ch == '\n') parser->lineno++;

  return ch;
}

static void
savech (BtorBTORParser *parser, int ch)
{
  assert (ch);
  assert (!parser->saved);

  parser->saved = ch;

  if (ch == '\n')
  {
    assert (parser->lineno > 1);
    parser->lineno--;
  }
}

static const char *
parse_non_negative_int (BtorBTORParser *parser, int *res_ptr)
{
  int res, ch;

  ch = nextch (parser);
  if (!isdigit (ch)) return parse_error (parser, "expected digit");

  if (ch == '0')
  {
    res = 0;
    ch  = nextch (parser);
    if (isdigit (ch)) return parse_error (parser, "digit after '0'");
  }
  else
  {
    res = ch - '0';

    while (isdigit (ch = nextch (parser))) res = 10 * res + (ch - '0');
  }

  savech (parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_positive_int (BtorBTORParser *parser, int *res_ptr)
{
  int res, ch;

  ch = nextch (parser);
  if (!isdigit (ch)) return parse_error (parser, "expected digit");

  if (ch == '0') return parse_error (parser, "expected non zero digit");

  res = ch - '0';

  while (isdigit (ch = nextch (parser))) res = 10 * res + (ch - '0');

  savech (parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_non_zero_int (BtorBTORParser *parser, int *res_ptr)
{
  int res, sign, ch;

  ch = nextch (parser);

  if (ch == '-')
  {
    sign = -1;
    ch   = nextch (parser);

    if (!isdigit (ch) || ch == '0')
      return parse_error (parser, "expected non zero digit after '-'");
  }
  else
  {
    sign = 1;
    if (!isdigit (ch) || ch == '0')
      return parse_error (parser, "expected non zero digit or '-'");
  }

  res = ch - '0';

  while (isdigit (ch = nextch (parser))) res = 10 * res + (ch - '0');

  savech (parser, ch);

  res *= sign;
  *res_ptr = res;

  return 0;
}

static BtorExp *
parse_exp (BtorBTORParser *parser, int expected_len)
{
  int lit, idx, len_res;
  BtorExp *res;

  lit = 0;
  if (parse_non_zero_int (parser, &lit)) return 0;

  idx = abs (lit);

  if (!idx)
  {
    (void) parse_error (parser, "invalid index '0'");
    return 0;
  }

  if (idx >= BTOR_COUNT_STACK (parser->exps)
      || !(res = parser->exps.start[idx]))
  {
    (void) parse_error (parser, "literal '%d' undefined", lit);
    return 0;
  }

  if (expected_len)
  {
    len_res = btor_get_exp_len (parser->btor, res);
    if (expected_len != len_res)
    {
      (void) parse_error (parser,
                          "literal '%d' has length '%d' but expected '%d'",
                          lit,
                          len_res,
                          expected_len);
      return 0;
    }
  }

  if (lit < 0)
    res = btor_not_exp (parser->btor, res);
  else
    res = btor_copy_exp (parser->btor, res);

  return res;
}

static const char *
parse_space (BtorBTORParser *parser)
{
  int ch;

  ch = nextch (parser);
  if (ch != ' ' && ch != '\t')
    return parse_error (parser, "expected space or tab");

SKIP:
  ch = nextch (parser);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (!ch) return parse_error (parser, "unexpected character");

  savech (parser, ch);

  return 0;
}

static BtorExp *
parse_var (BtorBTORParser *parser, int len)
{
  const char *name;
  char buffer[20];
  BtorExp *res;
  int ch;

  while ((ch = nextch (parser)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  UNEXPECTED_EOF:
  {
    (void) parse_error (parser, "unexpected EOF");
    return 0;
  }

    if (ch == '\n')
    {
      sprintf (buffer, "%d", parser->idx);
      name = buffer;
    }
    else
    {
      assert (BTOR_EMPTY_STACK (parser->varname));

      BTOR_PUSH_STACK (parser->mm, parser->varname, ch);

      while (!isspace (ch = nextch (parser)))
      {
        if (ch == EOF) goto UNEXPECTED_EOF;

        BTOR_PUSH_STACK (parser->mm, parser->varname, ch);
      }

      BTOR_PUSH_STACK (parser->mm, parser->varname, 0);
      BTOR_RESET_STACK (parser->varname);
      name = parser->varname.start;
    }

  savech (parser, ch);

  res = btor_var_exp (parser->btor, len, name);
  BTOR_PUSH_STACK (parser->mm, parser->vars, res);

  return res;
}

static BtorExp *
parse_array (BtorBTORParser *parser, int len)
{
  char buffer[20];
  BtorExp *res;
  int idx_len;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx_len)) return 0;

  sprintf (buffer, "%d", parser->idx);
  res = btor_array_exp (parser->btor, len, idx_len);

  return res;
}

static BtorExp *
parse_const (BtorBTORParser *parser, int len)
{
  BtorExp *res;
  int ch, clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->bits));
  while (!isspace (ch = nextch (parser)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) parse_error (parser, "expected '0' or '1'");
      return 0;
    }

    BTOR_PUSH_STACK (parser->mm, parser->bits, ch);
  }

  savech (parser, ch);
  clen = BTOR_COUNT_STACK (parser->bits);
  BTOR_PUSH_STACK (parser->mm, parser->bits, 0);
  BTOR_RESET_STACK (parser->bits);

  if (clen != len)
  {
    (void) parse_error (parser,
                        "constant '%s' has %d bits but expected %d",
                        parser->bits.start,
                        clen,
                        len);
    return 0;
  }

  res = btor_const_exp (parser->btor, parser->bits.start);

  return res;
}

static void
push_bit (BtorBTORParser *parser, int bit)
{
  assert (bit == 0 || bit == 1);
  BTOR_PUSH_STACK (parser->mm, parser->constant, '0' + bit);
}

static void
push_four_bits (BtorBTORParser *parser, int a, int b, int c, int d)
{
  push_bit (parser, a);
  push_bit (parser, b);
  push_bit (parser, c);
  push_bit (parser, d);
}

static BtorExp *
parse_consth (BtorBTORParser *parser, int len)
{
  int ch, clen, skip;
  BtorExp *res;
  char *p;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));
  while (!isspace (ch = nextch (parser)) && ch != EOF && ch != ';')
  {
    switch (ch)
    {
      case '0': push_four_bits (parser, 0, 0, 0, 0); break;
      case '1': push_four_bits (parser, 0, 0, 0, 1); break;
      case '2': push_four_bits (parser, 0, 0, 1, 0); break;
      case '3': push_four_bits (parser, 0, 0, 1, 1); break;
      case '4': push_four_bits (parser, 0, 1, 0, 0); break;
      case '5': push_four_bits (parser, 0, 1, 0, 1); break;
      case '6': push_four_bits (parser, 0, 1, 1, 0); break;
      case '7': push_four_bits (parser, 0, 1, 1, 1); break;
      case '8': push_four_bits (parser, 1, 0, 0, 0); break;
      case '9': push_four_bits (parser, 1, 0, 0, 1); break;
      case 'A':
      case 'a': push_four_bits (parser, 1, 0, 1, 0); break;
      case 'B':
      case 'b': push_four_bits (parser, 1, 0, 1, 1); break;
      case 'C':
      case 'c': push_four_bits (parser, 1, 1, 0, 0); break;
      case 'D':
      case 'd': push_four_bits (parser, 1, 1, 0, 1); break;
      case 'E':
      case 'e': push_four_bits (parser, 1, 1, 1, 0); break;
      case 'F':
      case 'f': push_four_bits (parser, 1, 1, 1, 1); break;
      default:
        (void) parse_error (parser, "expected hexidecimal digit");
        return 0;
    }
  }

  savech (parser, ch);
  clen = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->mm, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  if (clen >= len)
  {
    if (clen >= len + 4)
    {
    EXCEEDS_WIDTH:
      (void) parse_error (
          parser, "constant '%s' exceeds width", parser->constant.start);
      return 0;
    }

    for (skip = 0; clen > len; clen--, skip++)
      if (parser->constant.start[skip] != '0') goto EXCEEDS_WIDTH;

    assert (skip <= 3);
    res = btor_const_exp (parser->btor, parser->constant.start + skip);
  }
  else
  {
    assert (BTOR_EMPTY_STACK (parser->bits));

    while (clen++ < len) BTOR_PUSH_STACK (parser->mm, parser->bits, '0');

    for (p = parser->constant.start; (ch = *p); p++)
      BTOR_PUSH_STACK (parser->mm, parser->bits, ch);

    BTOR_PUSH_STACK (parser->mm, parser->bits, 0);
    BTOR_RESET_STACK (parser->bits);

    res = btor_const_exp (parser->btor, parser->bits.start);
  }

  assert (btor_get_exp_len (parser->btor, res) == len);

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
parse_constd (BtorBTORParser *parser, int len)
{
  const char *p, *msb;
  char *c, ch, *tmp;
  BtorExp *res;
  int pad;

  if (parse_space (parser)) return 0;

  ch = nextch (parser);
  if (!isdigit (ch))
  {
    (void) parse_error (parser, "expected digit");
    return 0;
  }

  if (ch == '0')
  {
    ch = nextch (parser);

    if (isdigit (ch))
    {
      (void) parse_error (parser, "digit after '0'");
      return 0;
    }

    c = btor_strdup (parser->mm, "");
  }
  else
  {
    c = btor_strdup (parser->mm, digit2const (ch));

    while (isdigit (ch = nextch (parser)))
    {
      tmp = btor_mult_unbounded_const (parser->mm, c, "1010"); /* *10 */
      btor_delete_const (parser->mm, c);
      c = tmp;

      tmp = btor_add_unbounded_const (parser->mm, c, digit2const (ch));
      btor_delete_const (parser->mm, c);
      c = tmp;
    }
  }

  savech (parser, ch);

  for (msb = c; *msb == '0'; msb++)
    ;

  pad = len - strlen (msb);
  if (pad < 0)
  {
    (void) parse_error (parser, "constant exceeds bit width");
    btor_freestr (parser->mm, c);
    return 0;
  }

  assert (BTOR_EMPTY_STACK (parser->bits));

  while (pad--) BTOR_PUSH_STACK (parser->mm, parser->bits, '0');

  for (p = msb; *p; p++) BTOR_PUSH_STACK (parser->mm, parser->bits, *p);

  BTOR_PUSH_STACK (parser->mm, parser->bits, 0);
  BTOR_RESET_STACK (parser->bits);

  btor_freestr (parser->mm, c);

  assert (strlen (parser->bits.start) == (size_t) len);
  res = btor_const_exp (parser->btor, parser->bits.start);

  return res;
}

static BtorExp *
parse_root (BtorBTORParser *parser, int len)
{
  BtorExp *res;

  if (parse_space (parser)) return 0;

  if (!(res = parse_exp (parser, len))) return 0;

  BTOR_PUSH_STACK (parser->mm, parser->roots, res);

  return res;
}

static BtorExp *
parse_unary (BtorBTORParser *parser, int len, Unary f)
{
  BtorExp *tmp, *res;

  assert (len);
  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, len))) return 0;

  res = f (parser->btor, tmp);
  btor_release_exp (parser->btor, tmp);
  assert (btor_get_exp_len (parser->btor, res) == len);

  return res;
}

static BtorExp *
parse_not (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, btor_not_exp);
}

static BtorExp *
parse_neg (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, btor_neg_exp);
}

static BtorExp *
parse_redunary_and_nego (BtorBTORParser *parser, int len, Unary f)
{
  BtorExp *tmp, *res;

  (void) len;
  assert (len == 1);

  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, 0))) return 0;

  res = f (parser->btor, tmp);
  btor_release_exp (parser->btor, tmp);
  assert (btor_get_exp_len (parser->btor, res) == 1);

  return res;
}

static BtorExp *
parse_redand (BtorBTORParser *parser, int len)
{
  return parse_redunary_and_nego (parser, len, btor_redand_exp);
}

static BtorExp *
parse_redor (BtorBTORParser *parser, int len)
{
  return parse_redunary_and_nego (parser, len, btor_redor_exp);
}

static BtorExp *
parse_redxor (BtorBTORParser *parser, int len)
{
  return parse_redunary_and_nego (parser, len, btor_redxor_exp);
}

static BtorExp *
parse_nego (BtorBTORParser *parser, int len)
{
  return parse_redunary_and_nego (parser, len, btor_nego_exp);
}

static BtorExp *
parse_binary (BtorBTORParser *parser, int len, Binary f)
{
  BtorExp *l, *r, *res;

  assert (len);

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, len))) goto RELEASE_L_AND_RETURN_ERROR;

  res = f (parser->btor, l, r);
  btor_release_exp (parser->btor, r);
  btor_release_exp (parser->btor, l);
  assert (btor_get_exp_len (parser->btor, res) == len);

  return res;
}

static BtorExp *
parse_add (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_add_exp);
}

static BtorExp *
parse_and (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_and_exp);
}

static BtorExp *
parse_smod (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_smod_exp);
}

static BtorExp *
parse_smul (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_smul_exp);
}

static BtorExp *
parse_sub (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_sub_exp);
}

static BtorExp *
parse_udiv (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_udiv_exp);
}

static BtorExp *
parse_umod (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_umod_exp);
}

static BtorExp *
parse_umul (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_umul_exp);
}

static BtorExp *
parse_xor (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_xor_exp);
}

static BtorExp *
parse_xnor (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_xnor_exp);
}

static BtorExp *
parse_or (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_or_exp);
}

static BtorExp *
parse_sdiv (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_sdiv_exp);
}

static BtorExp *
parse_compare_and_overflow (BtorBTORParser *parser, int len, Binary f)
{
  BtorExp *l, *r, *res;
  int llen, rlen;

  if (len != 1)
  {
    (void) parse_error (parser, "operator returns %d bits", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0))) goto RELEASE_L_AND_RETURN_ERROR;

  llen = btor_get_exp_len (parser->btor, l);
  rlen = btor_get_exp_len (parser->btor, r);

  if (llen != rlen)
  {
    (void) parse_error (
        parser, "operands have different bit width %d and %d", llen, rlen);

    btor_release_exp (parser->btor, r);
    btor_release_exp (parser->btor, l);
    return 0;
  }

  res = f (parser->btor, l, r);
  btor_release_exp (parser->btor, r);
  btor_release_exp (parser->btor, l);
  assert (btor_get_exp_len (parser->btor, res) == 1);

  return res;
}

static BtorExp *
parse_eq (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_eq_exp);
}

static BtorExp *
parse_ne (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ne_exp);
}

static BtorExp *
parse_sgt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_sgt_exp);
}

static BtorExp *
parse_sgte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_sgte_exp);
}

static BtorExp *
parse_slt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_slt_exp);
}

static BtorExp *
parse_slte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_slte_exp);
}

static BtorExp *
parse_ugt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ugt_exp);
}

static BtorExp *
parse_ugte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ugte_exp);
}

static BtorExp *
parse_ult (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ult_exp);
}

static BtorExp *
parse_ulte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ulte_exp);
}

static BtorExp *
parse_saddo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_saddo_exp);
}

static BtorExp *
parse_ssubo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ssubo_exp);
}

static BtorExp *
parse_smulo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_smulo_exp);
}

static BtorExp *
parse_sdivo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_sdivo_exp);
}

static BtorExp *
parse_uaddo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_uaddo_exp);
}

static BtorExp *
parse_usubo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_usubo_exp);
}

static BtorExp *
parse_umulo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_umulo_exp);
}

static BtorExp *
parse_concat (BtorBTORParser *parser, int len)
{
  BtorExp *l, *r, *res;
  int llen, rlen;

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0))) goto RELEASE_L_AND_RETURN_ERROR;

  llen = btor_get_exp_len (parser->btor, l);
  rlen = btor_get_exp_len (parser->btor, r);

  if (llen + rlen != len)
  {
    (void) parse_error (parser,
                        "operands widths %d and %d do not add up to %d",
                        llen,
                        rlen,
                        len);

    btor_release_exp (parser->btor, r);
    btor_release_exp (parser->btor, l);
    return 0;
  }

  res = btor_concat_exp (parser->btor, l, r);
  btor_release_exp (parser->btor, r);
  btor_release_exp (parser->btor, l);
  assert (btor_get_exp_len (parser->btor, res) == len);

  return res;
}

static BtorExp *
parse_shift (BtorBTORParser *parser, int len, Shift f)
{
  BtorExp *l, *r, *res;
  int rlen;

  for (rlen = 1; rlen <= 30 && len != (1 << rlen); rlen++)
    ;

  if (len != (1 << rlen))
  {
    (void) parse_error (parser, "length %d is not a power of two", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, rlen))) goto RELEASE_L_AND_RETURN_ERROR;

  res = f (parser->btor, l, r);
  btor_release_exp (parser->btor, r);
  btor_release_exp (parser->btor, l);
  assert (btor_get_exp_len (parser->btor, res) == len);

  return res;
}

static BtorExp *
parse_rol (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, btor_rol_exp);
}

static BtorExp *
parse_ror (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, btor_ror_exp);
}

static BtorExp *
parse_sll (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, btor_sll_exp);
}

static BtorExp *
parse_sra (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, btor_sra_exp);
}

static BtorExp *
parse_srl (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, btor_srl_exp);
}

static BtorExp *
parse_cond (BtorBTORParser *parser, int len)
{
  BtorExp *c, *t, *e, *res;

  if (parse_space (parser)) return 0;

  if (!(c = parse_exp (parser, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, c);
    return 0;
  }

  if (!(t = parse_exp (parser, len))) goto RELEASE_C_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp (parser, len))) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  res = btor_cond_exp (parser->btor, c, t, e);
  btor_release_exp (parser->btor, e);
  btor_release_exp (parser->btor, t);
  btor_release_exp (parser->btor, c);

  return res;
}

static BtorExp *
parse_slice (BtorBTORParser *parser, int len)
{
  int arglen, upper, lower, delta;
  BtorExp *res, *arg;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, arg);
    return 0;
  }

  arglen = btor_get_exp_len (parser->btor, arg);

  if (parse_non_negative_int (parser, &upper))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper > arglen)
  {
    (void) parse_error (
        parser, "upper index '%d' exceeds argument width '%d", upper, arglen);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  if (parse_space (parser)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (parse_non_negative_int (parser, &lower))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper < lower)
  {
    (void) parse_error (
        parser, "upper index '%d' smaller than lower index '%d'", upper, lower);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  delta = upper - lower + 1;
  if (delta != len)
  {
    (void) parse_error (parser,
                        "slice width '%d' not equal to expected width '%d'",
                        delta,
                        len);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = btor_slice_exp (parser->btor, arg, upper, lower);
  btor_release_exp (parser->btor, arg);

  return res;
}

static BtorExp *
parse_read (BtorBTORParser *parser, int len)
{
  BtorExp *array, *idx, *res;
  int idxlen;

  if (parse_space (parser)) return 0;

  if (!(array = parse_exp (parser, len))) return 0;

  if (!btor_is_array_exp (parser->btor, array))
  {
    (void) parse_error (parser, "expected array as first argument");
  RELEASE_ARRAY_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, array);
    return 0;
  }

  if (parse_space (parser)) goto RELEASE_ARRAY_AND_RETURN_ERROR;

  idxlen = btor_get_index_exp_len (parser->btor, array);
  if (!(idx = parse_exp (parser, idxlen))) goto RELEASE_ARRAY_AND_RETURN_ERROR;

  res = btor_read_exp (parser->btor, array, idx);
  btor_release_exp (parser->btor, idx);
  btor_release_exp (parser->btor, array);

  return res;
}

static BtorExp *
parse_ext (BtorBTORParser *parser, int len, Extend f)
{
  BtorExp *res, *arg;
  int alen, elen;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0))) return 0;

  alen = btor_get_exp_len (parser->btor, arg);

  if (parse_space (parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, arg);
    return 0;
  }

  if (parse_non_negative_int (parser, &elen)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (alen + elen != len)
  {
    (void) parse_error (parser,
                        "argument length of %d plus %d does not match %d",
                        alen,
                        elen,
                        len);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = f (parser->btor, arg, elen);
  assert (btor_get_exp_len (parser->btor, res) == len);
  btor_release_exp (parser->btor, arg);

  return res;
}

static BtorExp *
parse_sext (BtorBTORParser *parser, int len)
{
  return parse_ext (parser, len, btor_sext_exp);
}

static BtorExp *
parse_uext (BtorBTORParser *parser, int len)
{
  return parse_ext (parser, len, btor_uext_exp);
}

#if 0
static BtorExp *
parse_not_implemented (BtorBTORParser * parser, int len)
{
  (void) parse_error (parser, "parser for '%s' not implemented", parser->op.start);
  return 0;
}
#endif

static void
new_parser (BtorBTORParser *parser, BtorOpParser op_parser, const char *op)
{
  unsigned p, d;

  p = hash_op (op, 0);
  assert (p < SIZE_PARSERS);

  if (parser->ops[p])
  {
    d = hash_op (op, 1);
    if (!(d & 1)) d++;

    do
    {
      p += d;
      if (p >= SIZE_PARSERS) p -= SIZE_PARSERS;
      assert (p < SIZE_PARSERS);
    } while (parser->ops[p]);
  }

  parser->ops[p]     = op;
  parser->parsers[p] = op_parser;
}

static BtorOpParser
find_parser (BtorBTORParser *parser, const char *op)
{
  const char *str;
  unsigned p, d;

  p = hash_op (op, 0);
  if ((str = parser->ops[p]) && strcasecmp (str, op))
  {
    d = hash_op (op, 1);
    if (!(d & 1)) d++;

    do
    {
      p += d;
      if (p >= SIZE_PARSERS) p -= SIZE_PARSERS;
    } while ((str = parser->ops[p]) && strcasecmp (str, op));
  }

  return str ? parser->parsers[p] : 0;
}

static BtorBTORParser *
btor_new_btor_parser (BtorExpMgr *btor, int verbosity)
{
  BtorMemMgr *mm = btor_get_mem_mgr_exp_mgr (btor);
  BtorBTORParser *res;

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

static void
btor_delete_btor_parser (BtorBTORParser *parser)
{
  BtorExp *e;
  int i;

  for (i = 0; i < BTOR_COUNT_STACK (parser->exps); i++)
    if ((e = parser->exps.start[i]))
      btor_release_exp (parser->btor, parser->exps.start[i]);

  BTOR_RELEASE_STACK (parser->mm, parser->exps);
  BTOR_RELEASE_STACK (parser->mm, parser->vars);
  BTOR_RELEASE_STACK (parser->mm, parser->roots);

  BTOR_RELEASE_STACK (parser->mm, parser->op);
  BTOR_RELEASE_STACK (parser->mm, parser->bits);
  BTOR_RELEASE_STACK (parser->mm, parser->constant);
  BTOR_RELEASE_STACK (parser->mm, parser->varname);

  BTOR_DELETEN (parser->mm, parser->parsers, SIZE_PARSERS);
  BTOR_DELETEN (parser->mm, parser->ops, SIZE_PARSERS);

  btor_freestr (parser->mm, parser->error);

  btor_free (parser->mm, parser, sizeof *parser);
}

static const char *
btor_parse_btor_parser (BtorBTORParser *parser,
                        FILE *file,
                        const char *name,
                        BtorParseResult *res)
{
  BtorOpParser op_parser;
  int ch, len;
  BtorExp *e;

  assert (name);
  assert (file);

  if (parser->verbosity > 0) print_verbose_msg ("parsing BTOR file %s", name);

  parser->file   = file;
  parser->name   = name;
  parser->lineno = 1;

  memset (res, 0, sizeof *res);

NEXT:
  assert (!parser->error);
  ch = nextch (parser);
  if (isspace (ch)) /* also skip empty lines */
    goto NEXT;

  if (ch == EOF)
  {
  DONE:
    if (res)
    {
      res->vars  = parser->vars.start;
      res->nvars = BTOR_COUNT_STACK (parser->vars);

      res->roots  = parser->roots.start;
      res->nroots = BTOR_COUNT_STACK (parser->roots);
    }

    return 0;
  }

  if (ch == ';') /* skip comments */
  {
  COMMENTS:
    while ((ch = nextch (parser)) != '\n')
      if (ch == EOF) goto DONE;

    goto NEXT;
  }

  if (!isdigit (ch)) return parse_error (parser, "expected ';' or digit");

  savech (parser, ch);

  if (parse_positive_int (parser, &parser->idx)) return parser->error;

  while (BTOR_COUNT_STACK (parser->exps) <= parser->idx)
    BTOR_PUSH_STACK (parser->mm, parser->exps, 0);

  if (parser->exps.start[parser->idx])
    return parse_error (parser, "'%d' defined twice", parser->idx);

  if (parse_space (parser)) return parser->error;

  assert (BTOR_EMPTY_STACK (parser->op));
  while (!isspace (ch = nextch (parser)) && ch != EOF)
    BTOR_PUSH_STACK (parser->mm, parser->op, ch);

  BTOR_PUSH_STACK (parser->mm, parser->op, 0);
  BTOR_RESET_STACK (parser->op);
  savech (parser, ch);

  if (parse_space (parser)) return parser->error;

  if (parse_positive_int (parser, &len)) return parser->error;

  if (!(op_parser = find_parser (parser, parser->op.start)))
    return parse_error (parser, "invalid operator '%s'", parser->op);

  if (!(e = op_parser (parser, len)))
  {
    assert (parser->error);
    return parser->error;
  }

  assert (btor_get_exp_len (parser->btor, e) == len);
  parser->exps.start[parser->idx] = e;

SKIP:
  ch = nextch (parser);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (ch == ';') goto COMMENTS; /* ... and force new line */

  if (ch != '\n') return parse_error (parser, "expected new line");

  goto NEXT;
}

static BtorParserAPI api = {
    (BtorInitParser) btor_new_btor_parser,
    (BtorResetParser) btor_delete_btor_parser,
    (BtorParse) btor_parse_btor_parser,
};

const BtorParserAPI *btor_btor_parser_api = &api;
