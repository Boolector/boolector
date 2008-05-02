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
typedef BtorExp *(*Unary) (Btor *, BtorExp *);
typedef BtorExp *(*Binary) (Btor *, BtorExp *, BtorExp *);
typedef BtorExp *(*Shift) (Btor *, BtorExp *, BtorExp *);
typedef BtorExp *(*Extend) (Btor *, BtorExp *, int);

#define SIZE_PARSERS 128

typedef struct Info Info;

struct Info
{
  unsigned var : 1;
  unsigned array : 1;
  unsigned next : 1;
};

BTOR_DECLARE_STACK (Info, Info);

struct BtorBTORParser
{
  BtorMemMgr *mem;
  Btor *btor;

  FILE *file;
  int lineno;
  int saved;
  const char *name;
  char *error;

  BtorExpPtrStack exps;
  BtorInfoStack info;

  BtorExpPtrStack inputs;
  BtorExpPtrStack outputs;
  BtorExpPtrStack regs;
  BtorExpPtrStack nexts;

  BtorCharStack op;
  BtorCharStack constant;
  BtorCharStack symbol;

  BtorOpParser *parsers;
  const char **ops;

  int idx;
  int verbosity;

  int found_arrays;
};

static unsigned primes[4] = {111130391, 22237357, 33355519, 444476887};

#define PRIMES ((sizeof primes) / sizeof primes[0])

static void
print_verbose_msg (char *fmt, ...)
{
  va_list ap;
  fprintf (stdout, "[btorbtor] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
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
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start (ap, fmt);
    bytes = btor_parse_error_message_length (parser->name, fmt, ap);
    va_end (ap);

    va_start (ap, fmt);
    parser->error = btor_parse_error_message (
        parser->mem, parser->name, parser->lineno, fmt, ap, bytes);
    va_end (ap);
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
parse_exp (BtorBTORParser *parser, int expected_len, int can_be_array)
{
  int lit, idx, len_res;
  BtorExp *res;

  lit = 0;
  if (parse_non_zero_int (parser, &lit)) return 0;

  idx = abs (lit);
  assert (idx);

  if (idx >= BTOR_COUNT_STACK (parser->exps)
      || !(res = parser->exps.start[idx]))
  {
    (void) parse_error (parser, "literal '%d' undefined", lit);
    return 0;
  }

  if (!can_be_array && btor_is_array_exp (parser->btor, res))
  {
    (void) parse_error (
        parser, "literal '%d' refers to an unexpected array expression", lit);
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

static int
parse_symbol (BtorBTORParser *parser)
{
  char buffer[20];
  const char *p;
  int ch;

  while ((ch = nextch (parser)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  UNEXPECTED_EOF:
  {
    (void) parse_error (parser, "unexpected EOF");
    return 0;
  }

    assert (BTOR_EMPTY_STACK (parser->symbol));

  if (ch == '\n')
  {
    sprintf (buffer, "%d", parser->idx);
    for (p = buffer; *p; p++) BTOR_PUSH_STACK (parser->mem, parser->symbol, *p);
  }
  else
  {
    BTOR_PUSH_STACK (parser->mem, parser->symbol, ch);

    while (!isspace (ch = nextch (parser)))
    {
      if (ch == EOF) goto UNEXPECTED_EOF;

      BTOR_PUSH_STACK (parser->mem, parser->symbol, ch);
    }
  }

  savech (parser, ch);

  BTOR_PUSH_STACK (parser->mem, parser->symbol, 0);
  BTOR_RESET_STACK (parser->symbol);

  return 1;
}

static BtorExp *
parse_var (BtorBTORParser *parser, int len)
{
  BtorExp *res;

  if (!parse_symbol (parser)) return 0;

  res = btor_var_exp (parser->btor, len, parser->symbol.start);
  BTOR_PUSH_STACK (parser->mem, parser->inputs, res);
  parser->info.start[parser->idx].var = 1;

  return res;
}

static BtorExp *
parse_array (BtorBTORParser *parser, int len)
{
  BtorExp *res;
  int idx_len;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx_len)) return 0;

  /* TODO: symbols for arrays */

  res = btor_array_exp (parser->btor, len, idx_len);
  BTOR_PUSH_STACK (parser->mem, parser->inputs, res);
  parser->info.start[parser->idx].array = 1;

  parser->found_arrays = 1;

  return res;
}

static BtorExp *
parse_array_exp (BtorBTORParser *parser, int len)
{
  BtorExp *res;

  res = parse_exp (parser, len, 1);
  if (!res) return 0;

  if (btor_is_array_exp (parser->btor, res)) return res;

  (void) parse_error (parser, "expected array expression");
  btor_release_exp (parser->btor, res);

  return 0;
}

static BtorExp *
parse_next (BtorBTORParser *parser, int len)
{
  int idx;
  BtorExp *current, *next;
  Info info;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx)) return 0;

  if (idx >= BTOR_COUNT_STACK (parser->exps)
      || !(current = parser->exps.start[idx]))
  {
    (void) parse_error (parser, "invalid next index %d", idx);
    return 0;
  }

  info = parser->info.start[idx];

  if (!info.var)
  {
    (void) parse_error (parser, "next index %d is not a variable", idx);
    return 0;
  }

  if (info.next)
  {
    (void) parse_error (parser, "next index %d already used", idx);
    return 0;
  }

  if (parse_space (parser)) return 0;

  assert (!btor_is_array_exp (parser->btor, current));
  if (!(next = parse_exp (parser, len, 0))) return 0;

  BTOR_PUSH_STACK (parser->mem, parser->regs, current);
  BTOR_PUSH_STACK (parser->mem, parser->nexts, next);
  parser->info.start[idx].next = 1;

  return next;
}

static BtorExp *
parse_anext (BtorBTORParser *parser, int len)
{
  int idx, current_idx_len, idx_len;
  BtorExp *current, *next;
  Info info;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx_len)) return 0;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx)) return 0;

  if (idx >= BTOR_COUNT_STACK (parser->exps)
      || !(current = parser->exps.start[idx]))
  {
    (void) parse_error (parser, "invalid next index %d", idx);
    return 0;
  }

  info = parser->info.start[idx];
  if (!info.array)
  {
    (void) parse_error (parser, "next index %d is not an array", idx);
    return 0;
  }

  if (info.next)
  {
    (void) parse_error (parser, "next index %d already used", idx);
    return 0;
  }

  if (parse_space (parser)) return 0;

  assert (btor_is_array_exp (parser->btor, current));
  if (!(next = parse_array_exp (parser, len))) return 0;

  current_idx_len = btor_get_index_exp_len (parser->btor, current);
  if (idx_len != current_idx_len)
  {
    btor_release_exp (parser->btor, next);
    (void) parse_error (parser,
                        "arrays with different index width %d and %d",
                        current_idx_len,
                        idx_len);
    return 0;
  }

  BTOR_PUSH_STACK (parser->mem, parser->regs, current);
  BTOR_PUSH_STACK (parser->mem, parser->nexts, next);
  parser->info.start[idx].next = 1;

  return next;
}

static BtorExp *
parse_const (BtorBTORParser *parser, int len)
{
  BtorExp *res;
  int ch, clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));
  while (!isspace (ch = nextch (parser)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) parse_error (parser, "expected '0' or '1'");
      return 0;
    }

    BTOR_PUSH_STACK (parser->mem, parser->constant, ch);
  }

  savech (parser, ch);
  clen = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->mem, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  if (clen != len)
  {
    (void) parse_error (parser,
                        "binary constant '%s' exceeds bit width %d",
                        parser->constant.start,
                        len);
    return 0;
  }

  res = btor_const_exp (parser->btor, parser->constant.start);

  return res;
}

static BtorExp *
parse_consth (BtorBTORParser *parser, int len)
{
  char *tmp, *extended;
  BtorExp *res;
  int ch, clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));

  while (!isspace (ch = nextch (parser)) && ch != EOF && ch != ';')
  {
    if (!isxdigit (ch))
    {
      (void) parse_error (parser, "expected hexidecimal digit");
      return 0;
    }

    BTOR_PUSH_STACK (parser->mem, parser->constant, ch);
  }

  savech (parser, ch);

  clen = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->mem, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  tmp  = btor_hex_to_const_n (parser->mem, parser->constant.start, clen);
  clen = (int) strlen (tmp);

  if (clen > len)
  {
    (void) parse_error (parser,
                        "hexadecimal constant '%s' exceeds bit width %d",
                        parser->constant.start,
                        len);

    btor_freestr (parser->mem, tmp);
    return 0;
  }

  if (clen < len)
  {
    extended = btor_uext_const (parser->mem, tmp, len - clen);
    btor_delete_const (parser->mem, tmp);
    tmp = extended;
  }

  assert (len == (int) strlen (tmp));
  res = btor_const_exp (parser->btor, tmp);
  btor_freestr (parser->mem, tmp);

  assert (btor_get_exp_len (parser->btor, res) == len);

  return res;
}

static BtorExp *
parse_constd (BtorBTORParser *parser, int len)
{
  char ch, *tmp, *extended;
  BtorExp *res;
  int clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));

  ch = nextch (parser);
  if (!isdigit (ch))
  {
    (void) parse_error (parser, "expected digit");
    return 0;
  }

  BTOR_PUSH_STACK (parser->mem, parser->constant, ch);

  if (ch == '0')
  {
    ch = nextch (parser);

    if (isdigit (ch))
    {
      (void) parse_error (parser, "digit after '0'");
      return 0;
    }

    tmp = btor_strdup (parser->mem, "");
  }
  else
  {
    while (isdigit (ch = nextch (parser)))
      BTOR_PUSH_STACK (parser->mem, parser->constant, ch);

    clen = BTOR_COUNT_STACK (parser->constant);

    tmp = btor_decimal_to_const_n (parser->mem, parser->constant.start, clen);
  }

  BTOR_PUSH_STACK (parser->mem, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  savech (parser, ch);

  clen = (int) strlen (tmp);
  if (clen > len)
  {
    (void) parse_error (parser,
                        "decimal constant '%s' exceeds bit width %d",
                        parser->constant.start,
                        len);
    btor_freestr (parser->mem, tmp);
    return 0;
  }

  if (clen < len)
  {
    extended = btor_uext_const (parser->mem, tmp, len - clen);
    btor_delete_const (parser->mem, tmp);
    tmp = extended;
  }

  assert (len == (int) strlen (tmp));
  res = btor_const_exp (parser->btor, tmp);
  btor_delete_const (parser->mem, tmp);

  assert (btor_get_exp_len (parser->btor, res) == len);

  return res;
}

static BtorExp *
parse_zero (BtorBTORParser *parser, int len)
{
  return btor_zeros_exp (parser->btor, len);
}

static BtorExp *
parse_one (BtorBTORParser *parser, int len)
{
  return btor_one_exp (parser->btor, len);
}

static BtorExp *
parse_ones (BtorBTORParser *parser, int len)
{
  return btor_ones_exp (parser->btor, len);
}

static BtorExp *
parse_root (BtorBTORParser *parser, int len)
{
  BtorExp *res;

  if (parse_space (parser)) return 0;

  if (!(res = parse_exp (parser, len, 0))) return 0;

  BTOR_PUSH_STACK (parser->mem, parser->outputs, res);

  return res;
}

static BtorExp *
parse_unary (BtorBTORParser *parser, int len, Unary f)
{
  BtorExp *tmp, *res;

  assert (len);
  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, len, 0))) return 0;

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
parse_proxy (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, btor_copy_exp);
}

static BtorExp *
parse_redunary_and_nego (BtorBTORParser *parser, int len, Unary f)
{
  BtorExp *tmp, *res;

  (void) len;
  assert (len == 1);

  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, 0, 0))) return 0;

  if (f != btor_nego_exp && btor_get_exp_len (parser->btor, tmp) == 1)
  {
    (void) parse_error (parser, "argument of reduction operation of width 1");
    btor_release_exp (parser->btor, tmp);
    return 0;
  }

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

  if (!(l = parse_exp (parser, len, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, len, 0))) goto RELEASE_L_AND_RETURN_ERROR;

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
parse_srem (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_srem_exp);
}

static BtorExp *
parse_mul (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_mul_exp);
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
parse_urem (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_urem_exp);
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
parse_nor (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_nor_exp);
}

static BtorExp *
parse_nand (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_nand_exp);
}

static BtorExp *
parse_sdiv (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, btor_sdiv_exp);
}

static BtorExp *
parse_logical (BtorBTORParser *parser, int len, Binary f)
{
  BtorExp *l, *r, *res;

  if (len != 1)
  {
    (void) parse_error (parser, "logical operator bit width '%d'", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, 0))) return 0;

  if (btor_get_exp_len (parser->btor, l) != 1)
  {
  BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN:
    (void) parse_error (parser, "expected argument of bit width '1'");
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (parse_space (parser)) goto RELEASE_L_AND_RETURN_ERROR;

  if (!(r = parse_exp (parser, 0, 0))) goto RELEASE_L_AND_RETURN_ERROR;

  if (btor_get_exp_len (parser->btor, r) != 1)
  {
    btor_release_exp (parser->btor, r);
    goto BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN;
  }

  res = f (parser->btor, l, r);
  btor_release_exp (parser->btor, r);
  btor_release_exp (parser->btor, l);
  assert (btor_get_exp_len (parser->btor, res) == 1);

  return res;
}

static BtorExp *
parse_implies (BtorBTORParser *parser, int len)
{
  return parse_logical (parser, len, btor_implies_exp);
}

static BtorExp *
parse_iff (BtorBTORParser *parser, int len)
{
  return parse_logical (parser, len, btor_iff_exp);
}

static BtorExp *
parse_compare_and_overflow (BtorBTORParser *parser,
                            int len,
                            Binary f,
                            int can_be_array)
{
  BtorExp *l, *r, *res;
  int llen, rlen;

  if (len != 1)
  {
    (void) parse_error (
        parser, "comparison or overflow operator returns %d bits", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, can_be_array))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, can_be_array)))
    goto RELEASE_L_AND_RETURN_ERROR;

  llen = btor_get_exp_len (parser->btor, l);
  rlen = btor_get_exp_len (parser->btor, r);

  if (llen != rlen)
  {
    (void) parse_error (
        parser, "operands have different bit width %d and %d", llen, rlen);
  RELEASE_L_AND_R_AND_RETURN_ZERO:
    btor_release_exp (parser->btor, r);
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (can_be_array)
  {
    if (btor_is_array_exp (parser->btor, l)
        && !btor_is_array_exp (parser->btor, r))
    {
      (void) parse_error (parser, "first operand is array and second not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }

    if (!btor_is_array_exp (parser->btor, l)
        && btor_is_array_exp (parser->btor, r))
    {
      (void) parse_error (parser, "second operand is array and first not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }

    if (btor_is_array_exp (parser->btor, l)
        && btor_is_array_exp (parser->btor, r))
    {
      llen = btor_get_index_exp_len (parser->btor, l);
      rlen = btor_get_index_exp_len (parser->btor, r);

      if (llen != rlen)
      {
        (void) parse_error (
            parser,
            "array operands have different index width %d and %d",
            llen,
            rlen);
        goto RELEASE_L_AND_R_AND_RETURN_ZERO;
      }
    }
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
  return parse_compare_and_overflow (parser, len, btor_eq_exp, 1);
}

static BtorExp *
parse_ne (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ne_exp, 1);
}

static BtorExp *
parse_sgt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_sgt_exp, 0);
}

static BtorExp *
parse_sgte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_sgte_exp, 0);
}

static BtorExp *
parse_slt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_slt_exp, 0);
}

static BtorExp *
parse_slte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_slte_exp, 0);
}

static BtorExp *
parse_ugt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ugt_exp, 0);
}

static BtorExp *
parse_ugte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ugte_exp, 0);
}

static BtorExp *
parse_ult (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ult_exp, 0);
}

static BtorExp *
parse_ulte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ulte_exp, 0);
}

static BtorExp *
parse_saddo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_saddo_exp, 0);
}

static BtorExp *
parse_ssubo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_ssubo_exp, 0);
}

static BtorExp *
parse_smulo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_smulo_exp, 0);
}

static BtorExp *
parse_sdivo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_sdivo_exp, 0);
}

static BtorExp *
parse_uaddo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_uaddo_exp, 0);
}

static BtorExp *
parse_usubo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_usubo_exp, 0);
}

static BtorExp *
parse_umulo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, btor_umulo_exp, 0);
}

static BtorExp *
parse_concat (BtorBTORParser *parser, int len)
{
  BtorExp *l, *r, *res;
  int llen, rlen;

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, 0))) goto RELEASE_L_AND_RETURN_ERROR;

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

  if (!(l = parse_exp (parser, len, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, rlen, 0))) goto RELEASE_L_AND_RETURN_ERROR;

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

  if (!(c = parse_exp (parser, 1, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, c);
    return 0;
  }

  if (!(t = parse_exp (parser, len, 0))) goto RELEASE_C_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp (parser, len, 0))) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  res = btor_cond_exp (parser->btor, c, t, e);
  btor_release_exp (parser->btor, e);
  btor_release_exp (parser->btor, t);
  btor_release_exp (parser->btor, c);

  return res;
}

static BtorExp *
parse_acond (BtorBTORParser *parser, int len)
{
  BtorExp *c, *t, *e, *res;
  int idxlen;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idxlen)) return 0;

  if (parse_space (parser)) return 0;

  if (!(c = parse_exp (parser, 1, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, c);
    return 0;
  }

  if (!(t = parse_array_exp (parser, len))) goto RELEASE_C_AND_RETURN_ERROR;

  if (idxlen != btor_get_index_exp_len (parser->btor, t))
  {
    (void) parse_error (parser, "mismatch of index bit width of 'then' array");
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (parse_space (parser)) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (!(e = parse_array_exp (parser, len)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (idxlen != btor_get_index_exp_len (parser->btor, e))
  {
    (void) parse_error (parser, "mismatch of index bit width of 'else' array");
    btor_release_exp (parser->btor, e);
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;
  }

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

  if (!(arg = parse_exp (parser, 0, 0))) return 0;

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

  if (!(array = parse_array_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, array);
    return 0;
  }

  idxlen = btor_get_index_exp_len (parser->btor, array);
  if (!(idx = parse_exp (parser, idxlen, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  res = btor_read_exp (parser->btor, array, idx);
  btor_release_exp (parser->btor, idx);
  btor_release_exp (parser->btor, array);

  return res;
}

static BtorExp *
parse_write (BtorBTORParser *parser, int len)
{
  BtorExp *array, *idx, *val, *res;
  int idxlen, vallen;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idxlen)) return 0;

  if (parse_space (parser)) return 0;

  if (!(array = parse_array_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, array);
    return 0;
  }

  if (!(idx = parse_exp (parser, idxlen, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR:
    btor_release_exp (parser->btor, idx);
    goto RELEASE_ARRAY_AND_RETURN_ERROR;
  }

  vallen = btor_get_exp_len (parser->btor, array);
  if (!(val = parse_exp (parser, vallen, 0)))
    goto RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR;

  res = btor_write_exp (parser->btor, array, idx, val);

  btor_release_exp (parser->btor, array);
  btor_release_exp (parser->btor, idx);
  btor_release_exp (parser->btor, val);

  return res;
}

static BtorExp *
parse_ext (BtorBTORParser *parser, int len, Extend f)
{
  BtorExp *res, *arg;
  int alen, elen;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0, 0))) return 0;

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
btor_new_btor_parser (Btor *btor, int verbosity)
{
  BtorMemMgr *mem = btor_get_mem_mgr_btor (btor);
  BtorBTORParser *res;

  assert (verbosity >= -1);

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->mem  = mem;
  res->btor = btor;

  BTOR_NEWN (mem, res->parsers, SIZE_PARSERS);
  BTOR_NEWN (mem, res->ops, SIZE_PARSERS);
  BTOR_CLRN (res->ops, SIZE_PARSERS);

  new_parser (res, parse_add, "add");
  new_parser (res, parse_and, "and");
  new_parser (res, parse_array, "array");
  new_parser (res, parse_concat, "concat");
  new_parser (res, parse_cond, "cond");
  new_parser (res, parse_acond, "acond");
  new_parser (res, parse_const, "const");
  new_parser (res, parse_constd, "constd");
  new_parser (res, parse_consth, "consth");
  new_parser (res, parse_eq, "eq");
  new_parser (res, parse_iff, "iff");
  new_parser (res, parse_implies, "implies");
  new_parser (res, parse_mul, "mul");
  new_parser (res, parse_nand, "nand");
  new_parser (res, parse_neg, "neg");
  new_parser (res, parse_nego, "nego");
  new_parser (res, parse_ne, "ne");
  new_parser (res, parse_next, "next");   /* only in parser */
  new_parser (res, parse_anext, "anext"); /* only in parser */
  new_parser (res, parse_nor, "nor");
  new_parser (res, parse_not, "not");
  new_parser (res, parse_one, "one");
  new_parser (res, parse_ones, "ones");
  new_parser (res, parse_or, "or");
  new_parser (res, parse_proxy, "proxy");
  new_parser (res, parse_read, "read");
  new_parser (res, parse_redand, "redand");
  new_parser (res, parse_redor, "redor");
  new_parser (res, parse_redxor, "redxor");
  new_parser (res, parse_rol, "rol");
  new_parser (res, parse_root, "root"); /* only in parser */
  new_parser (res, parse_ror, "ror");
  new_parser (res, parse_saddo, "saddo");
  new_parser (res, parse_sdivo, "sdivo");
  new_parser (res, parse_sdiv, "sdiv");
  new_parser (res, parse_sext, "sext");
  new_parser (res, parse_sgte, "sgte");
  new_parser (res, parse_sgt, "sgt");
  new_parser (res, parse_slice, "slice");
  new_parser (res, parse_sll, "sll");
  new_parser (res, parse_slte, "slte");
  new_parser (res, parse_slt, "slt");
  new_parser (res, parse_smod, "smod");
  new_parser (res, parse_smulo, "smulo");
  new_parser (res, parse_sra, "sra");
  new_parser (res, parse_srem, "srem");
  new_parser (res, parse_srl, "srl");
  new_parser (res, parse_ssubo, "ssubo");
  new_parser (res, parse_sub, "sub");
  new_parser (res, parse_uaddo, "uaddo");
  new_parser (res, parse_udiv, "udiv");
  new_parser (res, parse_uext, "uext");
  new_parser (res, parse_ugte, "ugte");
  new_parser (res, parse_ugt, "ugt");
  new_parser (res, parse_ulte, "ulte");
  new_parser (res, parse_ult, "ult");
  new_parser (res, parse_umulo, "umulo");
  new_parser (res, parse_urem, "urem");
  new_parser (res, parse_usubo, "usubo");
  new_parser (res, parse_var, "var");
  new_parser (res, parse_write, "write");
  new_parser (res, parse_xnor, "xnor");
  new_parser (res, parse_xor, "xor");
  new_parser (res, parse_zero, "zero");

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

  BTOR_RELEASE_STACK (parser->mem, parser->exps);
  BTOR_RELEASE_STACK (parser->mem, parser->info);
  BTOR_RELEASE_STACK (parser->mem, parser->inputs);
  BTOR_RELEASE_STACK (parser->mem, parser->outputs);
  BTOR_RELEASE_STACK (parser->mem, parser->regs);
  BTOR_RELEASE_STACK (parser->mem, parser->nexts);

  BTOR_RELEASE_STACK (parser->mem, parser->op);
  BTOR_RELEASE_STACK (parser->mem, parser->constant);
  BTOR_RELEASE_STACK (parser->mem, parser->symbol);

  BTOR_DELETEN (parser->mem, parser->parsers, SIZE_PARSERS);
  BTOR_DELETEN (parser->mem, parser->ops, SIZE_PARSERS);

  btor_freestr (parser->mem, parser->error);
  BTOR_DELETE (parser->mem, parser);
}

static void
remove_regs_from_vars (BtorBTORParser *parser)
{
  BtorExp **p, **q, *e;
  Info info;
  int i;

  p = q = parser->inputs.start;
  for (i = 1; i <= parser->idx; i++)
  {
    info = parser->info.start[i];

    if (!info.var && !info.array) continue;

    e = parser->exps.start[i];
    assert (*p == e);
    p++;

    if (!info.next) *q++ = e;
  }
  assert (p == parser->inputs.top);
  parser->inputs.top = q;
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

  if (parser->verbosity > 0) print_verbose_msg ("parsing %s", name);

  parser->file   = file;
  parser->name   = name;
  parser->lineno = 1;

  BTOR_CLR (res);

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
      remove_regs_from_vars (parser);

      if (parser->found_arrays)
        res->logic = BTOR_LOGIC_QF_AUFBV;
      else
        res->logic = BTOR_LOGIC_QF_BV;
      res->status = BTOR_PARSE_SAT_STATUS_UNKNOWN;

      res->ninputs = BTOR_COUNT_STACK (parser->inputs);
      res->inputs  = parser->inputs.start;

      res->noutputs = BTOR_COUNT_STACK (parser->outputs);
      res->outputs  = parser->outputs.start;

      res->nregs = BTOR_COUNT_STACK (parser->regs);
      res->regs  = parser->regs.start;
      res->nexts = parser->nexts.start;

      if (parser->verbosity > 0)
      {
        print_verbose_msg ("parsed %d inputs", res->ninputs);
        print_verbose_msg ("parsed %d registers", res->nregs);
        print_verbose_msg ("parsed %d outputs", res->noutputs);
      }
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
  {
    Info info;
    memset (&info, 0, sizeof info);
    BTOR_PUSH_STACK (parser->mem, parser->info, info);
    BTOR_PUSH_STACK (parser->mem, parser->exps, 0);
  }

  if (parser->exps.start[parser->idx])
    return parse_error (parser, "'%d' defined twice", parser->idx);

  if (parse_space (parser)) return parser->error;

  assert (BTOR_EMPTY_STACK (parser->op));
  while (!isspace (ch = nextch (parser)) && ch != EOF)
    BTOR_PUSH_STACK (parser->mem, parser->op, ch);

  BTOR_PUSH_STACK (parser->mem, parser->op, 0);
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
