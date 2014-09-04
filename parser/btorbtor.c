/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *  Copyright (C) 2013-2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbtor.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorparse.h"
#include "btorstack.h"
#include "btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

void boolector_set_btor_id (Btor *, BoolectorNode *, int);

/*------------------------------------------------------------------------*/

typedef struct BtorBTORParser BtorBTORParser;

typedef BoolectorNode *(*BtorOpParser) (BtorBTORParser *, int len);
typedef BoolectorNode *(*Unary) (Btor *, BoolectorNode *);
typedef BoolectorNode *(*Binary) (Btor *, BoolectorNode *, BoolectorNode *);
typedef BoolectorNode *(*Shift) (Btor *, BoolectorNode *, BoolectorNode *);
typedef BoolectorNode *(*Extend) (Btor *, BoolectorNode *, int);

#define SIZE_PARSERS 128

typedef struct Info Info;

struct Info
{
  unsigned var : 1;
  unsigned array : 1;
};

BTOR_DECLARE_STACK (BtorInfo, Info);
BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

struct BtorBTORParser
{
  BtorMemMgr *mem;
  Btor *btor;

  int nprefix;
  BtorCharStack *prefix;
  FILE *file;
  int lineno;
  int saved; /* boolean flag */
  int saved_char;
  const char *name;
  char *error;

  BoolectorNodePtrStack exps;
  BtorInfoStack info;

  BoolectorNodePtrStack inputs;
  BoolectorNodePtrStack outputs;
  BoolectorNodePtrStack regs;
  BoolectorNodePtrStack lambdas;
  BoolectorNodePtrStack params;

  BtorCharStack op;
  BtorCharStack constant;
  BtorCharStack symbol;

  BtorOpParser *parsers;
  const char **ops;

  int idx;
  int verbosity;

  int found_arrays;
  int found_lambdas;
  int found_aeq;
};

/*------------------------------------------------------------------------*/

static void
btor_msg_btor (char *fmt, ...)
{
  va_list ap;
  fprintf (stdout, "[btorbtor] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static const char *
btor_perr_btor (BtorBTORParser *parser, const char *fmt, ...)
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
        parser->mem, parser->name, parser->lineno, 0, fmt, ap, bytes);
    va_end (ap);
  }

  return parser->error;
}

/*------------------------------------------------------------------------*/

static unsigned btor_primes_btor[4] = {
    111130391, 22237357, 33355519, 444476887};

#define BTOR_PRIMES_BTOR \
  ((sizeof btor_primes_btor) / sizeof btor_primes_btor[0])

static unsigned
hash_op (const char *str, unsigned salt)
{
  unsigned i, res;
  const char *p;

  assert (salt < BTOR_PRIMES_BTOR);

  res = 0;
  i   = salt;
  for (p = str; *p; p++)
  {
    res += btor_primes_btor[i++] * (unsigned) *p;
    if (i == BTOR_PRIMES_BTOR) i = 0;
  }

  res &= SIZE_PARSERS - 1;

  return res;
}

/*------------------------------------------------------------------------*/

static int
btor_nextch_btor (BtorBTORParser *parser)
{
  int ch;

  if (parser->saved)
  {
    ch            = parser->saved_char;
    parser->saved = 0;
  }
  else if (parser->prefix
           && parser->nprefix < BTOR_COUNT_STACK (*parser->prefix))
  {
    ch = parser->prefix->start[parser->nprefix++];
  }
  else
    ch = getc (parser->file);

  if (ch == '\n') parser->lineno++;

  return ch;
}

static void
btor_savech_btor (BtorBTORParser *parser, int ch)
{
  assert (!parser->saved);

  parser->saved_char = ch;
  parser->saved      = 1;

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

  ch = btor_nextch_btor (parser);
  if (!isdigit (ch)) return btor_perr_btor (parser, "expected digit");

  if (ch == '0')
  {
    res = 0;
    ch  = btor_nextch_btor (parser);
    if (isdigit (ch)) return btor_perr_btor (parser, "digit after '0'");
  }
  else
  {
    res = ch - '0';

    while (isdigit (ch = btor_nextch_btor (parser)))
      res = 10 * res + (ch - '0');
  }

  btor_savech_btor (parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_positive_int (BtorBTORParser *parser, int *res_ptr)
{
  int res, ch;

  ch = btor_nextch_btor (parser);
  if (!isdigit (ch)) return btor_perr_btor (parser, "expected digit");

  if (ch == '0') return btor_perr_btor (parser, "expected non zero digit");

  res = ch - '0';

  while (isdigit (ch = btor_nextch_btor (parser))) res = 10 * res + (ch - '0');

  btor_savech_btor (parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_non_zero_int (BtorBTORParser *parser, int *res_ptr)
{
  int res, sign, ch;

  ch = btor_nextch_btor (parser);

  if (ch == '-')
  {
    sign = -1;
    ch   = btor_nextch_btor (parser);

    if (!isdigit (ch) || ch == '0')
      return btor_perr_btor (parser, "expected non zero digit after '-'");
  }
  else
  {
    sign = 1;
    if (!isdigit (ch) || ch == '0')
      return btor_perr_btor (parser, "expected non zero digit or '-'");
  }

  res = ch - '0';

  while (isdigit (ch = btor_nextch_btor (parser))) res = 10 * res + (ch - '0');

  btor_savech_btor (parser, ch);

  res *= sign;
  *res_ptr = res;

  return 0;
}

static BoolectorNode *
parse_exp (BtorBTORParser *parser,
           int expected_len,
           int can_be_array,
           int can_be_inverted)
{
  int lit, idx, len_res;
  BoolectorNode *res;

  lit = 0;
  if (parse_non_zero_int (parser, &lit)) return 0;

  if (!can_be_inverted && lit < 0)
  {
    (void) btor_perr_btor (parser, "positive literal expected");
    return 0;
  }

  idx = abs (lit);
  assert (idx);

  if (idx >= BTOR_COUNT_STACK (parser->exps)
      || !(res = parser->exps.start[idx]))
  {
    (void) btor_perr_btor (parser, "literal '%d' undefined", lit);
    return 0;
  }

  if (boolector_is_param (parser->btor, res)
      && boolector_is_bound_param (parser->btor, res))
  {
    (void) btor_perr_btor (
        parser, "param '%d' cannot be used outside of its defined scope", lit);
    return 0;
  }

  if (!can_be_array && boolector_is_array (parser->btor, res))
  {
    (void) btor_perr_btor (
        parser, "literal '%d' refers to an unexpected array expression", lit);
    return 0;
  }

  if (expected_len)
  {
    len_res = boolector_get_width (parser->btor, res);

    if (expected_len != len_res)
    {
      (void) btor_perr_btor (parser,
                             "literal '%d' has length '%d' but expected '%d'",
                             lit,
                             len_res,
                             expected_len);

      return 0;
    }
  }

  if (lit < 0)
    res = boolector_not (parser->btor, res);
  else
    res = boolector_copy (parser->btor, res);

  return res;
}

static const char *
parse_space (BtorBTORParser *parser)
{
  int ch;

  ch = btor_nextch_btor (parser);
  if (ch != ' ' && ch != '\t')
    return btor_perr_btor (parser, "expected space or tab");

SKIP:
  ch = btor_nextch_btor (parser);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (!ch) return btor_perr_btor (parser, "unexpected character");

  btor_savech_btor (parser, ch);

  return 0;
}

static int
parse_symbol (BtorBTORParser *parser)
{
  int ch;

  while ((ch = btor_nextch_btor (parser)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  {
  UNEXPECTED_EOF:
    (void) btor_perr_btor (parser, "unexpected EOF");
    return 0;
  }

  assert (BTOR_EMPTY_STACK (parser->symbol));

  if (ch != '\n')
  {
    BTOR_PUSH_STACK (parser->mem, parser->symbol, ch);

    while (!isspace (ch = btor_nextch_btor (parser)))
    {
      if (!isprint (ch)) btor_perr_btor (parser, "invalid character");
      if (ch == EOF) goto UNEXPECTED_EOF;
      BTOR_PUSH_STACK (parser->mem, parser->symbol, ch);
    }
  }

  btor_savech_btor (parser, ch);
  BTOR_PUSH_STACK (parser->mem, parser->symbol, 0);
  BTOR_RESET_STACK (parser->symbol);
  return 1;
}

static BoolectorNode *
parse_var (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;

  if (!parse_symbol (parser)) return 0;

  res = boolector_var (
      parser->btor, len, parser->symbol.start[0] ? parser->symbol.start : 0);
  boolector_set_btor_id (parser->btor, res, parser->idx);
  BTOR_PUSH_STACK (parser->mem, parser->inputs, res);
  parser->info.start[parser->idx].var = 1;

  return res;
}

static BoolectorNode *
parse_param (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;

  if (!parse_symbol (parser)) return 0;

  res = boolector_param (
      parser->btor, len, parser->symbol.start[0] ? parser->symbol.start : 0);
  BTOR_PUSH_STACK (parser->mem, parser->params, res);

  return res;
}

static BoolectorNode *
parse_param_exp (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;

  res = parse_exp (parser, len, 0, 0);
  if (!res) return 0;

  if (boolector_is_param (parser->btor, res)) return res;

  (void) btor_perr_btor (parser, "expected parameter");
  boolector_release (parser->btor, res);

  return 0;
}

static BoolectorNode *
parse_array (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;
  int idx_len;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx_len)) return 0;

  if (!parse_symbol (parser)) return 0;

  res = boolector_array (parser->btor,
                         len,
                         idx_len,
                         parser->symbol.start[0] ? parser->symbol.start : 0);
  boolector_set_btor_id (parser->btor, res, parser->idx);
  BTOR_PUSH_STACK (parser->mem, parser->inputs, res);
  parser->info.start[parser->idx].array = 1;

  parser->found_arrays = 1;

  return res;
}

static BoolectorNode *
parse_array_exp (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;

  res = parse_exp (parser, len, 1, 0);
  if (!res) return 0;

  if (boolector_is_array (parser->btor, res)) return res;

  (void) btor_perr_btor (parser, "expected array expression");
  boolector_release (parser->btor, res);

  return 0;
}

static BoolectorNode *
parse_const (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;
  int ch, clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));
  while (!isspace (ch = btor_nextch_btor (parser)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) btor_perr_btor (parser, "expected '0' or '1'");
      return 0;
    }

    BTOR_PUSH_STACK (parser->mem, parser->constant, ch);
  }

  btor_savech_btor (parser, ch);
  clen = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->mem, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  if (clen != len)
  {
    (void) btor_perr_btor (parser,
                           "binary constant '%s' exceeds bit width %d",
                           parser->constant.start,
                           len);
    return 0;
  }

  res = boolector_const (parser->btor, parser->constant.start);

  return res;
}

static BoolectorNode *
parse_consth (BtorBTORParser *parser, int len)
{
  char *tmp, *extended;
  BoolectorNode *res;
  int ch, clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));

  while (!isspace (ch = btor_nextch_btor (parser)) && ch != EOF && ch != ';')
  {
    if (!isxdigit (ch))
    {
      (void) btor_perr_btor (parser, "expected hexidecimal digit");
      return 0;
    }

    BTOR_PUSH_STACK (parser->mem, parser->constant, ch);
  }

  btor_savech_btor (parser, ch);

  clen = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->mem, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  tmp  = btor_hex_to_const_n (parser->mem, parser->constant.start, clen);
  clen = (int) strlen (tmp);

  if (clen > len)
  {
    (void) btor_perr_btor (parser,
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
  res = boolector_const (parser->btor, tmp);
  btor_freestr (parser->mem, tmp);

  assert (boolector_get_width (parser->btor, res) == len);

  return res;
}

static BoolectorNode *
parse_constd (BtorBTORParser *parser, int len)
{
  char ch, *tmp, *extended;
  BoolectorNode *res;
  int clen;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));

  ch = btor_nextch_btor (parser);
  if (!isdigit (ch))
  {
    (void) btor_perr_btor (parser, "expected digit");
    return 0;
  }

  BTOR_PUSH_STACK (parser->mem, parser->constant, ch);

  if (ch == '0')
  {
    ch = btor_nextch_btor (parser);

    if (isdigit (ch))
    {
      (void) btor_perr_btor (parser, "digit after '0'");
      return 0;
    }

    tmp = btor_strdup (parser->mem, "");
  }
  else
  {
    while (isdigit (ch = btor_nextch_btor (parser)))
      BTOR_PUSH_STACK (parser->mem, parser->constant, ch);

    clen = BTOR_COUNT_STACK (parser->constant);

    tmp = btor_decimal_to_const_n (parser->mem, parser->constant.start, clen);
  }

  BTOR_PUSH_STACK (parser->mem, parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  btor_savech_btor (parser, ch);

  clen = (int) strlen (tmp);
  if (clen > len)
  {
    (void) btor_perr_btor (parser,
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
  res = boolector_const (parser->btor, tmp);
  btor_delete_const (parser->mem, tmp);

  assert (boolector_get_width (parser->btor, res) == len);

  return res;
}

static BoolectorNode *
parse_zero (BtorBTORParser *parser, int len)
{
  return boolector_zero (parser->btor, len);
}

static BoolectorNode *
parse_one (BtorBTORParser *parser, int len)
{
  return boolector_one (parser->btor, len);
}

static BoolectorNode *
parse_ones (BtorBTORParser *parser, int len)
{
  return boolector_ones (parser->btor, len);
}

static BoolectorNode *
parse_root (BtorBTORParser *parser, int len)
{
  BoolectorNode *res;

  if (parse_space (parser)) return 0;

  if (!(res = parse_exp (parser, len, 0, 1))) return 0;

  BTOR_PUSH_STACK (parser->mem, parser->outputs, res);

  return res;
}

static BoolectorNode *
parse_unary (BtorBTORParser *parser, int len, Unary f)
{
  BoolectorNode *tmp, *res;

  assert (len);
  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, len, 0, 1))) return 0;

  res = f (parser->btor, tmp);
  boolector_release (parser->btor, tmp);
  assert (boolector_get_width (parser->btor, res) == len);

  return res;
}

static BoolectorNode *
parse_not (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, boolector_not);
}

static BoolectorNode *
parse_neg (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, boolector_neg);
}

static BoolectorNode *
parse_inc (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, boolector_inc);
}

static BoolectorNode *
parse_dec (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, boolector_dec);
}

static BoolectorNode *
parse_proxy (BtorBTORParser *parser, int len)
{
  return parse_unary (parser, len, boolector_copy);
}

static BoolectorNode *
parse_redunary (BtorBTORParser *parser, int len, Unary f)
{
  BoolectorNode *tmp, *res;

  (void) len;
  assert (len == 1);

  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, 0, 0, 1))) return 0;

  if (boolector_get_width (parser->btor, tmp) == 1)
  {
    (void) btor_perr_btor (parser,
                           "argument of reduction operation of width 1");
    boolector_release (parser->btor, tmp);
    return 0;
  }

  res = f (parser->btor, tmp);
  boolector_release (parser->btor, tmp);
  assert (boolector_get_width (parser->btor, res) == 1);

  return res;
}

static BoolectorNode *
parse_redand (BtorBTORParser *parser, int len)
{
  return parse_redunary (parser, len, boolector_redand);
}

static BoolectorNode *
parse_redor (BtorBTORParser *parser, int len)
{
  return parse_redunary (parser, len, boolector_redor);
}

static BoolectorNode *
parse_redxor (BtorBTORParser *parser, int len)
{
  return parse_redunary (parser, len, boolector_redxor);
}

static BoolectorNode *
parse_binary (BtorBTORParser *parser, int len, Binary f)
{
  BoolectorNode *l, *r, *res;

  assert (len);

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, len, 0, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, len, 0, 1))) goto RELEASE_L_AND_RETURN_ERROR;

  res = f (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == len);

  return res;
}

static BoolectorNode *
parse_add (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_add);
}

static BoolectorNode *
parse_and (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_and);
}

static BoolectorNode *
parse_smod (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_smod);
}

static BoolectorNode *
parse_srem (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_srem);
}

static BoolectorNode *
parse_mul (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_mul);
}

static BoolectorNode *
parse_sub (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_sub);
}

static BoolectorNode *
parse_udiv (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_udiv);
}

static BoolectorNode *
parse_urem (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_urem);
}

static BoolectorNode *
parse_xor (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_xor);
}

static BoolectorNode *
parse_xnor (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_xnor);
}

static BoolectorNode *
parse_or (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_or);
}

static BoolectorNode *
parse_nor (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_nor);
}

static BoolectorNode *
parse_nand (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_nand);
}

static BoolectorNode *
parse_sdiv (BtorBTORParser *parser, int len)
{
  return parse_binary (parser, len, boolector_sdiv);
}

static BoolectorNode *
parse_logical (BtorBTORParser *parser, int len, Binary f)
{
  BoolectorNode *l, *r, *res;

  if (len != 1)
  {
    (void) btor_perr_btor (parser, "logical operator bit width '%d'", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, 0, 1))) return 0;

  if (boolector_get_width (parser->btor, l) != 1)
  {
  BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN:
    (void) btor_perr_btor (parser, "expected argument of bit width '1'");
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (parse_space (parser)) goto RELEASE_L_AND_RETURN_ERROR;

  if (!(r = parse_exp (parser, 0, 0, 1))) goto RELEASE_L_AND_RETURN_ERROR;

  if (boolector_get_width (parser->btor, r) != 1)
  {
    boolector_release (parser->btor, r);
    goto BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN;
  }

  res = f (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == 1);

  return res;
}

static BoolectorNode *
parse_implies (BtorBTORParser *parser, int len)
{
  return parse_logical (parser, len, boolector_implies);
}

static BoolectorNode *
parse_iff (BtorBTORParser *parser, int len)
{
  return parse_logical (parser, len, boolector_iff);
}

static BoolectorNode *
parse_compare_and_overflow (BtorBTORParser *parser,
                            int len,
                            Binary f,
                            int can_be_array)
{
  BoolectorNode *l, *r, *res;
  int llen, rlen;

  if (len != 1)
  {
    (void) btor_perr_btor (
        parser, "comparison or overflow operator returns %d bits", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, can_be_array, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, can_be_array, 1)))
    goto RELEASE_L_AND_RETURN_ERROR;

  llen = boolector_get_width (parser->btor, l);
  rlen = boolector_get_width (parser->btor, r);

  if (llen != rlen)
  {
    (void) btor_perr_btor (
        parser, "operands have different bit width %d and %d", llen, rlen);
  RELEASE_L_AND_R_AND_RETURN_ZERO:
    boolector_release (parser->btor, r);
    boolector_release (parser->btor, l);
    return 0;
  }

  if (can_be_array)
  {
    if (boolector_is_array (parser->btor, l)
        && !boolector_is_array (parser->btor, r))
    {
      (void) btor_perr_btor (parser, "first operand is array and second not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }

    if (!boolector_is_array (parser->btor, l)
        && boolector_is_array (parser->btor, r))
    {
      (void) btor_perr_btor (parser, "second operand is array and first not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }

    if (boolector_is_array (parser->btor, l)
        && boolector_is_array (parser->btor, r))
    {
      llen = boolector_get_index_width (parser->btor, l);
      rlen = boolector_get_index_width (parser->btor, r);

      if (llen != rlen)
      {
        (void) btor_perr_btor (
            parser,
            "array operands have different index width %d and %d",
            llen,
            rlen);
        goto RELEASE_L_AND_R_AND_RETURN_ZERO;
      }

#if 0
	  if (boolector_is_fun (parser->btor, l)
	      || boolector_is_fun (parser->btor, r))
	    {
	      (void) btor_perr_btor (
		       parser, "extensionality on lambdas not supported");

	      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
	    }
#endif

      parser->found_aeq = 1;
    }
  }

  res = f (parser->btor, l, r);

  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);

  assert (boolector_get_width (parser->btor, res) == 1);

  return res;
}

static BoolectorNode *
parse_eq (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_eq, 1);
}

static BoolectorNode *
parse_ne (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_ne, 1);
}

static BoolectorNode *
parse_sgt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_sgt, 0);
}

static BoolectorNode *
parse_sgte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_sgte, 0);
}

static BoolectorNode *
parse_slt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_slt, 0);
}

static BoolectorNode *
parse_slte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_slte, 0);
}

static BoolectorNode *
parse_ugt (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_ugt, 0);
}

static BoolectorNode *
parse_ugte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_ugte, 0);
}

static BoolectorNode *
parse_ult (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_ult, 0);
}

static BoolectorNode *
parse_ulte (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_ulte, 0);
}

static BoolectorNode *
parse_saddo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_saddo, 0);
}

static BoolectorNode *
parse_ssubo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_ssubo, 0);
}

static BoolectorNode *
parse_smulo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_smulo, 0);
}

static BoolectorNode *
parse_sdivo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_sdivo, 0);
}

static BoolectorNode *
parse_uaddo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_uaddo, 0);
}

static BoolectorNode *
parse_usubo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_usubo, 0);
}

static BoolectorNode *
parse_umulo (BtorBTORParser *parser, int len)
{
  return parse_compare_and_overflow (parser, len, boolector_umulo, 0);
}

static BoolectorNode *
parse_concat (BtorBTORParser *parser, int len)
{
  BoolectorNode *l, *r, *res;
  int llen, rlen;

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, 0, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, 0, 1))) goto RELEASE_L_AND_RETURN_ERROR;

  llen = boolector_get_width (parser->btor, l);
  rlen = boolector_get_width (parser->btor, r);

  if (llen + rlen != len)
  {
    (void) btor_perr_btor (parser,
                           "operands widths %d and %d do not add up to %d",
                           llen,
                           rlen,
                           len);

    boolector_release (parser->btor, r);
    boolector_release (parser->btor, l);
    return 0;
  }

  res = boolector_concat (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == len);

  return res;
}

static BoolectorNode *
parse_shift (BtorBTORParser *parser, int len, Shift f)
{
  BoolectorNode *l, *r, *res;
  int rlen;

  for (rlen = 1; rlen <= 30 && len != (1 << rlen); rlen++)
    ;

  if (len != (1 << rlen))
  {
    (void) btor_perr_btor (parser, "length %d is not a power of two", len);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, len, 0, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, rlen, 0, 1))) goto RELEASE_L_AND_RETURN_ERROR;

  res = f (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == len);

  return res;
}

static BoolectorNode *
parse_rol (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, boolector_rol);
}

static BoolectorNode *
parse_ror (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, boolector_ror);
}

static BoolectorNode *
parse_sll (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, boolector_sll);
}

static BoolectorNode *
parse_sra (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, boolector_sra);
}

static BoolectorNode *
parse_srl (BtorBTORParser *parser, int len)
{
  return parse_shift (parser, len, boolector_srl);
}

static BoolectorNode *
parse_cond (BtorBTORParser *parser, int len)
{
  BoolectorNode *c, *t, *e, *res;

  if (parse_space (parser)) return 0;

  if (!(c = parse_exp (parser, 1, 0, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    boolector_release (parser->btor, c);
    return 0;
  }

  if (!(t = parse_exp (parser, len, 0, 1))) goto RELEASE_C_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    boolector_release (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp (parser, len, 0, 1)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  res = boolector_cond (parser->btor, c, t, e);
  boolector_release (parser->btor, e);
  boolector_release (parser->btor, t);
  boolector_release (parser->btor, c);

  return res;
}

static BoolectorNode *
parse_acond (BtorBTORParser *parser, int len)
{
  BoolectorNode *c, *t, *e, *res;
  int idxlen;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idxlen)) return 0;

  if (parse_space (parser)) return 0;

  if (!(c = parse_exp (parser, 1, 0, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    boolector_release (parser->btor, c);
    return 0;
  }

  if (!(t = parse_array_exp (parser, len))) goto RELEASE_C_AND_RETURN_ERROR;

  if (idxlen != boolector_get_index_width (parser->btor, t))
  {
    (void) btor_perr_btor (parser,
                           "mismatch of index bit width of 'then' array");
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    boolector_release (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (parse_space (parser)) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (!(e = parse_array_exp (parser, len)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (idxlen != boolector_get_index_width (parser->btor, e))
  {
    (void) btor_perr_btor (parser,
                           "mismatch of index bit width of 'else' array");
    boolector_release (parser->btor, e);
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;
  }

  res = boolector_cond (parser->btor, c, t, e);
  boolector_release (parser->btor, e);
  boolector_release (parser->btor, t);
  boolector_release (parser->btor, c);

  return res;
}

static BoolectorNode *
parse_slice (BtorBTORParser *parser, int len)
{
  int arglen, upper, lower, delta;
  BoolectorNode *res, *arg;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0, 0, 1))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    boolector_release (parser->btor, arg);
    return 0;
  }

  arglen = boolector_get_width (parser->btor, arg);

  if (parse_non_negative_int (parser, &upper))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper >= arglen)
  {
    (void) btor_perr_btor (
        parser, "upper index '%d' >= argument width '%d", upper, arglen);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  if (parse_space (parser)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (parse_non_negative_int (parser, &lower))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper < lower)
  {
    (void) btor_perr_btor (
        parser, "upper index '%d' smaller than lower index '%d'", upper, lower);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  delta = upper - lower + 1;
  if (delta != len)
  {
    (void) btor_perr_btor (parser,
                           "slice width '%d' not equal to expected width '%d'",
                           delta,
                           len);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = boolector_slice (parser->btor, arg, upper, lower);
  boolector_release (parser->btor, arg);

  return res;
}

static BoolectorNode *
parse_read (BtorBTORParser *parser, int len)
{
  BoolectorNode *array, *idx, *res;
  int idxlen;

  if (parse_space (parser)) return 0;

  if (!(array = parse_array_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    boolector_release (parser->btor, array);
    return 0;
  }

  idxlen = boolector_get_index_width (parser->btor, array);
  if (!(idx = parse_exp (parser, idxlen, 0, 1)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  res = boolector_read (parser->btor, array, idx);
  boolector_release (parser->btor, idx);
  boolector_release (parser->btor, array);

  return res;
}

static BoolectorNode *
parse_write (BtorBTORParser *parser, int len)
{
  BoolectorNode *array, *idx, *val, *res;
  int idxlen, vallen;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idxlen)) return 0;

  if (parse_space (parser)) return 0;

  if (!(array = parse_array_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    boolector_release (parser->btor, array);
    return 0;
  }

  if (!(idx = parse_exp (parser, idxlen, 0, 1)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR:
    boolector_release (parser->btor, idx);
    goto RELEASE_ARRAY_AND_RETURN_ERROR;
  }

  vallen = boolector_get_width (parser->btor, array);
  if (!(val = parse_exp (parser, vallen, 0, 1)))
    goto RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR;

  res = boolector_write (parser->btor, array, idx, val);

  boolector_release (parser->btor, array);
  boolector_release (parser->btor, idx);
  boolector_release (parser->btor, val);

  return res;
}

static BoolectorNode *
parse_lambda (BtorBTORParser *parser, int len)
{
  int paramlen;
  BoolectorNode **params, *exp, *res;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &paramlen)) return 0;

  if (parse_space (parser)) return 0;

  BTOR_NEW (parser->mem, params);
  if (!(params[0] = parse_param_exp (parser, paramlen))) return 0;

  if (boolector_is_bound_param (parser->btor, params[0]))
  {
    btor_perr_btor (parser, "param already bound by other lambda");
    goto RELEASE_PARAM_AND_RETURN_ERROR;
  }

  if (parse_space (parser))
  {
  RELEASE_PARAM_AND_RETURN_ERROR:
    boolector_release (parser->btor, params[0]);
    return 0;
  }

  if (!(exp = parse_exp (parser, len, 1, 1)))
    goto RELEASE_PARAM_AND_RETURN_ERROR;

  res = boolector_fun (parser->btor, 1, params, exp);

  boolector_release (parser->btor, params[0]);
  BTOR_DELETE (parser->mem, params);
  boolector_release (parser->btor, exp);

  parser->found_lambdas = 1;
  BTOR_PUSH_STACK (parser->mem, parser->lambdas, res);

  return res;
}

static BoolectorNode *
parse_apply (BtorBTORParser *parser, int len)
{
  int argslen;
  BoolectorNode *res, *fun, *args;

  if (parse_space (parser)) return 0;

  if (!(fun = parse_array_exp (parser, len))) return 0;

  if (parse_space (parser))
  {
  RELEASE_FUN_AND_RETURN_ERROR:
    boolector_release (parser->btor, fun);
    return 0;
  }

  argslen = boolector_get_index_width (parser->btor, fun);
  // TODO: we ignore argslen for now
  (void) argslen;
  if (!(args = parse_exp (parser, 0, 0, 1))) goto RELEASE_FUN_AND_RETURN_ERROR;

  if (!boolector_is_args (parser->btor, args))
  {
    boolector_release (parser->btor, args);
    btor_perr_btor (parser,
                    "apply only takes a function and arguments as children");
    goto RELEASE_FUN_AND_RETURN_ERROR;
  }

  if (boolector_is_array_var (parser->btor, fun)
      && boolector_get_args_arity (parser->btor, args) != 1)
  {
    boolector_release (parser->btor, args);
    btor_perr_btor (parser, "invalid number of arguments for apply");
    goto RELEASE_FUN_AND_RETURN_ERROR;
  }

  if (!boolector_is_array_var (parser->btor, fun)
      && boolector_get_fun_arity (parser->btor, fun)
             != boolector_get_args_arity (parser->btor, args))
  {
    boolector_release (parser->btor, args);
    btor_perr_btor (parser, "invalid number of arguments for apply");
    goto RELEASE_FUN_AND_RETURN_ERROR;
  }

  res = boolector_apply_args (parser->btor, args, fun);
  boolector_release (parser->btor, fun);
  boolector_release (parser->btor, args);

  return res;
}

static BoolectorNode *
parse_args (BtorBTORParser *parser, int len)
{
  int i;
  BoolectorNode *res, *arg;
  BoolectorNodePtrStack args;

  BTOR_INIT_STACK (args);
  i = len;
  while (i > 0)
  {
    if (parse_space (parser)) return 0;

    if (!(arg = parse_exp (parser, 0, 0, 1))) return 0;

    BTOR_PUSH_STACK (parser->mem, args, arg);
    i -= boolector_get_width (parser->btor, arg);
  }

  res = boolector_args (parser->btor, BTOR_COUNT_STACK (args), args.start);

  while (!BTOR_EMPTY_STACK (args))
  {
    arg = BTOR_POP_STACK (args);
    boolector_release (parser->btor, arg);
  }
  BTOR_RELEASE_STACK (parser->mem, args);

  return res;
}

static BoolectorNode *
parse_ext (BtorBTORParser *parser, int len, Extend f)
{
  BoolectorNode *res, *arg;
  int alen, elen;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0, 0, 1))) return 0;

  alen = boolector_get_width (parser->btor, arg);

  if (parse_space (parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    boolector_release (parser->btor, arg);
    return 0;
  }

  if (parse_non_negative_int (parser, &elen)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (alen + elen != len)
  {
    (void) btor_perr_btor (parser,
                           "argument length of %d plus %d does not match %d",
                           alen,
                           elen,
                           len);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = f (parser->btor, arg, elen);
  assert (boolector_get_width (parser->btor, res) == len);
  boolector_release (parser->btor, arg);

  return res;
}

static BoolectorNode *
parse_sext (BtorBTORParser *parser, int len)
{
  return parse_ext (parser, len, boolector_sext);
}

static BoolectorNode *
parse_uext (BtorBTORParser *parser, int len)
{
  return parse_ext (parser, len, boolector_uext);
}

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
btor_new_btor_parser (Btor *btor, BtorParseOpt *opts)
{
  BtorMemMgr *mem = btor_new_mem_mgr ();
  BtorBTORParser *res;

  (void) opts->incremental;  // TODO what about incremental?
  (void) opts->need_model;   // TODO use at least this

  assert (opts->verbosity >= -1);

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
  new_parser (res, parse_inc, "inc");
  new_parser (res, parse_dec, "dec");
  new_parser (res, parse_ne, "ne");
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
  new_parser (res, parse_param, "param");
  new_parser (res, parse_lambda, "lambda");
  new_parser (res, parse_apply, "apply");
  new_parser (res, parse_args, "args");

  res->verbosity = opts->verbosity;

  return res;
}

static void
btor_delete_btor_parser (BtorBTORParser *parser)
{
  BoolectorNode *e;
  BtorMemMgr *mm;
  int i;

  for (i = 0; i < BTOR_COUNT_STACK (parser->exps); i++)
    if ((e = parser->exps.start[i]))
      boolector_release (parser->btor, parser->exps.start[i]);

  mm = parser->mem;

  BTOR_RELEASE_STACK (mm, parser->exps);
  BTOR_RELEASE_STACK (mm, parser->info);
  BTOR_RELEASE_STACK (mm, parser->inputs);
  BTOR_RELEASE_STACK (mm, parser->outputs);
  BTOR_RELEASE_STACK (mm, parser->regs);
  BTOR_RELEASE_STACK (mm, parser->lambdas);
  BTOR_RELEASE_STACK (mm, parser->params);

  BTOR_RELEASE_STACK (mm, parser->op);
  BTOR_RELEASE_STACK (mm, parser->constant);
  BTOR_RELEASE_STACK (mm, parser->symbol);

  BTOR_DELETEN (mm, parser->parsers, SIZE_PARSERS);
  BTOR_DELETEN (mm, parser->ops, SIZE_PARSERS);

  btor_freestr (mm, parser->error);
  BTOR_DELETE (mm, parser);
  btor_delete_mem_mgr (mm);
}

static const char *
check_params_bound (BtorBTORParser *parser)
{
  assert (parser);

  int i;
  BoolectorNode *param;

  for (i = 0; i < BTOR_COUNT_STACK (parser->params); i++)
  {
    param = parser->params.start[i];
    assert (boolector_is_param (parser->btor, param));

    if (!boolector_is_bound_param (parser->btor, param))
    {
      assert (boolector_get_symbol (parser->btor, param));
      return btor_perr_btor (parser,
                             "param '%s' not bound to any lambda expression",
                             boolector_get_symbol (parser->btor, param));
    }
  }

  return 0;
}

#if 0
static const char *
check_lambdas_consistent (BtorBTORParser * parser)
{
  assert (parser);

  int i;
  BoolectorNode *cur, *lambda;
  BoolectorNodePtrStack stack;
  BoolectorNodePtrStack unmark;

  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (unmark);

  while (!BTOR_EMPTY_STACK (parser->lambdas))
    {
      lambda = BTOR_POP_STACK (parser->lambdas);
      assert (BTOR_IS_REGULAR_NODE (lambda));
      assert (BTOR_IS_LAMBDA_NODE (lambda));

      if (BTOR_IS_NESTED_LAMBDA_NODE (lambda)
	  && !BTOR_IS_FIRST_NESTED_LAMBDA (lambda))
	continue;

      assert (BTOR_EMPTY_STACK (stack));
      assert (BTOR_EMPTY_STACK (unmark));
      BTOR_PUSH_STACK (parser->mem, stack, lambda);

      while (!BTOR_EMPTY_STACK (stack))
	{
	  cur = BTOR_POP_STACK (stack);
	  assert (BTOR_IS_REGULAR_NODE (cur));

	  if (btor_is_param_exp (parser->btor, cur) && !cur->mark)
	    {
	      BTOR_RELEASE_STACK (parser->mem, stack);
	      BTOR_RELEASE_STACK (parser->mem, unmark);

	      return btor_perr_btor (parser,
		  "invalid scope for param '%d'",
		  cur->symbol ? atoi (cur->symbol) : cur->id);
	    }

	  if (cur->mark)
	    continue;

	  cur->mark = 1;
	  BTOR_PUSH_STACK (parser->mem, unmark, cur);

	  if (boolector_is_fun (parser->btor, cur))
	    {
	      BTOR_REAL_ADDR_NODE (cur->e[0])->mark = 1;
	      BTOR_PUSH_STACK (parser->mem, unmark,
			       BTOR_REAL_ADDR_NODE (cur->e[0]));
	      BTOR_PUSH_STACK (parser->mem, stack,
			       BTOR_REAL_ADDR_NODE (cur->e[1]));
	    }
	  else
	    {
	      for (i = 0; i < cur->arity; i++)
		if (BTOR_REAL_ADDR_NODE (cur->e[i])->parameterized)
		  BTOR_PUSH_STACK (parser->mem, stack,
				   BTOR_REAL_ADDR_NODE (cur->e[i]));
	    }
	}

      while (!BTOR_EMPTY_STACK (unmark))
	{
	  cur = BTOR_POP_STACK (unmark);
	  assert (BTOR_IS_REGULAR_NODE (cur));
	  assert (cur->mark);
	  cur->mark = 0;
	}
    }

  BTOR_RELEASE_STACK (parser->mem, stack);
  BTOR_RELEASE_STACK (parser->mem, unmark);

  return 0;
}
#endif

/* Note: we need prefix in case of stdin as input (also applies to compressed
 * input files). */
static const char *
btor_parse_btor_parser (BtorBTORParser *parser,
                        BtorCharStack *prefix,
                        FILE *file,
                        const char *name,
                        BtorParseResult *res)
{
  BtorOpParser op_parser;
  int ch, len;
  BoolectorNode *e;

  assert (name);
  assert (file);

  if (parser->verbosity > 0) btor_msg_btor ("parsing %s", name);

  parser->nprefix = 0;
  parser->prefix  = prefix;
  parser->file    = file;
  parser->name    = name;
  parser->lineno  = 1;
  parser->saved   = 0;

  BTOR_INIT_STACK (parser->lambdas);
  BTOR_INIT_STACK (parser->params);

  BTOR_CLR (res);

NEXT:
  assert (!parser->error);
  ch = btor_nextch_btor (parser);
  if (isspace (ch)) /* also skip empty lines */
    goto NEXT;

  if (ch == EOF)
  {
  DONE:

    if (res)
    {
      if (check_params_bound (parser)) return parser->error;

      //	  if (check_lambdas_consistent (parser))
      //	    return parser->error;

      if (parser->found_lambdas && parser->found_aeq)
      {
        btor_perr_btor (parser, "extensionality with lambdas is not supported");
        return parser->error;
      }

      if (parser->found_arrays || parser->found_lambdas)
        res->logic = BTOR_LOGIC_QF_AUFBV;
      else
        res->logic = BTOR_LOGIC_QF_BV;
      res->status = BOOLECTOR_UNKNOWN;

      res->ninputs = BTOR_COUNT_STACK (parser->inputs);
      res->inputs  = parser->inputs.start;

      res->noutputs = BTOR_COUNT_STACK (parser->outputs);
      res->outputs  = parser->outputs.start;

      if (parser->verbosity > 0)
      {
        btor_msg_btor ("parsed %d inputs", res->ninputs);
        btor_msg_btor ("parsed %d outputs", res->noutputs);
      }
    }

    return 0;
  }

  if (ch == ';') /* skip comments */
  {
  COMMENTS:
    while ((ch = btor_nextch_btor (parser)) != '\n')
      if (ch == EOF) goto DONE;

    goto NEXT;
  }

  if (!isdigit (ch)) return btor_perr_btor (parser, "expected ';' or digit");

  btor_savech_btor (parser, ch);

  if (parse_positive_int (parser, &parser->idx)) return parser->error;

  while (BTOR_COUNT_STACK (parser->exps) <= parser->idx)
  {
    Info info;
    memset (&info, 0, sizeof info);
    BTOR_PUSH_STACK (parser->mem, parser->info, info);
    BTOR_PUSH_STACK (parser->mem, parser->exps, 0);
  }

  if (parser->exps.start[parser->idx])
    return btor_perr_btor (parser, "'%d' defined twice", parser->idx);

  if (parse_space (parser)) return parser->error;

  assert (BTOR_EMPTY_STACK (parser->op));
  while (!isspace (ch = btor_nextch_btor (parser)) && ch != EOF)
    BTOR_PUSH_STACK (parser->mem, parser->op, ch);

  BTOR_PUSH_STACK (parser->mem, parser->op, 0);
  BTOR_RESET_STACK (parser->op);
  btor_savech_btor (parser, ch);

  if (parse_space (parser)) return parser->error;

  if (parse_positive_int (parser, &len)) return parser->error;

  if (!(op_parser = find_parser (parser, parser->op.start)))
    return btor_perr_btor (parser, "invalid operator '%s'", parser->op.start);

  if (!(e = op_parser (parser, len)))
  {
    assert (parser->error);
    return parser->error;
  }

  assert (boolector_get_width (parser->btor, e) == len);
  parser->exps.start[parser->idx] = e;

SKIP:
  ch = btor_nextch_btor (parser);
  if (ch == ' ' || ch == '\t' || ch == '\r') goto SKIP;

  if (ch == ';') goto COMMENTS; /* ... and force new line */

  if (ch != '\n') return btor_perr_btor (parser, "expected new line");

  goto NEXT;
}

static BtorParserAPI static_btor_btor_parser_api = {
    (BtorInitParser) btor_new_btor_parser,
    (BtorResetParser) btor_delete_btor_parser,
    (BtorParse) btor_parse_btor_parser,
};

const BtorParserAPI *
btor_btor_parser_api ()
{
  return &static_btor_btor_parser_api;
}
