/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *  Copyright (C) 2013-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorbv.h"
#include "btormsg.h"
#include "btorparse.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#include "btorbtor.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

void boolector_set_btor_id (Btor *, BoolectorNode *, int32_t);

/*------------------------------------------------------------------------*/

typedef struct BtorBTORParser BtorBTORParser;

typedef BoolectorNode *(*BtorOpParser) (BtorBTORParser *, uint32_t width);
typedef BoolectorNode *(*Unary) (Btor *, BoolectorNode *);
typedef BoolectorNode *(*Binary) (Btor *, BoolectorNode *, BoolectorNode *);
typedef BoolectorNode *(*Shift) (Btor *, BoolectorNode *, BoolectorNode *);
typedef BoolectorNode *(*Extend) (Btor *, BoolectorNode *, uint32_t);

#define SIZE_PARSERS 128

typedef struct Info Info;

struct Info
{
  uint32_t var : 1;
  uint32_t array : 1;
};

BTOR_DECLARE_STACK (BtorInfo, Info);
BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

struct BtorBTORParser
{
  BtorMemMgr *mem;
  Btor *btor;

  uint32_t nprefix;
  BtorCharStack *prefix;
  FILE *infile;
  const char *infile_name;
  uint32_t lineno;
  bool saved;
  int32_t saved_char;
  char *error;

  BoolectorNodePtrStack exps;
  BtorInfoStack info;

  BoolectorNodePtrStack regs;
  BoolectorNodePtrStack lambdas;
  BoolectorNodePtrStack params;

  BtorCharStack op;
  BtorCharStack constant;
  BtorCharStack symbol;

  BtorOpParser *parsers;
  const char **ops;

  uint32_t idx;

  bool found_arrays;
  bool found_lambdas;
};

/*------------------------------------------------------------------------*/

static const char *
perr_btor (BtorBTORParser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start (ap, fmt);
    bytes = btor_mem_parse_error_msg_length (parser->infile_name, fmt, ap);
    va_end (ap);

    va_start (ap, fmt);
    parser->error = btor_mem_parse_error_msg (
        parser->mem, parser->infile_name, parser->lineno, 0, fmt, ap, bytes);
    va_end (ap);
  }

  return parser->error;
}

/*------------------------------------------------------------------------*/

static uint32_t btor_primes_btor[4] = {
    111130391, 22237357, 33355519, 444476887};

#define BTOR_PRIMES_BTOR \
  ((sizeof btor_primes_btor) / sizeof btor_primes_btor[0])

static uint32_t
hash_op (const char *str, uint32_t salt)
{
  uint32_t i, res;
  const char *p;

  assert (salt < BTOR_PRIMES_BTOR);

  res = 0;
  i   = salt;
  for (p = str; *p; p++)
  {
    res += btor_primes_btor[i++] * (uint32_t) *p;
    if (i == BTOR_PRIMES_BTOR) i = 0;
  }

  res &= SIZE_PARSERS - 1;

  return res;
}

/*------------------------------------------------------------------------*/

static int32_t
nextch_btor (BtorBTORParser *parser)
{
  int32_t ch;

  if (parser->saved)
  {
    ch            = parser->saved_char;
    parser->saved = false;
  }
  else if (parser->prefix
           && parser->nprefix < BTOR_COUNT_STACK (*parser->prefix))
  {
    ch = parser->prefix->start[parser->nprefix++];
  }
  else
    ch = getc (parser->infile);

  if (ch == '\n') parser->lineno++;

  return ch;
}

static void
savech_btor (BtorBTORParser *parser, int32_t ch)
{
  assert (!parser->saved);

  parser->saved_char = ch;
  parser->saved      = true;

  if (ch == '\n')
  {
    assert (parser->lineno > 1);
    parser->lineno--;
  }
}

static const char *
parse_non_negative_int (BtorBTORParser *parser, uint32_t *res_ptr)
{
  int32_t res, ch;

  ch = nextch_btor (parser);
  if (!isdigit (ch)) return perr_btor (parser, "expected digit");

  if (ch == '0')
  {
    res = 0;
    ch  = nextch_btor (parser);
    if (isdigit (ch)) return perr_btor (parser, "digit after '0'");
  }
  else
  {
    res = ch - '0';

    while (isdigit (ch = nextch_btor (parser))) res = 10 * res + (ch - '0');
  }

  savech_btor (parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_positive_int (BtorBTORParser *parser, uint32_t *res_ptr)
{
  int32_t res, ch;

  ch = nextch_btor (parser);
  if (!isdigit (ch)) return perr_btor (parser, "expected digit");

  if (ch == '0') return perr_btor (parser, "expected non zero digit");

  res = ch - '0';

  while (isdigit (ch = nextch_btor (parser))) res = 10 * res + (ch - '0');

  savech_btor (parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_non_zero_int (BtorBTORParser *parser, int32_t *res_ptr)
{
  int32_t res, sign, ch;

  ch = nextch_btor (parser);

  if (ch == '-')
  {
    sign = -1;
    ch   = nextch_btor (parser);

    if (!isdigit (ch) || ch == '0')
      return perr_btor (parser, "expected non zero digit after '-'");
  }
  else
  {
    sign = 1;
    if (!isdigit (ch) || ch == '0')
      return perr_btor (parser, "expected non zero digit or '-'");
  }

  res = ch - '0';

  while (isdigit (ch = nextch_btor (parser))) res = 10 * res + (ch - '0');

  savech_btor (parser, ch);

  res *= sign;
  *res_ptr = res;

  return 0;
}

static BoolectorNode *
parse_exp (BtorBTORParser *parser,
           uint32_t expected_width,
           bool can_be_array,
           bool can_be_inverted,
           int32_t *rlit)
{
  size_t idx;
  int32_t lit;
  uint32_t width_res;
  const char *err_msg;
  BoolectorNode *res;

  lit = 0;
  err_msg = parse_non_zero_int (parser, &lit);
  if (rlit) *rlit = lit;
  if (err_msg) return 0;

  if (!can_be_inverted && lit < 0)
  {
    (void) perr_btor (parser, "positive literal expected");
    return 0;
  }

  idx = abs (lit);
  assert (idx);

  if (idx >= BTOR_COUNT_STACK (parser->exps)
      || !(res = parser->exps.start[idx]))
  {
    (void) perr_btor (parser, "literal '%d' undefined", lit);
    return 0;
  }

  if (boolector_is_param (parser->btor, res)
      && boolector_is_bound_param (parser->btor, res))
  {
    (void) perr_btor (
        parser, "param '%d' cannot be used outside of its defined scope", lit);
    return 0;
  }

  if (!can_be_array && boolector_is_array (parser->btor, res))
  {
    (void) perr_btor (
        parser, "literal '%d' refers to an unexpected array expression", lit);
    return 0;
  }

  if (expected_width)
  {
    width_res = boolector_get_width (parser->btor, res);

    if (expected_width != width_res)
    {
      (void) perr_btor (parser,
                        "literal '%d' has width '%d' but expected '%d'",
                        lit,
                        width_res,
                        expected_width);

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
  int32_t ch;

  ch = nextch_btor (parser);
  if (ch != ' ' && ch != '\t')
    return perr_btor (parser, "expected space or tab");

SKIP:
  ch = nextch_btor (parser);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (!ch) return perr_btor (parser, "unexpected character");

  savech_btor (parser, ch);

  return 0;
}

static int32_t
parse_symbol (BtorBTORParser *parser)
{
  int32_t ch;

  while ((ch = nextch_btor (parser)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  {
  UNEXPECTED_EOF:
    (void) perr_btor (parser, "unexpected EOF");
    return 0;
  }

  assert (BTOR_EMPTY_STACK (parser->symbol));

  if (ch != '\n')
  {
    BTOR_PUSH_STACK (parser->symbol, ch);

    while (!isspace (ch = nextch_btor (parser)))
    {
      if (!isprint (ch)) perr_btor (parser, "invalid character");
      if (ch == EOF) goto UNEXPECTED_EOF;
      BTOR_PUSH_STACK (parser->symbol, ch);
    }
  }

  savech_btor (parser, ch);
  BTOR_PUSH_STACK (parser->symbol, 0);
  BTOR_RESET_STACK (parser->symbol);
  return 1;
}

static BoolectorNode *
parse_var (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  BoolectorSort s;

  if (!parse_symbol (parser)) return 0;

  s   = boolector_bitvec_sort (parser->btor, width);
  res = boolector_var (
      parser->btor, s, parser->symbol.start[0] ? parser->symbol.start : 0);
  boolector_release_sort (parser->btor, s);
  boolector_set_btor_id (parser->btor, res, parser->idx);
  parser->info.start[parser->idx].var = 1;
  return res;
}

static BoolectorNode *
parse_param (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  BoolectorSort s;

  if (!parse_symbol (parser)) return 0;

  s   = boolector_bitvec_sort (parser->btor, width);
  res = boolector_param (
      parser->btor, s, parser->symbol.start[0] ? parser->symbol.start : 0);
  boolector_release_sort (parser->btor, s);
  BTOR_PUSH_STACK (parser->params, res);

  return res;
}

static BoolectorNode *
parse_param_exp (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;

  res = parse_exp (parser, width, false, false, 0);
  if (!res) return 0;

  if (boolector_is_param (parser->btor, res)) return res;

  (void) perr_btor (parser, "expected parameter");
  boolector_release (parser->btor, res);

  return 0;
}

static BoolectorNode *
parse_array (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  BoolectorSort s, is, es;
  uint32_t idx_width;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idx_width)) return 0;

  if (!parse_symbol (parser)) return 0;

  is  = boolector_bitvec_sort (parser->btor, idx_width);
  es  = boolector_bitvec_sort (parser->btor, width);
  s   = boolector_array_sort (parser->btor, is, es);
  res = boolector_array (
      parser->btor, s, parser->symbol.start[0] ? parser->symbol.start : 0);
  boolector_release_sort (parser->btor, is);
  boolector_release_sort (parser->btor, es);
  boolector_release_sort (parser->btor, s);
  boolector_set_btor_id (parser->btor, res, parser->idx);
  parser->info.start[parser->idx].array = 1;
  parser->found_arrays = true;
  return res;
}

static BoolectorNode *
parse_array_exp (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;

  res = parse_exp (parser, width, true, false, 0);
  if (!res) return 0;

  if (boolector_is_array (parser->btor, res)) return res;

  (void) perr_btor (parser, "expected array expression");
  boolector_release (parser->btor, res);

  return 0;
}

static BoolectorNode *
parse_fun_exp (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;

  res = parse_exp (parser, width, true, false, 0);
  if (!res) return 0;

  if (boolector_is_fun (parser->btor, res)) return res;

  (void) perr_btor (parser, "expected function expression");
  boolector_release (parser->btor, res);

  return 0;
}

static BoolectorNode *
parse_const (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  int32_t ch;
  uint32_t cwidth;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));
  while (!isspace (ch = nextch_btor (parser)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) perr_btor (parser, "expected '0' or '1'");
      return 0;
    }

    BTOR_PUSH_STACK (parser->constant, ch);
  }

  savech_btor (parser, ch);
  cwidth = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  if (cwidth != width)
  {
    (void) perr_btor (parser,
                      "binary constant '%s' exceeds bit width %d",
                      parser->constant.start,
                      width);
    return 0;
  }

  res = boolector_const (parser->btor, parser->constant.start);

  return res;
}

static BoolectorNode *
parse_consth (BtorBTORParser *parser, uint32_t width)
{
  int32_t ch;
  uint32_t cwidth;
  char *tmp, *ext;
  BtorBitVector *tmpbv, *extbv;
  BoolectorNode *res;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));

  while (!isspace (ch = nextch_btor (parser)) && ch != EOF && ch != ';')
  {
    if (!isxdigit (ch))
    {
      (void) perr_btor (parser, "expected hexidecimal digit");
      return 0;
    }

    BTOR_PUSH_STACK (parser->constant, ch);
  }

  savech_btor (parser, ch);

  cwidth = BTOR_COUNT_STACK (parser->constant);
  BTOR_PUSH_STACK (parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  tmp =
      btor_util_hex_to_bin_str_n (parser->mem, parser->constant.start, cwidth);
  cwidth = strlen (tmp);

  if (cwidth > width)
  {
    (void) perr_btor (parser,
                      "hexadecimal constant '%s' exceeds bit width %d",
                      parser->constant.start,
                      width);
    btor_mem_freestr (parser->mem, tmp);
    return 0;
  }

  if (cwidth < width)
  {
    tmpbv = 0;
    if (!strcmp (tmp, ""))
      extbv = btor_bv_new (parser->mem, width - cwidth);
    else
    {
      tmpbv = btor_bv_char_to_bv (parser->mem, tmp);
      extbv = btor_bv_uext (parser->mem, tmpbv, width - cwidth);
    }
    ext = btor_bv_to_char (parser->mem, extbv);
    btor_mem_freestr (parser->mem, tmp);
    btor_bv_free (parser->mem, extbv);
    if (tmpbv) btor_bv_free (parser->mem, tmpbv);
    tmp = ext;
  }

  assert (width == strlen (tmp));
  res = boolector_const (parser->btor, tmp);
  btor_mem_freestr (parser->mem, tmp);

  assert (boolector_get_width (parser->btor, res) == width);

  return res;
}

static BoolectorNode *
parse_constd (BtorBTORParser *parser, uint32_t width)
{
  int32_t ch;
  uint32_t cwidth;
  char *tmp, *ext;
  BtorBitVector *tmpbv, *extbv;
  BoolectorNode *res;

  if (parse_space (parser)) return 0;

  assert (BTOR_EMPTY_STACK (parser->constant));

  ch = nextch_btor (parser);
  if (!isdigit (ch))
  {
    (void) perr_btor (parser, "expected digit");
    return 0;
  }

  BTOR_PUSH_STACK (parser->constant, ch);

  if (ch == '0')
  {
    ch = nextch_btor (parser);

    if (isdigit (ch))
    {
      (void) perr_btor (parser, "digit after '0'");
      return 0;
    }

    tmp = btor_mem_strdup (parser->mem, "");
  }
  else
  {
    while (isdigit (ch = nextch_btor (parser)))
      BTOR_PUSH_STACK (parser->constant, ch);

    cwidth = BTOR_COUNT_STACK (parser->constant);

    tmp = btor_util_dec_to_bin_str_n (
        parser->mem, parser->constant.start, cwidth);
  }

  BTOR_PUSH_STACK (parser->constant, 0);
  BTOR_RESET_STACK (parser->constant);

  savech_btor (parser, ch);

  cwidth = strlen (tmp);
  if (cwidth > width)
  {
    (void) perr_btor (parser,
                      "decimal constant '%s' exceeds bit width %d",
                      parser->constant.start,
                      width);
    btor_mem_freestr (parser->mem, tmp);
    return 0;
  }

  if (cwidth < width)
  {
    tmpbv = 0;
    if (!strcmp (tmp, ""))
      extbv = btor_bv_new (parser->mem, width - cwidth);
    else
    {
      tmpbv = btor_bv_char_to_bv (parser->mem, tmp);
      extbv = btor_bv_uext (parser->mem, tmpbv, width - cwidth);
    }
    ext = btor_bv_to_char (parser->mem, extbv);
    btor_mem_freestr (parser->mem, tmp);
    btor_bv_free (parser->mem, extbv);
    if (tmpbv) btor_bv_free (parser->mem, tmpbv);
    tmp = ext;
  }

  assert (width == strlen (tmp));
  res = boolector_const (parser->btor, tmp);
  btor_mem_freestr (parser->mem, tmp);

  assert (boolector_get_width (parser->btor, res) == width);

  return res;
}

static BoolectorNode *
parse_zero (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  BoolectorSort s;

  s   = boolector_bitvec_sort (parser->btor, width);
  res = boolector_zero (parser->btor, s);
  boolector_release_sort (parser->btor, s);
  return res;
}

static BoolectorNode *
parse_one (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  BoolectorSort s;

  s   = boolector_bitvec_sort (parser->btor, width);
  res = boolector_one (parser->btor, s);
  boolector_release_sort (parser->btor, s);
  return res;
}

static BoolectorNode *
parse_ones (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res;
  BoolectorSort s;

  s   = boolector_bitvec_sort (parser->btor, width);
  res = boolector_ones (parser->btor, s);
  boolector_release_sort (parser->btor, s);
  return res;
}

static BoolectorNode *
parse_root (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *res, *tmp;

  if (parse_space (parser)) return 0;
  if (!(res = parse_exp (parser, width, false, true, 0))) return 0;
  if (width > 1)
  {
    tmp = res;
    res = boolector_redor (parser->btor, tmp);
    boolector_release (parser->btor, tmp);
  }
  boolector_assert (parser->btor, res);
  return res;
}

static BoolectorNode *
parse_unary (BtorBTORParser *parser, uint32_t width, Unary f)
{
  assert (width);

  BoolectorNode *tmp, *res;

  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, width, false, true, 0))) return 0;

  res = f (parser->btor, tmp);
  boolector_release (parser->btor, tmp);
  assert (boolector_get_width (parser->btor, res) == width);

  return res;
}

static BoolectorNode *
parse_not (BtorBTORParser *parser, uint32_t width)
{
  return parse_unary (parser, width, boolector_not);
}

static BoolectorNode *
parse_neg (BtorBTORParser *parser, uint32_t width)
{
  return parse_unary (parser, width, boolector_neg);
}

static BoolectorNode *
parse_inc (BtorBTORParser *parser, uint32_t width)
{
  return parse_unary (parser, width, boolector_inc);
}

static BoolectorNode *
parse_dec (BtorBTORParser *parser, uint32_t width)
{
  return parse_unary (parser, width, boolector_dec);
}

static BoolectorNode *
parse_proxy (BtorBTORParser *parser, uint32_t width)
{
  return parse_unary (parser, width, boolector_copy);
}

static BoolectorNode *
parse_redunary (BtorBTORParser *parser, uint32_t width, Unary f)
{
  assert (width == 1);

  BoolectorNode *tmp, *res;

  (void) width;

  if (parse_space (parser)) return 0;

  if (!(tmp = parse_exp (parser, 0, false, true, 0))) return 0;

  if (boolector_get_width (parser->btor, tmp) == 1)
  {
    (void) perr_btor (parser, "argument of reduction operation of width 1");
    boolector_release (parser->btor, tmp);
    return 0;
  }

  res = f (parser->btor, tmp);
  boolector_release (parser->btor, tmp);
  assert (boolector_get_width (parser->btor, res) == 1);

  return res;
}

static BoolectorNode *
parse_redand (BtorBTORParser *parser, uint32_t width)
{
  return parse_redunary (parser, width, boolector_redand);
}

static BoolectorNode *
parse_redor (BtorBTORParser *parser, uint32_t width)
{
  return parse_redunary (parser, width, boolector_redor);
}

static BoolectorNode *
parse_redxor (BtorBTORParser *parser, uint32_t width)
{
  return parse_redunary (parser, width, boolector_redxor);
}

static BoolectorNode *
parse_binary (BtorBTORParser *parser, uint32_t width, Binary f)
{
  assert (width);

  BoolectorNode *l, *r, *res;

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, width, false, true, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, width, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  res = f (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == width);

  return res;
}

static BoolectorNode *
parse_add (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_add);
}

static BoolectorNode *
parse_and (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_and);
}

static BoolectorNode *
parse_smod (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_smod);
}

static BoolectorNode *
parse_srem (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_srem);
}

static BoolectorNode *
parse_mul (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_mul);
}

static BoolectorNode *
parse_sub (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_sub);
}

static BoolectorNode *
parse_udiv (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_udiv);
}

static BoolectorNode *
parse_urem (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_urem);
}

static BoolectorNode *
parse_xor (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_xor);
}

static BoolectorNode *
parse_xnor (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_xnor);
}

static BoolectorNode *
parse_or (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_or);
}

static BoolectorNode *
parse_nor (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_nor);
}

static BoolectorNode *
parse_nand (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_nand);
}

static BoolectorNode *
parse_sdiv (BtorBTORParser *parser, uint32_t width)
{
  return parse_binary (parser, width, boolector_sdiv);
}

static BoolectorNode *
parse_logical (BtorBTORParser *parser, uint32_t width, Binary f)
{
  BoolectorNode *l, *r, *res;

  if (width != 1)
  {
    (void) perr_btor (parser, "logical operator bit width '%d'", width);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, false, true, 0))) return 0;

  if (boolector_get_width (parser->btor, l) != 1)
  {
  BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN:
    (void) perr_btor (parser, "expected argument of bit width '1'");
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (parse_space (parser)) goto RELEASE_L_AND_RETURN_ERROR;

  if (!(r = parse_exp (parser, 0, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

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
parse_implies (BtorBTORParser *parser, uint32_t width)
{
  return parse_logical (parser, width, boolector_implies);
}

static BoolectorNode *
parse_iff (BtorBTORParser *parser, uint32_t width)
{
  return parse_logical (parser, width, boolector_iff);
}

static BoolectorNode *
parse_compare_and_overflow (BtorBTORParser *parser,
                            uint32_t width,
                            Binary f,
                            bool can_be_array)
{
  BoolectorNode *l, *r, *res;

  if (width != 1)
  {
    (void) perr_btor (
        parser, "comparison or overflow operator returns %d bits", width);
    return 0;
  }

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, can_be_array, true, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, can_be_array, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  if (!boolector_is_equal_sort (parser->btor, l, r))
  {
    (void) perr_btor (parser, "operands have different sort");
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
      (void) perr_btor (parser, "first operand is array and second not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }

    if (!boolector_is_array (parser->btor, l)
        && boolector_is_array (parser->btor, r))
    {
      (void) perr_btor (parser, "second operand is array and first not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }
  }

  res = f (parser->btor, l, r);

  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);

  assert (boolector_get_width (parser->btor, res) == 1);

  return res;
}

static BoolectorNode *
parse_eq (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_eq, 1);
}

static BoolectorNode *
parse_ne (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_ne, 1);
}

static BoolectorNode *
parse_sgt (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_sgt, 0);
}

static BoolectorNode *
parse_sgte (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_sgte, 0);
}

static BoolectorNode *
parse_slt (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_slt, 0);
}

static BoolectorNode *
parse_slte (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_slte, 0);
}

static BoolectorNode *
parse_ugt (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_ugt, 0);
}

static BoolectorNode *
parse_ugte (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_ugte, 0);
}

static BoolectorNode *
parse_ult (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_ult, 0);
}

static BoolectorNode *
parse_ulte (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_ulte, 0);
}

static BoolectorNode *
parse_saddo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_saddo, 0);
}

static BoolectorNode *
parse_ssubo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_ssubo, 0);
}

static BoolectorNode *
parse_smulo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_smulo, 0);
}

static BoolectorNode *
parse_sdivo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_sdivo, 0);
}

static BoolectorNode *
parse_uaddo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_uaddo, 0);
}

static BoolectorNode *
parse_usubo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_usubo, 0);
}

static BoolectorNode *
parse_umulo (BtorBTORParser *parser, uint32_t width)
{
  return parse_compare_and_overflow (parser, width, boolector_umulo, 0);
}

static BoolectorNode *
parse_concat (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *l, *r, *res;
  uint32_t lwidth, rwidth;

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, 0, false, true, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  lwidth = boolector_get_width (parser->btor, l);
  rwidth = boolector_get_width (parser->btor, r);

  if (lwidth + rwidth != width)
  {
    (void) perr_btor (parser,
                      "operands widths %d and %d do not add up to %d",
                      lwidth,
                      rwidth,
                      width);

    boolector_release (parser->btor, r);
    boolector_release (parser->btor, l);
    return 0;
  }

  res = boolector_concat (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == width);

  return res;
}

static BoolectorNode *
parse_shift (BtorBTORParser *parser, uint32_t width, Shift f)
{
  BoolectorNode *l, *r, *res, *tmp;
  int32_t lit;
  uint32_t rwidth, rw;

  for (rwidth = 1; rwidth <= 30u && width != (1u << rwidth); rwidth++)
    ;

  if (parse_space (parser)) return 0;

  if (!(l = parse_exp (parser, width, false, true, &lit))) return 0;

  if (parse_space (parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    boolector_release (parser->btor, l);
    return 0;
  }

  if (!(r = parse_exp (parser, 0, false, true, &lit)))
    goto RELEASE_L_AND_RETURN_ERROR;

  rw = boolector_get_width (parser->btor, r);
  if (width != rw)
  {
    if (btor_util_is_power_of_2 (width))
    {
      if (rw != btor_util_log_2 (width))
      {
        (void) perr_btor (parser,
                          "literal '%d' has width '%d' but expected '%d'",
                          lit,
                          rw,
                          btor_util_log_2 (width));
        boolector_release (parser->btor, l);
        boolector_release (parser->btor, r);
        return 0;
      }
      tmp = boolector_uext (parser->btor, r, width - rw);
      boolector_release (parser->btor, r);
      r = tmp;
    }
    else
    {
      (void) perr_btor (parser,
                        "literal '%d' has width '%d' but expected '%d'",
                        lit,
                        rw,
                        width);
      boolector_release (parser->btor, l);
      boolector_release (parser->btor, r);
      return 0;
    }
  }
  res = f (parser->btor, l, r);
  boolector_release (parser->btor, r);
  boolector_release (parser->btor, l);
  assert (boolector_get_width (parser->btor, res) == width);

  return res;
}

static BoolectorNode *
parse_rol (BtorBTORParser *parser, uint32_t width)
{
  return parse_shift (parser, width, boolector_rol);
}

static BoolectorNode *
parse_ror (BtorBTORParser *parser, uint32_t width)
{
  return parse_shift (parser, width, boolector_ror);
}

static BoolectorNode *
parse_sll (BtorBTORParser *parser, uint32_t width)
{
  return parse_shift (parser, width, boolector_sll);
}

static BoolectorNode *
parse_sra (BtorBTORParser *parser, uint32_t width)
{
  return parse_shift (parser, width, boolector_sra);
}

static BoolectorNode *
parse_srl (BtorBTORParser *parser, uint32_t width)
{
  return parse_shift (parser, width, boolector_srl);
}

static BoolectorNode *
parse_cond (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *c, *t, *e, *res;

  if (parse_space (parser)) return 0;

  if (!(c = parse_exp (parser, 1, false, true, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    boolector_release (parser->btor, c);
    return 0;
  }

  if (!(t = parse_exp (parser, width, false, true, 0)))
    goto RELEASE_C_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    boolector_release (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp (parser, width, false, true, 0)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  res = boolector_cond (parser->btor, c, t, e);
  boolector_release (parser->btor, e);
  boolector_release (parser->btor, t);
  boolector_release (parser->btor, c);

  return res;
}

static BoolectorNode *
parse_acond (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *c, *t, *e, *res;
  uint32_t idxwidth;

  idxwidth = 0;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idxwidth)) return 0;

  if (parse_space (parser)) return 0;

  if (!(c = parse_exp (parser, 1, false, true, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    boolector_release (parser->btor, c);
    return 0;
  }

  if (!(t = parse_array_exp (parser, width))) goto RELEASE_C_AND_RETURN_ERROR;

  if (idxwidth != boolector_get_index_width (parser->btor, t))
  {
    (void) perr_btor (parser, "mismatch of index bit width of 'then' array");
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    boolector_release (parser->btor, t);
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (parse_space (parser)) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (!(e = parse_array_exp (parser, width)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (idxwidth != boolector_get_index_width (parser->btor, e))
  {
    (void) perr_btor (parser, "mismatch of index bit width of 'else' array");
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
parse_slice (BtorBTORParser *parser, uint32_t width)
{
  uint32_t argwidth, upper, lower, delta;
  BoolectorNode *res, *arg;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0, false, true, 0))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    boolector_release (parser->btor, arg);
    return 0;
  }

  argwidth = boolector_get_width (parser->btor, arg);

  if (parse_non_negative_int (parser, &upper))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper >= argwidth)
  {
    (void) perr_btor (
        parser, "upper index '%d' >= argument width '%d", upper, argwidth);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  if (parse_space (parser)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (parse_non_negative_int (parser, &lower))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper < lower)
  {
    (void) perr_btor (
        parser, "upper index '%d' smaller than lower index '%d'", upper, lower);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  delta = upper - lower + 1;
  if (delta != width)
  {
    (void) perr_btor (parser,
                      "slice width '%d' not equal to expected width '%d'",
                      delta,
                      width);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = boolector_slice (parser->btor, arg, upper, lower);
  boolector_release (parser->btor, arg);

  return res;
}

static BoolectorNode *
parse_read (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *array, *idx, *res;
  uint32_t idxwidth;

  if (parse_space (parser)) return 0;

  if (!(array = parse_array_exp (parser, width))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    boolector_release (parser->btor, array);
    return 0;
  }

  idxwidth = boolector_get_index_width (parser->btor, array);
  if (!(idx = parse_exp (parser, idxwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  res = boolector_read (parser->btor, array, idx);
  boolector_release (parser->btor, idx);
  boolector_release (parser->btor, array);

  return res;
}

static BoolectorNode *
parse_write (BtorBTORParser *parser, uint32_t width)
{
  BoolectorNode *array, *idx, *val, *res;
  uint32_t idxwidth, valwidth;

  idxwidth = 0;
  valwidth = 0;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &idxwidth)) return 0;

  if (parse_space (parser)) return 0;

  if (!(array = parse_array_exp (parser, width))) return 0;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    boolector_release (parser->btor, array);
    return 0;
  }

  if (!(idx = parse_exp (parser, idxwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  if (parse_space (parser))
  {
  RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR:
    boolector_release (parser->btor, idx);
    goto RELEASE_ARRAY_AND_RETURN_ERROR;
  }

  valwidth = boolector_get_width (parser->btor, array);
  if (!(val = parse_exp (parser, valwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR;

  res = boolector_write (parser->btor, array, idx, val);

  boolector_release (parser->btor, array);
  boolector_release (parser->btor, idx);
  boolector_release (parser->btor, val);

  return res;
}

static BoolectorNode *
parse_lambda (BtorBTORParser *parser, uint32_t width)
{
  uint32_t paramwidth;
  BoolectorNode **params, *exp, *res;

  paramwidth = 0;

  if (parse_space (parser)) return 0;

  if (parse_positive_int (parser, &paramwidth)) return 0;

  if (parse_space (parser)) return 0;

  BTOR_NEW (parser->mem, params);
  if (!(params[0] = parse_param_exp (parser, paramwidth))) return 0;

  if (boolector_is_bound_param (parser->btor, params[0]))
  {
    perr_btor (parser, "param already bound by other lambda");
    goto RELEASE_PARAM_AND_RETURN_ERROR;
  }

  if (parse_space (parser))
  {
  RELEASE_PARAM_AND_RETURN_ERROR:
    boolector_release (parser->btor, params[0]);
    return 0;
  }

  if (!(exp = parse_exp (parser, width, true, true, 0)))
    goto RELEASE_PARAM_AND_RETURN_ERROR;

  res = boolector_fun (parser->btor, params, 1, exp);

  boolector_release (parser->btor, params[0]);
  BTOR_DELETE (parser->mem, params);
  boolector_release (parser->btor, exp);

  parser->found_lambdas = true;
  BTOR_PUSH_STACK (parser->lambdas, res);

  return res;
}

static BoolectorNode *
parse_apply (BtorBTORParser *parser, uint32_t width)
{
  uint32_t i, arity;
  BoolectorNode *res, *fun, *arg;
  BoolectorNodePtrStack args;

  if (parse_space (parser)) return 0;

  if (!(fun = parse_fun_exp (parser, width))) return 0;

  BTOR_INIT_STACK (parser->mem, args);

  if (parse_space (parser))
  {
  RELEASE_FUN_AND_RETURN_ERROR:
    while (!BTOR_EMPTY_STACK (args))
      boolector_release (parser->btor, BTOR_POP_STACK (args));
    BTOR_RELEASE_STACK (args);
    boolector_release (parser->btor, fun);
    return 0;
  }

  arity = boolector_get_fun_arity (parser->btor, fun);
  for (i = 0; i < arity; i++)
  {
    arg = parse_exp (parser, 0, false, true, 0);
    if (!arg) goto RELEASE_FUN_AND_RETURN_ERROR;

    if (i < arity - 1)
      if (parse_space (parser)) goto RELEASE_FUN_AND_RETURN_ERROR;

    BTOR_PUSH_STACK (args, arg);
  }

  res = boolector_apply (parser->btor, args.start, arity, fun);
  boolector_release (parser->btor, fun);

  while (!BTOR_EMPTY_STACK (args))
    boolector_release (parser->btor, BTOR_POP_STACK (args));
  BTOR_RELEASE_STACK (args);

  return res;
}

static BoolectorNode *
parse_ext (BtorBTORParser *parser, uint32_t width, Extend f)
{
  BoolectorNode *res, *arg;
  uint32_t awidth, ewidth;

  if (parse_space (parser)) return 0;

  if (!(arg = parse_exp (parser, 0, false, true, 0))) return 0;

  awidth = boolector_get_width (parser->btor, arg);

  if (parse_space (parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    boolector_release (parser->btor, arg);
    return 0;
  }

  if (parse_non_negative_int (parser, &ewidth))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (awidth + ewidth != width)
  {
    (void) perr_btor (parser,
                      "argument width of %d plus %d does not match %d",
                      awidth,
                      ewidth,
                      width);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = f (parser->btor, arg, ewidth);
  assert (boolector_get_width (parser->btor, res) == width);
  boolector_release (parser->btor, arg);

  return res;
}

static BoolectorNode *
parse_sext (BtorBTORParser *parser, uint32_t width)
{
  return parse_ext (parser, width, boolector_sext);
}

static BoolectorNode *
parse_uext (BtorBTORParser *parser, uint32_t width)
{
  return parse_ext (parser, width, boolector_uext);
}

static void
new_parser (BtorBTORParser *parser, BtorOpParser op_parser, const char *op)
{
  uint32_t p, d;

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
  uint32_t p, d;

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
new_btor_parser (Btor *btor)
{
  BtorMemMgr *mem = btor_mem_mgr_new ();
  BtorBTORParser *res;

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->mem  = mem;
  res->btor = btor;

  BTOR_NEWN (mem, res->parsers, SIZE_PARSERS);
  BTOR_NEWN (mem, res->ops, SIZE_PARSERS);
  BTOR_CLRN (res->ops, SIZE_PARSERS);

  BTOR_INIT_STACK (mem, res->exps);
  BTOR_INIT_STACK (mem, res->info);
  BTOR_INIT_STACK (mem, res->regs);
  BTOR_INIT_STACK (mem, res->lambdas);
  BTOR_INIT_STACK (mem, res->params);
  BTOR_INIT_STACK (mem, res->op);
  BTOR_INIT_STACK (mem, res->constant);
  BTOR_INIT_STACK (mem, res->symbol);

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

  return res;
}

static void
delete_btor_parser (BtorBTORParser *parser)
{
  BoolectorNode *e;
  BtorMemMgr *mm;
  uint32_t i;

  for (i = 0; i < BTOR_COUNT_STACK (parser->exps); i++)
    if ((e = parser->exps.start[i]))
      boolector_release (parser->btor, parser->exps.start[i]);

  mm = parser->mem;

  BTOR_RELEASE_STACK (parser->exps);
  BTOR_RELEASE_STACK (parser->info);
  BTOR_RELEASE_STACK (parser->regs);
  BTOR_RELEASE_STACK (parser->lambdas);
  BTOR_RELEASE_STACK (parser->params);

  BTOR_RELEASE_STACK (parser->op);
  BTOR_RELEASE_STACK (parser->constant);
  BTOR_RELEASE_STACK (parser->symbol);

  BTOR_DELETEN (mm, parser->parsers, SIZE_PARSERS);
  BTOR_DELETEN (mm, parser->ops, SIZE_PARSERS);

  btor_mem_freestr (mm, parser->error);
  BTOR_DELETE (mm, parser);
  btor_mem_mgr_delete (mm);
}

/* Note: we need prefix in case of stdin as input (also applies to compressed
 * input files). */
static const char *
parse_btor_parser (BtorBTORParser *parser,
                   BtorCharStack *prefix,
                   FILE *infile,
                   const char *infile_name,
                   FILE *outfile,
                   BtorParseResult *res)
{
  BtorOpParser op_parser;
  int32_t ch;
  uint32_t width;
  BoolectorNode *e;

  assert (infile);
  assert (infile_name);
  (void) outfile;

  BTOR_MSG (
      boolector_get_btor_msg (parser->btor), 1, "parsing %s", infile_name);

  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->infile      = infile;
  parser->infile_name = infile_name;
  parser->lineno      = 1;
  parser->saved       = false;

  BTOR_INIT_STACK (parser->mem, parser->lambdas);
  BTOR_INIT_STACK (parser->mem, parser->params);

  BTOR_CLR (res);

NEXT:
  assert (!parser->error);
  ch = nextch_btor (parser);
  if (isspace (ch)) /* also skip empty lines */
    goto NEXT;

  if (ch == EOF)
  {
  DONE:

    if (res)
    {
      if (parser->found_arrays || parser->found_lambdas)
        res->logic = BTOR_LOGIC_QF_AUFBV;
      else
        res->logic = BTOR_LOGIC_QF_BV;
      res->status = BOOLECTOR_UNKNOWN;
    }

    return 0;
  }

  if (ch == ';') /* skip comments */
  {
  COMMENTS:
    while ((ch = nextch_btor (parser)) != '\n')
      if (ch == EOF) goto DONE;

    goto NEXT;
  }

  if (!isdigit (ch)) return perr_btor (parser, "expected ';' or digit");

  savech_btor (parser, ch);

  if (parse_positive_int (parser, &parser->idx)) return parser->error;

  while (BTOR_COUNT_STACK (parser->exps) <= parser->idx)
  {
    Info info;
    memset (&info, 0, sizeof info);
    BTOR_PUSH_STACK (parser->info, info);
    BTOR_PUSH_STACK (parser->exps, 0);
  }

  if (parser->exps.start[parser->idx])
    return perr_btor (parser, "'%d' defined twice", parser->idx);

  if (parse_space (parser)) return parser->error;

  assert (BTOR_EMPTY_STACK (parser->op));
  while (!isspace (ch = nextch_btor (parser)) && ch != EOF)
    BTOR_PUSH_STACK (parser->op, ch);

  BTOR_PUSH_STACK (parser->op, 0);
  BTOR_RESET_STACK (parser->op);
  savech_btor (parser, ch);

  if (parse_space (parser)) return parser->error;

  if (parse_positive_int (parser, &width)) return parser->error;

  if (!(op_parser = find_parser (parser, parser->op.start)))
    return perr_btor (parser, "invalid operator '%s'", parser->op.start);

  if (!(e = op_parser (parser, width)))
  {
    assert (parser->error);
    return parser->error;
  }

#ifndef NDEBUG
  uint32_t w = boolector_get_width (parser->btor, e);
  if (!strcmp (parser->op.start, "root"))
    assert (w == 1);
  else
    assert (w == width);
#endif
  parser->exps.start[parser->idx] = e;

SKIP:
  ch = nextch_btor (parser);
  if (ch == ' ' || ch == '\t' || ch == '\r') goto SKIP;

  if (ch == ';') goto COMMENTS; /* ... and force new line */

  if (ch != '\n') return perr_btor (parser, "expected new line");

  goto NEXT;
}

static BtorParserAPI parsebtor_parser_api = {
    (BtorInitParser) new_btor_parser,
    (BtorResetParser) delete_btor_parser,
    (BtorParse) parse_btor_parser,
};

const BtorParserAPI *
btor_parsebtor_parser_api ()
{
  return &parsebtor_parser_api;
}
