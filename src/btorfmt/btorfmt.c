/**
 *  BtorFMT: A tool package for the BTOR format.
 *
 *  Copyright (c) 2012-2018 Armin Biere.
 *  Copyright (c) 2017 Mathias Preiner.
 *  Copyright (c) 2017-2018 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of the BtorFMT package.
 *  See LICENSE.txt for more information on using this software.
 */

#include "btorfmt.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "util/btorfmtstack.h"

struct BtorFormatReader
{
  char *error;
  BtorFormatLine **table, *new_line;
  BtorFormatSort **stable;
  long sztable, ntable, szstable, nstable, szbuf, nbuf, lineno;
  int saved;
  char *buf;
  FILE *file;
};

static void *
btorfmt_malloc (size_t size)
{
  assert (size);

  void *res = malloc (size);
  if (!res)
  {
    fprintf (stderr, "[btorfmt] memory allocation failed\n");
    abort ();
  }
  return res;
}

static char *
btorfmt_strdup (const char *str)
{
  assert (str);

  char *res = btorfmt_malloc (strlen (str) + 1);
  strcpy (res, str);
  return res;
}

BtorFormatReader *
btorfmt_new ()
{
  BtorFormatReader *res = btorfmt_malloc (sizeof *res);
  memset (res, 0, sizeof *res);
  return res;
}

static void
reset_bfr (BtorFormatReader *bfr)
{
  int i;
  assert (bfr);
  if (bfr->error)
  {
    free (bfr->error);
    bfr->error = 0;
  }
  if (bfr->table)
  {
    for (i = 0; i < bfr->ntable; i++)
    {
      BtorFormatLine *l = bfr->table[i];
      if (!l) continue;
      if (l->symbol) free (l->symbol);
      if (l->constant) free (l->constant);
      free (l->args);
      free (l);
    }
    free (bfr->table);
    bfr->table  = 0;
    bfr->ntable = bfr->sztable = 0;
  }
  if (bfr->buf)
  {
    free (bfr->buf);
    bfr->buf  = 0;
    bfr->nbuf = bfr->szbuf = 0;
  }
}

void
btorfmt_delete (BtorFormatReader *bfr)
{
  reset_bfr (bfr);
  free (bfr);
}

static int
getc_bfr (BtorFormatReader *bfr)
{
  int ch;
  if ((ch = bfr->saved) == EOF)
    ch = getc (bfr->file);
  else
    bfr->saved = EOF;
  if (ch == '\n') bfr->lineno++;
  return ch;
}

static void
ungetc_bfr (BtorFormatReader *bfr, int ch)
{
  assert (bfr->saved == EOF);
  if (ch == EOF) return;
  bfr->saved = ch;
  if (ch == '\n')
  {
    assert (bfr->lineno > 1);
    bfr->lineno--;
  }
}

static int
perr_bfr (BtorFormatReader *bfr, const char *fmt, ...)
{
  assert (!bfr->error);
  char buf[1024];

  va_list ap;
  va_start (ap, fmt);
  vsnprintf (buf, 1023, fmt, ap);
  va_end (ap);
  buf[1023] = '\0';

  bfr->error = btorfmt_malloc (strlen (buf) + 28);
  sprintf (bfr->error, "line %ld: %s", bfr->lineno, buf);
  return 0;
}

static void
pushc_bfr (BtorFormatReader *bfr, int ch)
{
  if (bfr->nbuf >= bfr->szbuf)
  {
    bfr->szbuf = bfr->szbuf ? 2 * bfr->szbuf : 1;
    bfr->buf   = realloc (bfr->buf, bfr->szbuf * sizeof *bfr->buf);
  }
  bfr->buf[bfr->nbuf++] = ch;
}

static void
pusht_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (bfr->ntable >= bfr->sztable)
  {
    bfr->sztable = bfr->sztable ? 2 * bfr->sztable : 1;
    bfr->table   = realloc (bfr->table, bfr->sztable * sizeof *bfr->table);
  }
  bfr->table[bfr->ntable++] = l;
}

static int
parse_id_bfr (BtorFormatReader *bfr, long *res)
{
  long id;
  int ch;
  ch = getc_bfr (bfr);
  if (ch == '0') return perr_bfr (bfr, "id should start with non-zero digit");
  if (!isdigit (ch)) return perr_bfr (bfr, "id should start with digit");
  id = ch - '0';
  while (isdigit (ch = getc_bfr (bfr)))
  {
    id = 10 * id + (ch - '0');
    if (id >= BTOR_FORMAT_MAXID) return perr_bfr (bfr, "id exceeds maximum");
  }
  ungetc_bfr (bfr, ch);
  *res = id;
  return 1;
}

static int
parse_signed_id_bfr (BtorFormatReader *bfr, long *res)
{
  int ch, sign;
  ch = getc_bfr (bfr);
  if (ch == '-')
    sign = -1;
  else
  {
    ungetc_bfr (bfr, ch);
    sign = 1;
  }
  if (!parse_id_bfr (bfr, res)) return 0;
  if (sign < 0) *res = -*res;
  return 1;
}

static int
parse_pos_number_bfr (BtorFormatReader *bfr, unsigned *res)
{
  long num;
  int ch;
  ch = getc_bfr (bfr);
  if (!isdigit (ch))
  {
    if (isprint (ch))
      return perr_bfr (bfr, "expected number but got '%c'", ch);
    else if (ch == '\n')
      return perr_bfr (bfr, "expected number but got new line");
    else
      return perr_bfr (
          bfr, "expected number but got character code 0x%02x", ch);
  }
  num = ch - '0';
  ch  = getc_bfr (bfr);
  /* number with leading zero */
  if (num == 0 && isdigit (ch))
    return perr_bfr (bfr, "number should start with non-zero digit");
  while (isdigit (ch))
  {
    num = 10 * num + (ch - '0');
    if (num >= BTOR_FORMAT_MAXBITWIDTH)
      return perr_bfr (bfr,
                       "number exceeds maximum bit width of %ld",
                       BTOR_FORMAT_MAXBITWIDTH);
    ch = getc_bfr (bfr);
  }
  ungetc_bfr (bfr, ch);
  *res = num;
  return 1;
}

static BtorFormatLine *
id2line_bfr (BtorFormatReader *bfr, long id)
{
  long absid = labs (id);
  if (!absid || absid >= bfr->ntable) return 0;
  return bfr->table[absid];
}

static int
skip_comment (BtorFormatReader *bfr)
{
  int ch;
  while ((ch = getc_bfr (bfr)) != '\n')
  {
    if (ch == EOF) return perr_bfr (bfr, "unexpected end-of-file in comment");
  }
  return 1;
}

static int
cmp_sort_ids (BtorFormatReader *bfr, long sort_id1, long sort_id2)
{
  (void) bfr;
  BtorFormatLine *s1, *s2;

  s1 = id2line_bfr (bfr, sort_id1);
  s2 = id2line_bfr (bfr, sort_id2);
  if (s1->sort.tag != s2->sort.tag) return 1;
  if (s1->sort.tag == BTOR_FORMAT_TAG_SORT_bitvec)
    return s1->sort.bitvec.width - s2->sort.bitvec.width;
  assert (s1->sort.tag == BTOR_FORMAT_TAG_SORT_array);
  if (cmp_sort_ids (bfr, s1->sort.array.index, s2->sort.array.index)) return 1;
  return cmp_sort_ids (bfr, s1->sort.array.element, s2->sort.array.element);
}

static int
cmp_sorts (BtorFormatReader *bfr, BtorFormatLine *l1, BtorFormatLine *l2)
{
  return cmp_sort_ids (bfr, l1->sort.id, l2->sort.id);
}

static int
parse_sort_id_bfr (BtorFormatReader *bfr, BtorFormatSort *res)
{
  long sort_id;
  BtorFormatLine *s;
  if (!parse_id_bfr (bfr, &sort_id)) return 0;

  if (sort_id >= bfr->ntable || id2line_bfr (bfr, sort_id) == 0)
    return perr_bfr (bfr, "undefined sort id");

  s = id2line_bfr (bfr, sort_id);
  if (s->tag != BTOR_FORMAT_TAG_sort)
    return perr_bfr (bfr, "id after tag is not a sort id");
  *res = s->sort;
  return 1;
}

static const char *
parse_tag (BtorFormatReader *bfr)
{
  int ch;
  bfr->nbuf = 0;
  while ('a' <= (ch = getc_bfr (bfr)) && ch <= 'z') pushc_bfr (bfr, ch);
  if (!bfr->nbuf)
  {
    perr_bfr (bfr, "expected tag");
    return 0;
  }
  if (ch != ' ')
  {
    perr_bfr (bfr, "expected space after tag");
    return 0;
  }
  pushc_bfr (bfr, 0);
  return bfr->buf;
}

static int
parse_symbol_bfr (BtorFormatReader *bfr)
{
  int ch;
  bfr->nbuf = 0;
  while ((ch = getc_bfr (bfr)) != '\n')
  {
    if (ch == EOF)
      return perr_bfr (bfr, "unexpected end-of-file in symbol");
    else if (ch == ' ' || ch == '\t')
    {
      ch = getc_bfr (bfr);
      if (ch == ';')
      {
        if (!skip_comment (bfr)) return 0;
        break;
      }
      else
        return perr_bfr (bfr, "unexpected white-space in symbol");
    }
    pushc_bfr (bfr, ch);
  }
  if (!bfr->nbuf)
  {
    assert (bfr->lineno > 1);
    bfr->lineno--;
    return perr_bfr (bfr, "empty symbol");
  }
  pushc_bfr (bfr, 0);
  return 1;
}

static int
parse_opt_symbol_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  int ch;
  if ((ch = getc_bfr (bfr)) == ' ')
  {
    ch = getc_bfr (bfr);
    if (ch == ';')
    {
      if (!skip_comment (bfr)) return 0;
    }
    else
    {
      ungetc_bfr (bfr, ch);
      if (!parse_symbol_bfr (bfr)) return 0;
      l->symbol = btorfmt_strdup (bfr->buf);
    }
  }
  else if (ch != '\n')
    return perr_bfr (
        bfr, "expected new-line at the end of the line got '%c'", ch);
  return 1;
}

static BtorFormatLine *
new_line_bfr (BtorFormatReader *bfr,
              long id,
              long lineno,
              const char *name,
              BtorFormatTag tag)
{
  BtorFormatLine *res;
  assert (0 < id);
  assert (bfr->ntable <= id);
  res = btorfmt_malloc (sizeof *res);
  memset (res, 0, sizeof (*res));
  res->id     = id;
  res->lineno = lineno;
  res->tag    = tag;
  res->name   = name;
  res->args   = btorfmt_malloc (sizeof (long) * 3);
  memset (res->args, 0, sizeof (long) * 3);
  while (bfr->ntable < id) pusht_bfr (bfr, 0);
  assert (bfr->ntable == id);
  return res;
}

static int
check_sort_bitvec (BtorFormatReader *bfr,
                   BtorFormatLine *l,
                   BtorFormatLine *args[])
{
  unsigned i;
  /* check if bit-vector operators have bit-vector operands */
  if (l->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec)
    return perr_bfr (bfr, "expected bitvec sort for %s", l->name);
  for (i = 0; i < l->nargs; i++)
  {
    if (args[i]->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec)
      return perr_bfr (bfr,
                       "expected bitvec sort for %s argument of %s",
                       i == 0 ? "first" : (i == 1 ? "second" : "third"),
                       l->name);
  }
  return 1;
}

static int
is_constant_bfr (BtorFormatReader *bfr, long id)
{
  BtorFormatLine *l = id2line_bfr (bfr, id);
  assert (l);
  BtorFormatTag tag = l->tag;
  return tag == BTOR_FORMAT_TAG_const || tag == BTOR_FORMAT_TAG_constd
         || tag == BTOR_FORMAT_TAG_consth || tag == BTOR_FORMAT_TAG_one
         || tag == BTOR_FORMAT_TAG_ones || tag == BTOR_FORMAT_TAG_zero;
}

static int
check_sorts_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  BtorFormatLine *arg;
  BtorFormatLine *args[3];
  unsigned i;
  if (l->tag != BTOR_FORMAT_TAG_justice)
  {
    for (i = 0; i < l->nargs; i++) args[i] = id2line_bfr (bfr, l->args[i]);
  }

  switch (l->tag)
  {
    /* n -> n */
    case BTOR_FORMAT_TAG_dec:
    case BTOR_FORMAT_TAG_inc:
    case BTOR_FORMAT_TAG_neg:
    case BTOR_FORMAT_TAG_not:
    case BTOR_FORMAT_TAG_output:
      assert (l->nargs == 1);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      if (l->sort.bitvec.width != args[0]->sort.bitvec.width)
        return perr_bfr (bfr,
                         "expected bitvec of size %u for "
                         "argument but got %u",
                         l->sort.bitvec.width,
                         args[0]->sort.bitvec.width);
      break;

    /* n -> 1 */
    case BTOR_FORMAT_TAG_redand:
    case BTOR_FORMAT_TAG_redor:
    case BTOR_FORMAT_TAG_redxor:
      assert (l->nargs == 1);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      if (l->sort.bitvec.width != 1)
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for "
                         "%s but got %u",
                         l->name,
                         l->sort.bitvec.width);
      break;

    /* n x n -> n */
    case BTOR_FORMAT_TAG_add:
    case BTOR_FORMAT_TAG_and:
    case BTOR_FORMAT_TAG_mul:
    case BTOR_FORMAT_TAG_nand:
    case BTOR_FORMAT_TAG_nor:
    case BTOR_FORMAT_TAG_or:
    case BTOR_FORMAT_TAG_rol:
    case BTOR_FORMAT_TAG_ror:
    case BTOR_FORMAT_TAG_sdiv:
    case BTOR_FORMAT_TAG_sll:
    case BTOR_FORMAT_TAG_smod:
    case BTOR_FORMAT_TAG_sra:
    case BTOR_FORMAT_TAG_srem:
    case BTOR_FORMAT_TAG_srl:
    case BTOR_FORMAT_TAG_sub:
    case BTOR_FORMAT_TAG_udiv:
    case BTOR_FORMAT_TAG_urem:
    case BTOR_FORMAT_TAG_xnor:
    case BTOR_FORMAT_TAG_xor:
      assert (l->nargs == 2);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      if (l->sort.bitvec.width != args[0]->sort.bitvec.width)
        return perr_bfr (bfr,
                         "expected bitvec of size %u for "
                         "first argument but got %u",
                         l->sort.bitvec.width,
                         args[0]->sort.bitvec.width);
      if (l->sort.bitvec.width != args[1]->sort.bitvec.width)
        return perr_bfr (bfr,
                         "expected bitvec of size %u for "
                         "second argument but got %u",
                         l->sort.bitvec.width,
                         args[1]->sort.bitvec.width);
      break;

    case BTOR_FORMAT_TAG_init:
      if (l->sort.tag == BTOR_FORMAT_TAG_SORT_array)
      {
        if (cmp_sorts (bfr, l, args[0]))
          return perr_bfr (bfr, "sort of first argument does not match");

        // special case for constant initialization for arrays
        if (args[1]->sort.tag == BTOR_FORMAT_TAG_SORT_bitvec)
        {
          if (!is_constant_bfr (bfr, args[1]->id))
            return perr_bfr (bfr,
                             "expected bit-vector constant as second argument");
          if (cmp_sort_ids (bfr, l->sort.array.element, args[1]->sort.id))
            return perr_bfr (bfr,
                             "sort of init value does not match element "
                             "sort of state '%ld'",
                             args[0]->id);
        }
        break;
      }
      // else fall through
    case BTOR_FORMAT_TAG_next:
      assert (l->nargs == 2);
      if (cmp_sorts (bfr, l, args[0]))
        return perr_bfr (bfr, "sort of first argument does not match");
      if (cmp_sorts (bfr, l, args[1]))
        return perr_bfr (bfr, "sort of second argument does not match");
      break;

    /* n x n -> 1 */
    case BTOR_FORMAT_TAG_uaddo:
    case BTOR_FORMAT_TAG_ugt:
    case BTOR_FORMAT_TAG_ugte:
    case BTOR_FORMAT_TAG_ult:
    case BTOR_FORMAT_TAG_ulte:
    case BTOR_FORMAT_TAG_umulo:
    case BTOR_FORMAT_TAG_usubo:
    case BTOR_FORMAT_TAG_saddo:
    case BTOR_FORMAT_TAG_sdivo:
    case BTOR_FORMAT_TAG_sgt:
    case BTOR_FORMAT_TAG_sgte:
    case BTOR_FORMAT_TAG_slt:
    case BTOR_FORMAT_TAG_slte:
    case BTOR_FORMAT_TAG_smulo:
    case BTOR_FORMAT_TAG_ssubo:
      assert (l->nargs == 2);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      if (l->sort.bitvec.width != 1)
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for "
                         "%s but got %u",
                         l->name,
                         l->sort.bitvec.width);
      if (args[0]->sort.bitvec.width != args[1]->sort.bitvec.width)
        return perr_bfr (bfr,
                         "sorts of first and second "
                         "argument do not match");
      break;

    case BTOR_FORMAT_TAG_eq:
    case BTOR_FORMAT_TAG_ne:
      assert (l->nargs == 2);
      if (l->sort.bitvec.width != 1)
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for %s but got %u",
                         l->name,
                         l->sort.bitvec.width);
      if (cmp_sorts (bfr, args[0], args[1]))
        return perr_bfr (bfr,
                         "sorts of first and second "
                         "argument do not match");
      break;

    /* n x m -> n + m */
    case BTOR_FORMAT_TAG_concat:
      assert (l->nargs == 2);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      if (l->sort.bitvec.width
          != args[0]->sort.bitvec.width + args[1]->sort.bitvec.width)
        return perr_bfr (
            bfr,
            "expected bitvec of size %u for %s but got %u",
            l->sort.bitvec.width,
            l->name,
            args[0]->sort.bitvec.width + args[1]->sort.bitvec.width);
      break;

    /* [u:l] -> u - l + 1 */
    case BTOR_FORMAT_TAG_slice:
      assert (l->nargs == 1);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      /* NOTE: this cast is safe since l->args[1] and l->args[2] contains
       *       upper and lower indices, which are unsigned */
      unsigned upper = (unsigned) l->args[1];
      unsigned lower = (unsigned) l->args[2];
      if (l->sort.bitvec.width != upper - lower + 1)
        return perr_bfr (bfr,
                         "expected bitvec of size %u for %s but got %u",
                         l->sort.bitvec.width,
                         l->name,
                         upper - lower + 1);
      break;

    /* 1 x 1 -> 1 */
    case BTOR_FORMAT_TAG_iff:
    case BTOR_FORMAT_TAG_implies:
      assert (l->nargs == 2);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      if (l->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec
          || l->sort.bitvec.width != 1)
        return perr_bfr (bfr, "expected bitvec of size 1");
      if (cmp_sorts (bfr, args[0], l))
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for "
                         "first argument");
      if (cmp_sorts (bfr, args[1], l))
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for "
                         "second argument");
      break;

    /* 1 */
    case BTOR_FORMAT_TAG_bad:
    case BTOR_FORMAT_TAG_constraint:
    case BTOR_FORMAT_TAG_fair:
      assert (l->nargs == 1);
      if (args[0]->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec)
        return perr_bfr (bfr, "expected bitvec of size 1 for %s", l->name);
      if (args[0]->sort.bitvec.width != 1)
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for %s "
                         "but got %u",
                         l->name,
                         args[0]->sort.bitvec.width);
      break;

    case BTOR_FORMAT_TAG_ite:
      assert (l->nargs == 3);
      if (args[0]->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec)
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for ",
                         "first argument of %s",
                         l->name);
      if (args[0]->sort.bitvec.width != 1)
        return perr_bfr (bfr,
                         "expected bitvec of size 1 for "
                         "first argument of %s but got %u",
                         l->name,
                         args[0]->sort.bitvec.width);
      if (cmp_sorts (bfr, args[1], args[2]))
        return perr_bfr (bfr,
                         "sorts of second and third "
                         "argument do not match");
      break;

    case BTOR_FORMAT_TAG_justice:
      for (i = 0; i < l->nargs; i++)
      {
        arg = id2line_bfr (bfr, l->args[i]);
        if (arg->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec)
          return perr_bfr (bfr, "expected bitvec of size 1 for argument %u", i);
        if (arg->sort.bitvec.width != 1)
          return perr_bfr (bfr,
                           "expected bitvec of size 1 for argument %u "
                           "but got %u",
                           i,
                           arg->sort.bitvec.width);
      }
      break;

    case BTOR_FORMAT_TAG_sext:
    case BTOR_FORMAT_TAG_uext:
      assert (l->nargs == 1);
      if (!check_sort_bitvec (bfr, l, args)) return 0;
      /* NOTE: this cast is safe since l->args[1] contains the extension
       *       bit-width, which is unsigned */
      unsigned ext = args[0]->sort.bitvec.width + (unsigned) l->args[1];
      if (l->sort.bitvec.width != ext)
        return perr_bfr (bfr,
                         "expected bitvec of size %u for %s but got %u",
                         l->sort.bitvec.width,
                         l->name,
                         ext);
      break;

    case BTOR_FORMAT_TAG_read:
      assert (l->nargs == 2);
      if (args[0]->sort.tag != BTOR_FORMAT_TAG_SORT_array)
        return perr_bfr (
            bfr, "expected array sort for first argument of %s", l->name);
      if (cmp_sort_ids (bfr, l->sort.id, args[0]->sort.array.element))
        return perr_bfr (bfr,
                         "sort of %s does not match element sort of first "
                         "argument",
                         l->name);
      if (cmp_sort_ids (bfr, args[1]->sort.id, args[0]->sort.array.index))
        return perr_bfr (bfr,
                         "sort of second argument does not match index "
                         "sort of first argument");
      break;

    case BTOR_FORMAT_TAG_write:
      assert (l->nargs == 3);
      if (l->sort.tag != BTOR_FORMAT_TAG_SORT_array)
        return perr_bfr (bfr, "expected array sort for %s", l->name);
      if (args[0]->sort.tag != BTOR_FORMAT_TAG_SORT_array)
        return perr_bfr (
            bfr, "expected array sort for first argument of %s", l->name);
      if (cmp_sort_ids (bfr, args[1]->sort.id, args[0]->sort.array.index))
        return perr_bfr (bfr,
                         "sort of second argument does not match index "
                         "sort of first argument",
                         l->name);

      if (cmp_sort_ids (bfr, args[2]->sort.id, args[0]->sort.array.element))
        return perr_bfr (bfr,
                         "sort of third argument does not match element "
                         "sort of first argument",
                         l->name);
      break;

    /* no sort checking */
    case BTOR_FORMAT_TAG_const:
    case BTOR_FORMAT_TAG_constd:
    case BTOR_FORMAT_TAG_consth:
    case BTOR_FORMAT_TAG_input:
    case BTOR_FORMAT_TAG_one:
    case BTOR_FORMAT_TAG_ones:
    case BTOR_FORMAT_TAG_sort:
    case BTOR_FORMAT_TAG_state:
    case BTOR_FORMAT_TAG_zero: break;

    default:
      assert (0);
      return perr_bfr (bfr, "invalid tag '%s' for sort checking", l->tag);
  }
  return 1;
}

static long
parse_arg_bfr (BtorFormatReader *bfr)
{
  BtorFormatLine *l;
  long res, absres;
  if (!parse_signed_id_bfr (bfr, &res)) return 0;
  absres = labs (res);
  if (absres >= bfr->ntable)
    return perr_bfr (bfr, "argument id too large (undefined)");
  l = bfr->table[absres];
  if (!l) return perr_bfr (bfr, "undefined argument id");
  if (l->tag == BTOR_FORMAT_TAG_sort || l->tag == BTOR_FORMAT_TAG_init
      || l->tag == BTOR_FORMAT_TAG_next || l->tag == BTOR_FORMAT_TAG_bad
      || l->tag == BTOR_FORMAT_TAG_constraint || l->tag == BTOR_FORMAT_TAG_fair
      || l->tag == BTOR_FORMAT_TAG_justice)
  {
    return perr_bfr (bfr, "'%s' cannot be used as argument", l->name);
  }
  if (!l->sort.id) return perr_bfr (bfr, "declaration used as argument");
  return res;
}

static int
parse_sort_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  const char *tag;
  BtorFormatSort tmp, s;
  tag = parse_tag (bfr);
  if (!tag) return 0;
  if (!strcmp (tag, "bitvec"))
  {
    tmp.tag  = BTOR_FORMAT_TAG_SORT_bitvec;
    tmp.name = "bitvec";
    if (!parse_pos_number_bfr (bfr, &tmp.bitvec.width)) return 0;
    if (tmp.bitvec.width == 0)
      return perr_bfr (bfr, "bit width must be greater than 0");
  }
  else if (!strcmp (tag, "array"))
  {
    tmp.tag  = BTOR_FORMAT_TAG_SORT_array;
    tmp.name = "array";
    if (!parse_sort_id_bfr (bfr, &s)) return 0;
    if (getc_bfr (bfr) != ' ') return perr_bfr (bfr, "expected space");
    tmp.array.index = s.id;
    if (!parse_sort_id_bfr (bfr, &s)) return 0;
    tmp.array.element = s.id;
  }
  else
  {
    return perr_bfr (bfr, "invalid sort tag");
  }
  tmp.id  = l->id;
  l->sort = tmp;
  return 1;
}

static int
parse_args (BtorFormatReader *bfr, BtorFormatLine *l, unsigned nargs)
{
  unsigned i = 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after sort id");
  while (i < nargs)
  {
    if (!(l->args[i] = parse_arg_bfr (bfr))) return 0;
    if (i < nargs - 1 && getc_bfr (bfr) != ' ')
      return perr_bfr (bfr, "expected space after argument (argument missing)");
    i++;
  }
  l->nargs = nargs;
  return 1;
}

static int
parse_unary_op_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 1)) return 0;
  return 1;
}

static int
parse_ext_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  unsigned ext;
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 1)) return 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after first argument");
  if (!parse_pos_number_bfr (bfr, &ext)) return 0;
  l->args[1] = ext;
  return 1;
}

static int
parse_slice_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  unsigned lower;
  if (!parse_ext_bfr (bfr, l)) return 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after second argument");
  if (!parse_pos_number_bfr (bfr, &lower)) return 0;
  l->args[2] = lower;
  if (lower > l->args[1])
    return perr_bfr (bfr, "lower has to be less than or equal to upper");
  return 1;
}

static int
parse_binary_op_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 2)) return 0;
  return 1;
}

static int
parse_ternary_op_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 3)) return 0;
  return 1;
}

static int
check_consth (const char *consth, unsigned width)
{
  char c;
  size_t i, len, req_width;

  len       = strlen (consth);
  req_width = len * 4;
  for (i = 0; i < len; i++)
  {
    c = consth[i];
    assert (isxdigit (c));
    if (c >= 'A' && c <= 'F') c = tolower (c);

    if (c == '0')
    {
      req_width -= 4;
      continue;
    }
    c = (c >= '0' && c <= '9') ? c - '0' : c - 'a' + 0xa;
    assert (c > 0 && c <= 15);
    if (c >> 1 == 0)
      req_width -= 3;
    else if (c >> 2 == 0)
      req_width -= 2;
    else if (c >> 3 == 0)
      req_width -= 1;
    break;
  }
  if (req_width <= width) return 1;
  return 0;
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

static char *
mult_unbounded_bin_str (const char *a, const char *b)
{
  assert (a);
  assert (b);
  assert (is_bin_str (a));
  assert (is_bin_str (b));

  char *res, *r, c, x, y, s, m;
  unsigned alen, blen, rlen, i;
  const char *p;

  a = strip_zeroes (a);
  if (!*a) return btorfmt_strdup ("");
  if (a[0] == '1' && !a[1]) return btorfmt_strdup (b);

  b = strip_zeroes (b);
  if (!*b) return btorfmt_strdup ("");
  if (b[0] == '1' && !b[1]) return btorfmt_strdup (a);

  alen      = strlen (a);
  blen      = strlen (b);
  rlen      = alen + blen;
  res       = btorfmt_malloc (rlen + 1);
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

static char *
add_unbounded_bin_str (const char *a, const char *b)
{
  assert (a);
  assert (b);
  assert (is_bin_str (a));
  assert (is_bin_str (b));

  char *res, *r, c, x, y, s, *tmp;
  unsigned alen, blen, rlen;
  const char *p, *q;

  a = strip_zeroes (a);
  b = strip_zeroes (b);

  if (!*a) return btorfmt_strdup (b);
  if (!*b) return btorfmt_strdup (a);

  alen = strlen (a);
  blen = strlen (b);
  rlen = (alen < blen) ? blen : alen;
  rlen++;

  res = btorfmt_malloc (rlen + 1);

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
    tmp = btorfmt_strdup (p);
    if (!tmp)
    {
      free (res);
      return 0;
    }
    free (res);
    res = tmp;
  }

  return res;
}

static char *
dec_to_bin_str (const char *str, unsigned len)
{
  assert (str);

  const char *end, *p;
  char *res, *tmp;

  res = btorfmt_strdup ("");
  if (!res) return 0;

  end = str + len;
  for (p = str; p < end; p++)
  {
    tmp = mult_unbounded_bin_str (res, "1010"); /* *10 */
    if (!tmp)
    {
      free (res);
      return 0;
    }
    free (res);
    res = tmp;

    tmp = add_unbounded_bin_str (res, digit2const (*p));
    if (!tmp)
    {
      free (res);
      return 0;
    }
    free (res);
    res = tmp;
  }

  assert (strip_zeroes (res) == res);
  if (strlen (res)) return res;
  free (res);
  return btorfmt_strdup ("0");
}

int
check_constd (const char *str, unsigned width)
{
  assert (str);
  assert (width);

  int is_neg, is_min_val = 0, res;
  char *bits;
  size_t size_bits, len;

  is_neg    = (str[0] == '-');
  len       = is_neg ? strlen (str) - 1 : strlen (str);
  bits      = dec_to_bin_str (is_neg ? str + 1 : str, len);
  size_bits = strlen (bits);
  if (is_neg)
  {
    is_min_val = (bits[0] == '1');
    for (size_t i = 1; is_min_val && i < size_bits; i++)
      is_min_val = (bits[i] == '0');
  }
  res = ((is_neg && !is_min_val) || size_bits <= width)
        && (!is_neg || is_min_val || size_bits + 1 <= width);
  free (bits);
  return res;
}

static int
parse_constant_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;

  if (l->sort.tag != BTOR_FORMAT_TAG_SORT_bitvec)
    return perr_bfr (bfr, "expected bitvec sort for %s", l->name);

  if (l->tag == BTOR_FORMAT_TAG_one || l->tag == BTOR_FORMAT_TAG_ones
      || l->tag == BTOR_FORMAT_TAG_zero)
  {
    return 1;
  }

  int ch = getc_bfr (bfr);
  if (ch != ' ') return perr_bfr (bfr, "expected space after sort id");

  bfr->nbuf = 0;
  if (l->tag == BTOR_FORMAT_TAG_const)
  {
    while ('0' == (ch = getc_bfr (bfr)) || ch == '1') pushc_bfr (bfr, ch);
  }
  else if (l->tag == BTOR_FORMAT_TAG_constd)
  {
    /* allow negative numbers */
    if ((ch = getc_bfr (bfr)) && (ch == '-' || isdigit (ch)))
      pushc_bfr (bfr, ch);
    while (isdigit ((ch = getc_bfr (bfr)))) pushc_bfr (bfr, ch);
  }
  else if (l->tag == BTOR_FORMAT_TAG_consth)
  {
    while (isxdigit ((ch = getc_bfr (bfr)))) pushc_bfr (bfr, ch);
  }
  if (!bfr->nbuf)
  {
    perr_bfr (bfr, "expected number");
    return 0;
  }
  if (ch != '\n')
  {
    perr_bfr (bfr, "invalid character '%c' in constant definition", ch);
    return 0;
  }
  ungetc_bfr (bfr, '\n');
  pushc_bfr (bfr, 0);

  if (l->tag == BTOR_FORMAT_TAG_const
      && strlen (bfr->buf) != l->sort.bitvec.width)
  {
    return perr_bfr (bfr,
                     "constant '%s' does not match bit-vector sort size %u",
                     bfr->buf,
                     l->sort.bitvec.width);
  }
  else if (l->tag == BTOR_FORMAT_TAG_constd
           && !check_constd (bfr->buf, l->sort.bitvec.width))
  {
    return perr_bfr (bfr,
                     "constant '%s' does not match bit-vector sort size %u",
                     bfr->buf,
                     l->sort.bitvec.width);
  }
  else if (l->tag == BTOR_FORMAT_TAG_consth
           && !check_consth (bfr->buf, l->sort.bitvec.width))
  {
    return perr_bfr (bfr,
                     "constant '%s' does not fit into bit-vector of size %u",
                     bfr->buf,
                     l->sort.bitvec.width);
  }
  l->constant = btorfmt_strdup (bfr->buf);
  return 1;
}

static int
parse_input_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  return parse_sort_id_bfr (bfr, &l->sort);
}

BTORFMT_DECLARE_STACK (BtorFmtLong, long);

static int
check_state_init (BtorFormatReader *bfr, long state_id, long init_id)
{
  assert (state_id > init_id);
  (void) state_id;

  int res = 1;
  long id;
  unsigned i;
  BtorFormatLine *line;
  BtorFmtLongStack stack;
  char *cache;

  line = id2line_bfr (bfr, init_id);

  // 'init_id' is the highest id we will see when traversing down
  size_t size = (init_id + 1) * sizeof (char);
  cache       = btorfmt_malloc (size);
  memset (cache, 0, size);

  BTORFMT_INIT_STACK (stack);
  BTORFMT_PUSH_STACK (stack, init_id);
  do
  {
    id = BTORFMT_POP_STACK (stack);
    assert (id);
    if (id < 0) id = -id;

    // no cycles possible since state_id > init_id
    assert (id != state_id);
    if (cache[id]) continue;

    cache[id] = 1;
    line      = id2line_bfr (bfr, id);

    if (line->tag == BTOR_FORMAT_TAG_input)
    {
      res = perr_bfr (bfr,
                      "inputs are not allowed in initialization expressions, "
                      "use a state instead of input %ld.",
                      id);
      break;
    }
    for (i = 0; i < line->nargs; i++) BTORFMT_PUSH_STACK (stack, line->args[i]);
  } while (!BTORFMT_EMPTY_STACK (stack));

  free (cache);
  return res;
}

static int
parse_init_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  BtorFormatLine *state;
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 2)) return 0;
  if (l->args[0] < 0) return perr_bfr (bfr, "invalid negated first argument");
  state = id2line_bfr (bfr, l->args[0]);
  if (state->tag != BTOR_FORMAT_TAG_state)
    return perr_bfr (bfr, "expected state as first argument");
  if (l->args[0] < abs (l->args[1]))
    return perr_bfr (bfr, "state id must be greater than id of second operand");
  if (!check_state_init (bfr, l->args[0], l->args[1])) return 0;
  if (state->init)
    return perr_bfr (bfr, "state %ld initialized twice", state->id);
  state->init = l->args[1];
  return 1;
}

static int
parse_next_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  BtorFormatLine *state;
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 2)) return 0;
  if (l->args[0] < 0) return perr_bfr (bfr, "invalid negated first argument");
  state = id2line_bfr (bfr, l->args[0]);
  if (state->tag != BTOR_FORMAT_TAG_state)
    return perr_bfr (bfr, "expected state as first argument");
  if (state->next)
    return perr_bfr (bfr, "next for state %ld set twice", state->id);
  state->next = l->args[1];
  return 1;
}

static int
parse_constraint_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  /* contraint, bad, justice, fairness do not have a sort id after the tag */
  if (!(l->args[0] = parse_arg_bfr (bfr))) return 0;
  BtorFormatLine *arg = id2line_bfr (bfr, l->args[0]);
  if (arg->tag == BTOR_FORMAT_TAG_sort)
    return perr_bfr (bfr, "unexpected sort id after tag");
  l->nargs = 1;
  return 1;
}

static int
parse_justice_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  unsigned nargs;
  if (!parse_pos_number_bfr (bfr, &nargs)) return 0;
  l->args  = realloc (l->args, sizeof (long) * nargs);
  l->nargs = nargs;
  if (!parse_args (bfr, l, nargs)) return 0;
  return 1;
}

#define PARSE(NAME, GENERIC)                                                   \
  do                                                                           \
  {                                                                            \
    if (!strcmp (tag, #NAME))                                                  \
    {                                                                          \
      BtorFormatLine *LINE =                                                   \
          new_line_bfr (bfr, id, lineno, #NAME, BTOR_FORMAT_TAG_##NAME);       \
      if (parse_##GENERIC##_bfr (bfr, LINE))                                   \
      {                                                                        \
        pusht_bfr (bfr, LINE);                                                 \
        assert (bfr->table[id] == LINE);                                       \
        if (!check_sorts_bfr (bfr, LINE) || !parse_opt_symbol_bfr (bfr, LINE)) \
        {                                                                      \
          return 0;                                                            \
        }                                                                      \
        return 1;                                                              \
      }                                                                        \
      else                                                                     \
      {                                                                        \
        return 0;                                                              \
      }                                                                        \
    }                                                                          \
  } while (0)

// draft changes:
// 1) allow white spaces at beginning of the line
// 2) allow comments at the end of the line

static int
readl_bfr (BtorFormatReader *bfr)
{
  const char *tag;
  long lineno;
  long id;
  int ch;
START:
  // skip white spaces at the beginning of the line
  while ((ch = getc_bfr (bfr)) == ' ')
    ;
  if (ch == EOF) return 0;
  if (ch == '\n') goto START;
  if (ch == '\t')
    return perr_bfr (bfr, "unexpected tab character at start of line");
  if (ch == ';')
  {
    if (!skip_comment (bfr)) return 0;
    goto START;
  }
  ungetc_bfr (bfr, ch);
  if (!parse_id_bfr (bfr, &id)) return 0;
  if (getc_bfr (bfr) != ' ') return perr_bfr (bfr, "expected space after id");
  if (id < bfr->ntable)
  {
    if (id2line_bfr (bfr, id) != 0) return perr_bfr (bfr, "id already defined");
    return perr_bfr (bfr, "id out-of-order");
  }
  lineno = bfr->lineno;
  tag    = parse_tag (bfr);
  if (!tag) return 0;
  switch (tag[0])
  {
    case 'a':
      PARSE (add, binary_op);
      PARSE (and, binary_op);
      break;
    case 'b': PARSE (bad, constraint); break;
    case 'c':
      PARSE (constraint, constraint);
      PARSE (concat, binary_op);
      PARSE (const, constant);
      PARSE (constd, constant);
      PARSE (consth, constant);
      break;
    case 'd': PARSE (dec, unary_op); break;
    case 'e': PARSE (eq, binary_op); break;
    case 'f': PARSE (fair, constraint); break;
    case 'i':
      PARSE (implies, binary_op);
      PARSE (iff, binary_op);
      PARSE (inc, unary_op);
      PARSE (init, init);
      PARSE (input, input);
      PARSE (ite, ternary_op);
      break;
    case 'j': PARSE (justice, justice); break;
    case 'l': PARSE (state, input); break;
    case 'm': PARSE (mul, binary_op); break;
    case 'n':
      PARSE (nand, binary_op);
      PARSE (ne, binary_op);
      PARSE (neg, unary_op);
      PARSE (next, next);
      PARSE (nor, binary_op);
      PARSE (not, unary_op);
      break;
    case 'o':
      PARSE (one, constant);
      PARSE (ones, constant);
      PARSE (or, binary_op);
      PARSE (output, unary_op);
      break;
    case 'r':
      PARSE (read, binary_op);
      PARSE (redand, unary_op);
      PARSE (redor, unary_op);
      PARSE (redxor, unary_op);
      PARSE (rol, binary_op);
      PARSE (ror, binary_op);
      break;
    case 's':
      PARSE (saddo, binary_op);
      PARSE (sext, ext);
      PARSE (sgt, binary_op);
      PARSE (sgte, binary_op);
      PARSE (sdiv, binary_op);
      PARSE (sdivo, binary_op);
      PARSE (slice, slice);
      PARSE (sll, binary_op);
      PARSE (slt, binary_op);
      PARSE (slte, binary_op);
      PARSE (sort, sort);
      PARSE (smod, binary_op);
      PARSE (smulo, binary_op);
      PARSE (ssubo, binary_op);
      PARSE (sra, binary_op);
      PARSE (srl, binary_op);
      PARSE (srem, binary_op);
      PARSE (state, input);
      PARSE (sub, binary_op);
      break;
    case 'u':
      PARSE (uaddo, binary_op);
      PARSE (udiv, binary_op);
      PARSE (uext, ext);
      PARSE (ugt, binary_op);
      PARSE (ugte, binary_op);
      PARSE (ult, binary_op);
      PARSE (ulte, binary_op);
      PARSE (umulo, binary_op);
      PARSE (urem, binary_op);
      PARSE (usubo, binary_op);
      break;
    case 'w': PARSE (write, ternary_op); break;
    case 'x':
      PARSE (xnor, binary_op);
      PARSE (xor, binary_op);
      break;
    case 'z': PARSE (zero, constant); break;
  }
  return perr_bfr (bfr, "invalid tag '%s'", tag);
}

int
btorfmt_read_lines (BtorFormatReader *bfr, FILE *file)
{
  reset_bfr (bfr);
  bfr->lineno = 1;
  bfr->saved  = EOF;
  bfr->file   = file;
  while (readl_bfr (bfr))
    ;
  return !bfr->error;
}

const char *
btorfmt_error (BtorFormatReader *bfr)
{
  return bfr->error;
}

static long
find_non_zero_line_bfr (BtorFormatReader *bfr, long start)
{
  long res;
  for (res = start; res < bfr->ntable; res++)
    if (bfr->table[res]) return res;
  return 0;
}

BtorFormatLineIterator
btorfmt_iter_init (BtorFormatReader *bfr)
{
  BtorFormatLineIterator res;
  res.reader = bfr;
  if (bfr->error)
    res.next = 0;
  else
    res.next = find_non_zero_line_bfr (bfr, 1);
  return res;
}

BtorFormatLine *
btorfmt_iter_next (BtorFormatLineIterator *it)
{
  BtorFormatLine *res;
  if (!it->next) return 0;
  assert (0 < it->next);
  assert (it->next < it->reader->ntable);
  res      = it->reader->table[it->next];
  it->next = find_non_zero_line_bfr (it->reader, it->next + 1);
  return res;
}

BtorFormatLine *
btorfmt_get_line_by_id (BtorFormatReader *bfr, long id)
{
  return id2line_bfr (bfr, id);
}

long
btorfmt_max_id (BtorFormatReader *bfr)
{
  return bfr->ntable - 1;
}
