/*
The BtorFMT software provides a generic parser for the BTOR format.
In contrast to Boolector it falls under the following MIT style license:

Copyright (c) 2012-2015, Armin Biere, Johannes Kepler University, Linz
Copyright (c) 2017, Mathias Preiner

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.
*/

#include "btorfmt.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

struct BtorFormatReader
{
  char *error, *prefix;
  BtorFormatLine **table, *new_line;
  BtorFormatSort** stable;
  long sztable, ntable, szstable, nstable, szbuf, nbuf, lineno;
  int verbosity, saved;
  char* buf;
  FILE* file;
};

BtorFormatReader*
new_btor_format_reader ()
{
  BtorFormatReader* res = malloc (sizeof *res);
  if (!res) return 0;
  memset (res, 0, sizeof *res);
  res->prefix = strdup ("");
  return res;
}

void
set_btor_format_reader_verbosity (BtorFormatReader* bfr, int verbosity)
{
  bfr->verbosity = verbosity;
}

void
set_btor_format_reader_prefix (BtorFormatReader* bfr, const char* prefix)
{
  free (bfr->prefix);
  bfr->prefix = strdup (prefix ? prefix : "");
}

#if 0
static void msg_bfr (BtorFormatReader * bfr, int level,
                     const char * fmt, ...) {
  va_list ap;
  if (bfr->verbosity < level) return;
  va_start (ap, fmt);
  fflush (stdout);
  fputs (bfr->prefix, stderr);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}
#endif

static void
reset_bfr (BtorFormatReader* bfr)
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
      BtorFormatLine* l = bfr->table[i];
      if (!l) continue;
      if (l->symbol) free (l->symbol);
      if (l->constant) free (l->constant);
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
  if (bfr->prefix)
  {
    free (bfr->prefix);
    bfr->prefix = 0;
  }
}

void
delete_btor_format_reader (BtorFormatReader* bfr)
{
  reset_bfr (bfr);
  free (bfr);
}

static int
getc_bfr (BtorFormatReader* bfr)
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
ungetc_bfr (BtorFormatReader* bfr, int ch)
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
perr_bfr (BtorFormatReader* bfr, const char* fmt, ...)
{
  assert (!bfr->error);
  char buf[1024];

  va_list ap;
  va_start (ap, fmt);
  vsnprintf (buf, 1023, fmt, ap);
  va_end (ap);
  buf[1023] = '\0';

  bfr->error = malloc (strlen (buf) + 28);
  sprintf (bfr->error, "line %ld: %s", bfr->lineno, buf);
  return 0;
}

static void
pushc_bfr (BtorFormatReader* bfr, int ch)
{
  if (bfr->nbuf >= bfr->szbuf)
  {
    bfr->szbuf = bfr->szbuf ? 2 * bfr->szbuf : 1;
    bfr->buf   = realloc (bfr->buf, bfr->szbuf * sizeof *bfr->buf);
  }
  bfr->buf[bfr->nbuf++] = ch;
}

static void
pusht_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  if (bfr->ntable >= bfr->sztable)
  {
    bfr->sztable = bfr->sztable ? 2 * bfr->sztable : 1;
    bfr->table   = realloc (bfr->table, bfr->sztable * sizeof *bfr->table);
  }
  bfr->table[bfr->ntable++] = l;
}

static int
parse_id_bfr (BtorFormatReader* bfr, long* res)
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
parse_signed_id_bfr (BtorFormatReader* bfr, long* res)
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
parse_bit_width_bfr (BtorFormatReader* bfr, unsigned* res)
{
  long num;
  int ch;
  ch = getc_bfr (bfr);
  if (!isdigit (ch)) return perr_bfr (bfr, "expected number but got '%c'", ch);
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

static BtorFormatLine*
id2line_bfr (BtorFormatReader* bfr, long id)
{
  long absid = labs (id);
  if (!absid || absid >= bfr->ntable) return 0;
  return bfr->table[absid];
}

static int
skip_comment (BtorFormatReader* bfr)
{
  int ch;
  while ((ch = getc_bfr (bfr)) != '\n')
  {
    if (ch == EOF) return perr_bfr (bfr, "unexpected end-of-file in comment");
  }
  return 1;
}

static int
cmp_sort_ids (BtorFormatReader* bfr, long sort_id1, long sort_id2)
{
  (void) bfr;
  // TODO: better sort comparison with sort hashing
  //       we can have differnt sort ids that are essentially the same sort
  //       1 sort bitvec 2
  //       2 sort bitvec 2
  //       1 != 2, but it the same sort
  return sort_id1 - sort_id2;
}

static int
cmp_sorts (BtorFormatReader* bfr, BtorFormatLine* l1, BtorFormatLine* l2)
{
  return cmp_sort_ids (bfr, l1->sort.id, l2->sort.id);
}

static int
parse_sort_id_bfr (BtorFormatReader* bfr, BtorFormatSort* res)
{
  long sort_id;
  BtorFormatLine* s;
  if (!parse_id_bfr (bfr, &sort_id)) return 0;

  if (sort_id >= bfr->ntable || id2line_bfr (bfr, sort_id) == 0)
    return perr_bfr (bfr, "undefined sort id");

  s = id2line_bfr (bfr, sort_id);
  if (s->tag != BTOR_FORMAT_TAG_sort)
    return perr_bfr (bfr, "id after tag is not a sort id");
  *res = s->sort;
  return 1;
}

static const char*
parse_tag (BtorFormatReader* bfr)
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
parse_symbol_bfr (BtorFormatReader* bfr)
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
  if (!bfr->nbuf) return perr_bfr (bfr, "empty symbol");
  pushc_bfr (bfr, 0);
  return 1;
}

static int
parse_opt_symbol_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
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
      l->symbol = strdup (bfr->buf);
    }
  }
  else if (ch != '\n')
    return perr_bfr (
        bfr, "expected new-line at the end of the line got '%c'", ch);
  return 1;
}

static BtorFormatLine*
new_line_bfr (BtorFormatReader* bfr,
              long id,
              const char* name,
              BtorFormatTag tag)
{
  BtorFormatLine* res;
  assert (0 < id);
  assert (bfr->ntable <= id);
  res = malloc (sizeof *res);
  memset (res, 0, sizeof (*res));
  res->id   = id;
  res->tag  = tag;
  res->name = name;
  while (bfr->ntable < id) pusht_bfr (bfr, 0);
  assert (bfr->ntable == id);
  return res;
}

static int
sort_check_bitvec (BtorFormatReader* bfr,
                   BtorFormatLine* l,
                   BtorFormatLine* args[])
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
sort_check_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  BtorFormatLine* args[3];
  unsigned i;
  for (i = 0; i < l->nargs; i++) args[i] = id2line_bfr (bfr, l->arg[i]);

  switch (l->tag)
  {
    /* n -> n */
    case BTOR_FORMAT_TAG_dec:
    case BTOR_FORMAT_TAG_inc:
    case BTOR_FORMAT_TAG_neg:
    case BTOR_FORMAT_TAG_not:
    case BTOR_FORMAT_TAG_output:
      assert (l->nargs == 1);
      if (!sort_check_bitvec (bfr, l, args)) return 0;
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
      if (!sort_check_bitvec (bfr, l, args)) return 0;
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
      if (!sort_check_bitvec (bfr, l, args)) return 0;
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
      if (!sort_check_bitvec (bfr, l, args)) return 0;
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
      if (!sort_check_bitvec (bfr, l, args)) return 0;
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
      if (!sort_check_bitvec (bfr, l, args)) return 0;
      /* NOTE: this cast is safe since l->arg[1] and l->arg[2] contains
       *       upper and lower indices, which are unsigned */
      unsigned upper = (unsigned) l->arg[1];
      unsigned lower = (unsigned) l->arg[2];
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
      if (!sort_check_bitvec (bfr, l, args)) return 0;
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
      // TODO: check that every argument is 1?
      break;

    case BTOR_FORMAT_TAG_sext:
    case BTOR_FORMAT_TAG_uext:
      assert (l->nargs == 1);
      if (!sort_check_bitvec (bfr, l, args)) return 0;
      /* NOTE: this cast is safe since l->arg[1] contains the extension
       *       bit-width, which is unsigned */
      unsigned ext = args[0]->sort.bitvec.width + (unsigned) l->arg[1];
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
parse_arg_bfr (BtorFormatReader* bfr)
{
  BtorFormatLine* l;
  long res, absres;
  if (!parse_signed_id_bfr (bfr, &res)) return 0;
  absres = labs (res);
  if (absres >= bfr->ntable)
    return perr_bfr (bfr, "argument id too large (undefined)");
  l = bfr->table[absres];
  if (!l) return perr_bfr (bfr, "undefined argument id");
  if (!l->sort.id) return perr_bfr (bfr, "declaration used as argument");
  return res;
}

static int
parse_sort_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  const char* tag;
  BtorFormatSort tmp, s;
  tag = parse_tag (bfr);
  if (!tag) return 0;
  if (!strcmp (tag, "bitvec"))
  {
    tmp.tag  = BTOR_FORMAT_TAG_SORT_bitvec;
    tmp.name = "bitvec";
    if (!parse_bit_width_bfr (bfr, &tmp.bitvec.width))
      return perr_bfr (bfr, "invalid width for sort bitvec");
    if (tmp.bitvec.width == 0)
      return perr_bfr (bfr, "bit width must be greater than 0");
  }
  else if (!strcmp (tag, "array"))
  {
    tmp.tag  = BTOR_FORMAT_TAG_SORT_array;
    tmp.name = "array";
    if (!parse_sort_id_bfr (bfr, &s))
      return perr_bfr (bfr, "invalid index sort for array");
    if (getc_bfr (bfr) != ' ') return perr_bfr (bfr, "expected space");
    tmp.array.index = s.id;
    if (!parse_sort_id_bfr (bfr, &s))
    {
      printf ("id: %ld\n", s.id);
      return perr_bfr (bfr, "invalid element sort for array");
    }
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
parse_args (BtorFormatReader* bfr, BtorFormatLine* l, unsigned nargs)
{
  assert (nargs <= 3);

  unsigned i = 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after sort id");
  while (i < nargs)
  {
    if (!(l->arg[i] = parse_arg_bfr (bfr))) return 0;
    if (i < nargs - 1 && getc_bfr (bfr) != ' ')
      return perr_bfr (bfr, "expected space after argument (argument missing)");
    i++;
  }
  l->nargs = nargs;
  return 1;
}

static int
parse_unary_op_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 1)) return 0;
  return 1;
}

static int
parse_ext_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  unsigned ext;
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 1)) return 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after first argument");
  if (!parse_bit_width_bfr (bfr, &ext)) return 0;
  l->arg[1] = ext;
  return 1;
}

static int
parse_slice_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  unsigned lower;
  if (!parse_ext_bfr (bfr, l)) return 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after second argument");
  if (!parse_bit_width_bfr (bfr, &lower)) return 0;
  l->arg[2] = lower;
  if (lower > l->arg[1])
    return perr_bfr (bfr, "lower has to be less than or equal to upper");
  return 1;
}

static int
parse_binary_op_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 2)) return 0;
  return 1;
}

static int
parse_ternary_op_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 3)) return 0;
  return 1;
}

static int
parse_constant_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
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
  else if (l->tag == BTOR_FORMAT_TAG_constd)
  {
    // TODO: check if number fits into sort.bitvec.width bits
  }
  else if (l->tag == BTOR_FORMAT_TAG_consth
           && strlen (bfr->buf) * 4 != l->sort.bitvec.width)
  {
    return perr_bfr (bfr,
                     "constant '%s' does not match bit-vector sort size %u",
                     bfr->buf,
                     l->sort.bitvec.width);
  }
  l->constant = strdup (bfr->buf);
  return 1;
}

static int
parse_input_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  return parse_sort_id_bfr (bfr, &l->sort);
}

static int
is_constant_bfr (BtorFormatReader* bfr, long id)
{
  BtorFormatLine* l = id2line_bfr (bfr, id);
  assert (l);
  BtorFormatTag tag = l->tag;
  return tag == BTOR_FORMAT_TAG_const || tag == BTOR_FORMAT_TAG_constd
         || tag == BTOR_FORMAT_TAG_consth || tag == BTOR_FORMAT_TAG_one
         || tag == BTOR_FORMAT_TAG_ones || tag == BTOR_FORMAT_TAG_zero;
}

static int
parse_init_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  BtorFormatLine* state;
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 2)) return 0;
  if (l->arg[0] < 0) return perr_bfr (bfr, "invalid negated first argument");
  state = id2line_bfr (bfr, l->arg[0]);
  // TODO: allow initialization of arrays?
  if (state->tag != BTOR_FORMAT_TAG_state)
    return perr_bfr (bfr, "expected state as first argument");
  if (!is_constant_bfr (bfr, l->arg[1]))
    return perr_bfr (bfr, "expected id of constant as second argument");
  if (state->init)
    return perr_bfr (bfr, "state %ld initialized twice", state->id);
  state->init = l->arg[1];
  return 1;
}

static int
parse_next_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  BtorFormatLine* state;
  if (!parse_sort_id_bfr (bfr, &l->sort)) return 0;
  if (!parse_args (bfr, l, 2)) return 0;
  if (l->arg[0] < 0) return perr_bfr (bfr, "invalid negated first argument");
  state = id2line_bfr (bfr, l->arg[0]);
  if (state->tag != BTOR_FORMAT_TAG_state)
    return perr_bfr (bfr, "expected state as first argument");
  if (state->next)
    return perr_bfr (bfr, "next for state %ld set twice", state->id);
  state->next = l->arg[1];
  return 1;
}

static int
parse_output_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  (void) bfr;
  (void) l;
  return 0;
}

static int
parse_constraint_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  /* contraint, bad, justice, fairness do not have a sort id after the tag */
  if (!(l->arg[0] = parse_arg_bfr (bfr))) return 0;
  BtorFormatLine* arg = id2line_bfr (bfr, l->arg[0]);
  if (arg->tag == BTOR_FORMAT_TAG_sort)
    return perr_bfr (bfr, "unexpected sort id after tag");
  l->nargs = 1;
  return 1;
}

static int
parse_justice_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  // TODO: implement
  (void) bfr;
  (void) l;
  return 1;
}

#define PARSE(NAME, GENERIC)                                                  \
  do                                                                          \
  {                                                                           \
    if (!strcmp (tag, #NAME))                                                 \
    {                                                                         \
      BtorFormatLine* LINE =                                                  \
          new_line_bfr (bfr, id, #NAME, BTOR_FORMAT_TAG_##NAME);              \
      if (parse_##GENERIC##_bfr (bfr, LINE))                                  \
      {                                                                       \
        pusht_bfr (bfr, LINE);                                                \
        assert (bfr->table[id] == LINE);                                      \
        if (!sort_check_bfr (bfr, LINE) || !parse_opt_symbol_bfr (bfr, LINE)) \
        {                                                                     \
          return 0;                                                           \
        }                                                                     \
        return 1;                                                             \
      }                                                                       \
      else                                                                    \
      {                                                                       \
        return 0;                                                             \
      }                                                                       \
    }                                                                         \
  } while (0)

// TODO: can next/init be operand of other ops?
//         -> if not check that next/init is not operand of any other op
//       can arrays be initialized
//         -> if yes, with constants? all values are set to constant?
//         -> of lambdas?  -> more complicated
//
//

// draft changes:
// 1) allow white spaces at beginning of the line
// 2) allow comments at the end of the line

static int
readl_bfr (BtorFormatReader* bfr)
{
  const char* tag;
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
  tag = parse_tag (bfr);
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
    case 'j':
      //      PARSE (justice, justice);
      break;
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
read_btor_format_lines (BtorFormatReader* bfr, FILE* file)
{
  reset_bfr (bfr);
  bfr->lineno = 1;
  bfr->saved  = EOF;
  bfr->file   = file;
  while (readl_bfr (bfr))
    ;
  return !bfr->error;
}

const char*
error_btor_format_reader (BtorFormatReader* bfr)
{
  return bfr->error;
}

static long
find_non_zero_line_bfr (BtorFormatReader* bfr, long start)
{
  long res;
  for (res = start; res < bfr->ntable; res++)
    if (bfr->table[res]) return res;
  return 0;
}

BtorFormatLineIterator
iterate_btor_format_line (BtorFormatReader* bfr)
{
  BtorFormatLineIterator res;
  res.reader = bfr;
  if (bfr->error)
    res.next = 0;
  else
    res.next = find_non_zero_line_bfr (bfr, 1);
  return res;
}

BtorFormatLine*
next_btor_format_line (BtorFormatLineIterator* it)
{
  BtorFormatLine* res;
  if (!it->next) return 0;
  assert (0 < it->next);
  assert (it->next < it->reader->ntable);
  res      = it->reader->table[it->next];
  it->next = find_non_zero_line_bfr (it->reader, it->next + 1);
  return res;
}

BtorFormatLine*
get_btor_format_line_from_id (BtorFormatReader* bfr, long id)
{
  return id2line_bfr (bfr, id);
}
