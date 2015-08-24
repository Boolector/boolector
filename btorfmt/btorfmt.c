/*
The BtorFMT software provides a generic parser for the BTOR format.
In contrast to Boolector it falls under the following MIT style license:

Copyright (c) 2012-2015, Armin Biere, Johannes Kepler University, Linz

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
  long sztable, ntable, szbuf, nbuf, lineno;
  int verbosity, saved;
  char *buf;
  FILE *file;
};

BtorFormatReader *
new_btor_format_reader ()
{
  BtorFormatReader *res = malloc (sizeof *res);
  if (!res) return 0;
  memset (res, 0, sizeof *res);
  res->prefix = strdup ("");
  return res;
}

void
set_btor_format_reader_verbosity (BtorFormatReader *bfr, int verbosity)
{
  bfr->verbosity = verbosity;
}

void
set_btor_format_reader_prefix (BtorFormatReader *bfr, const char *prefix)
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
delete_btor_format_reader (BtorFormatReader *bfr)
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
perr_bfr (BtorFormatReader *bfr, const char *str)
{
  assert (!bfr->error);
  bfr->error = malloc (strlen (str) + 20);
  sprintf (bfr->error, "line %ld: %s", bfr->lineno, str);
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
parse_len_bfr (BtorFormatReader *bfr, int *res)
{
  long len;
  int ch;
  ch = getc_bfr (bfr);
  if (ch == '0')
    return perr_bfr (bfr, "length should start with non-zero digit");
  if (!isdigit (ch)) return perr_bfr (bfr, "length should start with digit");
  len = ch - '0';
  while (isdigit (ch = getc_bfr (bfr)))
  {
    len = 10 * len + (ch - '0');
    if (len >= BTOR_FORMAT_MAXLEN)
      return perr_bfr (bfr, "length exceeds maximum");
  }
  ungetc_bfr (bfr, ch);
  *res = len;
  return 1;
}

static BtorFormatLine *
new_line_bfr (BtorFormatReader *bfr,
              long id,
              const char *name,
              BtorFormatTag tag)
{
  BtorFormatLine *res;
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

static BtorFormatLine *
id2line_bfr (BtorFormatReader *bfr, long id)
{
  long absid = labs (id);
  if (!absid || absid >= bfr->ntable) return 0;
  return bfr->table[absid];
}

static long
parse_arg_bfr (BtorFormatReader *bfr)
{
  long res, absres;
  if (!parse_signed_id_bfr (bfr, &res)) return 0;
  absres = labs (res);
  if (absres >= bfr->ntable)
  {
    (void) perr_bfr (bfr, "argument id too large");
    return 0;
  }
  if (!(bfr->table[absres]))
  {
    (void) perr_bfr (bfr, "undefined argument id");
    return 0;
  }
  return res;
}

static long
parse_bit_vector_arg_bfr (BtorFormatReader *bfr)
{
  BtorFormatLine *l;
  long res;
  if (!(res = parse_arg_bfr (bfr))) return 0;
  l = id2line_bfr (bfr, res);
  if (l->type.idxlen)
  {
    (void) perr_bfr (bfr, "expected bit-vector argument");
    return 0;
  }
  return res;
}

static int
parse_two_args_with_same_len (BtorFormatReader *bfr, BtorFormatLine *l)
{
  BtorFormatLine *l0, *l1;
  int ch;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after length");
  if (!(l->arg[0] = parse_bit_vector_arg_bfr (bfr))) return 0;
  if (getc_bfr (bfr) != ' ')
    return perr_bfr (bfr, "expected space after first argument");
  if (!(l->arg[1] = parse_bit_vector_arg_bfr (bfr))) return 0;
  l0 = id2line_bfr (bfr, l->arg[0]);
  l1 = id2line_bfr (bfr, l->arg[1]);
  if (l0->type.len != l1->type.len)
    return perr_bfr (bfr, "length of arguments does not match");
  ch = getc_bfr (bfr);
  if (ch == ' ')
    return perr_bfr (bfr,
                     "unexpected trailing space (after two argument operator)");
  if (ch != '\n')
    return perr_bfr (bfr, "expected new-line (after two argument operator)");
  l->arity = 2;
  return 1;
}

static int
parse_op2_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  BtorFormatLine *arg;
  assert (l->type.len > 0);
  assert (!l->type.idxlen);
  if (!parse_two_args_with_same_len (bfr, l)) return 0;
  arg = id2line_bfr (bfr, l->arg[0]);
  if (arg->type.len != l->type.len)
    return perr_bfr (bfr, "arguments length does not match output length");
  return 1;
}

static int
parse_no_arg_const_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  int ch = getc_bfr (bfr);
  if (ch == ' ')
    return perr_bfr (bfr, "unexpected space (after no argument constant)");
  if (ch != '\n')
    return perr_bfr (bfr, "expected new-line (after no argument constant)");
  l->arity = 0;
  return 1;
}

#define PARSE(NAME, GENERIC)                                     \
  do                                                             \
  {                                                              \
    if (!strcmp (tag, #NAME))                                    \
    {                                                            \
      BtorFormatLine *LINE =                                     \
          new_line_bfr (bfr, id, #NAME, BTOR_FORMAT_TAG_##NAME); \
      if (parse_len_bfr (bfr, &LINE->type.len)                   \
          && parse_##GENERIC##_bfr (bfr, LINE))                  \
      {                                                          \
        pusht_bfr (bfr, LINE);                                   \
        assert (bfr->table[id] == LINE);                         \
        return 1;                                                \
      }                                                          \
      else                                                       \
      {                                                          \
        free (LINE);                                             \
        return 0;                                                \
      }                                                          \
    }                                                            \
  } while (0)

static int
readl_bfr (BtorFormatReader *bfr)
{
  const char *tag;
  long id;
  int ch;
START:
  ch = getc_bfr (bfr);
  if (ch == EOF) return 0;
  if (ch == '\n') goto START;
  if (ch == ' ')
    return perr_bfr (bfr, "unexpected space character at start of line");
  if (ch == '\t')
    return perr_bfr (bfr, "unexpected tab character at start of line");
  if (ch == ';')
  {
    while ((ch = getc_bfr (bfr)) != '\n')
      if (ch == EOF) return perr_bfr (bfr, "unexpected end-of-file in comment");
    goto START;
  }
  ungetc_bfr (bfr, ch);
  if (!parse_id_bfr (bfr, &id)) return 0;
  if (getc_bfr (bfr) != ' ') return perr_bfr (bfr, "expected space after id");
  if (id < bfr->ntable) return perr_bfr (bfr, "id out-of-order");
  bfr->nbuf = 0;
  while ('a' <= (ch = getc_bfr (bfr)) && ch <= 'z') pushc_bfr (bfr, ch);
  if (ch != ' ' || !bfr->nbuf) return perr_bfr (bfr, "expected tag");
  pushc_bfr (bfr, 0);
  tag = bfr->buf;
  switch (bfr->buf[0])
  {
    case 'a':
      PARSE (add, op2);
      PARSE (and, op2);
      break;
    case 'i': PARSE (implies, op2); break;
    case 'm': PARSE (mul, op2); break;
    case 'n':
      PARSE (nand, op2);
      PARSE (nor, op2);
      break;
    case 'o':
      PARSE (one, no_arg_const);
      PARSE (ones, no_arg_const);
      PARSE (or, op2);
      break;
    case 's':
      PARSE (sdiv, op2);
      PARSE (srem, op2);
      PARSE (smod, op2);
      PARSE (sub, op2);
      break;
    case 'u':
      PARSE (udiv, op2);
      PARSE (urem, op2);
      break;
    case 'x':
      PARSE (xnor, op2);
      PARSE (xor, op2);
      break;
    case 'z': PARSE (zero, no_arg_const); break;
  }
  return perr_bfr (bfr, "invalid tag");
}

int
read_btor_format_lines (BtorFormatReader *bfr, FILE *file)
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
error_btor_format_reader (BtorFormatReader *bfr)
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
iterate_btor_format_line (BtorFormatReader *bfr)
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
next_btor_format_line (BtorFormatLineIterator *it)
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
get_btor_format_line_from_id (BtorFormatReader *bfr, long id)
{
  return id2line_bfr (bfr, id);
}
