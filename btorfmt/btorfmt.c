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
  BtorFormatLine **lines, **table;
  long szlines, nlines, sztable, ntable, szbuf, nbuf, lineno;
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

static void
msg_bfr (BtorFormatReader *bfr, int level, const char *fmt, ...)
{
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
  if (bfr->lines)
  {
    free (bfr->lines);
    bfr->lines  = 0;
    bfr->nlines = bfr->szlines = 0;
  }
  if (bfr->buf)
  {
    free (bfr->buf);
    bfr->buf  = 0;
    bfr->nbuf = bfr->szbuf = 0;
  }
  free (bfr->prefix);
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
pushl_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (bfr->nlines >= bfr->szlines)
  {
    bfr->szlines = bfr->szlines ? 2 * bfr->szlines : 1;
    bfr->lines   = realloc (bfr->lines, bfr->szlines * sizeof *bfr->lines);
  }
  bfr->lines[bfr->nlines++] = l;
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
              const char *tagastr,
              BtorFormatTag tag)
{
  BtorFormatLine *res;
  assert (0 < id);
  assert (bfr->ntable <= id);
  res = malloc (sizeof *res);
  memset (res, 0, sizeof (*res));
  res->id      = id;
  res->tag     = tag;
  res->tagastr = tagastr;
  while (bfr->ntable < id) pusht_bfr (bfr, 0);
  assert (bfr->ntable == id);
  pusht_bfr (bfr, res);
  assert (bfr->table[id] == res);
  return res;
}

static BtorFormatLine *
parse_arg_bfr (BtorFormatReader *bfr)
{
  BtorFormatLine *res;
  long id;
  if (!parse_id_bfr (bfr, &id)) return 0;
  assert (bfr->ntable > 0);
  if (id >= bfr->ntable - 1)
  {
    (void) perr_bfr (bfr, "argument id too large");
    return 0;
  }
  res = bfr->table[id];
  if (!res)
  {
    (void) perr_bfr (bfr, "undefined argument id");
    return 0;
  }
  return res;
}

static BtorFormatLine *
parse_bit_vector_arg_bfr (BtorFormatReader *bfr)
{
  BtorFormatLine *res = parse_arg_bfr (bfr);
  if (res && res->type.idxlen)
  {
    (void) perr_bfr (bfr, "expected bit-vector argument");
    return 0;
  }
  return res;
}

static int
parse_two_args_with_same_len (BtorFormatReader *bfr, BtorFormatLine *l)
{
  if (!(l->arg[0] = parse_bit_vector_arg_bfr (bfr))) return 0;
  if (!(l->arg[1] = parse_bit_vector_arg_bfr (bfr))) return 0;
  if (l->arg[0]->type.len != l->arg[1]->type.len)
    return perr_bfr (bfr, "length of arguments does not match");
  return 1;
}

static int
parse_op2_bfr (BtorFormatReader *bfr, BtorFormatLine *l)
{
  pushl_bfr (bfr, l);
  return 0;
}

#define PARSE(NAME, GENERIC)                                     \
  do                                                             \
  {                                                              \
    if (!strcmp (tag, #NAME))                                    \
    {                                                            \
      BtorFormatLine *LINE =                                     \
          new_line_bfr (bfr, id, #NAME, BTOR_FORMAT_TAG_##NAME); \
      if (!parse_len_bfr (bfr, &LINE->type.len)) return 0;       \
      if (!getc_bfr (bfr) == ' ')                                \
        return perr_bfr (bfr, "expected space after length");    \
      return parse_##GENERIC##_bfr (bfr, LINE);                  \
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
  if (id < bfr->ntable) perr_bfr (bfr, "id out-of-order");
  bfr->nbuf = 0;
  while ('a' <= (ch = getc_bfr (bfr)) && ch <= 'z') pushc_bfr (bfr, ch);
  if (ch != ' ' || !bfr->nbuf) return perr_bfr (bfr, "expected tag");
  pushc_bfr (bfr, 0);
  tag = bfr->buf;
  PARSE (and, op2);
  return perr_bfr (bfr, "invalid tag");
}

BtorFormatLine **
read_btor_format_lines (BtorFormatReader *bfr, FILE *file)
{
  reset_bfr (bfr);
  bfr->lineno = 1;
  bfr->saved  = EOF;
  bfr->file   = file;
  while (readl_bfr (bfr))
    ;
  if (bfr->error) return 0;
  pushl_bfr (bfr, 0);
  return bfr->lines;
}

const char *
error_btor_format_reader (BtorFormatReader *bfr)
{
  return bfr->error;
}
