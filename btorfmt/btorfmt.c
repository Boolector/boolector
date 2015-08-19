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
  BtorFormatLine** lines;
  int verbosity, szlines, nlines, szbuf, nbuf;
  char* buf;
  struct
  {
    int x, y;
  } coo, errcoo;
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
set_btor_format_reader_prefix (BtorFormatReader* bfr, char* prefix)
{
  free (bfr->prefix);
  bfr->prefix = strdup (prefix ? prefix : "");
}

static void
msg_bfr (BtorFormatReader* bfr, int level, const char* fmt, ...)
{
  va_list ap;
  if (bfr->verbosity < level) return;
  ap = va_start (ap, fmt);
  fflush (stdout);
  fputs (bfs->prefix, stderr);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stdrr);
}

static void
reset_bfr (BtorFormatReader* bfr)
{
  int i;
  assert (bfr);
  if (bfr->error) free (bfr->error), bfr->error = 0;
  if (bfr->lines)
  {
    for (i = 0; i < bfr->nlines; i++)
    {
      BtorFormatLine* l = bfr->lines[i];
      if (!l) continue;
      if (l->symbol) free (l->symbol);
      free (l);
    }
    free (bfr->lines);
    bfr->lines  = 0;
    bfr->nlines = bfr->szlines = 0;
  }
  free (bfr->prefix);
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
  int ch = getc (bfr->file);
  if (ch == '\n')
    bfr->coo.x++, bfr->coo.y = 1;
  else
    bfr->coo.y++;
  return ch;
}

static int
perr_bfr (BtorFormatReader* bfr, const char* str)
{
  assert (!bfr->error);
  bfr->error = malloc (strlen (str) + 20);
  sprintf (
      bfr->error, "line %d column %d: %s", bfr->errcoo.x, bfr->errcoo.y, str);
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

#define PARSETAG(TAG, STR)       \
  do                             \
  {                              \
    if (!strcmp (bfr->buf, STR)) \
    {                            \
      line.tag = TAG;            \
      goto TAGDONE;              \
    }                            \
  } while (0)

static int
readl_bfr (BtorFormatReader* bfr)
{
  BtorFormatLine line;
  int ch;
START:
  bfr->errcoo = bfr->coo;
  ch          = getc_bfr (bfr);
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
  if (ch == '0') return perr_bfr (bfr, "expected non-zero digit");
  if (!isdigit (ch)) return perr_bfr (bfr, "expected digit");
  memset (&line, 0, sizeof line);
  line.id = ch - '0';
  while (isdigit (ch = getc_bfr (bfr))) line.id = 10 * line.id + (ch - '0');
  if (ch != ' ') return perr_bfr (bfr, "expected space after id");
  bfr->errcoo = bfr->coo;
  bfr->nbuf   = 0;
  assert (!line.tag);
  assert (line.tag == BTOR_FORMAT_INVALID_TAG);
  while ('a' <= (ch = getc_bfr (bfr)) && ch <= 'z') pushc_bfr (bfr, ch);
  if (ch != ' ' || !bfr->nbuf) return perr_bfr (bfr, "expected tag");
  pushc_bfr (bfr, 0);
  PARSETAG (BTOR_FORMAT_TAG_ADD, "add");
  PARSETAG (BTOR_FORMAT_TAG_AND, "and");
  PARSETAG (BTOR_FORMAT_TAG_ARRAY, "array");
  PARSETAG (BTOR_FORMAT_TAG_CONCAT, "concat");
  PARSETAG (BTOR_FORMAT_TAG_COND, "cond");
  PARSETAG (BTOR_FORMAT_TAG_ACOND, "acond");
  PARSETAG (BTOR_FORMAT_TAG_CONST, "const");
  PARSETAG (BTOR_FORMAT_TAG_CONSTD, "constd");
  PARSETAG (BTOR_FORMAT_TAG_CONSTH, "consth");
  PARSETAG (BTOR_FORMAT_TAG_EQ, "eq");
  PARSETAG (BTOR_FORMAT_TAG_IFF, "iff");
  PARSETAG (BTOR_FORMAT_TAG_IMPLIES, "implies");
  PARSETAG (BTOR_FORMAT_TAG_MUL, "mul");
  PARSETAG (BTOR_FORMAT_TAG_NAND, "nand");
  PARSETAG (BTOR_FORMAT_TAG_NEG, "neg");
  PARSETAG (BTOR_FORMAT_TAG_INC, "inc");
  PARSETAG (BTOR_FORMAT_TAG_DEC, "dec");
  PARSETAG (BTOR_FORMAT_TAG_NE, "ne");
  PARSETAG (BTOR_FORMAT_TAG_NEXT, "next");
  PARSETAG (BTOR_FORMAT_TAG_ANEXT, "anext");
  PARSETAG (BTOR_FORMAT_TAG_NOR, "nor");
  PARSETAG (BTOR_FORMAT_TAG_NOT, "not");
  PARSETAG (BTOR_FORMAT_TAG_ONE, "one");
  PARSETAG (BTOR_FORMAT_TAG_ONES, "ones");
  PARSETAG (BTOR_FORMAT_TAG_OR, "or");
  PARSETAG (BTOR_FORMAT_TAG_PROXY, "proxy");
  PARSETAG (BTOR_FORMAT_TAG_READ, "read");
  PARSETAG (BTOR_FORMAT_TAG_REDAND, "redand");
  PARSETAG (BTOR_FORMAT_TAG_REDOR, "redor");
  PARSETAG (BTOR_FORMAT_TAG_REDXOR, "redxor");
  PARSETAG (BTOR_FORMAT_TAG_ROL, "rol");
  PARSETAG (BTOR_FORMAT_TAG_ROOT, "root");
  PARSETAG (BTOR_FORMAT_TAG_ROR, "ror");
  PARSETAG (BTOR_FORMAT_TAG_SADDO, "saddo");
  PARSETAG (BTOR_FORMAT_TAG_SDIVO, "sdivo");
  PARSETAG (BTOR_FORMAT_TAG_SDIV, "sdiv");
  PARSETAG (BTOR_FORMAT_TAG_SEXT, "sext");
  PARSETAG (BTOR_FORMAT_TAG_SGTE, "sgte");
  PARSETAG (BTOR_FORMAT_TAG_SGT, "sgt");
  PARSETAG (BTOR_FORMAT_TAG_SLICE, "slice");
  PARSETAG (BTOR_FORMAT_TAG_SLL, "sll");
  PARSETAG (BTOR_FORMAT_TAG_SLTE, "slte");
  PARSETAG (BTOR_FORMAT_TAG_SLT, "slt");
  PARSETAG (BTOR_FORMAT_TAG_SMOD, "smod");
  PARSETAG (BTOR_FORMAT_TAG_SMULO, "smulo");
  PARSETAG (BTOR_FORMAT_TAG_SRA, "sra");
  PARSETAG (BTOR_FORMAT_TAG_SREM, "srem");
  PARSETAG (BTOR_FORMAT_TAG_SRL, "srl");
  PARSETAG (BTOR_FORMAT_TAG_SSUBO, "ssubo");
  PARSETAG (BTOR_FORMAT_TAG_SUB, "sub");
  PARSETAG (BTOR_FORMAT_TAG_UADDO, "uaddo");
  PARSETAG (BTOR_FORMAT_TAG_UDIV, "udiv");
  PARSETAG (BTOR_FORMAT_TAG_UEXT, "uext");
  PARSETAG (BTOR_FORMAT_TAG_UGTE, "ugte");
  PARSETAG (BTOR_FORMAT_TAG_UGT, "ugt");
  PARSETAG (BTOR_FORMAT_TAG_ULTE, "ulte");
  PARSETAG (BTOR_FORMAT_TAG_ULT, "ult");
  PARSETAG (BTOR_FORMAT_TAG_UMULO, "umulo");
  PARSETAG (BTOR_FORMAT_TAG_UREM, "urem");
  PARSETAG (BTOR_FORMAT_TAG_USUBO, "usubo");
  PARSETAG (BTOR_FORMAT_TAG_VAR, "var");
  PARSETAG (BTOR_FORMAT_TAG_WRITE, "write");
  PARSETAG (BTOR_FORMAT_TAG_XNOR, "xnor");
  PARSETAG (BTOR_FORMAT_TAG_XOR, "xor");
  PARSETAG (BTOR_FORMAT_TAG_ZERO, "zero");
  return perr_bfr (bfr, "invalid tag");
TAGDONE:
  return 1;
}

static void
pushl_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
{
  if (bfr->nlines >= bfr->szlines)
  {
    bfr->szlines = bfr->szlines ? 2 * bfr->szlines : 1;
    bfr->lines   = realloc (bfr->lines, bfr->szlines * sizeof *bfr->lines);
  }
  bfr->lines[bfr->nlines++] = l;
}

BtorFormatLine**
read_btor_format_lines (BtorFormatReader* bfr, FILE* file)
{
  reset_bfr (bfr);
  bfr->coo.x = bfr->coo.y = 1;
  bfr->file               = file;
  while (readl_bfr (bfr))
    ;
  if (bfr->error) return 0;
  pushl_bfr (bfr, 0);
  return bfr->lines;
}

const char*
error_btor_format_reader (BtorFormatReader* bfr)
{
  return bfr->error;
}
