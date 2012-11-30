#include "btorfmt.h"

#include <assert.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

struct BtorFormatReader
{
  char* error;
  BtorFormatLine** lines;
  int szlines, nlines, saved, savedy;
  struct
  {
    int x, y;
  } coo;
  FILE* file;
};

BtorFormatReader*
new_btor_format_reader ()
{
  BtorFormatReader* res = malloc (sizeof *res);
  if (!res) return 0;
  memset (res, 0, sizeof *res);
  res->saved = EOF;
  return res;
}

static void
reset_bfr (BtorFormatReader* bfr)
{
  int i;
  assert (bfr);
  if (bfr->error) free (bfr->error), bfr->error = 0;
  if (bfr->lines)
  {
    for (i = 0; i < bfr->nlines; bfr++)
    {
      BtorFormatLine* l = bfr->lines[i];
      if (!l) continue;
      if (l->symbol) free (l->symbol);
      free (l);
    }
    free (bfr->lines), bfr->lines = 0;
    bfr->nlines = bfr->szlines = 0;
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
  int ch = bfr->saved;
  if (ch == EOF)
    ch = getc (bfr->file);
  else
    bfr->saved = EOF;
  if (ch == '\n')
  {
    bfr->coo.x++;
    bfr->savedy = bfr->coo.y;
    bfr->coo.y  = 0;
  }
  else
    bfr->coo.y++;
  return ch;
}

#if 0
static void ungetc_bfr (BtorFormatReader * bfr, int ch) {
  assert (bfr->saved == EOF);
  if (ch == '\n') {
    assert (bfr->coo.x > 1), bfr->coo.x--;
    bfr->coo.y = bfr->savedy;
  } else if (ch != EOF) assert (bfr->coo.y > 0), bfr->coo.y--;
  bfr->saved = ch;
}
#endif

static int
perr_bfr (BtorFormatReader* bfr, const char* str)
{
  assert (!bfr->error);
  bfr->error = malloc (strlen (str) + 20);
  sprintf (bfr->error, "line %d column %d: %s", bfr->coo.x, bfr->coo.y, str);
  return 0;
}

static int
readl_bfr (BtorFormatReader* bfr)
{
  int ch;
RESTART:
  ch = getc_bfr (bfr);
  if (ch == EOF) return 0;
  if (ch == '\n') goto RESTART;
  if (ch == ' ')
    return perr_bfr (bfr, "unexpected space character at start of line");
  if (ch == '\t')
    return perr_bfr (bfr, "unexpected tab character at start of line");
  if (ch == ';')
  {
    while ((ch = getc_bfr (bfr)) != '\n')
      if (ch == EOF) return perr_bfr (bfr, "unexpected end-of-file in comment");
  }
  if (ch == '0') return perr_bfr (bfr, "expected non-zero digit");
  if (!isdigit (ch)) return perr_bfr (bfr, "expected digit");
  return 1;
}

static void
push_line_bfr (BtorFormatReader* bfr, BtorFormatLine* l)
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
  bfr->coo.x = 1, bfr->coo.y = 0;
  bfr->saved = EOF;
  bfr->file  = file;
  while (readl_bfr (bfr))
    ;
  if (!bfr->error) push_line_bfr (bfr, 0);
  return bfr->error ? 0 : bfr->lines;
}
