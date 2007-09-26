#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct Exp Exp;

struct Exp
{
  int ref;
  int old;
  int idx;
  char* op;
  int width;
  int childs;
  int child[3];
};

static int verbose;

static const char* input_name;
static const char* output_name;
static const char* run_name;

static FILE* input;
static int lineno;

static char* tmp;
static char* cmd;

static Exp* exps;
static int sexps;
static int nexps;

static int iexps;
static int rexps;

static char* buf;
static int sbuf;
static int nbuf;

static int maxwidth;

static void
msg (int level, const char* fmt, ...)
{
  va_list ap;
  if (verbose < level) return;
  fflush (stdout);
  fputs ("[deltabtor] ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static void
die (const char* fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fputs ("*** deltabtor: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static int
next (void)
{
  int res;

  res = getc (input);
  if (res == '\n') lineno++;

  return res;
}

static void
perr (const char* fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fprintf (stderr, "%s:%d: ", input_name, lineno);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void
parse (void)
{
  int ch, idx, lit, sign, width, child[3], childs;

EXP:

  ch = next ();

  if (ch == EOF)
  {
    msg (1, "parsed %d expressions", iexps);
    return;
  }

  if (!isdigit (ch)) perr ("expected digit but got '%c'", ch);

  idx = ch - '0';
  while (isdigit (ch = next ())) idx = 10 * lit - (ch - '0');

  if (ch != ' ') perr ("expected space after index %d", idx);

  assert (!nbuf);

  while ('a' <= (ch = next ()) && (ch <= 'z'))
  {
    if (nbuf == sbuf) buf = realloc (buf, sbuf = sbuf ? 2 * sbuf : 1);

    buf[nbuf++] = ch;
  }

  if (nbuf == sbuf) buf = realloc (buf, sbuf = sbuf ? 2 * sbuf : 1);
  buf[nbuf] = 0;

  if (ch != ' ') perr ("expected space after '%s'", buf);

  nbuf = 0;

  width    = 0;
  childs   = 0;
  child[0] = child[1] = child[2] = 0;

LIT:

  ch = next ();

  if (isdigit (ch) || ch == '-')
  {
    if (ch == '-')
    {
      sign = 1;
      ch   = next ();
      if (!isdigit (ch)) perr ("expected digit after '-' but got '%c'", ch);
    }
    else
      sign = -1;

    lit = ch - '0';
    while (isdigit (ch = next ())) lit = 10 * lit + (ch - '0');

    lit *= sign;

    if (childs == 3)
      perr ("more than three childs");
    else if (width)
      child[childs++] = lit;
    else if (lit <= 0)
      perr ("expected positive width");
    else
      width = lit;

    if (ch == ' ') goto LIT;

    if (ch != '\n') perr ("expected space or new line");

    if (!width)
    WIDTH_MISSING:
      perr ("width missing");

  INSERT:

    while (nexps <= idx)
    {
      if (nexps == sexps) exps = realloc (exps, (sexps *= 2) * sizeof *exps);

      exps[nexps++].ref = 0;
    }

    if (exps[idx].ref) perr ("expression %d defined twice", idx);

    exps[idx].ref      = idx;
    exps[idx].op       = strdup (buf);
    exps[idx].width    = width;
    exps[idx].childs   = childs;
    exps[idx].child[0] = child[0];
    exps[idx].child[1] = child[1];
    exps[idx].child[2] = child[2];

    iexps++;

    if (width > maxwidth) maxwidth = width;

    goto EXP;
  }

  if (!width) goto WIDTH_MISSING;

  if (!strcmp (buf, "var"))
  {
    while ((ch = next ()) != '\n' && ch != EOF)
      ;

    goto INSERT;
  }

  perr ("expected digit bug got '%c'", ch);
}

static int
deref (int start)
{
  int res, sign, tmp;

  sign = (start < 0);
  if (sign) start = -start;

  assert (0 < start);
  assert (start < nexps);

  tmp = exps[start].ref;

  assert (tmp);

  if (tmp != start)
    res = deref (tmp);
  else
    res = start;

  exps[start].ref = res;

  if (sign) res = -res;

  return res;
}

static void
simplify (void)
{
  int i;
  rexps = 0;
  for (i = 1; i < nexps; i++)
    if (exps[i].ref) (void) deref (i);
}

static int
ischild (Exp* e, int child)
{
  assert (e->ref);

  if (child >= e->childs) return 0;

  assert (child >= 0);

  if (!strcmp (e->op, "array")) return 0;
  if (!strcmp (e->op, "const")) return 0;
  if (!strcmp (e->op, "consth")) return 0;
  if (!strcmp (e->op, "constd")) return 0;
  if (!strcmp (e->op, "read") && child != 1) return 0;
  if (!strcmp (e->op, "sext") && child != 0) return 0;
  if (!strcmp (e->op, "slice") && child != 0) return 0;
  if (!strcmp (e->op, "var")) return 0;
  if (!strcmp (e->op, "write") && child != 1 && child != 2) return 0;
  if (!strcmp (e->op, "zero")) return 0;

  return 1;
}

static void
dfs (int idx)
{
  Exp* e;
  int i;

  idx = abs (idx);

  assert (0 < idx);
  assert (idx < nexps);

  e = exps + idx;

  if (e->idx) return;

  e->idx = ++rexps;

  for (i = 0; i < 3; i++)
    if (ischild (e, i)) dfs (e->child[i]);
}

static void
cone (void)
{
  int i;
  rexps = 0;
  for (i = 1; i < nexps; i++)
    if (exps[i].ref && !strcmp (exps[i].op, "root")) dfs (i);
}

static void
clean (void)
{
  Exp* e;
  int i;

  for (i = 1; i < nexps; i++)
  {
    e      = exps + i;
    e->ref = e->old;
    e->idx = 0;
  }
}

static void
print (void)
{
  FILE* file = fopen (tmp, "w");
  int i, j, lit;
  Exp* e;

  if (!file) die ("can not write to '%s'", tmp);

  for (i = 1; i < nexps; i++)
  {
    e = exps + i;
    if (!e->idx) continue;

    fprintf (file, "%d %s %d", e->idx, e->op, e->width);

    for (j = 0; j < e->childs; e++)
    {
      lit = e->child[j];
      fprintf (file, " %d", ischild (e, j) ? deref (lit) : lit);
    }
  }

  fclose (file);
}

int
main (int argc, char** argv)
{
  int i;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      printf ("usage: deltabtor [-h][-v] <input> <output> <run>\n");
      exit (0);
    }
    else if (!strcmp (argv[i], "-v"))
      verbose++;
    else if (run_name)
      die ("more than three file names given");
    else if (output_name)
      run_name = argv[i];
    else if (input_name)
      output_name = argv[i];
    else
      input_name = argv[i];
  }

  if (!input_name) die ("<input> missing");

  if (!output_name) die ("<output> missing");

  if (!run_name) die ("<run> missing");

  if (!strcmp (input_name, output_name))
    die ("<input> and <output> are the same");

  if (!strcmp (input_name, run_name)) die ("<input> and <run> are the same");

  if (!strcmp (output_name, run_name)) die ("<output> and <run> are the same");

  nexps = sexps = 1;
  exps          = calloc (sexps, sizeof *exps);

  if (!(input = fopen (input_name, "r"))) die ("can not read '%s'", input_name);

  parse ();

  tmp = malloc (100);
  sprintf (tmp, "/tmp/deltabtor%u", (unsigned) getpid ());

  cmd = malloc (strlen (run_name) + strlen (tmp) + 2);
  sprintf (cmd, "%s %s", run_name, tmp);

  simplify ();
  cone ();
  print ();
  clean ();

  rename (tmp, output_name);

  unlink (tmp);

  free (tmp);
  free (cmd);

  for (i = 1; i < nexps; i++) free (exps[i].op);

  free (exps);

  return 0;
}
