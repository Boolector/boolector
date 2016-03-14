/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012 Aina Niemetz, Mathias Preiner.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <sys/wait.h> /* for WEXITSTATUS */

typedef struct Exp Exp;

struct Exp
{
  int ref;
  int idx;
  int cut;
  int oldref;
  int oldcut;
  char *op;
  int width;
  int addrwidth;
  int childs;
  int child[3];
  char *name;
};

static int verbose;
static int nosimp;
static int nosort;

static const char *input_name;
static const char *output_name;
static const char *run_name;

static FILE *input;
static int lineno;
static int saved;

static char *tmp;

static Exp *exps;
static int sexps;
static int nexps;

static int iexps;
static int rexps;
static int oexps;

static char *buf;

static int maxwidth;
static int runs;

static void
msg (int level, const char *fmt, ...)
{
  va_list ap;
  if (verbose < level) return;
  fflush (stdout);
  fputs ("[deltabtor] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
die (const char *fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fputs ("*** deltabtor: ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  exit (1);
}

static int
next (void)
{
  int res;

  if (saved != EOF)
  {
    res   = saved;
    saved = EOF;
  }
  else
    res = getc (input);

  if (res == ';')
  {
  SKIP_COMMENTS:
    while ((res = getc (input)) != '\n' && res != EOF)
      ;
  }
  else if (res == ' ' || res == '\t')
  {
    while ((res = getc (input)) == ' ' || res == '\t')
      ;

    if (res == ';') goto SKIP_COMMENTS;

    if (res != '\n')
    {
      saved = res;
      res   = ' ';
    }
  }

  if (res == '\n') lineno++;

  return res;
}

static void
perr (const char *fmt, ...)
{
  va_list ap;
  fflush (stdout);
  fprintf (stdout, "%s:%d: ", input_name, lineno);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  exit (1);
}

static int
isarrayop (const char *op)
{
  if (!strcmp (op, "array")) return 1;

  if (!strcmp (op, "acond")) return 1;

  if (!strcmp (op, "write")) return 1;

  if (!strcmp (op, "anext")) return 1;

  return 0;
}

static void
parse (void)
{
  int ch, idx, lit, sign, width, addrwidth, child[3], childs, needaddrwidth;
  char *op, *name;
  int sbuf = 0, nbuf = 0;

  lineno = 1;
  saved  = EOF;
  buf    = 0;
  iexps  = 0;

EXP:

  name = 0;
  op   = 0;

  while ((ch = next ()) == '\n')
    ;

  if (ch == EOF)
  {
    msg (1, "parsed %d expressions", iexps);
    return;
  }

  if (!isdigit (ch)) perr ("expected digit but got '0x%02x'", ch);

  idx = ch - '0';
  while (isdigit (ch = next ())) idx = 10 * idx + (ch - '0');

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
  op   = strdup (buf);

  needaddrwidth = isarrayop (op);

  width     = 0;
  addrwidth = 0;
  childs    = 0;
  child[0] = child[1] = child[2] = 0;

LIT:

  ch = next ();

  if (width && !childs)
  {
    if (!strcmp (op, "const") || !strcmp (op, "consth")
        || !strcmp (op, "constd") || !strcmp (op, "var"))
    {
      assert (!nbuf);

      while (!isspace (ch))
      {
        if (nbuf == sbuf) buf = realloc (buf, sbuf = sbuf ? 2 * sbuf : 1);

        buf[nbuf++] = ch;
        ch          = next ();
      }

      if (nbuf == sbuf) buf = realloc (buf, sbuf = sbuf ? 2 * sbuf : 1);
      buf[nbuf] = 0;
      nbuf      = 0;

      name = strdup (buf);

      goto INSERT;
    }
  }

  if (isdigit (ch) || ch == '-')
  {
    if (ch == '-')
    {
      sign = -1;
      ch   = next ();
      if (!isdigit (ch)) perr ("expected digit after '-' but got '0x%02x'", ch);
    }
    else
      sign = 1;

    lit = ch - '0';
    while (isdigit (ch = next ())) lit = 10 * lit + (ch - '0');

    lit *= sign;

    if (childs == 3)
      perr ("more than three childs");
    else if (!width)
    {
      if (lit <= 0) perr ("expected positive width");
      width = lit;
    }
    else if (needaddrwidth && !addrwidth)
    {
      if (lit <= 0) perr ("expected positive address bit width");

      addrwidth = lit;
    }
    else
      child[childs++] = lit;

    if (ch == ' ') goto LIT;

    if (ch != '\n') perr ("expected space or new line");

    if (!width)
    WIDTH_MISSING:
      perr ("width missing");

    if (needaddrwidth && !addrwidth) perr ("address bit width missing");

  INSERT:
    assert (idx >= 1);

    while (nexps <= idx)
    {
      if (nexps == sexps) exps = realloc (exps, (sexps *= 2) * sizeof *exps);

      exps[nexps++].ref = 0;
    }

    if (exps[idx].ref) perr ("expression %d defined twice", idx);

    exps[idx].ref       = idx;
    exps[idx].oldref    = idx;
    exps[idx].cut       = 0;
    exps[idx].oldcut    = 0;
    exps[idx].idx       = 0;
    exps[idx].op        = op;
    exps[idx].width     = width;
    exps[idx].addrwidth = addrwidth;
    exps[idx].childs    = childs;
    exps[idx].child[0]  = child[0];
    exps[idx].child[1]  = child[1];
    exps[idx].child[2]  = child[2];
    exps[idx].name      = name;

    iexps++;

    if (width > maxwidth) maxwidth = width;

    goto EXP;
  }

  if (!width) goto WIDTH_MISSING;

  perr ("expected digit but got '%c'", ch);
}

static void
save (void)
{
  Exp *e;
  int i;

  for (i = 1; i < nexps; i++)
  {
    e         = exps + i;
    e->oldref = e->ref;
    e->oldcut = e->cut;
  }
}

static int
deref (int start)
{
  int res, sign, tmp;
  Exp *e;

  sign = (start < 0);
  if (sign) start = -start;

  assert (0 < start);
  assert (start < nexps);

  e = exps + start;

  if (e->cut)
    res = start;
  else
  {
    tmp = e->ref;

    assert (tmp);

    if (tmp != start)
      res = deref (tmp);
    else
      res = start;

    exps[start].ref = res;
  }

  if (sign) res = -res;

  return res;
}

static int
deidx (int start)
{
  int res, sign, tmp;

  tmp  = deref (start);
  sign = (tmp < 0);
  if (sign) tmp = -tmp;

  res = exps[tmp].idx;
  assert (res);

  if (sign) res = -res;

  return res;
}

static int
isallone (int start)
{
  const char *p;
  Exp *e;

  start = deref (start);

  if (start < 0)
  {
    e = exps - start;
    if (!strcmp (e->op, "zero")) return 1;

    if (!e->name) return 0;

    if (!strcmp (e->op, "const") || !strcmp (e->op, "consth")
        || !strcmp (e->op, "constx"))
    {
      for (p = e->name; *p; p++)
        if (*p != '0') return 0;

      return 1;
    }
  }
  else
  {
    e = exps + start;

    if (!e->name) return 0;

    if (!strcmp (e->op, "const")
        || (e->width == 1
            && (!strcmp (e->op, "consth") || !strcmp (e->op, "constx"))))
    {
      for (p = e->name; *p; p++)
        if (*p != '1') return 0;

      return 1;
    }
  }

  return 0;
}

static int
isallzero (int start)
{
  return isallone (-start);
}

static void
simp (void)
{
  int i, c;
  Exp *e;

  if (nosimp) return;

  rexps = 0;
  for (i = 1; i < nexps; i++)
  {
    e = exps + i;

    if (!e->ref) continue;

    if (e->childs == 2 && !strcmp (e->op, "and"))
    {
      if (deref (e->child[0]) == deref (e->child[1]))
        e->ref = deref (e->child[0]);
      else if (deref (e->child[0]) == -deref (e->child[1]))
        e->ref = e->width;
      else if (isallzero (e->child[0]))
        e->ref = deref (e->child[0]);
      else if (isallzero (e->child[1]))
        e->ref = deref (e->child[1]);
      else if (isallone (e->child[0]))
        e->ref = deref (e->child[1]);
      else if (isallone (e->child[1]))
        e->ref = deref (e->child[0]);
    }

    if (e->childs == 3 && (!strcmp (e->op, "cond") || !strcmp (e->op, "acond")))
    {
      c = e->child[0];

      if (exps[abs (c)].width == 1)
      {
        if (isallone (c))
          e->ref = deref (e->child[0]);
        else if (isallzero (c))
          e->ref = deref (e->child[1]);
      }

      if (deref (e->child[1]) == deref (e->child[2]))
        e->ref = deref (e->child[1]);
    }

    if (e->childs == 2 && !strcmp (e->op, "add"))
    {
      if (isallzero (e->child[0]))
        e->ref = deref (e->child[1]);
      else if (isallzero (e->child[1]))
        e->ref = deref (e->child[0]);
    }

    if (e->childs == 2
        && (!strcmp (e->op, "eq") || !strcmp (e->op, "xnor")
            || !strcmp (e->op, "iff")))
    {
      if (deref (e->child[0]) == deref (e->child[1]))
        e->ref = -e->width;
      else if (deref (e->child[0]) == -deref (e->child[1]))
        e->ref = e->width;
    }

    if (e->childs == 2 && !strcmp (e->op, "xor"))
    {
      if (deref (e->child[0]) == deref (e->child[1]))
        e->ref = e->width;
      else if (deref (e->child[0]) == -deref (e->child[1]))
        e->ref = -e->width;
    }

    /* TODO: add more for 'implies', 'or'.
     * However, those are not part of the internal repr.
     */

    /* TODO: add
     *
     *   write(write (a,x), x, y) == write (a,x,y)
     */

    /* TODO: 'read?'
     */

    (void) deref (i);
  }
}

static int
ischild (Exp *e, int child)
{
  assert (e->ref);

  if (child >= e->childs) return 0;

  if (e->cut) return 0;

  assert (child >= 0);

  if (!strcmp (e->op, "array")) return 0;
  if (!strcmp (e->op, "const")) return 0;
  if (!strcmp (e->op, "consth")) return 0;
  if (!strcmp (e->op, "constd")) return 0;
  if (!strcmp (e->op, "root") && child != 0) return 0;
  if (!strcmp (e->op, "sext") && child != 0) return 0;
  if (!strcmp (e->op, "slice") && child != 0) return 0;
  if (!strcmp (e->op, "uext") && child != 0) return 0;
  if (!strcmp (e->op, "var")) return 0;
  if (!strcmp (e->op, "zero")) return 0;

  return 1;
}

static void
dfs (int idx)
{
  Exp *e;
  int i;

  idx = abs (idx);

  assert (0 < idx);
  assert (idx < nexps);

  e = exps + idx;

  if (e->idx) return;

  for (i = 0; i < 3; i++)
    if (ischild (e, i)) dfs (deref (e->child[i]));

  e->idx = ++rexps;
}

static void
cone (void)
{
  int i, true_roots = 0, false_roots = 0, non_trivial_roots = 0, skip;
  int changed;

  rexps = 0;

  for (i = 1; i < nexps; i++)
    if (exps[i].ref && !strcmp (exps[i].op, "root"))
    {
      if (isallzero (exps[i].child[0]))
        false_roots++;
      else if (isallone (exps[i].child[0]))
        true_roots++;
      else
        non_trivial_roots++;
    }

  for (i = 1; i < nexps; i++)
    if (exps[i].ref && !strcmp (exps[i].op, "root"))
    {
      skip = 0;

      if (isallzero (exps[i].child[0]))
      {
        if (false_roots)
          false_roots = 0;
        else
          skip = 1;
      }

      if (isallone (exps[i].child[0]))
      {
        if (!non_trivial_roots && true_roots)
          true_roots = 0;
        else
          skip = 1;
      }

      if (!skip) dfs (i);
    }

  do
  {
    changed = 0;
    for (i = 1; i < nexps; i++)
      if (exps[i].ref && !exps[i].idx
          && (!strcmp (exps[i].op, "anext") || !strcmp (exps[i].op, "next"))
          && exps[exps[i].child[0]].idx)
      {
        dfs (i);
        changed = 1;
      }
  } while (changed);
}

static void
clean (void)
{
  Exp *e;
  int i;

  for (i = 1; i < nexps; i++)
  {
    e = exps + i;
    if (!e->ref) continue;

    if (e->idx) e->idx = 0;
  }
}

static void
reset (void)
{
  Exp *e;
  int i;

  for (i = 1; i < nexps; i++)
  {
    e      = exps + i;
    e->ref = e->oldref;
    e->cut = e->oldcut;
  }
}

static int
cmp_by_idx (const void *p, const void *q)
{
  Exp *a = *(Exp **) p;
  Exp *b = *(Exp **) q;
  assert (a->ref);
  assert (a->idx);
  assert (b->ref);
  assert (b->idx);
  return a->idx - b->idx;
}

static void
print (void)
{
  FILE *file = fopen (tmp, "w");
  int i, j, lit, count;
  Exp *e, **sorted;

  if (!file) die ("can not write to '%s'", tmp);

  count = 0;

  for (i = 1; i < nexps; i++)
  {
    e = exps + i;

    if (!e->ref) continue;

    if (!e->idx) continue;

    count++;
  }

  sorted = count ? malloc (count * sizeof *sorted) : 0;

  j = 0;
  for (i = 1; i < nexps; i++)
  {
    e = exps + i;

    if (!e->ref) continue;

    if (!e->idx) continue;

    sorted[j++] = e;
  }

  assert (j == count);

  if (!nosort && sorted) qsort (sorted, count, sizeof *sorted, cmp_by_idx);

  for (i = 0; i < count; i++)
  {
    e = sorted[i];

    if (!e->ref) continue;

    if (!e->idx) continue;

    if (e->cut)
    {
      fprintf (file, "%d var %d\n", e->idx, e->width);
    }
    else
    {
      fprintf (file, "%d %s %d", e->idx, e->op, e->width);

      if (isarrayop (e->op)) fprintf (file, " %d", e->addrwidth);

      for (j = 0; j < e->childs; j++)
      {
        lit = e->child[j];
        fprintf (file, " %d", ischild (e, j) ? deidx (lit) : lit);
      }

      if (e->name) fprintf (file, " %s", e->name);

      fputc ('\n', file);
    }
  }

  fclose (file);

  free (sorted);
}

static void
expand (void)
{
  Exp *e, *old;
  int idx, j;

  nexps += maxwidth;

  old   = exps;
  sexps = nexps;
  exps  = calloc (nexps, sizeof *exps);

  for (idx = 1; idx <= maxwidth; idx++)
  {
    exps[idx].ref    = idx;
    exps[idx].oldref = idx;
    exps[idx].cut    = 0;
    exps[idx].oldcut = 0;
    exps[idx].idx    = 0;
    exps[idx].op     = strdup ("zero");
    exps[idx].width  = idx;
    exps[idx].childs = 0;
    exps[idx].name   = 0;
  }

  memcpy (exps + maxwidth + 1, old + 1, (nexps - maxwidth - 1) * sizeof *exps);

  for (idx = maxwidth + 1; idx < nexps; idx++)
  {
    e = exps + idx;
    if (!e->ref) continue;

    assert (e->ref == idx - maxwidth);
    e->ref += maxwidth;

    for (j = 0; j < e->childs; j++)
      if (ischild (e, j))
      {
        if (e->child[j] < 0)
          e->child[j] -= maxwidth;
        else
          e->child[j] += maxwidth;
      }
  }

  free (old);

  msg (1, "added %d zeroes", maxwidth);
}

static int
run (char *cmd)
{
  int tmp = system (cmd), res = WEXITSTATUS (tmp);
  runs++;
  return res;
}

static int
min (int a, int b)
{
  return a < b ? a : b;
}

static void
permanent (void)
{
  FILE *to = fopen (output_name, "w"), *from = fopen (tmp, "r");
  int ch;
  if (!from) die ("can not read '%s'", tmp);
  if (!to) die ("can not write '%s'", output_name);
  while ((ch = getc (from)) != EOF) fputc (ch, to);
  fclose (from);
  fclose (to);
}

int
main (int argc, char **argv)
{
  int changed, golden = 0, res, rounds, interval, fixed, sign, overwritten;
  int i, j, argstart, len, fixpoint = 0, prev_oexps, restart = 0;
  char *cmd, *cmd_golden;
  Exp *e;

  cmd = cmd_golden = 0;

  argstart = argc;

  for (i = 1; i < argc; i++)
  {
    if (run_name)
    {
      argstart = i;
      break;
    }
    else if (!strcmp (argv[i], "-h"))
    {
      printf (
          "usage: deltabtor "
          "[-h][-v][-g <val>][--no-simp][--no-sort] <in> <out> "
          "<run> [<opt> ...]\n");
      printf ("usage: %s ", argv[0]);
      printf ("[option] <infile> <outfile> <cmd> [<cmdopt>]\n\n");
      printf ("  options:\n");
      printf ("    -h           print this message and exit\n");
      printf ("    -v           be verbose ");
      printf ("multiple occurrences increase verbosity level)\n");
      printf ("    -g <val>     'golden' (reference) exit code ");
      printf ("(default: initial run on <in>)\n");
      printf ("    --no-simp    do not simplify expressions\n");
      printf ("    --no-sort    do not sort expressions\n");
      printf ("    --fixpoint   run until fixpoint reached\n");
      exit (0);
    }
    else if (!strcmp (argv[i], "-v"))
      verbose++;
    else if (!strcmp (argv[i], "-g"))
    {
      if (++i == argc) die ("golden <val> missing");
      golden = atoi (argv[i]);
    }
    else if (!strcmp (argv[i], "--no-simp"))
      nosimp = 1;
    else if (!strcmp (argv[i], "--no-sort"))
      nosort = 1;
    else if (!strcmp (argv[i], "--fixpoint"))
      fixpoint = 1;
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

RESTART:
  if (restart) input_name = output_name;

  nexps = sexps = 1;
  exps          = calloc (sexps, sizeof *exps);

  if (!(input = fopen (input_name, "r"))) die ("can not read '%s'", input_name);

  parse ();

  fclose (input);

  if (restart) goto CONTINUE;

  tmp = malloc (100);
  sprintf (tmp, "/tmp/deltabtor%u", (unsigned) getpid ());

  len = strlen (tmp);

  for (i = argstart; i < argc; i++) len += 1 + strlen (argv[i]);

  cmd        = malloc (strlen (run_name) + len + strlen (tmp) + 1);
  cmd_golden = malloc (strlen (run_name) + len + strlen (input_name) + 1);
  sprintf (cmd, "%s %s", run_name, tmp);
  sprintf (cmd_golden, "%s %s", run_name, input_name);

  for (i = argstart; i < argc; i++)
  {
    sprintf (cmd + strlen (cmd), " %s", argv[i]);
    sprintf (cmd_golden + strlen (cmd_golden), " %s", argv[i]);
  }

  sprintf (cmd + strlen (cmd), " > /dev/null 2>&1");
  sprintf (cmd_golden + strlen (cmd_golden), " > /dev/null 2>&1");

  if (!golden) golden = run (cmd_golden);
  msg (1, "golden exit code %d", golden);

CONTINUE:
  expand ();
  save ();
  simp ();
  cone ();
  print ();
  clean ();
  reset ();
  permanent ();

  rounds = 0;
  fixed  = 0;

  interval   = nexps - maxwidth;
  oexps      = rexps;
  prev_oexps = oexps;

  do
  {
    do
    {
      rounds++;
      msg (1, "interval %d size %d round %d", interval, oexps, rounds);

      changed = 0;

      for (i = maxwidth + 1; i < nexps; i += interval)
      {
        for (sign = 1; sign >= -3; sign -= 2)
        {
          overwritten = 0;

          for (j = i; j < i + interval && j < nexps; j++)
          {
            e = exps + j;

            if (!e->ref) continue;

            if (e->ref != j) continue;

            if (e->cut) continue;

            if (!strcmp (e->op, "root")) continue;

            if (!strcmp (e->op, "array")) continue;

            overwritten++;
          }

          if (!overwritten) continue;

          save ();

          for (j = i; j < i + interval && j < nexps; j++)
          {
            e = exps + j;

            if (!e->ref) continue;

            if (e->ref != j) continue;

            if (e->cut) continue;

            if (!strcmp (e->op, "root")) continue;

            if (!strcmp (e->op, "array")) continue;

            if (sign >= -1)
              e->ref = sign * e->width;
            else
              e->cut = 1;
          }

          msg (3,
               "trying to set %d expressions %d .. %d to %s",
               overwritten,
               i,
               min (i + interval, nexps) - 1,
               (sign < -1) ? "new variables" : (sign < 0) ? "all one" : "zero");

          simp ();
          cone ();
          print ();
          clean ();

          res = run (cmd);

          if (res == golden)
          {
            changed = 1;
            fixed += overwritten;

            msg (2, "fixed %d expressions", overwritten);
            permanent ();
            oexps = rexps;
            msg (2, "saved %d expressions in '%s'", rexps, output_name);
          }
          else
          {
            msg (3, "restored %d expressions", overwritten);
            reset ();
          }
        }
      }

    } while (changed);

    if (3 < interval && interval < 8)
      interval = 3;
    else if (interval == 3)
      interval = 2;
    else if (interval == 2)
      interval = 1;
    else if (interval == 1)
      interval = 0;
    else
      interval = (interval + 1) / 2;

  } while (interval);

  msg (2, "%d rounds", rounds);
  msg (2, "%d runs", runs);

  for (i = 1; i < nexps; i++)
  {
    if (!exps[i].ref) continue;

    free (exps[i].op);
    free (exps[i].name);
  }

  free (exps);
  free (buf);

  assert (prev_oexps >= oexps);
  if (fixpoint && prev_oexps - oexps > 0)
  {
    msg (1, "no fixpoint reached, restarting");
    restart = 1;
    goto RESTART;
  }

  unlink (tmp);
  free (tmp);
  free (cmd);
  free (cmd_golden);

  msg (1, "fixed %d expressions out of %d", fixed, iexps);
  msg (1, "wrote %d expressions to '%s'", oexps, output_name);

  return 0;
}
