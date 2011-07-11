#include <stdio.h>
#include <stdlib.h>

static FILE* file;
static const char* name;
static int lineno = 1;

static int
next (void)
{
  int res = getc (file);
  if (res == '\n') lineno++;
  return res;
}

static void
perr (const char* fmt)
{
  fflush (stdout);
  fprintf (stderr, "%s:%d: %s\n", name, lineno, fmt);
  fflush (stderr);
  exit (1);
}

int
main (int argc, char** argv)
{
  int m, n, lit, open, ch;
  if (argc > 2)
  {
    fprintf (stderr, "*** dimacs2smt2: more than one command line argument");
    exit (1);
  }
  if (argc == 1)
    file = stdin, name = "<stdin>";
  else if (!(file = fopen ((name = argv[1]), "r")))
  {
    fprintf (stderr, "*** dimacs2smt2: can not read '%s'", name);
    exit (1);
  }
HEADER:
  ch = next ();
  if (ch == EOF) perr ("unexpected end-of-file in header");
  if (ch == 'c')
  {
    while ((ch = next ()) != '\n')
      if (ch == EOF) perr ("unexpected end-of-file in comment");
    goto HEADER;
  }
  if (ch != 'p') perr ("expected header 'p' or comment 'c'");
  if (fscanf (file, " cnf %d %d", &m, &n) != 2) perr ("invalid header");
  printf ("(set-logic QF_BV)\n");
  for (lit = 1; lit <= m; lit++) printf ("(declare-fun v%d () Bool)\n", lit);
  open = 0;
  while (fscanf (file, "%d", &lit) == 1)
  {
    if (lit)
    {
      if (!open++) printf ("(assert (or");
      if (lit < 0)
        printf (" (not v%d)", abs (lit));
      else
        printf (" v%d", abs (lit));
    }
    else
    {
      while (open++ < 2) printf (" false");
      printf ("))\n");
      open = 0;
    }
  }
  if (argc == 2) fclose (file);
  if (open) perr ("last zero missing");
  printf ("(check-sat)\n");
  printf ("(exit)\n");
  return 0;
}
