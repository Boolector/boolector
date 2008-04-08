#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Cmd Cmd;

enum Tag
{
  NOOP = 0,

  LOAD,
  SAVE,
  ADD,
  LE,
  JMP,
  PEEK,
  POKE,
  GOTO,
  EXIT,
  PRINT
};

struct Cmd
{
  Tag tag;
  int reg;
  int next;
};

static FILE* input;
static const char* name;
static int lineno;

#define MAXLINE 1000
static Cmd[MAXLINE];

static void
die (const char* msg, ...)
{
  va_list ap;
  fputs ("*** btorbasic: ", stderr);
  va_start (ap, msg);
  vfprintf (stderr, msg, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void
perr (const char* msg, ...)
{
  va_list ap;
  fprintf (stderr, "%s:%d: ", name ? name : "<stdin>", lineno);
  va_start (ap, msg);
  vfprintf (stderr, msg, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

int
main (int argc, char** argv)
{
  int i, ch;

  name = 0;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: btorbasic [-<n>][<input>]\n");
      exit (0);
    }
    else if (argv[i][0] == '-')
      die ("invalid command line option '%s'", argv[i]);
    else if (name)
      die ("multiple input files '%s' and '%s'", name, argv[i]);
    else
      name = argv[i];
  }

  if (name)
  {
    if (!(input = fopen (name, "r"))) die ("can not read '%s'", name);
  }
  else
    input = stdin;

NEXT:

  return 0;
}
