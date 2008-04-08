#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Cmd Cmd;

enum Op
{
  NOOP = 0,

  ADD,
  EXIT,
  GOTO,
  JMP,
  LE,
  LT,
  LOAD,
  PEEK,
  POKE,
  PRINT,
  SAVE,
};

typedef enum Op Op;

struct Cmd
{
  Op op;
  unsigned short immediate;
  unsigned short arg;
  int next;
};

static FILE* input;
static int saved = EOF;
static const char* name;
static int lineno = 1;

#define MAXLINE (1 << 16)
#define MAXMEM (1 << 16)

static Cmd program[MAXLINE];
static unsigned mem[MAXMEM];
static unsigned regs[26];

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

  if (res == '\n') lineno++;

  return res;
}

static void
save (char ch)
{
  assert (ch != EOF);
  assert (saved == EOF);
  saved = ch;
  if (ch == '\n')
  {
    assert (lineno > 1);
    lineno--;
  }
}

int
main (int argc, char** argv)
{
  int i, ch, line, immediate, arg, sign;
  Op op;

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

  ch = next ();

  assert (!isspace (EOF));
  assert (!isspace ('\n'));

NEXTLINE:

  while (isspace (ch)) ch = next ();

  if (ch == EOF) goto DONE;

  if (!isdigit (ch)) perr ("expected digit at start of line");

  line = ch - '0';
  while (isdigit (ch = next ())) line = 10 * line + (ch - '0');

  if (!isspace (ch)) perr ("expected space after line number");

  if (program[line].op) perr ("line %d defined twice", line);

  ch = next ();

  switch (ch)
  {
    case 'A':
      if (next () != 'D') goto INVALIDOP;
      if (next () != 'D') goto INVALIDOP;
      op = ADD;
      break;

    case 'E':
      if (next () != 'X') goto INVALIDOP;
      if (next () != 'I') goto INVALIDOP;
      if (next () != 'T') goto INVALIDOP;
      op = EXIT;
      break;

    case 'G':
      if (next () != 'O') goto INVALIDOP;
      if (next () != 'T') goto INVALIDOP;
      if (next () != 'O') goto INVALIDOP;
      op = GOTO;
      break;

    case 'J':
      if (next () != 'M') goto INVALIDOP;
      if (next () != 'P') goto INVALIDOP;
      op = JMP;
      break;

    case 'L':
      if ((ch = next ()) == 'E')
        op = LE;
      else if (ch == 'T')
        op = LT;
      else
      {
        if (ch != 'O') goto INVALIDOP;
        if (next () != 'A') goto INVALIDOP;
        if (next () != 'D') goto INVALIDOP;
        op = LOAD;
      }
      break;

    case 'P':
      if ((ch = next ()) == 'E')
      {
        if (ch != 'E') goto INVALIDOP;
        if (ch != 'K') goto INVALIDOP;
        op = PEEK;
      }
      else if (ch == 'O')
      {
        if (ch != 'K') goto INVALIDOP;
        if (ch != 'E') goto INVALIDOP;
        op = POKE;
      }
      else if (ch == 'R')
      {
        if (ch != 'I') goto INVALIDOP;
        if (ch != 'N') goto INVALIDOP;
        if (ch != 'T') goto INVALIDOP;
        op = PRINT;
      }
      else
        goto INVALIDOP;

      break;

    case 'S':
      if (next () != 'A') goto INVALIDOP;
      if (next () != 'V') goto INVALIDOP;
      if (next () != 'E') goto INVALIDOP;
      op = SAVE;
      break;

    default:
    INVALIDOP:
      perr ("invalid operator");
  }

  if (!isspace (next ())) goto INVALIDOP;

  immediate = 0;
  ch        = next ();

  if (ch == '-')
  {
    sign = -1;
    if (!isdigit (ch = next ())) perr ("expected digit after '-'");
  }
  else
    sign = 1;

  if (isdigit (ch))
  {
    immediate = 1;
    arg       = ch - '0';

    while (isdigit (ch = next ())) arg = 10 * arg + (ch - '0');

    save (ch);
  }
  else
  {
    immediate = 0;

    if (ch < 'A' || 'Z' < ch) perr ("expected number or register as argument");

    arg = ch - 'A';
  }

  if (op == JMP || op == GOTO)
  {
    if (!immediate)
      perr ("can not handle indirect %s", op == JMP ? "jumps" : "gotos");

    if (arg < 0) perr ("negative %s target", op == JMP ? "jump" : "goto");

    if (arg >= MAXLINE) perr ("target line number too large");
  }

  if (op == PEEK || op == POKE)
  {
    if (immediate)
    {
      if (arg < 0) perr ("negative immediate address");

      if (arg >= MAXMEM) perr ("immediate address too large");
    }
  }

  if (arg < -32768) perr ("argument too small");

  if (arg >= 32768) perr ("argument too large");

  while (isspace (ch = next ()))
    ;

  if (ch != '\n') perr ("expected new line at end of command");

  program[line].op        = op;
  program[line].immediate = immediate;
  program[line].arg       = arg;

  goto NEXTLINE;

DONE:

  return 0;
}
