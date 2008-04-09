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
  EQ,
  EXIT,
  GOTO,
  JMP,
  LE,
  LT,
  LOAD,
  PEEK,
  POKE,
  PRINT,
  READ,
  SAVE,
  WRITE,
};

typedef enum Op Op;

struct Cmd
{
  Op op;
  unsigned short immediate;
  unsigned short arg;
  char* str;
  int next;
};

static FILE *input, *data;
static int saved = EOF;
static int instring;
static const char* inputname;
static const char* dataname;
static const char* name;
static int lineno = 1;
static char* buffer;
static int szbuf, nbuf;

#define MAXLINE (1 << 16)
#define MAXMEM (1 << 16)

static Cmd program[MAXLINE];
static unsigned short mem[MAXMEM];
static unsigned short regs[26];
static unsigned short accu;
static int flag;

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
  fprintf (stderr, "%s:%d: ", name, lineno);
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

  if (!instring && 'a' <= res && res <= 'z') res = 'A' + (res - 'a');

  if (res == '"') instring = !instring;

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

static int
spaceortab (char ch)
{
  return ch == ' ' || ch == '\t';
}

int
main (int argc, char** argv)
{
  int i, ch, line, immediate, arg, sign, last, first, pc, usarg;
  const char* str;
  Op op;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: btorbasic [-<n>][<program>[<data>]]\n");
      exit (0);
    }
    else if (argv[i][0] == '-')
      die ("invalid command line option '%s'", argv[i]);
    else if (dataname)
      die ("more than two input files");
    else if (inputname)
      dataname = argv[i];
    else
      inputname = argv[i];
  }

  if (inputname)
  {
    if (!(input = fopen (inputname, "r"))) die ("can not read '%s'", inputname);

    name = inputname;
  }
  else
  {
    name  = "<stdin>";
    input = stdin;
  }

NEXTLINE:

  ch = next ();

  while (spaceortab (ch)) ch = next ();

  if (ch == EOF) goto DONE;

  if (!isdigit (ch)) perr ("expected digit at start of line");

  line = ch - '0';
  while (isdigit (ch = next ())) line = 10 * line + (ch - '0');

  if (!spaceortab (ch)) perr ("expected space after line number");

  if (program[line].op) perr ("line %d defined twice", line);

  do
  {
    ch = next ();
  } while (spaceortab (ch));

  switch (ch)
  {
    case 'A':
      if (next () != 'D') goto INVALIDOP;
      if (next () != 'D') goto INVALIDOP;
      op = ADD;
      break;

    case 'E':
      if ((ch = next ()) == 'X')
      {
        if (next () != 'I') goto INVALIDOP;
        if (next () != 'T') goto INVALIDOP;
        op = EXIT;
      }
      else if (ch == 'Q')
        op = EQ;
      else
        goto INVALIDOP;
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
        if (next () != 'E') goto INVALIDOP;
        if (next () != 'K') goto INVALIDOP;
        op = PEEK;
      }
      else if (ch == 'O')
      {
        if (next () != 'K') goto INVALIDOP;
        if (next () != 'E') goto INVALIDOP;
        op = POKE;
      }
      else if (ch == 'R')
      {
        if (next () != 'I') goto INVALIDOP;
        if (next () != 'N') goto INVALIDOP;
        if (next () != 'T') goto INVALIDOP;
        op = PRINT;
      }
      else
        goto INVALIDOP;

      break;

    case 'R':
      if (next () != 'E') goto INVALIDOP;

      if ((ch = next ()) == 'M')
      {
        while ((ch = next ()) != '\n' && ch != EOF)
          ;

        if (ch == EOF) perr ("end of file in comment");

        goto NEXTLINE;
      }

      if (ch != 'A') goto INVALIDOP;
      if (next () != 'D') goto INVALIDOP;

      if (!inputname) perr ("can not read data from stdin as well");

      op = READ;
      break;

    case 'S':
      if (next () != 'A') goto INVALIDOP;
      if (next () != 'V') goto INVALIDOP;
      if (next () != 'E') goto INVALIDOP;
      op = SAVE;
      break;

    case 'W':
      if (next () != 'R') goto INVALIDOP;
      if (next () != 'I') goto INVALIDOP;
      if (next () != 'T') goto INVALIDOP;
      if (next () != 'E') goto INVALIDOP;
      op = WRITE;
      break;

    default:
    INVALIDOP:
      perr ("invalid operator");
  }

  if (!spaceortab (next ())) goto INVALIDOP;

  immediate = 0;
  ch        = next ();

  if (ch == '"')
  {
    if (op != PRINT) perr ("unexpected string argument");

    for (;;)
    {
      if (nbuf == szbuf)
        buffer = realloc (buffer, szbuf = (szbuf ? 2 * szbuf : 128));

      ch = next ();

      if (ch == '"')
      {
        buffer[nbuf++]    = 0;
        program[line].op  = PRINT;
        program[line].str = strdup (buffer);
        nbuf              = 0;

        while (spaceortab (ch = next ()))
          ;

        if (ch != '\n') perr ("expected new line after string");

        goto NEXTLINE;
      }

      if (ch == '\n') perr ("unexpected new line in string");

      if (ch == EOF) perr ("unexpected end of line in string");

      if (ch == '\\')
      {
        ch = next ();
        if (ch == 'r')
          ch = '\r';
        else if (ch == 'n')
          ch = '\n';
        else if (ch == 't')
          ch = '\t';
        else
          perr ("invalid escape sequence");
      }

      buffer[nbuf++] = ch;
    }
  }

  if (op == PRINT) perr ("expected string argument");

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

  if ((op == SAVE || op == READ) && immediate)
    perr ("expected register as argument");

  if (arg < -32768) perr ("argument too small");

  if (arg >= 32768) perr ("argument too large");

  while (spaceortab (ch = next ()))
    ;

  if (ch != '\n') perr ("expected new line at end of command");

  program[line].op        = op;
  program[line].immediate = immediate;
  program[line].arg       = arg;

  goto NEXTLINE;

DONE:

  if (inputname) fclose (input);

  if (dataname)
  {
    if (!(data = fopen (dataname, "r"))) perr ("can not read '%s'", dataname);

    name = dataname;
  }
  else
  {
    name = "<stdin>";
    data = stdin;
  }

  first = -1;
  last  = -1;

  for (i = 0; i < MAXLINE; i++) program[i].next = -1;

  for (i = 0; i < MAXLINE; i++)
  {
    if (!(op = program[i].op)) continue;

    arg = program[i].arg;
    if (op == GOTO || op == JMP)
    {
      if (!program[arg].op) perr ("line %d does not exist", arg);
    }

    if (last >= 0)
      program[last].next = i;
    else
      first = i;

    last = i;
  }

  pc = first;

NEXTCMD:

  if (pc < 0)
  {
    usarg = accu;
    goto EXIT;
  }

  op        = program[pc].op;
  str       = program[pc].str;
  immediate = program[pc].immediate;
  usarg     = program[pc].arg;
  if (op != SAVE && op != READ && !immediate) usarg = regs[usarg];
  pc = program[pc].next;

  if (op == GOTO)
    pc = usarg;
  else if (op == JMP)
  {
    if (flag) pc = usarg;
  }
  else
  {
    switch (op)
    {
      case ADD: accu += usarg; break;

      case EQ: flag = (accu == usarg); break;

      case LE: flag = (accu <= usarg); break;

      case LT: flag = (accu < usarg); break;

      case LOAD: accu = usarg; break;

      case PEEK: accu = mem[usarg]; break;

      case POKE: mem[usarg] = accu; break;

      case PRINT:
        fputs (str, stdout);
        fflush (stdout);
        break;

      case READ:
        if (fscanf (data, "%d", &arg) != 1) perr ("read failed");
        if (arg < -32768 || arg >= 32768) perr ("read value out of bounds");
        assert (usarg < 26);
        regs[usarg] = (unsigned short) arg;
        break;

      case SAVE:
        assert (usarg < 26);
        regs[usarg] = accu;
        break;

      case WRITE:
        printf ("%d\n", usarg);
        fflush (stdout);
        break;

      default:
        assert (op == EXIT);
      EXIT:
        if (dataname) fclose (data);
        for (i = 0; i < MAXLINE; i++)
          if (program[i].op == PRINT) free (program[i].str);
        free (buffer);
        exit (usarg);
    }
  }

  goto NEXTCMD;
}
