#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Cmd Cmd;

enum Op
{
  NOOP = 0,  // for debugging purposes only

  ADD,    // accu += arg
  EQ,     // flag = (accu == arg)
  EXIT,   // exit arg
  GE,     // flag = (accu >= arg)
  GT,     // flag = (accu > arg)
  GOTO,   // goto argi            immediate only
  JMP,    // if flag goto arg     immediate only
  LE,     // flag = (accu <= arg)
  LT,     // flag = (accu < arg)
  LOAD,   // accu = arg                           -> SAVE
  NE,     // flag = (accu != arg)
  PEEK,   // accu = mem[arg]                      -> POKE
  POKE,   // mem[arg] = accu                      -> PEEK
  PRINT,  // print "str"          simulation only
  READ,   // read arg             register only   -> WRITE
  SAVE,   // arg = accu           register only   -> LOAD
  WRITE,  // write arg            simulation only -> READ
};

typedef enum Op Op;

struct Cmd
{
  Op op;
  unsigned short immediate;
  unsigned short arg;
  char *str;
  int next;
  int pcid;
};

static FILE *input, *data;
static int saved = EOF;
static int instring;
static const char *inputname;
static const char *dataname;
static const char *name;
static int lineno = 1;
static char *buffer;
static int szbuf, nbuf;

#define MAXLINE (1 << 16)
#define MAXMEM (1 << 16)

static Cmd program[MAXLINE];
static unsigned short *mem;
static unsigned short *regs;
static unsigned short accu;
static int flag;

static void
die (const char *msg, ...)
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
perr (const char *msg, ...)
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
main (int argc, char **argv)
{
  int i, ch, line, immediate, arg, sign, last, first, pc, usarg, res;
  int nextpcid, nextaccuid, nextflagid, nextregsid, nextmemid, atthispcid;
  int regindexids[26], regwriteids[26], regreadids[26];
  int id, pcid, regsid, memid, accuid, flagid;
  int simulate, bits;
  const char *str;
  int tmp;
  Op op;

  simulate = 0;
  bits     = 16;

  for (i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fprintf (stderr, "usage: btorbasic [-32][-<s>][<program>[<data>]]\n");
      exit (0);
    }
    else if (!strcmp (argv[i], "-s"))
      simulate = 1;
    else if (!strcmp (argv[i], "-32"))
      bits = 32;
    else if (argv[i][0] == '-')
      die ("invalid command line option '%s'", argv[i]);
    else if (dataname)
      die ("more than two input files");
    else if (inputname)
      dataname = argv[i];
    else
      inputname = argv[i];
  }

  if (!simulate && dataname) die ("can only use data file in simulation mode");

  if (simulate && bits == 32) die ("can not simulate 32 bit architecture");

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
      if ((ch = next ()) == 'E')
        op = GE;
      else if (ch == 'T')
        op = GT;
      else if (ch != 'O')
        goto INVALIDOP;
      else if (next () != 'T')
        goto INVALIDOP;
      else if (next () != 'O')
        goto INVALIDOP;
      else
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

    case 'N':
      if (next () != 'E') goto INVALIDOP;
      op = NE;
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
      op = NOOP;
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

  first = -1;
  last  = -1;

  for (i = 0; i < MAXLINE; i++) program[i].next = -1;

  for (i = 0; i < MAXLINE; i++)
  {
    if (!(op = program[i].op)) continue;

    if (!simulate && program[i].op == PRINT) continue;

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

  if (first > 0)
  {
    program[0].op        = GOTO;
    program[0].immediate = 1;
    program[0].arg       = first;
    program[0].next      = first;
    first                = 0;
  }

  res = 0;

  if (!simulate) goto SYNTHESIZE;

  /* START OF SIMULATOR */

  /* Here starts the implementations of the simulator, which is used if
   * the '-s' command line option is specified.
   */
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

  pc = first;

  /* By allocating here, we can use 'valgrind'.
   */
  mem  = malloc (MAXMEM * sizeof *mem);
  regs = malloc (26 * sizeof *regs);

NEXTCMD:

  if (pc < 0) goto EXIT;

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

      case GE: flag = (accu >= usarg); break;

      case GT: flag = (accu > usarg); break;

      case LE: flag = (accu <= usarg); break;

      case LT: flag = (accu < usarg); break;

      case LOAD: accu = usarg; break;

      case NE: flag = (accu != usarg); break;

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
        res = usarg;
        goto EXIT;
    }
  }

  goto NEXTCMD;

  /* END OF SIMULATOR */

  /* START OF SYNTHESIZER */

SYNTHESIZE:

  id = 1;

  pcid = id++;
  printf ("%d var %d pc\n", pcid, bits);

  accuid = id++;
  printf ("%d var %d accu\n", accuid, bits);

  flagid = id++;
  printf ("%d var 1 flag\n", flagid);

  regsid = id++;
  printf ("%d array %d 5\n", regsid, bits);

  memid = id++;
  printf ("%d array %d %d\n", memid, bits, bits);

  pc = first;
  while (pc >= 0)
  {
    if (program[pc].pcid != PRINT)
    {
      program[pc].pcid = id;
      printf ("%d constd %d %d\n", id, bits, pc);
      id++;
    }
    pc = program[pc].next;
  }

  memset (regindexids, 0, sizeof regindexids);
  memset (regreadids, 0, sizeof regreadids);
  memset (regwriteids, 0, sizeof regwriteids);

  for (pc = first; pc >= 0; pc = program[pc].next)
  {
    op = program[pc].op;
    switch (op)
    {
      case ADD:
      case EQ:
      case EXIT:
      case GE:
      case GT:
      case LE:
      case LT:
      case LOAD:
      case NE:
      case PEEK:
      case POKE:
      case READ:
      case SAVE:
        immediate = program[pc].immediate;
        usarg     = program[pc].arg;

        if (!immediate)
        {
          if (!regindexids[usarg])
            printf ("%d constd 5 %d\n", regindexids[usarg] = id++, usarg);

          if (op == SAVE)
          {
            if (!regwriteids[usarg])
              printf ("%d write %d %d %d %d\n",
                      regwriteids[usarg] = id++,
                      bits,
                      regsid,
                      regindexids[usarg],
                      accuid);
          }
          else
          {
            if (!regreadids[usarg])
              printf ("%d read %d %d %d\n",
                      regreadids[usarg] = id++,
                      bits,
                      regsid,
                      regindexids[usarg]);
          }
        }
        break;
        ;

      case GOTO:
      case JMP:
      case PRINT: break;
      default: assert (op == WRITE); break;
    }
  }

  nextpcid   = pcid;
  nextaccuid = accuid;
  nextflagid = flagid;
  nextregsid = regsid;
  nextmemid  = memid;

  for (pc = first; pc >= 0; pc = program[pc].next)
  {
    op = program[pc].op;

    if (op == PRINT || op == WRITE) continue;

    usarg = program[pc].arg;

    printf ("%d eq 1 %d %d\n", atthispcid = id++, pcid, program[pc].pcid);

    /* DO NOT SEPERATE THIS CASE FROM THE PREVIOUS LINE !!! */

    if (op == GOTO)
    {
      printf ("%d cond %d %d %d %d\n",
              id,
              bits,
              atthispcid,
              program[usarg].pcid,
              nextpcid);

      nextpcid = id++;
    }
    else
    {
      if (program[pc].next >= 0)
      {
        printf ("%d cond %d %d %d %d\n",
                id,
                bits,
                atthispcid,
                program[program[pc].next].pcid,
                nextpcid);

        nextpcid = id++;
      }

      if (op == JMP)
      {
        printf ("%d and 1 %d %d\n", id++, atthispcid, flagid);
        printf ("%d cond %d %d %d %d\n",
                id,
                bits,
                id - 1,
                program[usarg].pcid,
                nextpcid);

        nextpcid = id++;
      }
    }

    immediate = program[pc].immediate;

    if (immediate)
      printf ("%d constd %d %d\n", tmp = id++, bits, usarg);
    else
      tmp = regreadids[usarg];

    if (op == EQ || op == GE || op == GT || op == LT || op == LE || op == NE)
    {
      if (op == EQ) printf ("%d eq 1 %d %d\n", id++, accuid, tmp);
      if (op == GE) printf ("%d sgte 1 %d %d\n", id++, accuid, tmp);
      if (op == GT) printf ("%d sgt 1 %d %d\n", id++, accuid, tmp);
      if (op == LE) printf ("%d slte 1 %d %d\n", id++, accuid, tmp);
      if (op == LT) printf ("%d slt 1 %d %d\n", id++, accuid, tmp);
      if (op == NE) printf ("%d ne 1 %d %d\n", id++, accuid, tmp);

      printf ("%d cond 1 %d %d %d\n", id, atthispcid, id - 1, nextflagid);
      nextflagid = id++;
    }
    else if (op == EXIT)
    {
      printf ("%d redor 1 %d\n", id++, tmp);
      printf ("%d and 1 %d %d\n", id, id - 1, atthispcid);
      id++;
      printf ("%d root 1 %d\n", id, id - 1);
      id++;
    }
    else if (op == PEEK)
    {
      printf ("%d read %d %d %d\n", id++, bits, memid, tmp);
      printf (
          "%d cond %d %d %d %d\n", id, bits, atthispcid, id - 1, nextaccuid);
      nextaccuid = id++;
    }
    else if (op == POKE)
    {
      printf ("%d write %d %d %d %d\n", id++, bits, nextmemid, tmp, accuid);
      printf ("%d cond %d %d %d %d\n", id, bits, atthispcid, id - 1, nextmemid);
      nextmemid = id++;
    }
    else if (op == READ)
    {
      assert (!immediate);
      printf ("%d var %d read_%c_at_line_%d\n", id++, bits, 'A' + usarg, pc);
      printf ("%d write %d %d %d %d\n",
              id,
              bits,
              nextregsid,
              regindexids[usarg],
              id - 1);
      id++;
      printf (
          "%d cond %d %d %d %d\n", id, bits, atthispcid, id - 1, nextregsid);
      nextregsid = id++;
    }
    else if (op == SAVE)
    {
      assert (!immediate);
      printf ("%d write %d %d %d %d\n",
              id++,
              bits,
              nextregsid,
              regindexids[usarg],
              accuid);
      printf (
          "%d cond %d %d %d %d\n", id, bits, atthispcid, id - 1, nextregsid);
      nextregsid = id++;
    }
    else if (op == LOAD)
    {
      printf ("%d cond %d %d %d %d\n", id, bits, atthispcid, tmp, nextaccuid);
      nextaccuid = id++;
    }
    else if (op == ADD)
    {
      printf ("%d add %d %d %d\n", id++, bits, nextaccuid, tmp);
      printf (
          "%d cond %d %d %d %d\n", id, bits, atthispcid, id - 1, nextaccuid);
      nextaccuid = id++;
    }
    else
      assert (op == GOTO || op == JMP); /* got all ops? */
  }

  printf ("%d next %d %d %d\n", id++, bits, pcid, nextpcid);
  printf ("%d next %d %d %d\n", id++, bits, accuid, nextaccuid);
  printf ("%d next 1 %d %d\n", id++, flagid, nextflagid);
  printf ("%d next %d %d %d\n", id++, bits, regsid, nextregsid);
  printf ("%d next %d %d %d\n", id++, bits, memid, nextmemid);

  /* END OF SYTHESIZER */

EXIT:

  if (dataname) fclose (data);
  for (i = 0; i < MAXLINE; i++)
    if (program[i].op == PRINT) free (program[i].str);
  free (buffer);
  if (simulate)
  {
    free (mem);
    free (regs);
  }
  exit (res);
}
