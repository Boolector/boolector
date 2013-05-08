#include "btoribv.h"

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <iostream>
#include <map>
#include <string>
#include <vector>

using namespace std;

struct Var
{
  string name;
  unsigned width;
  Var () {}
  Var (string n, int w) : name (n), width (w) {}
};

static BtorIBV* ibvm;

static map<string, unsigned> symtab;
static map<unsigned, Var> idtab;

static int lineno             = 1;
static FILE* input            = stdin;
static const char* input_name = "<stdin>";
static bool close_input;

static int szline, nline;
static char* line;

static struct
{
  int addVariable;
  int addRangeName;
  int addState;
  int addNonState;
  int addCondition;
  int addAssignment;
  int addBitNot;
  int addConstant;
  int addEqual;
  int addLogicalAnd;
  int addLogicalNot;

} stats;

static void
err (const char* fmt, ...)
{
  va_list ap;
  fputs ("*** btorimc: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void
msg (const char* fmt, ...)
{
  va_list ap;
  fputs ("[btorimc] ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
perr (const char* fmt, ...)
{
  va_list ap;
  fprintf (stderr, "%s:%d: ", input_name, lineno);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  exit (1);
}

static void
pushch (int ch)
{
  if (nline >= szline)
  {
    szline = szline ? 2 * szline : 1;
    line   = (char*) realloc (line, szline);
  }
  line[nline++] = ch;
}

static bool
read_line ()
{
  nline = 0;
  int ch;
  while ((ch = getc (input)) != '\n')
  {
    if (ch == ' ' || ch == '\t' || ch == '\r') continue;
    if (ch == EOF)
    {
      if (nline) perr ("unexpected end-of-file");
      if (line) free (line);
#if 0  // TODO print stats
      if (stats.vars) msg ("parsed %d variables", stats.vars);
      if (stats.rangenames) msg ("parsed %d range names", stats.rangenames);
#endif
      return false;
    }
    pushch (ch);
  }
  pushch (0);
  return true;
}

#define CHKARGS(EXPECTED)                                                  \
  do                                                                       \
  {                                                                        \
    if (EXPECTED != size - 1)                                              \
      perr ("operator '%s' expected exactly %d arguments but only got %d", \
            op,                                                            \
            EXPECTED,                                                      \
            size - 1);                                                     \
  } while (0)

#define CHKIDUNUSED(ID)                                                   \
  do                                                                      \
  {                                                                       \
    if (idtab.find (ID) != idtab.end ()) perr ("id %u already used", ID); \
  } while (0)

#define CHKID(ID)                                                      \
  do                                                                   \
  {                                                                    \
    if (idtab.find (ID) == idtab.end ()) perr ("id %u undefined", ID); \
  } while (0)

#define CHKSYMUNUSED(SYM)                              \
  do                                                   \
  {                                                    \
    if (symtab.find (SYM) != symtab.end ())            \
      perr ("symbol '%s' already used", SYM.c_str ()); \
  } while (0)

#define N(I) (assert ((I) < size), (unsigned) atoi (toks[I].c_str ()))
#define T(I) (assert ((I) < size), toks[I])

#define RANGE(NAME, SYM, MSB, LSB)                                          \
  if (symtab.find (SYM) == symtab.end ())                                   \
    perr ("symbol '%s' undefined", (SYM).c_str ());                         \
  if ((MSB) < (LSB)) perr ("MSB %u < LSB %u", (MSB), (LSB));                \
  {                                                                         \
    Var& V = idtab[symtab[(SYM)]];                                          \
    if ((MSB) >= V.width) perr ("MSB %u >= width of '%s'", (SYM).c_str ()); \
  }                                                                         \
  BitVector::BitRange NAME (symtab[(SYM)], MSB, LSB)

#define CHKRANGESAMEWIDTH(RANGE0, RANGE1)             \
  do                                                  \
  {                                                   \
    if (RANGE0.getWidth () != RANGE1.getWidth ())     \
      perr ("range [%u:%u] and [%u:%u] do not match", \
            RANGE0.m_nMsb,                            \
            RANGE0.m_nLsb,                            \
            RANGE1.m_nMsb,                            \
            RANGE1.m_nLsb);                           \
  } while (0)

#define UNARY(NAME)                 \
  (!strcmp (op, #NAME)) do          \
  {                                 \
    CHKARGS (6);                    \
    RANGE (c, T (1), N (2), N (3)); \
    RANGE (n, T (4), N (5), N (6)); \
    CHKRANGESAMEWIDTH (c, n);       \
    ibvm->NAME (c, n);              \
    stats.NAME++;                   \
  }                                 \
  while (0)

#define BINARY(NAME)                \
  (!strcmp (op, #NAME)) do          \
  {                                 \
    CHKARGS (9);                    \
    RANGE (c, T (1), N (2), N (3)); \
    RANGE (a, T (4), N (5), N (6)); \
    RANGE (b, T (7), N (8), N (9)); \
    CHKRANGESAMEWIDTH (c, a);       \
    CHKRANGESAMEWIDTH (c, b);       \
    ibvm->NAME (c, a, b);           \
    stats.NAME++;                   \
  }                                 \
  while (0)

#define PRED1(NAME)                 \
  (!strcmp (op, #NAME)) do          \
  {                                 \
    CHKARGS (5);                    \
    RANGE (c, T (1), N (2), N (2)); \
    RANGE (a, T (3), N (4), N (5)); \
    assert (c.getWidth () == 1);    \
    ibvm->NAME (c, a);              \
    stats.NAME++;                   \
  }                                 \
  while (0)

#define PRED2(NAME)                 \
  (!strcmp (op, #NAME)) do          \
  {                                 \
    CHKARGS (8);                    \
    RANGE (c, T (1), N (2), N (2)); \
    RANGE (a, T (3), N (4), N (5)); \
    RANGE (b, T (6), N (7), N (8)); \
    assert (c.getWidth () == 1);    \
    CHKRANGESAMEWIDTH (a, b);       \
    ibvm->NAME (c, a, b);           \
    stats.NAME++;                   \
  }                                 \
  while (0)

static void
parse_line ()
{
  const char* str;
  vector<string> toks;
  if (!(str = strtok (line, "("))) perr ("'(' missing");
  toks.push_back (string (str));
  while ((str = strtok (0, ",)"))) toks.push_back (string (str));
#if 1
  printf ("[btorimc] line %d : ", lineno);
  for (vector<string>::const_iterator it = toks.begin (); it != toks.end ();
       it++)
  {
    printf (" %s", (*it).c_str ());
  }
  printf ("\n");
#endif
  size_t size = toks.size ();
  assert (size > 0);
  const char* op = toks[0].c_str ();
  if (!strcmp (op, "addVariable"))
  {
    CHKARGS (7);
    string sym  = T (2);
    unsigned id = N (1);
    CHKIDUNUSED (id);
    CHKSYMUNUSED (sym);
    unsigned width = N (3);
    if (width <= 0) perr ("expected positive width but got %u", width);
    symtab[sym] = id;
    Var v (sym, width);
    idtab[id] = Var (sym, width);
    stats.addVariable++;
    ibvm->addVariable (
        id, sym, width, N (4), N (5), N (6), (BitVector::DirectionKind) N (7));
  }
  else if (!strcmp (op, "addRangeName"))
  {
    CHKARGS (6);
    RANGE (range, T (1), N (2), N (3));
    unsigned msb = N (5), lsb = N (6);
    if (msb < lsb) perr ("MSB %u < LSB %u", msb, lsb);
    ibvm->addRangeName (range, T (4), msb, lsb);
    stats.addRangeName++;
  }
  else if (!strcmp (op, "addConstant"))
  {
    CHKARGS (3);
    unsigned id = N (1);
    CHKIDUNUSED (id);
    char buf[20];
    sprintf (buf, "b0_v%u", id);  // TODO hack to get generated examples through
    string sym (buf);
    unsigned width = N (3);
    if (T (2).size () != width)
      perr ("constant string '%s' does not match width %u",
            T (2).c_str (),
            width);
    idtab[id]   = Var (T (2), width);
    symtab[sym] = id;
    ibvm->addConstant (id, T (2), width);
    stats.addConstant++;
  }
  else if (!strcmp (op, "addCondition"))
  {
    CHKARGS (12);
    RANGE (n, T (1), N (2), N (3));
    RANGE (c, T (4), N (5), N (6));
    RANGE (t, T (7), N (8), N (9));
    RANGE (e, T (7), N (8), N (9));
    CHKRANGESAMEWIDTH (n, t);
    CHKRANGESAMEWIDTH (n, e);
    if (c.getWidth () != 1) CHKRANGESAMEWIDTH (n, c);
    ibvm->addCondition (n, c, t, e);
    stats.addCondition++;
  }
  else if
    UNARY (addNonState);
  else if
    UNARY (addAssignment);
  else if
    UNARY (addBitNot);
  else if
    PRED1 (addLogicalNot);
  else if
    BINARY (addState);
  else if
    PRED2 (addEqual);
  else if
    PRED2 (addLogicalAnd);
  else
    perr ("unknown operator '%s'", op);
}

static void
parse ()
{
  while (read_line ()) parse_line (), lineno++;
}

int
main (int argc, char** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-h"))
    {
      fputs ("usage: btorimc [-h] [<ibvfile>]\n", stdout);
      exit (0);
    }
    else if (close_input)
      err ("more than one input");
    else if (!(input = fopen (input_name = argv[i], "r")))
      err ("can not read '%s'", argv[i]);
    else
      close_input = true;
  }
  msg ("reading '%s'", input_name);
  ibvm = new BtorIBV ();
  ibvm->setVerbosity (10);
  parse ();
  if (close_input) fclose (input);
  ibvm->analyze ();
  ibvm->translate ();
  delete ibvm;
  return 0;
}
