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
  int width;
  Var () {}
  Var (string n, int w) : name (n), width (w) {}
};

static map<string, int> symtab;
static map<int, Var> idtab;
static BtorIBV* ibvm;
static FILE* input            = stdin;
static int lineno             = 1;
static const char* input_name = "<stdin>";
static bool close_input;
static int szline, nline;
static char* line;

static struct
{
  int vars;
  int rangenames;
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
      if (stats.vars) msg ("parsed %d variables", stats.vars);
      if (stats.rangenames) msg ("parsed %d range names", stats.rangenames);
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
    if (idtab.find (ID) != idtab.end ()) perr ("id %d already used", ID); \
  } while (0)

#define CHKID(ID)                                                      \
  do                                                                   \
  {                                                                    \
    if (idtab.find (ID) == idtab.end ()) perr ("id %d undefined", ID); \
  } while (0)

#define CHKSYMUNUSED(SYM)                              \
  do                                                   \
  {                                                    \
    if (symtab.find (SYM) != symtab.end ())            \
      perr ("symbol '%s' already used", SYM.c_str ()); \
  } while (0)

#define NUM(I) atoi (toks[I].c_str ())

#define CHKUNUSEDRANGE(RANGE)                                                  \
  do                                                                           \
  {                                                                            \
    CHKIDUNUSED (RANGE.id);                                                    \
    if (RANGE.msb < RANGE.lsb) perr ("MSB %d < LSB %d", RANGE.msb, RANGE.lsb); \
  } while (0)

#define CHKRANGE(RANGE)                                                        \
  do                                                                           \
  {                                                                            \
    CHKID (RANGE.id);                                                          \
    if (RANGE.msb < RANGE.lsb) perr ("MSB %d < LSB %d", RANGE.msb, RANGE.lsb); \
    {                                                                          \
    }                                                                          \
  } while (0)

static void
parse_line ()
{
  const char* str;
  vector<string> toks;
  if (!(str = strtok (line, "("))) perr ("'(' missing");
  toks.push_back (string (str));
  while ((str = strtok (0, ",)"))) toks.push_back (string (str));
#if 1
  printf ("[btoimc] line %d : ", lineno);
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
    string sym = toks[2];
    int id     = NUM (1);
    CHKIDUNUSED (id);
    CHKSYMUNUSED (sym);
    int width = NUM (3);
    if (width <= 0) perr ("expected positive width but got %d", width);
    symtab[sym] = id;
    Var v (sym, width);
    idtab[id] = Var (sym, width);
    stats.vars++;
  }
  else if (!strcmp (op, "addRangeName"))
  {
    CHKARGS (6);
    stats.rangenames++;
  }
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
  parse ();
  if (close_input) fclose (input);
  ibvm = new BtorIBV ();
  ibvm->setVerbosity (10);
  ibvm->analyze ();
  ibvm->translate ();
  delete ibvm;
  return 0;
}
