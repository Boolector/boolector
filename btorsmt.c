#include "btorsmt.h"
#include "btorconst.h"
#include "btormem.h"
#include "btorstack.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>

typedef struct BtorSMTParser BtorSMTParser;
typedef struct BtorSMTNode BtorSMTNode;
typedef struct BtorSMTNodes BtorSMTNodes;
typedef struct BtorSMTSymbol BtorSMTSymbol;

enum BtorSMTCharacterClass
{
  BTOR_SMTCC_IDENTIFIER_START    = 1,
  BTOR_SMTCC_IDENTIFIER_MIDDLE   = 2,
  BTOR_SMTCC_ARITHMETIC_OPERATOR = 4,
  BTOR_SMTCC_NUMERAL_START       = 8,
  BTOR_SMTCC_DIGIT               = 16,
  BTOR_SMTCC_SPACE               = 32,
  BTOR_SMTCC_IDENTIFIER_PREFIX   = 64,
};

enum BtorSMTToken
{
  BTOR_SMTOK_ERR = 0,
  BTOR_SMTOK_EOF = EOF,

  BTOR_SMTOK_IDENTIFIER = 'a',
  BTOR_SMTOK_NUMERAL    = '0',
  BTOR_SMTOK_RATIONAL   = '.',
  BTOR_SMTOK_USERVAL    = '{',
  BTOR_SMTOK_LP         = '(',
  BTOR_SMTOK_RP         = ')',
  BTOR_SMTOK_STRING     = '"',
  BTOR_SMTOK_VAR        = '?',
  BTOR_SMTOK_FVAR       = '$',
  BTOR_SMTOK_ATTR       = ':',
  BTOR_SMTOK_ARITH      = '=',

  BTOR_SMTOK_KEYWORD      = 256, /* above ASCII codes */
  BTOR_SMTOK_AND          = 256,
  BTOR_SMTOK_ASSUMPTION   = 257,
  BTOR_SMTOK_BENCHMARK    = 258,
  BTOR_SMTOK_DISTINCT     = 259,
  BTOR_SMTOK_EXTRAFUNS    = 260,
  BTOR_SMTOK_EXTRAPREDS   = 261,
  BTOR_SMTOK_EXTRASORTS   = 262,
  BTOR_SMTOK_FALSE        = 263,
  BTOR_SMTOK_FLET         = 264,
  BTOR_SMTOK_FORMULA      = 265,
  BTOR_SMTOK_IFF          = 266,
  BTOR_SMTOK_IF_THEN_ELSE = 267,
  BTOR_SMTOK_IMPLIES      = 268,
  BTOR_SMTOK_ITE          = 269,
  BTOR_SMTOK_LET          = 270,
  BTOR_SMTOK_LOGICATTR    = 271,
  BTOR_SMTOK_NOT          = 272,
  BTOR_SMTOK_NOTES        = 273,
  BTOR_SMTOK_OR           = 274,
  BTOR_SMTOK_SAT          = 275,
  BTOR_SMTOK_STATUS       = 276,
  BTOR_SMTOK_TRUE         = 277,
  BTOR_SMTOK_UNKNOWN      = 278,
  BTOR_SMTOK_UNSAT        = 279,
  BTOR_SMTOK_XOR          = 280,

  BTOR_SMTOK_CONCAT  = 281, /* QF_BV specific symbols */
  BTOR_SMTOK_EQ      = 282,
  BTOR_SMTOK_EXTRACT = 283,
  BTOR_SMTOK_BIT0    = 284,
  BTOR_SMTOK_BIT1    = 285,
  BTOR_SMTOK_BVADD   = 286,
  BTOR_SMTOK_BVNOT   = 287,
  BTOR_SMTOK_BVMUL   = 288,
  BTOR_SMTOK_BVULE   = 289,
  BTOR_SMTOK_BVAND   = 290,
  BTOR_SMTOK_BVLSHR  = 291,
  BTOR_SMTOK_BVSLT   = 292,
  BTOR_SMTOK_BVULT   = 293,
  BTOR_SMTOK_BVNEG   = 294,
  BTOR_SMTOK_BVSLE   = 295,
  BTOR_SMTOK_BVSHL   = 296,
  BTOR_SMTOK_BVSUB   = 297,
  BTOR_SMTOK_BVSDIV  = 298,
  BTOR_SMTOK_BVASHR  = 299,
  BTOR_SMTOK_BVOR    = 300,
  BTOR_SMTOK_BVUDIV  = 301,
  BTOR_SMTOK_BVUREM  = 302,
  BTOR_SMTOK_BVNAND  = 303,
  BTOR_SMTOK_BVNOR   = 304,
  BTOR_SMTOK_BVUGT   = 305,
  BTOR_SMTOK_BVUGE   = 306,
  BTOR_SMTOK_BVSGT   = 307,
  BTOR_SMTOK_BVSGE   = 308,
  BTOR_SMTOK_BVCOMP  = 309,

  BTOR_SMTOK_REPEAT       = 310,
  BTOR_SMTOK_ZERO_EXTEND  = 311,
  BTOR_SMTOK_SIGN_EXTEND  = 312,
  BTOR_SMTOK_ROTATE_LEFT  = 313,
  BTOR_SMTOK_ROTATE_RIGHT = 314,

  BTOR_SMTOK_BVXOR  = 315,
  BTOR_SMTOK_BVSREM = 316,
  BTOR_SMTOK_BVSMOD = 317,
  BTOR_SMTOK_BVXNOR = 318,

  BTOR_SMTOK_SELECT = 319,
  BTOR_SMTOK_STORE  = 320,

  BTOR_SMTOK_UNSUPPORTED_KEYWORD = 512,
  BTOR_SMTOK_AXIOMS              = 512,
  BTOR_SMTOK_DEFINITIONS         = 513,
  BTOR_SMTOK_EXISTS              = 514,
  BTOR_SMTOK_EXTENSIONS          = 515,
  BTOR_SMTOK_FORALL              = 516,
  BTOR_SMTOK_FUNS                = 517,
  BTOR_SMTOK_LANGUAGE            = 518,
  BTOR_SMTOK_LOGIC               = 519,
  BTOR_SMTOK_PREDS               = 520,
  BTOR_SMTOK_SORTS               = 521,
  BTOR_SMTOK_THEORY              = 522,
  BTOR_SMTOK_THEORYATTR          = 523,

  BTOR_SMTOK_INTERNAL = 1024,
  BTOR_SMTOK_BIND     = 1024,
};

typedef enum BtorSMTToken BtorSMTToken;

struct BtorSMTNode
{
  BtorExp *exp;
  void *head;
  void *tail;
};

#define BTOR_SMT_NODES 10000

struct BtorSMTNodes
{
  BtorSMTNodes *next;
  BtorSMTNode nodes[BTOR_SMT_NODES];
};

BTOR_DECLARE_STACK (SMTNodePtr, BtorSMTNode *);

struct BtorSMTSymbol
{
  char *name;
  BtorSMTToken token;
  BtorSMTSymbol *next;
  BtorExp *exp;
};

struct BtorSMTParser
{
  BtorMemMgr *mem;
  Btor *btor;
  int verbosity;
  int parsed;

  const char *name;
  FILE *file;
  int lineno;
  int saved; /* boolean flag */
  int saved_char;

  unsigned long long bytes;

  char *error;
  BtorCharStack buffer;

  unsigned char types[256];

  BtorSMTSymbol *symbol;
  BtorSMTSymbol **symtab;
  unsigned szsymtab;
  unsigned symbols;

  unsigned constants;

  BtorSMTNode *bind;

  BtorSMTNodePtrStack stack;
  BtorSMTNodePtrStack work;
  BtorIntStack heads;

  BtorSMTNodes *chunks;
  BtorSMTNode *free;
  BtorSMTNode *last;
  unsigned nodes;

  BtorExpPtrStack inputs;
  BtorExpPtrStack outputs;
};

static unsigned primes[] = {1001311, 2517041, 3543763, 4026227};
#define PRIMES ((sizeof primes) / sizeof *primes)

static void *
car (BtorSMTNode *node)
{
  assert (node);
  return node->head;
}

static void *
cdr (BtorSMTNode *node)
{
  assert (node);
  return node->tail;
}

static BtorSMTNode *
cons (BtorSMTParser *parser, void *h, void *t)
{
  BtorSMTNodes *chunk;
  BtorSMTNode *res;

  if (parser->free == parser->last)
  {
    BTOR_NEW (parser->mem, chunk);
    BTOR_CLR (chunk);
    chunk->next    = parser->chunks;
    parser->chunks = chunk;

    parser->free = chunk->nodes;
    parser->last = chunk->nodes + BTOR_SMT_NODES;
  }

  res = parser->free++;
  parser->nodes++;

  res->exp  = 0;
  res->head = h;
  res->tail = t;

  return res;
}

static void
btor_smt_message (BtorSMTParser *parser, int level, const char *fmt, ...)
{
  va_list ap;

  assert (level >= 0);

  if (parser->verbosity < level) return;

  fflush (stdout);
  fprintf (stdout, "[btorsmt] ");
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#define isleaf(l) (1lu & (unsigned long) (l))
#define leaf(l) ((void *) (1lu | (unsigned long) (l)))
#define strip(l) ((BtorSMTSymbol *) ((~1lu) & (unsigned long) (l)))

static unsigned
length (BtorSMTNode *node)
{
  BtorSMTNode *p;
  unsigned res;

  assert (!isleaf (node));

  res = 0;
  for (p = node; p; p = cdr (p)) res++;

  return res;
}

static int
is_list_of_length (BtorSMTNode *node, unsigned l)
{
  if (isleaf (node)) return 0;

  return length (node) == l;
}

static void
btor_release_smt_symbols (BtorSMTParser *parser)
{
  BtorSMTSymbol *p, *next;
  BtorExp *e;
  unsigned i;

  for (i = 0; i < parser->szsymtab; i++)
  {
    for (p = parser->symtab[i]; p; p = next)
    {
      next = p->next;

      btor_freestr (parser->mem, p->name);

      if ((e = p->exp)) btor_release_exp (parser->btor, e);

      BTOR_DELETE (parser->mem, p);
    }
  }
  BTOR_DELETEN (parser->mem, parser->symtab, parser->szsymtab);
  parser->symtab   = 0;
  parser->szsymtab = 0;
}

static void
btor_release_smt_nodes (BtorSMTParser *parser)
{
  BtorSMTNodes *p, *next;
  BtorExp *e;
  unsigned i;

  for (p = parser->chunks; p; p = next)
  {
    next = p->next;

    for (i = 0; i < BTOR_SMT_NODES; i++)
      if ((e = p->nodes[i].exp)) btor_release_exp (parser->btor, e);

    BTOR_DELETE (parser->mem, p);
  }

  parser->chunks = 0;
}

static void
btor_release_smt_internals (BtorSMTParser *parser)
{
  btor_release_smt_symbols (parser);
  btor_release_smt_nodes (parser);

  BTOR_RELEASE_STACK (parser->mem, parser->stack);
  BTOR_RELEASE_STACK (parser->mem, parser->work);
  BTOR_RELEASE_STACK (parser->mem, parser->heads);
  BTOR_RELEASE_STACK (parser->mem, parser->buffer);
}

static void
btor_release_smt_vars (BtorSMTParser *parser)
{
  BtorExp **p;

  for (p = parser->inputs.start; p < parser->inputs.top; p++)
    btor_release_exp (parser->btor, *p);

  BTOR_RELEASE_STACK (parser->mem, parser->inputs);
}

static void
btor_delete_smt_parser (BtorSMTParser *parser)
{
  BtorExp **p;

  btor_release_smt_internals (parser);

  btor_freestr (parser->mem, parser->error);
  btor_release_smt_vars (parser);

  for (p = parser->outputs.start; p != parser->outputs.top; p++)
    btor_release_exp (parser->btor, *p);
  BTOR_RELEASE_STACK (parser->mem, parser->outputs);

  BTOR_DELETE (parser->mem, parser);
}

static char *
parse_error (BtorSMTParser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start (ap, fmt);
    bytes = btor_parse_error_message_length (parser->name, fmt, ap);
    va_end (ap);

    va_start (ap, fmt);
    parser->error = btor_parse_error_message (
        parser->mem, parser->name, parser->lineno, fmt, ap, bytes);
    va_end (ap);
  }

  return parser->error;
}

static unsigned
hash_name (const char *name)
{
  unsigned i, res;
  const char *p;
  char ch;

  i   = 0;
  res = 0;

  for (p = name; (ch = *p); p++)
  {
    res += primes[i++] * (unsigned) ch;

    if (i == PRIMES) i = 0;

    res = (res << 4) | (res >> 28);
  }

  return res;
}

static void
enlarge_symtab (BtorSMTParser *parser)
{
  BtorSMTSymbol *p, *next, **old_symtab, **new_symtab;
  unsigned h, i, old_size, new_size;

  old_symtab = parser->symtab;
  old_size   = parser->szsymtab;

  new_size = old_size ? 2 * old_size : 1;
  BTOR_NEWN (parser->mem, new_symtab, new_size);
  BTOR_CLRN (new_symtab, new_size);

  for (i = 0; i < old_size; i++)
  {
    for (p = old_symtab[i]; p; p = next)
    {
      next          = p->next;
      h             = hash_name (p->name) & (new_size - 1);
      p->next       = new_symtab[h];
      new_symtab[h] = p;
    }
  }

  BTOR_DELETEN (parser->mem, old_symtab, old_size);

  parser->symtab   = new_symtab;
  parser->szsymtab = new_size;
}

static BtorSMTSymbol **
find_symbol_position (BtorSMTParser *parser, const char *name)
{
  unsigned h = hash_name (name) & (parser->szsymtab - 1);
  BtorSMTSymbol **p, *s;

  for (p = parser->symtab + h; (s = *p) && strcmp (name, s->name); p = &s->next)
    ;

  return p;
}

static BtorSMTSymbol *
insert_symbol (BtorSMTParser *parser, const char *name)
{
  BtorSMTSymbol **p, *res;

  if (parser->szsymtab == parser->symbols) enlarge_symtab (parser);

  p = find_symbol_position (parser, name);
  if (!(res = *p))
  {
    BTOR_NEW (parser->mem, res);
    BTOR_CLR (res);

    res->token = BTOR_SMTOK_IDENTIFIER;
    res->name  = btor_strdup (parser->mem, name);

    parser->symbols++;
    *p = res;
  }

  return res;
}

static BtorSMTParser *
btor_new_smt_parser (Btor *btor, int verbosity)
{
  BtorMemMgr *mem = btor->mm;
  BtorSMTSymbol *bind;
  BtorSMTParser *res;
  unsigned char type;
  int ch;

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->verbosity = verbosity;

  btor_smt_message (res, 2, "initializing SMT parser");

  res->mem  = mem;
  res->btor = btor;

  type = BTOR_SMTCC_IDENTIFIER_START | BTOR_SMTCC_IDENTIFIER_MIDDLE;

  for (ch = 'a'; ch <= 'z'; ch++) res->types[ch] |= type;
  for (ch = 'A'; ch <= 'Z'; ch++) res->types[ch] |= type;

  res->types['_'] |= BTOR_SMTCC_IDENTIFIER_MIDDLE;
  res->types['.'] |= BTOR_SMTCC_IDENTIFIER_MIDDLE;
  res->types['\''] |= BTOR_SMTCC_IDENTIFIER_MIDDLE;

  type = BTOR_SMTCC_IDENTIFIER_MIDDLE;
  type |= BTOR_SMTCC_DIGIT;

  res->types['0'] |= type;

  type |= BTOR_SMTCC_NUMERAL_START;
  for (ch = '1'; ch <= '9'; ch++) res->types[ch] |= type;

  res->types['='] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['<'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['>'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['&'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['@'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['#'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['+'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['-'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['*'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['/'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['%'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['|'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['~'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;

  res->types[' '] |= BTOR_SMTCC_SPACE;
  res->types['\t'] |= BTOR_SMTCC_SPACE;
  res->types['\n'] |= BTOR_SMTCC_SPACE;

  res->types[':'] |= BTOR_SMTCC_IDENTIFIER_PREFIX;
  res->types['?'] |= BTOR_SMTCC_IDENTIFIER_PREFIX;
  res->types['$'] |= BTOR_SMTCC_IDENTIFIER_PREFIX;

  insert_symbol (res, "and")->token          = BTOR_SMTOK_AND;
  insert_symbol (res, ":assumption")->token  = BTOR_SMTOK_ASSUMPTION;
  insert_symbol (res, ":axioms")->token      = BTOR_SMTOK_AXIOMS;
  insert_symbol (res, "benchmark")->token    = BTOR_SMTOK_BENCHMARK;
  insert_symbol (res, ":definitions")->token = BTOR_SMTOK_DEFINITIONS;
  insert_symbol (res, "distinct")->token     = BTOR_SMTOK_DISTINCT;
  insert_symbol (res, "exists")->token       = BTOR_SMTOK_EXISTS;
  insert_symbol (res, ":extensions")->token  = BTOR_SMTOK_EXTENSIONS;
  insert_symbol (res, ":extrafuns")->token   = BTOR_SMTOK_EXTRAFUNS;
  insert_symbol (res, ":extrapreds")->token  = BTOR_SMTOK_EXTRAPREDS;
  insert_symbol (res, ":extrasorts")->token  = BTOR_SMTOK_EXTRASORTS;
  insert_symbol (res, "false")->token        = BTOR_SMTOK_FALSE;
  insert_symbol (res, "flet")->token         = BTOR_SMTOK_FLET;
  insert_symbol (res, "forall")->token       = BTOR_SMTOK_FORALL;
  insert_symbol (res, ":formula")->token     = BTOR_SMTOK_FORMULA;
  insert_symbol (res, ":funs")->token        = BTOR_SMTOK_FUNS;
  insert_symbol (res, "iff")->token          = BTOR_SMTOK_IFF;
  insert_symbol (res, "if_then_else")->token = BTOR_SMTOK_IF_THEN_ELSE;
  insert_symbol (res, "implies")->token      = BTOR_SMTOK_IMPLIES;
  insert_symbol (res, "ite")->token          = BTOR_SMTOK_ITE;
  insert_symbol (res, ":language")->token    = BTOR_SMTOK_LANGUAGE;
  insert_symbol (res, "let")->token          = BTOR_SMTOK_LET;
  insert_symbol (res, "logic")->token        = BTOR_SMTOK_LOGIC;
  insert_symbol (res, ":logic")->token       = BTOR_SMTOK_LOGICATTR;
  insert_symbol (res, ":notes")->token       = BTOR_SMTOK_NOTES;
  insert_symbol (res, "not")->token          = BTOR_SMTOK_NOT;
  insert_symbol (res, "or")->token           = BTOR_SMTOK_OR;
  insert_symbol (res, ":preds")->token       = BTOR_SMTOK_PREDS;
  insert_symbol (res, "sat")->token          = BTOR_SMTOK_SAT;
  insert_symbol (res, ":sorts")->token       = BTOR_SMTOK_SORTS;
  insert_symbol (res, ":status")->token      = BTOR_SMTOK_STATUS;
  insert_symbol (res, "theory")->token       = BTOR_SMTOK_THEORY;
  insert_symbol (res, ":theory")->token      = BTOR_SMTOK_THEORYATTR;
  insert_symbol (res, "true")->token         = BTOR_SMTOK_TRUE;
  insert_symbol (res, "unknown")->token      = BTOR_SMTOK_UNKNOWN;
  insert_symbol (res, "unsat")->token        = BTOR_SMTOK_UNSAT;
  insert_symbol (res, "xor")->token          = BTOR_SMTOK_XOR;

  bind        = insert_symbol (res, "_bind_");
  bind->token = BTOR_SMTOK_BIND;
  res->bind   = leaf (bind);

  insert_symbol (res, "=")->token      = BTOR_SMTOK_EQ;
  insert_symbol (res, "concat")->token = BTOR_SMTOK_CONCAT;
  insert_symbol (res, "bit0")->token   = BTOR_SMTOK_BIT0;
  insert_symbol (res, "bit1")->token   = BTOR_SMTOK_BIT1;
  insert_symbol (res, "bvadd")->token  = BTOR_SMTOK_BVADD;
  insert_symbol (res, "bvnot")->token  = BTOR_SMTOK_BVNOT;
  insert_symbol (res, "bvmul")->token  = BTOR_SMTOK_BVMUL;
  insert_symbol (res, "bvule")->token  = BTOR_SMTOK_BVULE;
  insert_symbol (res, "bvand")->token  = BTOR_SMTOK_BVAND;
  insert_symbol (res, "bvlshr")->token = BTOR_SMTOK_BVLSHR;
  insert_symbol (res, "bvslt")->token  = BTOR_SMTOK_BVSLT;
  insert_symbol (res, "bvult")->token  = BTOR_SMTOK_BVULT;
  insert_symbol (res, "bvneg")->token  = BTOR_SMTOK_BVNEG;
  insert_symbol (res, "bvsle")->token  = BTOR_SMTOK_BVSLE;
  insert_symbol (res, "bvshl")->token  = BTOR_SMTOK_BVSHL;
  insert_symbol (res, "bvsub")->token  = BTOR_SMTOK_BVSUB;
  insert_symbol (res, "bvsdiv")->token = BTOR_SMTOK_BVSDIV;
  insert_symbol (res, "bvashr")->token = BTOR_SMTOK_BVASHR;
  insert_symbol (res, "bvor")->token   = BTOR_SMTOK_BVOR;
  insert_symbol (res, "bvudiv")->token = BTOR_SMTOK_BVUDIV;
  insert_symbol (res, "bvurem")->token = BTOR_SMTOK_BVUREM;
  insert_symbol (res, "bvnor")->token  = BTOR_SMTOK_BVNOR;
  insert_symbol (res, "bvnand")->token = BTOR_SMTOK_BVNAND;
  insert_symbol (res, "bvugt")->token  = BTOR_SMTOK_BVUGT;
  insert_symbol (res, "bvuge")->token  = BTOR_SMTOK_BVUGE;
  insert_symbol (res, "bvsgt")->token  = BTOR_SMTOK_BVSGT;
  insert_symbol (res, "bvsge")->token  = BTOR_SMTOK_BVSGE;
  insert_symbol (res, "bvcomp")->token = BTOR_SMTOK_BVCOMP;
  insert_symbol (res, "bvxor")->token  = BTOR_SMTOK_BVXOR;
  insert_symbol (res, "bvsrem")->token = BTOR_SMTOK_BVSREM;
  insert_symbol (res, "bvsmod")->token = BTOR_SMTOK_BVSMOD;
  insert_symbol (res, "bvxnor")->token = BTOR_SMTOK_BVXNOR;
  insert_symbol (res, "select")->token = BTOR_SMTOK_SELECT;
  insert_symbol (res, "store")->token  = BTOR_SMTOK_STORE;

  return res;
}

static int
nextch (BtorSMTParser *parser)
{
  int res;

  if (parser->saved)
  {
    res           = parser->saved_char;
    parser->saved = 0;
  }
  else
  {
    parser->bytes++;
    res = getc (parser->file);
  }

  if (res == '\n') parser->lineno++;

  return res;
}

static void
savech (BtorSMTParser *parser, int ch)
{
  assert (ch);
  assert (!parser->saved);

  parser->saved_char = ch;
  parser->saved      = 1;

  if (ch == '\n')
  {
    assert (parser->lineno > 1);
    parser->lineno--;
  }
}

static unsigned char
int2type (BtorSMTParser *parser, int ch)
{
  assert (0 <= ch && ch < 256);
  return parser->types[ch];
}

static int
has_prefix (const char *str, const char *prefix)
{
  const char *p, *q;

  for (p = str, q = prefix; *q && *p == *q; p++, q++)
    ;

  return !*q;
}

static BtorSMTToken
nextok (BtorSMTParser *parser)
{
  unsigned char type;
  BtorSMTToken res;
  int ch, count;

  parser->symbol = 0;
  BTOR_RESET_STACK (parser->buffer);

SKIP_WHITE_SPACE:

  ch = nextch (parser);
  if (ch == EOF) return EOF;

  type = int2type (parser, ch);
  if (type & BTOR_SMTCC_SPACE) goto SKIP_WHITE_SPACE;

  if (type & BTOR_SMTCC_IDENTIFIER_START)
  {
    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    while (int2type (parser, (ch = nextch (parser)))
           & BTOR_SMTCC_IDENTIFIER_MIDDLE)
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    count = 0;

    if (ch == '[')
    {
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

      ch = nextch (parser);

      for (;;)
      {
        if (int2type (parser, ch) & BTOR_SMTCC_NUMERAL_START)
        {
          BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

          while (int2type (parser, (ch = nextch (parser))) & BTOR_SMTCC_DIGIT)
            BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

        COUNT_AND_CONTINUE_WITH_NEXT_INDEX:

          count++;

          if (ch == ']') break;

          if (ch != ':') goto UNEXPECTED_CHARACTER;

          BTOR_PUSH_STACK (parser->mem, parser->buffer, ':');
          ch = nextch (parser);
        }
        else if (ch == '0')
        {
          BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
          ch = nextch (parser);
          goto COUNT_AND_CONTINUE_WITH_NEXT_INDEX;
        }
        else
          goto UNEXPECTED_CHARACTER;
      }

      if (!count) return !parse_error (parser, "empty index list");

      assert (ch == ']');
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
    }
    else
    {
      if (!ch) goto UNEXPECTED_CHARACTER;

      savech (parser, ch);
    }

    BTOR_PUSH_STACK (parser->mem, parser->buffer, 0);

    parser->symbol = insert_symbol (parser, parser->buffer.start);

    if (count == 2 && has_prefix (parser->symbol->name, "extract["))
      parser->symbol->token = BTOR_SMTOK_EXTRACT;

    if (count == 1)
    {
      if (has_prefix (parser->symbol->name, "repeat["))
        parser->symbol->token = BTOR_SMTOK_REPEAT;

      if (has_prefix (parser->symbol->name, "zero_extend["))
        parser->symbol->token = BTOR_SMTOK_ZERO_EXTEND;

      if (has_prefix (parser->symbol->name, "sign_extend["))
        parser->symbol->token = BTOR_SMTOK_SIGN_EXTEND;

      if (has_prefix (parser->symbol->name, "rotate_left["))
        parser->symbol->token = BTOR_SMTOK_ROTATE_LEFT;

      if (has_prefix (parser->symbol->name, "rotate_right["))
        parser->symbol->token = BTOR_SMTOK_ROTATE_RIGHT;
    }

  CHECK_FOR_UNSUPPORTED_KEYWORD:

    if (parser->symbol->token >= BTOR_SMTOK_UNSUPPORTED_KEYWORD)
      return !parse_error (
          parser, "unsupported keyword '%s'", parser->buffer.start);

    return parser->symbol->token;
  }

  if (ch == '(') return BTOR_SMTOK_LP;

  if (ch == ')') return BTOR_SMTOK_RP;

  if (type & BTOR_SMTCC_IDENTIFIER_PREFIX)
  {
    res = ch;

    assert (ch == '?' || ch == '$' || ch == ':');

    assert ((ch == '?') == (res == BTOR_SMTOK_VAR));
    assert ((ch == '$') == (res == BTOR_SMTOK_FVAR));
    assert ((ch == ':') == (res == BTOR_SMTOK_ATTR));

    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    ch = nextch (parser);
    if (!(int2type (parser, ch) & BTOR_SMTCC_IDENTIFIER_START))
      return !parse_error (parser, "expected identifier after '%c'", res);

    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    while (int2type (parser, (ch = nextch (parser)))
           & BTOR_SMTCC_IDENTIFIER_MIDDLE)
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    if (!ch) goto UNEXPECTED_CHARACTER;

    savech (parser, ch);
    BTOR_PUSH_STACK (parser->mem, parser->buffer, 0);

    parser->symbol = insert_symbol (parser, parser->buffer.start);

    if (res == BTOR_SMTOK_VAR || res == BTOR_SMTOK_FVAR)
      parser->symbol->token = res;

    goto CHECK_FOR_UNSUPPORTED_KEYWORD;
  }

  if (type & BTOR_SMTCC_NUMERAL_START)
  {
    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    while (int2type (parser, (ch = nextch (parser))) & BTOR_SMTCC_DIGIT)
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

  CHECK_FOR_FRACTIONAL_PART:

    if (ch == '.')
    {
      res = BTOR_SMTOK_RATIONAL;

      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
      ch = nextch (parser);

      if (int2type (parser, ch) & BTOR_SMTCC_NUMERAL_START)
      {
        BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

        while (int2type (parser, (ch = nextch (parser)))
               & BTOR_SMTCC_NUMERAL_START)
          BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
      }
      else if (ch == '0')
      {
        BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

        ch = nextch (parser);
        if (int2type (parser, ch) & BTOR_SMTCC_DIGIT)
          goto UNEXPECTED_DIGIT_AFTER_ZERO;
      }
      else
        goto UNEXPECTED_CHARACTER;
    }
    else
      res = BTOR_SMTOK_NUMERAL;

    if (!ch) goto UNEXPECTED_CHARACTER;

    savech (parser, ch);
    BTOR_PUSH_STACK (parser->mem, parser->buffer, 0);

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = res;

    return res;
  }

  if (ch == '0')
  {
    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    ch = nextch (parser);
    if (int2type (parser, ch) & BTOR_SMTCC_DIGIT)
    {
    UNEXPECTED_DIGIT_AFTER_ZERO:
      return !parse_error (parser, "unexpected digit after '0'");
    }

    goto CHECK_FOR_FRACTIONAL_PART;
  }

  if (type & BTOR_SMTCC_ARITHMETIC_OPERATOR)
  {
    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    while (int2type (parser, (ch = nextch (parser)))
           & BTOR_SMTCC_ARITHMETIC_OPERATOR)
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    if (!ch) goto UNEXPECTED_CHARACTER;

    BTOR_PUSH_STACK (parser->mem, parser->buffer, 0);

    parser->symbol = insert_symbol (parser, parser->buffer.start);
    if (parser->symbol->token == BTOR_SMTOK_IDENTIFIER)
      parser->symbol->token = BTOR_SMTOK_ARITH;

    return parser->symbol->token;
  }

  if (ch == ';')
  {
    while ((ch = nextch (parser)) != '\n')
      if (ch == EOF) return BTOR_SMTOK_EOF;

    goto SKIP_WHITE_SPACE;
  }

  if (ch == '{')
  {
    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

    while ((ch = nextch (parser)) != '}')
    {
      if (ch == '{') return !parse_error (parser, "unescaped '{' after '{'");

      if (ch == '\\')
      {
        BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
        ch = nextch (parser);
      }

      if (ch == EOF) return !parse_error (parser, "unexpected EOF after '{'");

      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
    }

    assert (ch == '}');
    BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
    BTOR_PUSH_STACK (parser->mem, parser->buffer, 0);

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = BTOR_SMTOK_USERVAL;

    return BTOR_SMTOK_USERVAL;
  }

  if (ch == '"')
  {
    while ((ch = nextch (parser)) != '"')
    {
      if (ch == '\\')
      {
        BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
        ch = nextch (parser);
      }

      if (ch == EOF) return !parse_error (parser, "unexpected EOF after '\"'");

      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);
    }

    BTOR_PUSH_STACK (parser->mem, parser->buffer, 0);

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = BTOR_SMTOK_STRING;

    return BTOR_SMTOK_STRING;
  }

UNEXPECTED_CHARACTER:
  if (isprint (ch))
    return !parse_error (parser, "unexpected character '%c'", ch);

  return !parse_error (parser, "unexpected character with ASCII code %d", ch);
}

static void
btorsmtppaux (FILE *file, BtorSMTNode *node, int indent)
{
  int i;

  if (isleaf (node))
    fprintf (file, "%s", ((BtorSMTSymbol *) strip (node))->name);
  else
  {
    fputc ('(', file);

    for (;;)
    {
      btorsmtppaux (file, car (node), indent + 1);
      if (!(node = cdr (node))) break;

      fputc ('\n', file);
      for (i = 0; i <= indent; i++) fputc (' ', file);
    }

    fputc (')', file);
  }
}

void
btorsmtpp (BtorSMTNode *node)
{
  btorsmtppaux (stdout, node, 0);
  fputc ('\n', stdout);
  fflush (stdout);
}

static void
push_input (BtorSMTParser *parser, BtorExp *v)
{
  BTOR_PUSH_STACK (
      parser->mem, parser->inputs, btor_copy_exp (parser->btor, v));
}

static const char *
next_numeral (const char *str)
{
  const char *p = str;
  char ch;

  assert (str);

  if (isdigit (*p++))
  {
    while (isdigit (ch = *p++))
      ;

    if (ch == ':')
    {
      assert (isdigit (*p));
      return p;
    }

    assert (ch == ']');
  }
  else
  {
    while ((ch = *p++))
      if (ch == '[')
      {
        assert (isdigit (*p));
        return p;
      }
  }

  return 0;
}

static int
extrafun (BtorSMTParser *parser, BtorSMTNode *fdecl)
{
  BtorSMTSymbol *symbol, *sortsymbol;
  BtorSMTNode *node, *sort;
  int addrlen, datalen;
  const char *p;

  if (!fdecl || !cdr (fdecl) || isleaf (fdecl) || !isleaf (node = car (fdecl))
      || (symbol = strip (node))->token != BTOR_SMTOK_IDENTIFIER)
    return !parse_error (parser, "invalid function declaration");

  if (cdr (cdr (fdecl)))
    return !parse_error (parser,
                         "no support for function declaration "
                         "with more than one argument");

  sort = car (cdr (fdecl));
  if (!sort || !isleaf (sort)
      || (sortsymbol = strip (sort))->token != BTOR_SMTOK_IDENTIFIER)
  {
  INVALID_SORT:
    return !parse_error (parser,
                         "invalid or unsupported sort "
                         "in function declaration");
  }

  if (symbol->exp)
    return !parse_error (parser, "multiple definitions for '%s'", symbol->name);

  p = sortsymbol->name;

  if (has_prefix (p, "BitVec"))
  {
    if (!(p = next_numeral (p)) || next_numeral (p)) goto INVALID_SORT;

    datalen = atoi (p); /* TODO Overflow? */

    symbol->exp = btor_var_exp (parser->btor, datalen, symbol->name);
    push_input (parser, symbol->exp);
  }
  else if (has_prefix (p, "Array"))
  {
    if (!(p = next_numeral (p))) goto INVALID_SORT;

    addrlen = atoi (p); /* TODO Overflow? */

    if (!(p = next_numeral (p)) || next_numeral (p)) goto INVALID_SORT;

    datalen = atoi (p); /* TODO Overflow? */

    symbol->exp = btor_array_exp (parser->btor, datalen, addrlen, symbol->name);
    push_input (parser, symbol->exp);

    /* TODO what about 'symbol->name' back annotation? */
  }
  else
    goto INVALID_SORT;

  return 1;
}

static int
extrafuns (BtorSMTParser *parser, BtorSMTNode *list)
{
  BtorSMTNode *p;

  if (!list || isleaf (list))
    return !parse_error (parser,
                         "expected non empty list as argument to ':extrafuns'");

  for (p = list; p; p = cdr (p))
    if (!extrafun (parser, car (p))) return 0;

  return !parser->error;
}

static int
extrapred (BtorSMTParser *parser, BtorSMTNode *pdecl)
{
  BtorSMTSymbol *symbol;
  BtorSMTNode *node;

  if (!pdecl || isleaf (pdecl) || !isleaf (node = car (pdecl))
      || (symbol = strip (node))->token != BTOR_SMTOK_IDENTIFIER)
    return !parse_error (parser, "invalid predicate declaration");

  if (cdr (pdecl))
    return !parse_error (
        parser, "no support for predicate declarations with arguments");

  if (symbol->exp)
    return !parse_error (parser, "multiple definitions for '%s'", symbol->name);

  symbol->exp = btor_var_exp (parser->btor, 1, symbol->name);
  push_input (parser, symbol->exp);

  return 1;
}

static int
extrapreds (BtorSMTParser *parser, BtorSMTNode *list)
{
  BtorSMTNode *p;

  if (!list || isleaf (list))
    return !parse_error (
        parser, "expected non empty list as argument to ':extrapreds'");

  for (p = list; p; p = cdr (p))
    if (!extrapred (parser, car (p))) return 0;

  return !parser->error;
}

static BtorSMTToken
node2token (BtorSMTNode *node)
{
  return (node && isleaf (node)) ? strip (node)->token : BTOR_SMTOK_ERR;
}

static int
is_let_or_flet (BtorSMTNode *node)
{
  int token = node2token (node);
  return token == BTOR_SMTOK_LET || token == BTOR_SMTOK_FLET;
}

static BtorExp *
node2exp (BtorSMTParser *parser, BtorSMTNode *node)
{
  const char *p, *start, *end;
  char *tmp, *extended, ch;
  BtorSMTSymbol *symbol;
  int len, tlen, token;

  if (isleaf (node))
  {
    symbol = strip (node);
    if (symbol->exp) return symbol->exp;

    token = symbol->token;
    if (token == BTOR_SMTOK_TRUE || token == BTOR_SMTOK_BIT1)
      return symbol->exp = btor_const_exp (parser->btor, "1");

    if (token == BTOR_SMTOK_FALSE || token == BTOR_SMTOK_BIT0)
      return symbol->exp = btor_const_exp (parser->btor, "0");

    p = symbol->name;
    if (*p++ == 'b' && *p++ == 'v')
    {
      if (isdigit (*p))
      {
        start = p++;
        for (end = p; isdigit (*end); end++)
          ;

        if (*end == '[')
        {
          for (p = end + 1; isdigit (*p); p++)
            ;

          if (*p == ']')
          {
            len = atoi (end + 1);
            if (len)
            {
              tmp = btor_decimal_to_const_n (parser->mem, start, end - start);

              tlen = (int) strlen (tmp);

              if (tlen <= len)
              {
                if (tlen < len)
                {
                  extended = btor_uext_const (parser->mem, tmp, len - tlen);

                  btor_delete_const (parser->mem, tmp);
                  tmp = extended;
                }

                symbol->exp = btor_const_exp (parser->btor, tmp);
                parser->constants++;
              }

              btor_delete_const (parser->mem, tmp);
            }
          }
        }
      }
      else if (*p == 'b')
      {
        if (*++p == 'i' && *++p == 'n')
        {
          for (start = ++p; (ch = *p) == '0' || ch == '1'; p++)
            ;

          if (start < p && !*p)
          {
            symbol->exp = btor_const_exp (parser->btor, start);
            parser->constants++;
          }
        }
      }
      else if (*p++ == 'h' && *p++ == 'e' && *p++ == 'x')
      {
        for (start = p; isxdigit (*p); p++)
          ;

        if (start < p && !*p)
        {
          len  = 4 * (p - start);
          tmp  = btor_hex_to_const (parser->mem, start);
          tlen = (int) strlen (tmp);
          assert (tlen <= len);
          if (tlen < len)
          {
            extended = btor_uext_const (parser->mem, tmp, len - tlen);
            btor_delete_const (parser->mem, tmp);
            tmp = extended;
          }
          symbol->exp = btor_const_exp (parser->btor, tmp);
          btor_delete_const (parser->mem, tmp);
          parser->constants++;
        }
      }
      else
      {
        /* DO NOT ADD ANYTHING HERE BECAUSE 'p' CHANGED */
      }
    }

    if (symbol->exp) return symbol->exp;

    (void) parse_error (parser, "'%s' undefined", strip (node)->name);
    return 0;
  }
  else
  {
    assert (node->exp);
    return node->exp;
  }

  return 0;
}

static BtorExp *
node2nonarrayexp (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorExp *res;

  res = node2exp (parser, node);
  if (res && btor_is_array_exp (parser->btor, res))
  {
    (void) parse_error (parser, "unexpected array argument");
    res = 0;
  }

  return res;
}

static void
translate_unary (BtorSMTParser *parser,
                 BtorSMTNode *node,
                 const char *name,
                 BtorExp *(*f) (Btor *, BtorExp *) )
{
  BtorSMTNode *c;
  BtorExp *a;

  assert (!node->exp);

  if (!is_list_of_length (node, 2))
  {
    (void) parse_error (parser, "expected exactly one argument to '%s'", name);
    return;
  }

  c = car (cdr (node));
  if ((a = node2nonarrayexp (parser, c))) node->exp = f (parser->btor, a);
}

static void
translate_binary (BtorSMTParser *parser,
                  BtorSMTNode *node,
                  const char *name,
                  BtorExp *(*f) (Btor *, BtorExp *, BtorExp *) )
{
  BtorSMTNode *c0, *c1;
  BtorExp *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) parse_error (parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if ((a0 = node2nonarrayexp (parser, c0)))
    if ((a1 = node2nonarrayexp (parser, c1)))
    {
      if (btor_get_exp_len (parser->btor, a0)
          != btor_get_exp_len (parser->btor, a1))
        (void) parse_error (parser, "expression width mismatch");
      else
        node->exp = f (parser->btor, a0, a1);
    }
}

static void
translate_eq (BtorSMTParser *parser, BtorSMTNode *node)
{
  int isarray0, isarray1, len0, len1;
  BtorSMTNode *c0, *c1;
  BtorExp *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) parse_error (parser, "expected exactly two arguments to '='");
    return;
  }

  c0 = car (cdr (node));
  a0 = node2exp (parser, c0);
  if (!a0) return;

  c1 = car (cdr (cdr (node)));
  a1 = node2exp (parser, c1);
  if (!a1) return;

  len0 = btor_get_exp_len (parser->btor, a0);
  len1 = btor_get_exp_len (parser->btor, a1);

  if (len0 != len1)
  {
    (void) parse_error (parser, "expression width mismatch in '='");
    return;
  }

  isarray0 = btor_is_array_exp (parser->btor, a0);
  isarray1 = btor_is_array_exp (parser->btor, a1);

  if (isarray0 != isarray1)
  {
    (void) parse_error (parser, "'=' between array and non array expression");
    return;
  }

  if (isarray0 && isarray1)
  {
    len0 = btor_get_index_exp_len (parser->btor, a0);
    len1 = btor_get_index_exp_len (parser->btor, a1);

    if (len0 != len1)
    {
      (void) parse_error (parser, "index width mismatch in '='");
      return;
    }
  }

  assert (!parser->error);
  node->exp = btor_eq_exp (parser->btor, a0, a1);
}

static void
translate_associative_binary (BtorSMTParser *parser,
                              BtorSMTNode *node,
                              const char *name,
                              BtorExp *(*f) (Btor *, BtorExp *, BtorExp *) )
{
  BtorExp *res, *tmp, *exp;
  BtorSMTNode *child, *p;
  int len;

  assert (!node->exp);

  if (length (node) < 3)
  {
    (void) parse_error (
        parser, "expected at least two arguments to '%s'", name);
    return;
  }

  child = car (cdr (node));

  if (!(exp = node2nonarrayexp (parser, child)))
  {
  CHECK_FOR_PARSE_ERROR_AND_RETURN:
    assert (parser->error);
    return;
  }

  len = btor_get_exp_len (parser->btor, exp);
  res = btor_copy_exp (parser->btor, exp);

  for (p = cdr (cdr (node)); p; p = cdr (p))
  {
    child = car (p);
    if (!(exp = node2nonarrayexp (parser, child)))
    {
    RELEASE_RES_CHECK_FOR_PARSE_ERROR_AND_RETURN:
      assert (parser->error);
      goto CHECK_FOR_PARSE_ERROR_AND_RETURN;
    }

    if (btor_get_exp_len (parser->btor, exp) != len)
    {
      parse_error (parser, "mismatched width of arguments of '%s'", name);
      goto RELEASE_RES_CHECK_FOR_PARSE_ERROR_AND_RETURN;
    }

    tmp = f (parser->btor, res, exp); /* left associative ? */
    btor_release_exp (parser->btor, res);
    res = tmp;
  }

  node->exp = res;
}

static void
translate_cond (BtorSMTParser *parser, BtorSMTNode *node, const char *name)
{
  int isarray1, isarray2, len1, len2;
  BtorSMTNode *c0, *c1, *c2;
  BtorExp *a0, *a1, *a2;

  assert (!node->exp);

  if (!is_list_of_length (node, 4))
  {
    (void) parse_error (
        parser, "expected exactly three arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));
  c2 = car (cdr (cdr (cdr (node))));

  a0 = node2nonarrayexp (parser, c0);
  if (!a0) return;

  if (btor_get_exp_len (parser->btor, a0) != 1)
  {
    (void) parse_error (parser, "non boolean conditional");
    return;
  }

  a1 = node2exp (parser, c1);
  if (!a1) return;

  a2 = node2exp (parser, c2);
  if (!a2) return;

  len1 = btor_get_exp_len (parser->btor, a1);
  len2 = btor_get_exp_len (parser->btor, a2);

  if (len1 != len2)
  {
    (void) parse_error (parser, "expression width mismatch in conditional");
    return;
  }

  isarray1 = btor_is_array_exp (parser->btor, a1);
  isarray2 = btor_is_array_exp (parser->btor, a2);

  if (isarray1 != isarray2)
  {
    (void) parse_error (parser,
                        "conditional between array and non array expression");
    return;
  }

  if (isarray1 && isarray2)
  {
    len1 = btor_get_index_exp_len (parser->btor, a1);
    len2 = btor_get_index_exp_len (parser->btor, a2);

    if (len1 != len2)
    {
      (void) parse_error (parser, "index width mismatch in conditional");
      return;
    }
  }

  node->exp = btor_cond_exp (parser->btor, a0, a1, a2);
}

static void
translate_extract (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTSymbol *symbol;
  int upper, lower, len;
  const char *p;
  BtorExp *exp;

  assert (!node->exp);

  symbol = strip (car (node));
  assert (symbol->token == BTOR_SMTOK_EXTRACT);
  p = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) parse_error (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  len = btor_get_exp_len (parser->btor, exp);

  p = next_numeral (p);
  assert (p);
  upper = atoi (p); /* TODO Overflow? */
  p     = next_numeral (p);
  lower = atoi (p); /* TODO Overflow? */
  assert (!next_numeral (p));

  if (len <= upper || upper < lower)
  {
    (void) parse_error (
        parser, "invalid '%s' on expression of width %d", p, len);
    return;
  }

  node->exp = btor_slice_exp (parser->btor, exp, upper, lower);
}

static void
translate_repeat (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorExp *tmp, *exp, *res;
  BtorSMTSymbol *symbol;
  const char *p;
  int i, count;

  assert (!node->exp);

  symbol = strip (car (node));
  assert (symbol->token == BTOR_SMTOK_REPEAT);

  p = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) parse_error (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  p = next_numeral (p);
  assert (p);
  assert (!next_numeral (p));
  count = atoi (p); /* TODO Overflow? */

  if (!count)
  {
    (void) parse_error (parser, "can not handle 'repeat[0]'");
    return;
  }

  res = btor_copy_exp (parser->btor, exp);

  for (i = 1; i < count; i++)
  {
    tmp = btor_concat_exp (parser->btor, exp, res);
    btor_release_exp (parser->btor, res);
    res = tmp;
  }

  node->exp = res;
}

static void
translate_extend (BtorSMTParser *parser,
                  BtorSMTNode *node,
                  BtorExp *(*f) (Btor *, BtorExp *, int) )
{
  BtorSMTSymbol *symbol;
  const char *p;
  BtorExp *exp;
  int pad;

  assert (!node->exp);

  symbol = strip (car (node));
  p      = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) parse_error (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  p = next_numeral (p);
  assert (p);
  assert (!next_numeral (p));
  pad = atoi (p); /* TODO Overflow? */

  node->exp = f (parser->btor, exp, pad);
}

static void
translate_rotate (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorExp *exp, *l, *r;
  BtorSMTSymbol *symbol;
  int shift, token, len;
  const char *p;

  assert (!node->exp);

  symbol = strip (car (node));
  token  = symbol->token;
  assert (token == BTOR_SMTOK_ROTATE_LEFT || token == BTOR_SMTOK_ROTATE_RIGHT);

  p = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) parse_error (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  p = next_numeral (p);
  assert (p);
  assert (!next_numeral (p));
  shift = atoi (p); /* TODO Overflow? */
  assert (shift >= 0);

  len = btor_get_exp_len (parser->btor, exp);
  assert (len > 0);
  shift %= len;

  if (shift)
  {
    if (token == BTOR_SMTOK_ROTATE_LEFT) shift = len - shift;

    assert (1 <= shift && shift < len);

    l = btor_slice_exp (parser->btor, exp, shift - 1, 0);
    r = btor_slice_exp (parser->btor, exp, len - 1, shift);

    node->exp = btor_concat_exp (parser->btor, l, r);
    assert (btor_get_exp_len (parser->btor, node->exp) == len);

    btor_release_exp (parser->btor, l);
    btor_release_exp (parser->btor, r);
  }
  else
    node->exp = btor_copy_exp (parser->btor, exp);
}

static void
translate_concat (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c0, *c1;
  BtorExp *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) parse_error (parser, "expected exactly two arguments to 'concat'");
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if ((a0 = node2nonarrayexp (parser, c0)))
    if ((a1 = node2nonarrayexp (parser, c1)))
      node->exp = btor_concat_exp (parser->btor, a0, a1);
}

static void
translate_shift (BtorSMTParser *parser,
                 BtorSMTNode *node,
                 const char *name,
                 BtorExp *(*f) (Btor *, BtorExp *, BtorExp *) )
{
  BtorExp *a0, *a1, *c, *e, *t, *e0, *u, *l, *tmp;
  int len, l0, l1, p0, p1;
  BtorSMTNode *c0, *c1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) parse_error (parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if (!(a0 = node2nonarrayexp (parser, c0)))
  {
    assert (parser->error);
    return;
  }

  if (!(a1 = node2nonarrayexp (parser, c1)))
  {
    assert (parser->error);
    return;
  }

  len = btor_get_exp_len (parser->btor, a0);

  if (len != btor_get_exp_len (parser->btor, a1))
  {
    (void) parse_error (parser, "expression width mismatch");
    return;
  }

  l1 = 0;
  for (l0 = 1; l0 < len; l0 *= 2) l1++;

  assert (l0 == (1 << l1));

  if (len == 1)
  {
    assert (l0 == 1);
    assert (l1 == 0);

    if (f == btor_sra_exp)
      node->exp = btor_copy_exp (parser->btor, a0);
    else
    {
      tmp       = btor_not_exp (parser->btor, a1);
      node->exp = btor_and_exp (parser->btor, a0, tmp);
      btor_release_exp (parser->btor, tmp);
    }
  }
  else
  {
    assert (len >= 1);

    p0 = l0 - len;
    p1 = len - l1;

    assert (p0 >= 0);
    assert (p1 > 0);

    u = btor_slice_exp (parser->btor, a1, len - 1, len - p1);
    l = btor_slice_exp (parser->btor, a1, l1 - 1, 0);

    assert (btor_get_exp_len (parser->btor, u) == p1);
    assert (btor_get_exp_len (parser->btor, l) == l1);

    if (p1 > 1)
      c = btor_redor_exp (parser->btor, u);
    else
      c = btor_copy_exp (parser->btor, u);

    btor_release_exp (parser->btor, u);

    if (f == btor_sra_exp)
    {
      tmp = btor_slice_exp (parser->btor, a0, len - 1, len - 1);
      t   = btor_sext_exp (parser->btor, tmp, len - 1);
      btor_release_exp (parser->btor, tmp);
    }
    else
      t = btor_zero_exp (parser->btor, len);

    if (!p0)
      e0 = btor_copy_exp (parser->btor, a0);
    else if (f == btor_sra_exp)
      e0 = btor_sext_exp (parser->btor, a0, p0);
    else
      e0 = btor_uext_exp (parser->btor, a0, p0);

    assert (btor_get_exp_len (parser->btor, e0) == l0);

    e = f (parser->btor, e0, l);
    btor_release_exp (parser->btor, e0);
    btor_release_exp (parser->btor, l);

    if (p0 > 0)
    {
      tmp = btor_slice_exp (parser->btor, e, len - 1, 0);
      btor_release_exp (parser->btor, e);
      e = tmp;
    }

    node->exp = btor_cond_exp (parser->btor, c, t, e);
    btor_release_exp (parser->btor, c);
    btor_release_exp (parser->btor, t);
    btor_release_exp (parser->btor, e);
  }
}

static void
translate_select (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c0, *c1;
  BtorExp *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) parse_error (parser, "expected exactly two arguments to 'select'");
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if (!(a0 = node2exp (parser, c0)))
  {
    assert (parser->error);
    return;
  }

  if (!btor_is_array_exp (parser->btor, a0))
  {
    (void) parse_error (parser, "invalid first argument to 'select'");
    return;
  }

  if (!(a1 = node2nonarrayexp (parser, c1)))
  {
    assert (parser->error);
    return;
  }

  if (btor_get_index_exp_len (parser->btor, a0)
      != btor_get_exp_len (parser->btor, a1))
  {
    (void) parse_error (parser, "mismatched bit width of 'select' index");
    return;
  }

  node->exp = btor_read_exp (parser->btor, a0, a1);
}

static void
translate_store (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c0, *c1, *c2;
  BtorExp *a0, *a1, *a2;

  assert (!node->exp);

  if (!is_list_of_length (node, 4))
  {
    (void) parse_error (parser, "expected exactly three arguments to 'store'");
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));
  c2 = car (cdr (cdr (cdr (node))));

  if (!(a0 = node2exp (parser, c0)))
  {
    assert (parser->error);
    return;
  }

  if (!btor_is_array_exp (parser->btor, a0))
  {
    (void) parse_error (parser, "invalid first argument to 'store'");
    return;
  }

  if (!(a1 = node2nonarrayexp (parser, c1)))
  {
    assert (parser->error);
    return;
  }

  if (btor_get_index_exp_len (parser->btor, a0)
      != btor_get_exp_len (parser->btor, a1))
  {
    (void) parse_error (parser, "mismatched bit width of 'store' index");
    return;
  }

  if (!(a2 = node2nonarrayexp (parser, c2)))
  {
    assert (parser->error);
    return;
  }

  if (btor_get_exp_len (parser->btor, a2)
      != btor_get_exp_len (parser->btor, a0))
  {
    (void) parse_error (parser, "mismatched bit width of 'store' value");
    return;
  }

  node->exp = btor_write_exp (parser->btor, a0, a1, a2);
}

static char *
translate_formula (BtorSMTParser *parser, BtorSMTNode *root)
{
  BtorSMTNode *node, *child, *p, **s, **t, *tmp;
  BtorSMTNode *assignment, *body;
  BtorSMTSymbol *symbol;
  BtorSMTToken token;
  int start, end;
  BtorExp *exp;

  assert (BTOR_EMPTY_STACK (parser->work));
  assert (BTOR_EMPTY_STACK (parser->stack));

  assert (root);
  BTOR_PUSH_STACK (parser->mem, parser->stack, root);

  while (!BTOR_EMPTY_STACK (parser->stack))
  {
    node = BTOR_POP_STACK (parser->stack);

    if (node)
    {
      if (isleaf (node))
      {
        /* DO NOTHING HERE */
      }
      else if (car (node) == parser->bind)
      {
        BTOR_PUSH_STACK (parser->mem, parser->work, node);
      }
      else if (is_let_or_flet (car (node)))
      {
        /* node       == ([f]let assignment body)
         * assignment == (var term)
         */
        if (!cdr (node) || !(assignment = car (cdr (node)))
            || isleaf (assignment) || !(token = node2token (car (assignment)))
            || (token != BTOR_SMTOK_FVAR && token != BTOR_SMTOK_VAR)
            || !cdr (assignment) || cdr (cdr (assignment)) || !cdr (cdr (node))
            || cdr (cdr (cdr (node))))
          return parse_error (parser, "illformed 'let' or 'flet'");

        body = car (cdr (cdr (node)));

        BTOR_PUSH_STACK (parser->mem, parser->stack, node);
        BTOR_PUSH_STACK (parser->mem, parser->stack, 0);

        BTOR_PUSH_STACK (parser->mem, parser->stack, body);

        BTOR_PUSH_STACK (parser->mem,
                         parser->stack,
                         cons (parser, parser->bind, assignment));

        BTOR_PUSH_STACK (parser->mem, parser->stack, car (cdr (assignment)));
      }
      else
      {
        BTOR_PUSH_STACK (parser->mem, parser->stack, node);
        BTOR_PUSH_STACK (parser->mem, parser->stack, 0);

        start = BTOR_COUNT_STACK (parser->stack);

        for (p = node; p; p = cdr (p))
        {
          child = car (p);
          assert (child);
          BTOR_PUSH_STACK (parser->mem, parser->stack, child);
        }

        end = BTOR_COUNT_STACK (parser->stack);

        if (start < end)
        {
          s = parser->stack.start + start;
          t = parser->stack.start + end - 1;

          while (s < t)
          {
            tmp = *s;
            *s  = *t;
            *t  = tmp;

            s++;
            t--;
          }
        }
      }
    }
    else
    {
      assert (!BTOR_EMPTY_STACK (parser->stack));

      node = BTOR_POP_STACK (parser->stack);

      assert (node);
      assert (!isleaf (node));

      BTOR_PUSH_STACK (parser->mem, parser->work, node);
    }
  }

  node = 0;
  for (s = parser->work.start; s < parser->work.top; s++)
  {
    node = *s;

    assert (node);
    assert (!isleaf (node));

    child = car (node);

    if (!child || !isleaf (child)) return parse_error (parser, "list as head");

    symbol = strip (child);

    switch (symbol->token)
    {
      case BTOR_SMTOK_NOT:
        translate_unary (parser, node, "not", btor_not_exp);
        break;
      case BTOR_SMTOK_AND:
        translate_associative_binary (parser, node, "and", btor_and_exp);
        break;
      case BTOR_SMTOK_OR:
        translate_associative_binary (parser, node, "or", btor_or_exp);
        break;
      case BTOR_SMTOK_IMPLIES:
        translate_binary (parser, node, "implies", btor_implies_exp);
        break;
      case BTOR_SMTOK_XOR:
        translate_associative_binary (parser, node, "xor", btor_xor_exp);
        break;
      case BTOR_SMTOK_IFF:
        translate_associative_binary (parser, node, "iff", btor_xnor_exp);
        break;

      case BTOR_SMTOK_EQ: translate_eq (parser, node); break;

      case BTOR_SMTOK_DISTINCT:
        translate_binary (parser, node, "distinct", btor_ne_exp);
        break;
      case BTOR_SMTOK_ITE: translate_cond (parser, node, "ite"); break;
      case BTOR_SMTOK_IF_THEN_ELSE:
        translate_cond (parser, node, "if_then_else");
        break;
      case BTOR_SMTOK_BIND:
        assert (cdr (node));
        assert (cdr (cdr (node)));
        assert (!cdr (cdr (cdr (node))));
        assert (isleaf (car (cdr (node))));
        symbol = strip (car (cdr (node)));
        if (symbol->exp)
          return parse_error (parser, "unsupported nested '[f]let'");
        body = car (cdr (cdr (node)));
        if ((exp = node2exp (parser, body)))
        {
          if (symbol->token == BTOR_SMTOK_FVAR)
          {
            if (btor_get_exp_len (parser->btor, exp) != 1)
              return parse_error (parser, "flet assignment width not one");
          }
          else
            assert (symbol->token == BTOR_SMTOK_VAR);

          symbol->exp = btor_copy_exp (parser->btor, exp);
        }
        break;
      case BTOR_SMTOK_LET:
      case BTOR_SMTOK_FLET:
        symbol = strip (car (car (cdr (node))));
        assert (symbol->token == BTOR_SMTOK_FVAR
                || symbol->token == BTOR_SMTOK_VAR);
        assert (symbol->exp);
        btor_release_exp (parser->btor, symbol->exp);
        symbol->exp = 0;
        body        = car (cdr (cdr (node)));
        if ((exp = node2exp (parser, body)))
          node->exp = btor_copy_exp (parser->btor, exp);
        break;
      case BTOR_SMTOK_EXTRACT: translate_extract (parser, node); break;
      case BTOR_SMTOK_REPEAT: translate_repeat (parser, node); break;
      case BTOR_SMTOK_ZERO_EXTEND:
        translate_extend (parser, node, btor_uext_exp);
        break;
      case BTOR_SMTOK_SIGN_EXTEND:
        translate_extend (parser, node, btor_sext_exp);
        break;
      case BTOR_SMTOK_ROTATE_RIGHT:
      case BTOR_SMTOK_ROTATE_LEFT: translate_rotate (parser, node); break;
      case BTOR_SMTOK_CONCAT: translate_concat (parser, node); break;
      case BTOR_SMTOK_BVNOT:
        translate_unary (parser, node, "bvnot", btor_not_exp);
        break;
      case BTOR_SMTOK_BVNEG:
        translate_unary (parser, node, "bvneg", btor_neg_exp);
        break;
      case BTOR_SMTOK_BVADD:
        translate_binary (parser, node, "bvadd", btor_add_exp);
        break;
      case BTOR_SMTOK_BVSUB:
        translate_binary (parser, node, "bvsub", btor_sub_exp);
        break;
      case BTOR_SMTOK_BVSDIV:
        translate_binary (parser, node, "bvsdiv", btor_sdiv_exp);
        break;
      case BTOR_SMTOK_BVUDIV:
        translate_binary (parser, node, "bvudiv", btor_udiv_exp);
        break;
      case BTOR_SMTOK_BVUREM:
        translate_binary (parser, node, "bvurem", btor_urem_exp);
        break;
      case BTOR_SMTOK_BVSREM:
        translate_binary (parser, node, "bvsrem", btor_srem_exp);
        break;
      case BTOR_SMTOK_BVSMOD:
        translate_binary (parser, node, "bvsmod", btor_smod_exp);
        break;
      case BTOR_SMTOK_BVMUL:
        translate_binary (parser, node, "bvmul", btor_mul_exp);
        break;
      case BTOR_SMTOK_BVULE:
        translate_binary (parser, node, "bvule", btor_ulte_exp);
        break;
      case BTOR_SMTOK_BVSLE:
        translate_binary (parser, node, "bvsle", btor_slte_exp);
        break;
      case BTOR_SMTOK_BVSGT:
        translate_binary (parser, node, "bvsgt", btor_sgt_exp);
        break;
      case BTOR_SMTOK_BVSGE:
        translate_binary (parser, node, "bvsge", btor_sgte_exp);
        break;
      case BTOR_SMTOK_BVCOMP:
        translate_binary (parser, node, "bvcomp", btor_eq_exp);
        break;
      case BTOR_SMTOK_BVULT:
        translate_binary (parser, node, "bvult", btor_ult_exp);
        break;
      case BTOR_SMTOK_BVUGT:
        translate_binary (parser, node, "bvugt", btor_ugt_exp);
        break;
      case BTOR_SMTOK_BVUGE:
        translate_binary (parser, node, "bvuge", btor_ugte_exp);
        break;
      case BTOR_SMTOK_BVSLT:
        translate_binary (parser, node, "bvslt", btor_slt_exp);
        break;
      case BTOR_SMTOK_BVAND:
        translate_binary (parser, node, "bvand", btor_and_exp);
        break;
      case BTOR_SMTOK_BVOR:
        translate_binary (parser, node, "bvor", btor_or_exp);
        break;
      case BTOR_SMTOK_BVXOR:
        translate_binary (parser, node, "bvxor", btor_xor_exp);
        break;
      case BTOR_SMTOK_BVXNOR:
        translate_binary (parser, node, "bvxnor", btor_xnor_exp);
        break;
      case BTOR_SMTOK_BVNOR:
        translate_binary (parser, node, "bvnor", btor_nor_exp);
        break;
      case BTOR_SMTOK_BVNAND:
        translate_binary (parser, node, "bvnand", btor_nand_exp);
        break;
      case BTOR_SMTOK_BVLSHR:
        translate_shift (parser, node, "bvlshr", btor_srl_exp);
        break;
      case BTOR_SMTOK_BVASHR:
        translate_shift (parser, node, "bvashr", btor_sra_exp);
        break;
      case BTOR_SMTOK_BVSHL:
        translate_shift (parser, node, "bvshl", btor_sll_exp);
        break;
      case BTOR_SMTOK_SELECT: translate_select (parser, node); break;
      case BTOR_SMTOK_STORE: translate_store (parser, node); break;
      default:
        return parse_error (parser, "unsupported list head '%s'", symbol->name);
    }

    if (parser->error) return parser->error;
  }

  BTOR_RESET_STACK (parser->work);

  if (!(exp = node2exp (parser, root)))
  {
    assert (parser->error);
    return parser->error;
  }

  if (btor_get_exp_len (parser->btor, exp) != 1)
    return parse_error (parser, "non boolean formula");

  BTOR_PUSH_STACK (
      parser->mem, parser->outputs, btor_copy_exp (parser->btor, exp));

  assert (!parser->error);

  return 0;
}

static char *
translate_benchmark (BtorSMTParser *parser,
                     BtorSMTNode *top,
                     BtorParseResult *res)
{
  BtorSMTSymbol *symbol, *logic, *benchmark;
  const char *attrstr;
  BtorSMTNode *p, *node;
  BtorSMTToken status;

  btor_smt_message (parser, 2, "extracting expressions");

  p = top;

  if (!p || !(node = car (p)) || !isleaf (node)
      || strip (node)->token != BTOR_SMTOK_BENCHMARK)
    return parse_error (parser, "expected 'benchmark' keyword");

  p = cdr (p);

  if (!p || !(benchmark = car (p)) || !isleaf (benchmark)
      || strip (benchmark)->token != BTOR_SMTOK_IDENTIFIER)
    return parse_error (parser, "expected benchmark name");

  benchmark = strip (benchmark);

  btor_smt_message (parser, 2, "benchmark %s", benchmark->name);

  symbol = 0;

  for (p = top; p; p = cdr (p))
  {
    node = car (p);
    if (!isleaf (node)) continue;

    symbol = strip (node);

    if (symbol->token == BTOR_SMTOK_EXTRASORTS
        || symbol->token == BTOR_SMTOK_EXTRAFUNS
        || symbol->token == BTOR_SMTOK_EXTRAPREDS
        || symbol->token == BTOR_SMTOK_ASSUMPTION
        || symbol->token == BTOR_SMTOK_FORMULA)
      return parse_error (parser, "'%s' before ':logic'", symbol->name);

    if (symbol->token == BTOR_SMTOK_LOGICATTR) break;
  }

  if (!p) return parse_error (parser, "no ':logic' attribute found");

  p = cdr (p);
  if (!p) return parse_error (parser, "argument to ':logic' missing");

  node = car (p);
  if (!isleaf (node))
    return parse_error (parser, "invalid argument to ':logic'");

  logic = strip (node);
  if (!strcmp (logic->name, "QF_BV"))
    res->logic = BTOR_LOGIC_QF_BV;
  else if (!strcmp (logic->name, "QF_AUFBV"))
    res->logic = BTOR_LOGIC_QF_AUFBV;
  else
    return parse_error (parser, "unsupported logic '%s'", logic->name);

  for (p = top; p; p = cdr (p))
  {
    node = car (p);
    if (!isleaf (node)) continue;

    symbol = strip (node);
    if (symbol->token == BTOR_SMTOK_STATUS) break;
  }

  if (p)
  {
    p = cdr (p);
    if (!p) return parse_error (parser, "argument to ':status' missing");

    node = car (p);
    if (!isleaf (node))
    {
    INVALID_STATUS_ARGUMENT:
      return parse_error (parser, "invalid ':status' argument");
    }

    symbol = strip (node);
    status = symbol->token;

    if (status == BTOR_SMTOK_SAT)
      res->status = BTOR_PARSE_SAT_STATUS_SAT;
    else if (status == BTOR_SMTOK_UNSAT)
      res->status = BTOR_PARSE_SAT_STATUS_UNSAT;
    else if (status == BTOR_SMTOK_UNKNOWN)
      res->status = BTOR_PARSE_SAT_STATUS_UNKNOWN;
    else
      goto INVALID_STATUS_ARGUMENT;
  }

  for (p = top; p; p = cdr (p))
  {
    node = car (p);
  }

  for (p = top; p; p = cdr (p))
  {
    node = car (p);
    if (!isleaf (node)) continue;

    symbol  = strip (node);
    attrstr = ":formula";

    switch (symbol->token)
    {
      case BTOR_SMTOK_EXTRAFUNS:
        p = cdr (p);
        if (!p) return parse_error (parser, "argument to ':extrafuns' missing");

        if (!extrafuns (parser, car (p)))
        {
          assert (parser->error);
          return parser->error;
        }

        break;

      case BTOR_SMTOK_EXTRAPREDS:

        p = cdr (p);
        if (!p)
          return parse_error (parser, "argument to ':extrapreds' missing");

        if (!extrapreds (parser, car (p)))
        {
          assert (parser->error);
          return parser->error;
        }

        break;

      case BTOR_SMTOK_ASSUMPTION:
        attrstr = ":assumption";
        /* FALL THROUGH */
      case BTOR_SMTOK_FORMULA:

        p = cdr (p);
        if (!p)
          return parse_error (parser, "argument to '%s' missing", attrstr);

        if (translate_formula (parser, car (p)))
        {
          assert (parser->error);
          return parser->error;
        }

        break;

      case BTOR_SMTOK_EXTRASORTS:
        return parse_error (parser, "':extrasorts' unsupported");

      default: break;
    }
  }

  assert (!parser->error);

  return 0;
}

static const char *
parse (BtorSMTParser *parser,
       FILE *file,
       const char *name,
       BtorParseResult *res)
{
  BtorSMTNode *node, *top, **p, **first;
  BtorSMTToken token;
  int head;

  assert (!parser->parsed);
  parser->parsed = 1;

  btor_smt_message (parser, 1, "parsing SMT file %s", name);

  parser->name   = name;
  parser->file   = file;
  parser->lineno = 1;
  parser->saved  = 0;

  BTOR_CLR (res);

  assert (BTOR_EMPTY_STACK (parser->stack));
  assert (BTOR_EMPTY_STACK (parser->heads));

NEXT_TOKEN:

  token = nextok (parser);

  if (token == BTOR_SMTOK_LP)
  {
    head = BTOR_COUNT_STACK (parser->stack);
    BTOR_PUSH_STACK (parser->mem, parser->heads, head);
    goto NEXT_TOKEN;
  }

  if (token == BTOR_SMTOK_RP)
  {
    if (BTOR_EMPTY_STACK (parser->heads))
      return parse_error (parser, "too many closing ')'");

    node = 0;
    head = BTOR_POP_STACK (parser->heads);
    assert (head <= BTOR_COUNT_STACK (parser->stack));
    first = parser->stack.start + head;
    p     = parser->stack.top;
    while (first < p) node = cons (parser, *--p, node);

    parser->stack.top = first;
    BTOR_PUSH_STACK (parser->mem, parser->stack, node);

    if (!BTOR_EMPTY_STACK (parser->heads)) goto NEXT_TOKEN;

    token = nextok (parser);
    if (token != BTOR_SMTOK_EOF) return parse_error (parser, "expected EOF");

    assert (BTOR_COUNT_STACK (parser->stack) == 1);
    top = parser->stack.start[0];
    BTOR_RESET_STACK (parser->stack);

    btor_smt_message (parser, 2, "read %llu bytes", parser->bytes);
    btor_smt_message (parser, 2, "found %u symbols", parser->symbols);
    btor_smt_message (parser, 2, "generated %u nodes", parser->nodes);

#if 0
      /* TODO keep this for now until the parser really works.
       */
      if (parser->verbosity >= 3)
	btorsmtpp (top);
#endif

    if (translate_benchmark (parser, top, res))
    {
      assert (parser->error);
      return parser->error;
    }

    btor_smt_message (parser, 2, "found %u constants", parser->constants);

    res->inputs  = parser->inputs.start;
    res->ninputs = BTOR_COUNT_STACK (parser->inputs);

    res->noutputs = BTOR_COUNT_STACK (parser->outputs);
    res->outputs  = parser->outputs.start;

    return 0; /* DONE */
  }

  if (token == BTOR_SMTOK_ERR)
  {
    assert (parser->error);
    return parser->error;
  }

  if (token == BTOR_SMTOK_EOF) return parse_error (parser, "unexpected EOF");

  if (BTOR_EMPTY_STACK (parser->heads))
    return parse_error (parser, "expected '('");

  assert (parser->symbol);
  BTOR_PUSH_STACK (parser->mem, parser->stack, leaf (parser->symbol));

  goto NEXT_TOKEN;
}

static const char *
btor_parse_smt_parser (BtorSMTParser *parser,
                       FILE *file,
                       const char *name,
                       BtorParseResult *res)
{
  (void) parse (parser, file, name, res);
  btor_release_smt_internals (parser);
  return parser->error;
}

static BtorParserAPI api = {
    (BtorInitParser) btor_new_smt_parser,
    (BtorResetParser) btor_delete_smt_parser,
    (BtorParse) btor_parse_smt_parser,
};

const BtorParserAPI *btor_smt_parser_api = &api;
