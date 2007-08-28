#include "btorsmt.h"
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
  BTOR_SMTOK_CONCAT       = 281,

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
  BtorExpMgr *mgr;
  int verbosity;
  int parsed;

  const char *name;
  FILE *file;
  int lineno;
  int saved;

  unsigned long long bytes;

  char *error;
  BtorCharStack buffer;

  unsigned char types[256];

  BtorSMTSymbol *symbol;
  BtorSMTSymbol **symtab;
  unsigned szsymtab;
  unsigned symbols;

  BtorSMTNode *bind;

  BtorSMTNodePtrStack stack;
  BtorSMTNodePtrStack work;
  BtorIntStack heads;

  BtorSMTNodes *chunks;
  BtorSMTNode *free;
  BtorSMTNode *last;
  unsigned nodes;

  BtorExpPtrStack vars;
  BtorExp *root;
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

  fprintf (stderr, "[btorsmt] ");
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

#define isleaf(l) (1lu & (unsigned long) (l))
#define leaf(l) ((void *) (1lu | (unsigned long) (l)))
#define strip(l) ((BtorSMTSymbol *) ((~1lu) & (unsigned long) (l)))

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

      if ((e = p->exp)) btor_release_exp (parser->mgr, e);

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
      if ((e = p->nodes[i].exp)) btor_release_exp (parser->mgr, e);

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

  for (p = parser->vars.start; p < parser->vars.top; p++)
    btor_release_exp (parser->mgr, *p);

  BTOR_RELEASE_STACK (parser->mem, parser->vars);
}

static void
btor_delete_smt_parser (BtorSMTParser *parser)
{
  btor_release_smt_internals (parser);

  btor_freestr (parser->mem, parser->error);
  btor_release_smt_vars (parser);
  if (parser->root) btor_release_exp (parser->mgr, parser->root);

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
btor_new_smt_parser (BtorExpMgr *mgr, int verbosity)
{
  BtorMemMgr *mem = btor_get_mem_mgr_exp_mgr (mgr);
  BtorSMTSymbol *bind;
  BtorSMTParser *res;
  unsigned char type;
  int ch;

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->verbosity = verbosity;

  btor_smt_message (res, 2, "initializing SMT parser");

  res->mem = mem;
  res->mgr = mgr;

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

  insert_symbol (res, "concat")->token = BTOR_SMTOK_CONCAT;

  return res;
}

static int
nextch (BtorSMTParser *parser)
{
  int res;

  if (parser->saved)
  {
    res           = parser->saved;
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

  parser->saved = ch;

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

    if (ch == '[')
    {
      BTOR_PUSH_STACK (parser->mem, parser->buffer, ch);

      count = 0;
      ch    = nextch (parser);

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
    UNEXPECTED_DIGIT_AFTER_ZERO:
      return !parse_error (parser, "unexpected digit after '0'");

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

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = BTOR_SMTOK_ARITH;

    return BTOR_SMTOK_ARITH;
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
  btorsmtppaux (stderr, node, 0);
  fputc ('\n', stderr);
  fflush (stderr);
}

static void
push_var (BtorSMTParser *parser, BtorExp *v)
{
  BTOR_PUSH_STACK (parser->mem, parser->vars, btor_copy_exp (parser->mgr, v));
}

static int
extrafun (BtorSMTParser *parser, BtorSMTNode *fdecl)
{
  BtorSMTSymbol *symbol, *sortsymbol;
  BtorSMTNode *node, *sort;
  int addrlen, datalen;
  const char *p;
  char ch;

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
  INVALID_SORT:
    return !parse_error (parser,
                         "invalid or unsupported sort "
                         "in function declaration");

  if (symbol->exp)
    return !parse_error (parser, "multiple definitions for '%s'", symbol->name);

  p = sortsymbol->name;
  if ((ch = *p++) == 'B')
  {
    if (*p++ != 'i' || *p++ != 't' || *p++ != 'V' || *p++ != 'e' || *p++ != 'c'
        || *p++ != '[' || !isdigit (ch = *p++))
      goto INVALID_SORT;

    datalen = ch - '0';
    while (isdigit (ch = *p++)) datalen = 10 * datalen + (ch - '0');

    if (!datalen || ch != ']') goto INVALID_SORT;

    assert (!*p);

    symbol->exp = btor_var_exp (parser->mgr, datalen, symbol->name);
    push_var (parser, symbol->exp);
  }
  else if (ch == 'A')
  {
    if (*p++ != 'r' || *p++ != 'r' || *p++ != 'a' || *p++ != 'y' || *p++ != '['
        || !isdigit (ch = *p++))
      goto INVALID_SORT;

    addrlen = ch - '0';
    while (isdigit (ch = *p++)) addrlen = 10 * addrlen + (ch - '0');

    if (!addrlen || ch != ':' || !isdigit (ch = *p++)) goto INVALID_SORT;

    datalen = ch - '0';
    while (isdigit (ch = *p++)) datalen = 10 * datalen + (ch - '0');

    if (!datalen || ch != ']') goto INVALID_SORT;

    assert (!*p);

    symbol->exp = btor_array_exp (parser->mgr, datalen, addrlen);
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

  symbol->exp = btor_var_exp (parser->mgr, 1, symbol->name);
  push_var (parser, symbol->exp);

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
node2exp (BtorSMTNode *node)
{
  return isleaf (node) ? strip (node)->exp : node->exp;
}

static BtorExp *
node2exp_else_parse_error (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorExp *res = node2exp (node);

  if (res) return res;

  assert (isleaf (node));
  (void) parse_error (parser, "'%s' undefined", strip (node)->name);

  return 0;
}

static BtorExp *
node2nonarrayexp_else_parse_error (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorExp *res = node2exp_else_parse_error (parser, node);

  if (res && btor_is_array_exp (parser->mgr, res))
  {
    (void) parse_error (parser, "unexpected array expression");
    return 0;
  }

  return res;
}

static void
translate_unary (BtorSMTParser *parser,
                 BtorSMTNode *node,
                 const char *name,
                 BtorExp *(*f) (BtorExpMgr *, BtorExp *) )
{
  BtorSMTNode *c;
  BtorExp *a;

  if (!cdr (node) || cdr (cdr (node)))
  {
    (void) parse_error (parser, "expected exactly one argument to '%s'", name);
    return;
  }

  c = car (cdr (node));
  if ((a = node2nonarrayexp_else_parse_error (parser, c)))
    node->exp = f (parser->mgr, a);
}

static void
translate_binary (BtorSMTParser *parser,
                  BtorSMTNode *node,
                  const char *name,
                  BtorExp *(*f) (BtorExpMgr *, BtorExp *, BtorExp *) )
{
  BtorSMTNode *c0, *c1;
  BtorExp *a0, *a1;

  if (!cdr (node) || !cdr (cdr (node)) || cdr (cdr (cdr (node))))
  {
    (void) parse_error (parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if ((a0 = node2nonarrayexp_else_parse_error (parser, c0)))
    if ((a1 = node2nonarrayexp_else_parse_error (parser, c1)))
    {
      if (btor_get_exp_len (parser->mgr, a0)
          != btor_get_exp_len (parser->mgr, a1))
        (void) parse_error (parser, "expression width mismatch");
      else
        node->exp = f (parser->mgr, a0, a1);
    }
}

static char *
translate_formula (BtorSMTParser *parser, BtorSMTNode *root)
{
  BtorSMTNode *node, *child, *p, **s, **t, *tmp;
  BtorSMTNode *assignment, *body;
  BtorSMTSymbol *symbol;
  BtorExp *and, *exp;
  BtorSMTToken token;
  int start, end;

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
        symbol = strip (node);

        if (!symbol->exp)
        {
          if (symbol->token == BTOR_SMTOK_TRUE)
          {
            symbol->exp = btor_const_exp (parser->mgr, "1");
          }
          else if (symbol->token == BTOR_SMTOK_FALSE)
          {
            symbol->exp = btor_const_exp (parser->mgr, "0");
          }
        }
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

        BTOR_PUSH_STACK (parser->mem, parser->stack, cdr (assignment));
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

    if (!child || !isleaf (child))
      return parse_error (parser, "unsupported node");

    symbol = strip (child);

    switch (symbol->token)
    {
      case BTOR_SMTOK_NOT:
        translate_unary (parser, node, "not", btor_not_exp);
        break;
      case BTOR_SMTOK_AND:
        translate_binary (parser, node, "and", btor_and_exp);
        break;
      case BTOR_SMTOK_OR:
        translate_binary (parser, node, "or", btor_or_exp);
        break;
      case BTOR_SMTOK_XOR:
        translate_binary (parser, node, "xor", btor_xor_exp);
        break;
      case BTOR_SMTOK_IFF:
        translate_binary (parser, node, "iff", btor_xnor_exp);
        break;
      default:
        return parse_error (
            parser, "unsupported list head (%d)", symbol->token);
    }

    if (parser->error) return parser->error;
  }

  BTOR_RESET_STACK (parser->work);

  exp = node2exp (root);
  if (!exp)
  {
    assert (isleaf (exp));
    return parse_error (parser, "'%s' undefined", strip (root)->name);
  }

  if (btor_is_array_exp (parser->mgr, exp))
    return parse_error (parser, "array expression as formula");

  if (btor_get_exp_len (parser->mgr, exp) != 1)
    return parse_error (parser, "non boolean formula");

  if (parser->root)
  {
    assert (!btor_is_array_exp (parser->mgr, parser->root));
    assert (btor_get_exp_len (parser->mgr, parser->root) == 1);

    and = btor_and_exp (parser->mgr, parser->root, exp);
    btor_release_exp (parser->mgr, parser->root);
    parser->root = and;
  }
  else
    parser->root = btor_copy_exp (parser->mgr, exp);

  assert (!parser->error);

  return 0;
}

static char *
translate_benchmark (BtorSMTParser *parser, BtorSMTNode *top)
{
  const char *statusstr, *attrstr;
  BtorSMTSymbol *symbol, *logic;
  BtorSMTNode *p, *node;
  BtorSMTToken status;

  btor_smt_message (parser, 2, "extracting expressions");

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
  if (strcmp (logic->name, "QF_BV") && strcmp (logic->name, "QF_AUFBV"))
    return parse_error (parser, "unsupported logic '%s'", logic->name);

  btor_smt_message (parser, 2, "logic %s", logic->name);

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
    INVALID_STATUS_ARGUMENT:
      return parse_error (parser, "invalid ':status' argument");

    symbol = strip (node);
    status = symbol->token;

    if (status == BTOR_SMTOK_SAT)
      statusstr = "SAT";
    else if (status == BTOR_SMTOK_UNSAT)
      statusstr = "UNSAT";
    else if (status == BTOR_SMTOK_UNKNOWN)
      statusstr = "UNKNOWN";
    else
      goto INVALID_STATUS_ARGUMENT;

    btor_smt_message (parser, 2, "status %s", statusstr);
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

    /* TODO keep this for now until the parser works.
     */
    if (parser->verbosity >= 3) btorsmtpp (top);

    if (translate_benchmark (parser, top))
    {
      assert (parser->error);
      return parser->error;
    }

    res->vars  = parser->vars.start;
    res->nvars = BTOR_COUNT_STACK (parser->vars);

    res->roots  = &parser->root;
    res->nroots = 1;

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
