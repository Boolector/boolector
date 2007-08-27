#include "btorsmt.h"
#include "btormem.h"
#include "btorstack.h"

#include <assert.h>
#include <ctype.h> /* actually only for 'isprint' */
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

  BTOR_SMTOK_KEYWORD      = 256,
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
  BTOR_SMTOK_THEORYATTR          = 524

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
  BtorSMTToken token;
  char *name;
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

  BtorSMTNodePtrStack stack;
  BtorIntStack heads;

  BtorSMTNodes *chunks;
  BtorSMTNode *free;
  BtorSMTNode *last;
  unsigned nodes;
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
btor_delete_smt_parser (BtorSMTParser *parser)
{
  BtorSMTSymbol *p;
  BtorSMTNodes *q;
  void *next;
  unsigned i;

  for (i = 0; i < parser->szsymtab; i++)
  {
    for (p = parser->symtab[i]; p; p = next)
    {
      next = p->next;
      btor_freestr (parser->mem, p->name);
      BTOR_DELETE (parser->mem, p);
    }
  }
  BTOR_DELETEN (parser->mem, parser->symtab, parser->szsymtab);

  BTOR_RELEASE_STACK (parser->mem, parser->stack);
  BTOR_RELEASE_STACK (parser->mem, parser->heads);

  for (q = parser->chunks; q; q = next)
  {
    next = q->next;
    BTOR_DELETE (parser->mem, q);
  }

  btor_freestr (parser->mem, parser->error);
  BTOR_RELEASE_STACK (parser->mem, parser->buffer);
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

    res->token = BTOR_SMTOK_IDENTIFIER;
    res->name  = btor_strdup (parser->mem, name);
    res->next  = 0;
    res->exp   = 0;

    parser->symbols++;
    *p = res;
  }

  return res;
}

static BtorSMTParser *
btor_new_smt_parser (BtorExpMgr *mgr, int verbosity)
{
  BtorMemMgr *mem = btor_get_mem_mgr_exp_mgr (mgr);
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

  INSERT_SYMBOL_AND_CHECK_FOR_UNSUPPORTED_KEYWORD:

    parser->symbol = insert_symbol (parser, parser->buffer.start);
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

    goto INSERT_SYMBOL_AND_CHECK_FOR_UNSUPPORTED_KEYWORD;
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
      for (i = 0; i < indent; i++) fputc (' ', file);
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

static int
extrafun (BtorSMTParser *parser, BtorSMTNode *fdecl)
{
  return 1;
}

static int
extrafuns (BtorSMTParser *parser, BtorSMTNode *list)
{
  BtorSMTNode *p;

  if (isleaf (list))
    return !parse_error (parser, "expected list as argument to ':extrafuns'");

  for (p = list; p; p = cdr (p))
    if (!extrafun (parser, car (p))) return 0;

  return !parser->error;
}

static int
extrapred (BtorSMTParser *parser, BtorSMTNode *pdecl)
{
  return 1;
}

static int
extrapreds (BtorSMTParser *parser, BtorSMTNode *list)
{
  BtorSMTNode *p;

  if (isleaf (list))
    return !parse_error (parser, "expected list as argument to ':extrapreds'");

  for (p = list; p; p = cdr (p))
    if (!extrapred (parser, car (p))) return 0;

  return !parser->error;
}

static char *
node2exp (BtorSMTParser *parser, BtorSMTNode *top)
{
  const char *statusstr, *attrstr;
  BtorSMTSymbol *symbol, *logic;
  BtorSMTNode *p, *node;
  BtorSMTToken status;
  BtorExp *root;

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

  root = 0;

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

        break;

      case BTOR_SMTOK_EXTRASORTS:
        return parse_error (parser, "':extrasorts' unsupported");

      default: break;
    }
  }

  return parse_error (parser, "node2exp not fully implemented yet");
}

static const char *
btor_parse_smt_parser (BtorSMTParser *parser,
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

    if (BTOR_EMPTY_STACK (parser->heads))
    {
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

      return node2exp (parser, top);
    }

    goto NEXT_TOKEN;
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

static BtorParserAPI api = {
    (BtorInitParser) btor_new_smt_parser,
    (BtorResetParser) btor_delete_smt_parser,
    (BtorParse) btor_parse_smt_parser,
};

const BtorParserAPI *btor_smt_parser_api = &api;
