#include "btorsmt.h"
#include "btormem.h"
#include "btorstack.h"

#include <assert.h>
#include <stdarg.h>

typedef struct BtorSMTParser BtorSMTParser;
typedef struct BtorSMTNode BtorSMTNode;

enum BtorSMTType
{
  BTOR_SMT_TYPE_IDENTIFIER_START    = 1,
  BTOR_SMT_TYPE_IDENTIFIER_MIDDLE   = 2,
  BTOR_SMT_TYPE_ARITHMETIC_OPERATOR = 4,
  BTOR_SMT_TYPE_NUMERAL_START       = 8, /* non zero digit actually */
  BTOR_SMT_TYPE_DIGIT               = 16,
  BTOR_SMT_TYPE_SPACE               = 32,
  BTOR_SMT_TYPE_IDENTIFIER_PREFIX   = 64,
};

struct BtorSMTNode
{
  int tag;
  void* head;
  void* tail;
};

struct BtorSMTParser
{
  BtorMemMgr* mem;
  BtorExpMgr* mgr;
  int verbosity;

  const char* name;
  FILE* file;
  int lineno;
  int saved;

  char* error;
  BtorCharStack token;

  unsigned char types[256];
};

static void*
car (BtorSMTNode* node)
{
  assert (node);
  return node->head;
}

static void*
cdr (BtorSMTNode* node)
{
  assert (node);
  return node->tail;
}

static BtorSMTNode*
cons_function (BtorMemMgr* mem, void* h, void* t)
{
  BtorSMTNode* res;
  BTOR_NEW (mem, res);
  res->head = h;
  res->tail = t;
  return res;
}

#define cons(h, t) (cons_function (parser->mem, (h), (t)))
#define isleaf(l) (1lu & (unsigned long) (l))
#define leaf(l) ((void*) (1lu | (unsigned long) (l)))
#define strip(l) ((void*) ((~1lu) & (unsigned long) (l)))

static BtorSMTParser*
btor_new_smt_parser (BtorExpMgr* mgr, int verbosity)
{
  BtorMemMgr* mem = btor_get_mem_mgr_exp_mgr (mgr);
  BtorSMTParser* res;
  unsigned char type;
  int ch;

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->mem       = mem;
  res->mgr       = mgr;
  res->verbosity = verbosity;

  type = BTOR_SMT_TYPE_IDENTIFIER_START | BTOR_SMT_TYPE_IDENTIFIER_MIDDLE;

  for (ch = 'a'; ch <= 'z'; ch++) res->types[ch] |= type;
  for (ch = 'A'; ch <= 'Z'; ch++) res->types[ch] |= type;

  res->types['_'] |= BTOR_SMT_TYPE_IDENTIFIER_MIDDLE;
  res->types['.'] |= BTOR_SMT_TYPE_IDENTIFIER_MIDDLE;
  res->types['\''] |= BTOR_SMT_TYPE_IDENTIFIER_MIDDLE;

  type = BTOR_SMT_TYPE_IDENTIFIER_MIDDLE;
  type |= BTOR_SMT_TYPE_DIGIT;

  res->types['0'] |= type;

  type |= BTOR_SMT_TYPE_NUMERAL_START;
  for (ch = '1'; ch <= '9'; ch++) res->types[ch] |= type;

  res->types['='] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;
  res->types['<'] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;
  res->types['>'] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;
  res->types['+'] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;
  res->types['*'] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;
  res->types['/'] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;
  res->types['%'] |= BTOR_SMT_TYPE_ARITHMETIC_OPERATOR;

  res->types[' '] |= BTOR_SMT_TYPE_SPACE;
  res->types['\t'] |= BTOR_SMT_TYPE_SPACE;
  res->types['\n'] |= BTOR_SMT_TYPE_SPACE;

  return res;
}

static void
btor_delete_smt_parser (BtorSMTParser* parser)
{
  btor_freestr (parser->mem, parser->error);
  BTOR_RELEASE_STACK (parser->mem, parser->token);
  BTOR_DELETE (parser->mem, parser);
}

static char*
parse_error (BtorSMTParser* parser, const char* fmt, ...)
{
  va_list ap;

  if (!parser->error)
  {
    va_start (ap, fmt);
    parser->error = btor_parse_error_message (
        parser->mem, parser->name, parser->lineno, fmt, ap);
    va_end (ap);
  }

  return parser->error;
}

static int
nextch (BtorSMTParser* parser)
{
  int res;

  if (parser->saved)
  {
    res           = parser->saved;
    parser->saved = 0;
  }
  else
    res = getc (parser->file);

  if (res == '\n') parser->lineno++;

  return res;
}

static void
savech (BtorSMTParser* parser, int ch)
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
int2type (BtorSMTParser* parser, int ch)
{
  assert (0 <= ch && ch < 256);
  return parser->types[ch];
}

static int
nexttok (BtorSMTParser* parser)
{
  unsigned char type;
  int res, ch;

  assert (BTOR_EMPTY_STACK (parser->token));

SKIP_WHITE_SPACE:

  ch = nextch (parser);
  if (ch == EOF) return EOF;

  type = int2type (parser, ch);
  if (type & BTOR_SMT_TYPE_SPACE) goto SKIP_WHITE_SPACE;

  if (type == ';')
  {
    while ((ch = nextch (parser)) != '\n')
      if (ch == EOF) return EOF;

    goto SKIP_WHITE_SPACE;
  }

  {
  }
}

static const char*
btor_parse_smt_parser (BtorSMTParser* parser,
                       FILE* file,
                       const char* name,
                       BtorParseResult* res)
{
  parser->name   = name;
  parser->file   = file;
  parser->lineno = 1;
  parser->saved  = 0;
  BTOR_CLR (res);
  return parse_error (parser, "SMT parsing not implemented yet");
}

static BtorParserAPI api = {
    (BtorInitParser) btor_new_smt_parser,
    (BtorResetParser) btor_delete_smt_parser,
    (BtorParse) btor_parse_smt_parser,
};

const BtorParserAPI* btor_smt_parser_api = &api;
