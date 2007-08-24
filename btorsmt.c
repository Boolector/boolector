#include "btorsmt.h"
#include "btormem.h"
#include "btorstack.h"

#include <assert.h>
#include <stdarg.h>

typedef struct BtorSMTParser BtorSMTParser;
typedef struct BtorSMTNode BtorSMTNode;

typedef enum BtorSMTTag BtorSMTTag;

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

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->mem       = mem;
  res->mgr       = mgr;
  res->verbosity = verbosity;

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

static int
nexttok (BtorSMTParser* parser)
{
  return 0;
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
