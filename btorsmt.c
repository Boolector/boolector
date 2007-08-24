#include "btorsmt.h"
#include "btormem.h"

#include <assert.h>
#include <stdarg.h>

typedef struct BtorSMTParser BtorSMTParser;

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
};

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
