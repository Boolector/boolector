#include "btorsmt.h"
#include "btormem.h"

#include <assert.h>
#include <stdarg.h>

typedef struct BtorSMTParser BtorSMTParser;

struct BtorSMTParser
{
  BtorMemMgr *mem;
  BtorExpMgr *mgr;
  int verbosity;

  const char *name;
  FILE *file;
  int lineno;
  int saved;

  char *error;
};

static BtorSMTParser *
btor_new_smt_parser (BtorExpMgr *mgr, int verbosity)
{
  BtorMemMgr *mem = btor_get_mem_mgr_exp_mgr (mgr);
  BtorSMTParser *res;

  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->mem       = mem;
  res->mgr       = mgr;
  res->verbosity = verbosity;

  return res;
}

static void
btor_delete_smt_parser (BtorSMTParser *parser)
{
  btor_freestr (parser->mem, parser->error);
  BTOR_DELETE (parser->mem, parser);
}

static char *
parse_error (BtorSMTParser *parser, const char *fmt, ...)
{
  const char *p;
  size_t bytes;
  va_list ap;
  char *tmp;

  if (parser->error) return parser->error;

  bytes = strlen (parser->name) + 20; /* care for ':: \0' and lineno */

  va_start (ap, fmt);
  for (p = fmt; *p; p++)
  {
    if (*p == '%')
    {
      p++;
      assert (*p);
      if (*p == 'd' || *p == 'u')
        bytes += 12;
      else
      {
        assert (*p == 's');
        bytes += strlen (va_arg (ap, const char *));
      }
    }
    else
      bytes++;
  }
  va_end (ap);

  tmp = btor_malloc (parser->mem, bytes);
  sprintf (tmp, "%s:%d: ", parser->name, parser->lineno);
  assert (strlen (tmp) + 1 < bytes);
  va_start (ap, fmt);
  vsprintf (tmp + strlen (tmp), fmt, ap);
  va_end (ap);
  parser->error = btor_strdup (parser->mem, tmp);
  btor_free (parser->mem, tmp, bytes);

  return parser->error;
}

static const char *
btor_parse_smt_parser (BtorSMTParser *parser,
                       FILE *file,
                       const char *name,
                       BtorParseResult *res)
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

const BtorParserAPI *btor_smt_parser_api = &api;
