/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011 Armin Biere, FMV, JKU.
 *
 *  Institute for Formal Models and Verification,
 *  Johannes Kepler University, Linz, Austria.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "btorsmt2.h"
#include "btormem.h"

typedef struct BtorSMT2Parser
{
  Btor* btor;
  BtorMemMgr* mem;
  int verbosity, incremental;
  char* name;
  int lineno;
  FILE* file;
  char* error;
} BtorSMT2Parser;

static char*
btor_perr_smt2 (BtorSMT2Parser* parser, const char* fmt, ...)
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

static BtorSMT2Parser*
btor_new_smt2_parser (Btor* btor, int verbosity, int incremental)
{
  BtorSMT2Parser* res;
  BTOR_NEW (btor->mm, res);
  BTOR_CLR (res);
  res->verbosity   = verbosity;
  res->incremental = incremental;
  res->btor        = btor;
  res->mem         = btor->mm;
  return res;
}

static void
btor_delete_smt2_parser (BtorSMT2Parser* parser)
{
  BtorMemMgr* mem = parser->mem;
  if (parser->name) btor_freestr (mem, parser->name);
  if (parser->error) btor_freestr (mem, parser->error);
  BTOR_DELETE (mem, parser);
}

static const char*
btor_parse_smt2_parser (BtorSMT2Parser* parser,
                        FILE* file,
                        const char* name,
                        BtorParseResult* res)
{
  (void) parser;
  (void) file;
  (void) name;
  (void) res;
  parser->name   = btor_strdup (parser->mem, name);
  parser->lineno = 1;
  parser->file   = file;
  return 0;
}

static BtorParserAPI static_btor_smt2_parser_api = {
    (BtorInitParser) btor_new_smt2_parser,
    (BtorResetParser) btor_delete_smt2_parser,
    (BtorParse) btor_parse_smt2_parser};

const BtorParserAPI*
btor_smt2_parser_api ()
{
  return &static_btor_smt2_parser_api;
}
