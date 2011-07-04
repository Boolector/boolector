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
  int verbosity, incremental;
} BtorSMT2Parser;

static BtorSMT2Parser*
btor_new_smt2_parser (Btor* btor, int verbosity, int incremental)
{
  BtorSMT2Parser* res;
  BTOR_NEW (btor->mm, res);
  BTOR_CLR (res);
  res->verbosity   = verbosity;
  res->incremental = incremental;
  res->btor        = btor;
  return res;
}

static void
btor_delete_smt2_parser (BtorSMT2Parser* parser)
{
  BTOR_DELETE (parser->btor->mm, parser);
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
