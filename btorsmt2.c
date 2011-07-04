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

typedef enum BtorSMT2TagClass
{
  BTOR_CLASS_BITS_SMT2 = 5 BTOR_CONSTANT_TAG_CLASS_SMT2 =
      (1 << (BTOR_CLASS_BITS_SMT2 + 0)),
  BTOR_RESERVED_TAG_CLASS_SMT2 = (1 << (BTOR_CLASS_BITS_SMT2 + 1)),
  BTOR_COMMAND_TAG_CLASS_SMT2  = (1 << (BTOR_CLASS_BITS_SMT2 + 2)),
  BTOR_CORE_TAG_CLASS_SMT2     = (1 << (BTOR_CLASS_BITS_SMT2 + 3)),
  BTOR_BV_TAG_CLASS_SMT2       = (1 << (BTOR_CLASS_BITS_SMT2 + 4)),
} BtorSMT2TagClass;

typedef enum BtorSMT2Tag
{

  BTOR_NUMERAL_CONSTANT_TAG_SMT2     = 0 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_DECIMAL_CONSTANT_TAG_SMT2     = 1 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2 = 2 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_BINARY_CONSTANT_TAG_SMT2      = 3 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_STRING_CONSTANT_TAG_SMT2      = 4 + BTOR_CONSTANT_TAG_CLASS_SMT2,

  BTOR_PAR_TAG_SMT2                   = 0 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_NUMERAL_RESERVED_WORD_TAG_SMT2 = 1 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_DECIMAL_RESERVED_WORD_TAG_SMT2 = 2 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_STRING_TAG_SMT2                = 3 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_UNDERSCORE_TAG_SMT2            = 4 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_BANG_TAG_SMT2                  = 5 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_AS_TAG_SMT2                    = 6 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_LET_TAG_SMT2                   = 7 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_FORALL_TAG_SMT2                = 8 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_EXISTS_TAG_SMT2                = 9 + BTOR_RESERVED_TAG_CLASS_SMT2,

  BTOR_SET_LOGIC_TAG_SMT2      = 0 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_SET_OPTION_TAG_SMT2     = 1 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_SET_INFO_TAG_SMT2       = 2 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DECLARE_SORT_TAG_SMT2   = 3 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DEFINE_SORT_TAG_SMT2    = 4 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DECLARE_FUN_TAG_SMT2    = 5 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DEFINE_FUN_TAG_SMT2     = 6 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_PUSH_TAG_SMT2           = 7 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_POP_TAG_SMT2            = 8 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_ASSERT_TAG_SMT2         = 9 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_CHECK_SAT_TAG_SMT2      = 10 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_ASSERTIONS_TAG_SMT2 = 11 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_PROOF_TAG_SMT2      = 12 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_UNSAT_CORE_TAG_SMT2 = 13 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_VALUE_TAG_SMT2      = 14 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_ASSIGNMENT_TAG_SMT2 = 15 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_OPTION_TAG_SMT2     = 16 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_INFO_TAG_SMT2       = 17 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_EXIT_TAG_SMT2           = 18 + BTOR_COMMAND_TAG_CLASS_SMT2,

  BTOR_BOOL_TAG_SMT2     = 0 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_TRUE_TAG_SMT2     = 1 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_FALSE_TAG_SMT2    = 2 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_NOT_TAG_SMT2      = 3 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_IMPLIES_TAG_SMT2  = 4 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_AND_TAG_SMT2      = 5 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_OR_TAG_SMT2       = 6 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_XOR_TAG_SMT2      = 7 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_EQUAL_TAG_SMT2    = 8 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_DISTINCT_TAG_SMT2 = 9 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_ITE_TAG_SMT2      = 10 + BTOR_CORE_TAG_CLASS_SMT2,

} BtorSMT2Tag;

typedef struct BtorSMT2Symbol
{
  BtorSMT2Tag tag;
  char* name;
  struct BtorSMT2Symbol* next;
  int lineno;
} BtorSMT2Symbol;

typedef struct BtorSMT2Parser
{
  Btor* btor;
  BtorMemMgr* mem;
  int verbosity, incremental;
  char* name;
  int lineno;
  FILE* file;
  char* error;
  struct
  {
    unsigned size, count;
    BtorSMT2Symbol** table;
  } symbol;
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

static unsigned btor_primes_smt2[] = {
    1000000007u, 2000000011u, 3000000019u, 4000000007u};

#define BTOR_NPRIMES_SMT2 (sizeof btor_primes_smt2 / sizeof *btor_primes_smt2)

static unsigned
btor_hash_name_smt2 (BtorSMT2Parser* parser, const char* name)
{
  unsigned res = 0, i = 0;
  unsigned char ch;
  const char* p;
  for (p = name; (ch = *p); p++)
  {
    res += ch;
    res *= btor_primes_smt2[i++];
    if (i == BTOR_NPRIMES_SMT2) i = 0;
  }
  return res & (parser->symbol.size - 1);
}

static BtorSMT2Symbol**
btor_symbol_position_smt2 (BtorSMT2Parser* parser, const char* name)
{
  unsigned h = btor_hash_name_smt2 (parser, name);
  BtorSMT2Symbol **p, *s;
  for (p = parser->symbol.table + h; (s = *p) && strcmp (s->name, name);
       p = &s->next)
    ;
  return p;
}

static void
btor_enlarge_symbol_table_smt2 (BtorSMT2Parser* parser)
{
  unsigned old_size          = parser->symbol.size;
  unsigned new_size          = old_size ? 2 * old_size : 1;
  BtorSMT2Symbol **old_table = parser->symbol.table, *p, *next, **q;
  unsigned h, i;
  BTOR_NEWN (parser->mem, parser->symbol.table, new_size);
  parser->symbol.size = new_size;
  for (i = 0; i < old_size; i++)
    for (p = old_table[i]; p; p = next)
    {
      next    = p->next;
      h       = btor_hash_name_smt2 (parser, p->name);
      p->next = *(q = parser->symbol.table + h);
      *q      = p;
    }
  BTOR_DELETEN (parser->mem, old_table, old_size);
}

static void
btor_insert_symbol_smt2 (BtorSMT2Parser* parser, BtorSMT2Symbol* symbol)
{
  BtorSMT2Symbol** p;
  if (parser->symbol.size >= parser->symbol.count)
    btor_enlarge_symbol_table_smt2 (parser);
  p = btor_symbol_position_smt2 (parser, symbol->name);
  assert (*p);
  *p = symbol;
}

static BtorSMT2Symbol*
btor_find_symbol_smt2 (BtorSMT2Parser* parser, const char* name)
{
  return *btor_symbol_position_smt2 (parser, name);
}

static void
btor_release_symbol_smt2 (BtorSMT2Parser* parser, BtorSMT2Symbol* symbol)
{
  btor_freestr (parser->mem, symbol->name);
  BTOR_DELETE (parser->mem, symbol);
}

static void
btor_release_symbols_smt2 (BtorSMT2Parser* parser)
{
  BtorSMT2Symbol *p, *next;
  unsigned i;
  for (i = 0; i < parser->symbol.size; i++)
    for (p = parser->symbol.table[i]; p; p = next)
      next = p->next, btor_release_symbol_smt2 (parser, p);
  BTOR_DELETEN (parser->mem, parser->symbol.table, parser->symbol.size);
}

static void
btor_delete_smt2_parser (BtorSMT2Parser* parser)
{
  BtorMemMgr* mem = parser->mem;
  btor_release_symbols_smt2 (parser);
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
