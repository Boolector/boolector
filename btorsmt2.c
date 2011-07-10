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
#include "btorexp.h"
#include "btormem.h"
#include "btorutil.h"

#include <ctype.h>
#include <limits.h>
#include <stdarg.h>

typedef enum BtorSMT2TagClass
{
  BTOR_CLASS_BITS_SMT2 = 6,
  BTOR_CLASS_SIZE_SMT2 = (1 << BTOR_CLASS_BITS_SMT2),
  BTOR_CLASS_MASK_SMT2 = (BTOR_CLASS_SIZE_SMT2 - 1),

  BTOR_OTHER_TAG_CLASS_SMT2 = 0,

  BTOR_CONSTANT_TAG_CLASS_SMT2 = (BTOR_CLASS_SIZE_SMT2 << 0),
  BTOR_RESERVED_TAG_CLASS_SMT2 = (BTOR_CLASS_SIZE_SMT2 << 1),
  BTOR_COMMAND_TAG_CLASS_SMT2  = (BTOR_CLASS_SIZE_SMT2 << 2),
  BTOR_KEYWORD_TAG_CLASS_SMT2  = (BTOR_CLASS_SIZE_SMT2 << 3),
  BTOR_CORE_TAG_CLASS_SMT2     = (BTOR_CLASS_SIZE_SMT2 << 4),
  BTOR_ARRAY_TAG_CLASS_SMT2    = (BTOR_CLASS_SIZE_SMT2 << 5),
  BTOR_BITVEC_TAG_CLASS_SMT2   = (BTOR_CLASS_SIZE_SMT2 << 6),
  BTOR_LOGIC_TAG_CLASS_SMT2    = (BTOR_CLASS_SIZE_SMT2 << 7),
} BtorSMT2TagClass;

typedef enum BtorSMT2Tag
{

  BTOR_INVALID_TAG_SMT2   = 0 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_PARENT_TAG_SMT2    = 1 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_LPAR_TAG_SMT2      = 2 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_RPAR_TAG_SMT2      = 3 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_SYMBOL_TAG_SMT2    = 4 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_ATTRIBUTE_TAG_SMT2 = 5 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_EXP_TAG_SMT2       = 6 + BTOR_OTHER_TAG_CLASS_SMT2,

  BTOR_DECIMAL_CONSTANT_TAG_SMT2     = 0 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2 = 1 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_BINARY_CONSTANT_TAG_SMT2      = 2 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_STRING_CONSTANT_TAG_SMT2      = 3 + BTOR_CONSTANT_TAG_CLASS_SMT2,

  BTOR_PAR_TAG_SMT2                   = 0 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_NUMERAL_RESERVED_WORD_TAG_SMT2 = 1 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_DECIMAL_RESERVED_WORD_TAG_SMT2 = 2 + BTOR_RESERVED_TAG_CLASS_SMT2,
  BTOR_STRING_RESERVED_WORD_TAG_SMT2  = 3 + BTOR_RESERVED_TAG_CLASS_SMT2,
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

  BTOR_ALL_STATISTICS_TAG_SMT2         = 0 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_AUTHORS_TAG_SMT2                = 1 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_AXIOMS_TAG_SMT2                 = 2 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_CHAINABLE_TAG_SMT2              = 3 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_DEFINITION_TAG_SMT2             = 4 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_DIAG_OUTPUT_CHANNEL_TAG_SMT2    = 5 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_ERROR_BEHAVIOR_TAG_SMT2         = 6 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_EXPAND_DEFINITIONS_TAG_SMT2     = 7 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_EXTENSIONS_TAG_SMT2             = 8 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_FUNS_TAG_SMT2                   = 9 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_FUNS_DESCRIPTION_TAG_SMT2       = 10 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_INTERACTIVE_MODE_TAG_SMT2       = 11 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_LANGUAGE_TAG_SMT2               = 12 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_LEFT_ASSOC_TAG_SMT2             = 13 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_NAME_TAG_SMT2                   = 14 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_NAMED_TAG_SMT2                  = 15 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_NOTES_TAG_SMT2                  = 16 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRINT_SUCCESS_TAG_SMT2          = 17 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_ASSIGNMENTS_TAG_SMT2    = 18 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_MODELS_TAG_SMT2         = 19 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_PROOFS_TAG_SMT2         = 20 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_UNSAT_CORES_TAG_SMT2    = 21 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_RANDOM_SEED_TAG_SMT2            = 22 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_REASON_UNKNOWN_TAG_SMT2         = 23 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_REGULAR_OUTPUT_CHANNEL_TAG_SMT2 = 24 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_RIGHT_ASSOC_TAG_SMT2            = 25 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_SORTS_TAG_SMT2                  = 26 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_SORTS_DESCRIPTION_TAG_SMT2      = 27 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_STATUS_TAG_SMT2                 = 28 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_THEORIES_TAG_SMT2               = 29 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_VALUES_TAG_SMT2                 = 30 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_VERBOSITY_TAG_SMT2              = 31 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_VERSION_TAG_SMT2                = 32 + BTOR_KEYWORD_TAG_CLASS_SMT2,

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

  BTOR_ARRAY_TAG_SMT2  = 0 + BTOR_ARRAY_TAG_CLASS_SMT2,
  BTOR_SELECT_TAG_SMT2 = 1 + BTOR_ARRAY_TAG_CLASS_SMT2,
  BTOR_STORE_TAG_SMT2  = 2 + BTOR_ARRAY_TAG_CLASS_SMT2,

  BTOR_BITVEC_TAG_SMT2       = 0 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_CONCAT_TAG_SMT2       = 1 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_EXTRACT_TAG_SMT2      = 2 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVNOT_TAG_SMT2        = 3 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVNEG_TAG_SMT2        = 4 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVAND_TAG_SMT2        = 5 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVOR_TAG_SMT2         = 6 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVADD_TAG_SMT2        = 7 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVMUL_TAG_SMT2        = 8 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVUDIV_TAG_SMT2       = 9 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVUREM_TAG_SMT2       = 10 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSHL_TAG_SMT2        = 11 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVLSHR_TAG_SMT2       = 12 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVULT_TAG_SMT2        = 13 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVNAND_TAG_SMT2       = 14 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVNOR_TAG_SMT2        = 15 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVXOR_TAG_SMT2        = 16 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVXNOR_TAG_SMT2       = 17 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVCOMP_TAG_SMT2       = 18 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSUB_TAG_SMT2        = 19 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSDIV_TAG_SMT2       = 20 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSREM_TAG_SMT2       = 21 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSMOD_TAG_SMT2       = 22 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVASHR_TAG_SMT2       = 23 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_REPEAT_TAG_SMT2       = 24 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_ZERO_EXTEND_TAG_SMT2  = 25 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_SIGN_EXTEND_TAG_SMT2  = 26 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_ROTATE_LEFT_TAG_SMT2  = 27 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_ROTATE_RIGHT_TAG_SMT2 = 28 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVULE_TAG_SMT2        = 29 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVUGT_TAG_SMT2        = 30 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVUGE_TAG_SMT2        = 31 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSLT_TAG_SMT2        = 32 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSLE_TAG_SMT2        = 33 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSGT_TAG_SMT2        = 34 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVSGE_TAG_SMT2        = 35 + BTOR_BITVEC_TAG_CLASS_SMT2,

  BTOR_QF_BV_TAG_SMT2    = 0 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_ABV_TAG_SMT2   = 1 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UFBV_TAG_SMT2  = 2 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_AUFBV_TAG_SMT2 = 3 + BTOR_LOGIC_TAG_CLASS_SMT2,

} BtorSMT2Tag;

typedef enum BtorSMT2SortTag
{
  BTOR_UNDEFINED_SORT_SMT2 = 0,
  BTOR_BITVEC_SORT_SMT2    = 1,
  BTOR_ARRAY_SORT_SMT2     = 2,
} BtorSMT2SortTag;

typedef struct BtorSMT2Sort
{
  BtorSMT2SortTag tag;
  int width, domain;
} BtorSMT2Sort;

typedef struct BtorSMT2Node
{
  BtorSMT2Tag tag;
  int lineno;
  BtorSMT2Sort sort;
  BtorExp* exp;
  union
  {
    struct
    {
      char* name;
      struct BtorSMT2Node* next;
    };
    struct
    {
      struct BtorSMT2Node* child;
      int size;
    };
  };
} BtorSMT2Node;

typedef struct BtorSMT2Item
{
  BtorSMT2Tag tag;
  int lineno, num;
  union
  {
    BtorSMT2Node* node;
    BtorExp* exp;
    char* str;
  };
} BtorSMT2Item;

BTOR_DECLARE_STACK (SMT2Item, BtorSMT2Item);

static const char* btor_printable_ascii_chars_smt2 =
    "!\"#$%&'()*+,-./"
    "0123456789"
    ":;<=>?@"
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "[\\]^_`"
    "abcdefghijklmnopqrstuvwxyz"
    "{|}~"
    " \t\r\n";

static const char* btor_letters_smt2 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz";

static const char* btor_decimal_digits_smt2 = "0123456789";

static const char* btor_hexadecimal_digits_smt2 = "0123456789abcdefABCDEF";

static const char* btor_extra_symbol_chars_smt2 = "+-/*=%?!.$_~&^<>@";

static const char* btor_extra_keyword_chars_smt2 = "+-/*=%?!.$_~&^<>@";

typedef enum BtorSMT2CharClass
{
  BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2     = (1 << 0),
  BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2 = (1 << 1),
  BTOR_STRING_CHAR_CLASS_SMT2            = (1 << 2),
  BTOR_SYMBOL_CHAR_CLASS_SMT2            = (1 << 3),
  BTOR_QUOTED_SYMBOL_CHAR_CLASS_SMT2     = (1 << 4),
  BTOR_KEYWORD_CHAR_CLASS_SMT2           = (1 << 5),
} BtorSMT2CharClass;

typedef struct BtorSMT2Parser
{
  Btor* btor;
  BtorMemMgr* mem;
  int verbosity, incremental, need_arrays;
  char* name;
  int lineno, perrlineno;
  FILE* file;
  int saved;
  char savedch;
  BtorSMT2Node* last_node;
  int nprefix;
  BtorCharStack* prefix;
  char* error;
  struct
  {
    unsigned size, count;
    BtorSMT2Node** table;
  } symbol;
  unsigned char cc[256];
  BtorExpPtrStack outputs, inputs;
  BtorCharStack token;
  BtorSMT2ItemStack work;
  BtorParseResult* res;
  int set_logic_commands, assert_commands, check_sat_commands, exit_commands;
  int binding;
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
        parser->mem,
        parser->name,
        (parser->perrlineno ? parser->perrlineno : parser->lineno),
        fmt,
        ap,
        bytes);
    va_end (ap);
  }
  return parser->error;
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

static BtorSMT2Node**
btor_symbol_position_smt2 (BtorSMT2Parser* parser, const char* name)
{
  unsigned h = btor_hash_name_smt2 (parser, name);
  BtorSMT2Node **p, *s;
  for (p = parser->symbol.table + h; (s = *p) && strcmp (s->name, name);
       p = &s->next)
    ;
  return p;
}

static int
btor_nextch_smt2 (BtorSMT2Parser* parser)
{
  int res;
  if (parser->saved)
    res = parser->savedch, parser->saved = 0;
  else if (parser->prefix
           && parser->nprefix < BTOR_COUNT_STACK (*parser->prefix))
    res = parser->prefix->start[parser->nprefix++];
  else
    res = getc (parser->file);
  if (res == '\n') parser->lineno++;
  return res;
}

static void
btor_savech_smt2 (BtorSMT2Parser* parser, char ch)
{
  assert (!parser->saved);
  parser->saved   = 1;
  parser->savedch = ch;
  if (ch == '\n') assert (parser->lineno > 1), parser->lineno--;
}

static void
btor_enlarge_symbol_table_smt2 (BtorSMT2Parser* parser)
{
  unsigned old_size        = parser->symbol.size;
  unsigned new_size        = old_size ? 2 * old_size : 1;
  BtorSMT2Node **old_table = parser->symbol.table, *p, *next, **q;
  unsigned h, i;
  BTOR_NEWN (parser->mem, parser->symbol.table, new_size);
  BTOR_CLRN (parser->symbol.table, new_size);
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
btor_insert_symbol_smt2 (BtorSMT2Parser* parser, BtorSMT2Node* symbol)
{
  BtorSMT2Node** p;
  if (parser->symbol.size <= parser->symbol.count)
    btor_enlarge_symbol_table_smt2 (parser);
  p = btor_symbol_position_smt2 (parser, symbol->name);
  assert (!*p);
  *p = symbol;
  parser->symbol.count++;
  assert (parser->symbol.count > 0);
}

static BtorSMT2Node*
btor_find_symbol_smt2 (BtorSMT2Parser* parser, const char* name)
{
  return *btor_symbol_position_smt2 (parser, name);
}

static BtorSMT2Node*
btor_new_node_smt2 (BtorSMT2Parser* parser, BtorSMT2Tag tag)
{
  BtorSMT2Node* res;
  BTOR_NEW (parser->mem, res);
  BTOR_CLR (res);
  res->tag = tag;
  return res;
}

static void
btor_release_symbol_smt2 (BtorSMT2Parser* parser, BtorSMT2Node* symbol)
{
  assert (symbol->tag != BTOR_PARENT_TAG_SMT2);
  if (symbol->exp) btor_release_exp (parser->btor, symbol->exp);
  btor_freestr (parser->mem, symbol->name);
  BTOR_DELETE (parser->mem, symbol);
}

static void
btor_release_symbols_smt2 (BtorSMT2Parser* parser)
{
  BtorSMT2Node *p, *next;
  unsigned i;
  for (i = 0; i < parser->symbol.size; i++)
    for (p = parser->symbol.table[i]; p; p = next)
      next = p->next, btor_release_symbol_smt2 (parser, p);
  BTOR_DELETEN (parser->mem, parser->symbol.table, parser->symbol.size);
}

static void
btor_init_char_classes_smt2 (BtorSMT2Parser* parser)
{
  unsigned char* cc = parser->cc;
  const char* p;

  BTOR_CLRN (cc, 256);

  for (p = btor_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2;

  for (p = btor_hexadecimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2;

  for (p = btor_printable_ascii_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_STRING_CHAR_CLASS_SMT2;

  for (p = btor_letters_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_SYMBOL_CHAR_CLASS_SMT2;
  for (p = btor_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_SYMBOL_CHAR_CLASS_SMT2;
  for (p = btor_extra_symbol_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_SYMBOL_CHAR_CLASS_SMT2;

  for (p = btor_printable_ascii_chars_smt2; *p; p++)
    if (*p != '\\' && *p != '|')
      cc[(unsigned char) *p] |= BTOR_QUOTED_SYMBOL_CHAR_CLASS_SMT2;

  for (p = btor_letters_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_KEYWORD_CHAR_CLASS_SMT2;
  for (p = btor_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_KEYWORD_CHAR_CLASS_SMT2;
  for (p = btor_extra_keyword_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_KEYWORD_CHAR_CLASS_SMT2;
}

#define INSERT(STR, TAG)                                     \
  do                                                         \
  {                                                          \
    BtorSMT2Node* NODE = btor_new_node_smt2 (parser, (TAG)); \
    NODE->name         = btor_strdup (parser->mem, (STR));   \
    btor_insert_symbol_smt2 (parser, NODE);                  \
  } while (0)

static void
btor_insert_keywords_smt2 (BtorSMT2Parser* parser)
{
  INSERT (":all-statistics", BTOR_ALL_STATISTICS_TAG_SMT2);
  INSERT (":authors", BTOR_AUTHORS_TAG_SMT2);
  INSERT (":axioms", BTOR_AXIOMS_TAG_SMT2);
  INSERT (":chainable", BTOR_CHAINABLE_TAG_SMT2);
  INSERT (":definition", BTOR_DEFINITION_TAG_SMT2);
  INSERT (":diagnostic-output-channel", BTOR_DIAG_OUTPUT_CHANNEL_TAG_SMT2);
  INSERT (":error-behavior", BTOR_ERROR_BEHAVIOR_TAG_SMT2);
  INSERT (":expand-definitions", BTOR_EXPAND_DEFINITIONS_TAG_SMT2);
  INSERT (":extensions", BTOR_EXTENSIONS_TAG_SMT2);
  INSERT (":funs", BTOR_FUNS_TAG_SMT2);
  INSERT (":funs-description", BTOR_FUNS_DESCRIPTION_TAG_SMT2);
  INSERT (":interactive-mode", BTOR_INTERACTIVE_MODE_TAG_SMT2);
  INSERT (":language", BTOR_LANGUAGE_TAG_SMT2);
  INSERT (":left-assoc", BTOR_LEFT_ASSOC_TAG_SMT2);
  INSERT (":name", BTOR_NAME_TAG_SMT2);
  INSERT (":named", BTOR_NAMED_TAG_SMT2);
  INSERT (":notes", BTOR_NOTES_TAG_SMT2);
  INSERT (":print-success", BTOR_PRINT_SUCCESS_TAG_SMT2);
  INSERT (":produce-assignments", BTOR_PRODUCE_ASSIGNMENTS_TAG_SMT2);
  INSERT (":produce-models", BTOR_PRODUCE_MODELS_TAG_SMT2);
  INSERT (":produce-proofs", BTOR_PRODUCE_PROOFS_TAG_SMT2);
  INSERT (":produce-unsat-cores", BTOR_PRODUCE_UNSAT_CORES_TAG_SMT2);
  INSERT (":random-seed", BTOR_RANDOM_SEED_TAG_SMT2);
  INSERT (":reason-unknown", BTOR_REASON_UNKNOWN_TAG_SMT2);
  INSERT (":regular-output-channel", BTOR_REGULAR_OUTPUT_CHANNEL_TAG_SMT2);
  INSERT (":right-assoc", BTOR_RIGHT_ASSOC_TAG_SMT2);
  INSERT (":sorts", BTOR_SORTS_TAG_SMT2);
  INSERT (":sorts-description", BTOR_SORTS_DESCRIPTION_TAG_SMT2);
  INSERT (":status", BTOR_STATUS_TAG_SMT2);
  INSERT (":theories", BTOR_THEORIES_TAG_SMT2);
  INSERT (":values", BTOR_VALUES_TAG_SMT2);
  INSERT (":verbosity", BTOR_VERBOSITY_TAG_SMT2);
  INSERT (":version", BTOR_VERSION_TAG_SMT2);
}

static void
btor_insert_reserved_words_smt2 (BtorSMT2Parser* parser)
{
  INSERT ("!", BTOR_BANG_TAG_SMT2);
  INSERT ("_", BTOR_UNDERSCORE_TAG_SMT2);
  INSERT ("as", BTOR_AS_TAG_SMT2);
  INSERT ("DECIMAL", BTOR_DECIMAL_RESERVED_WORD_TAG_SMT2);
  INSERT ("exists", BTOR_EXISTS_TAG_SMT2);
  INSERT ("forall", BTOR_FORALL_TAG_SMT2);
  INSERT ("let", BTOR_LET_TAG_SMT2);
  INSERT ("par", BTOR_PAR_TAG_SMT2);
  INSERT ("STRING", BTOR_STRING_RESERVED_WORD_TAG_SMT2);
}

static void
btor_insert_commands_smt2 (BtorSMT2Parser* parser)
{
  INSERT ("assert", BTOR_ASSERT_TAG_SMT2);
  INSERT ("check-sat", BTOR_CHECK_SAT_TAG_SMT2);
  INSERT ("declare-sort", BTOR_DECLARE_SORT_TAG_SMT2);
  INSERT ("declare-fun", BTOR_DECLARE_FUN_TAG_SMT2);
  INSERT ("define-sort", BTOR_DEFINE_SORT_TAG_SMT2);
  INSERT ("define-fun", BTOR_DEFINE_FUN_TAG_SMT2);
  INSERT ("exit", BTOR_EXIT_TAG_SMT2);
  INSERT ("get-assertions", BTOR_GET_ASSERTIONS_TAG_SMT2);
  INSERT ("get-assignment", BTOR_GET_ASSIGNMENT_TAG_SMT2);
  INSERT ("get-info", BTOR_GET_INFO_TAG_SMT2);
  INSERT ("get-option", BTOR_GET_OPTION_TAG_SMT2);
  INSERT ("get-proof", BTOR_GET_PROOF_TAG_SMT2);
  INSERT ("get-unsat-core", BTOR_GET_UNSAT_CORE_TAG_SMT2);
  INSERT ("get-value", BTOR_GET_VALUE_TAG_SMT2);
  INSERT ("pop", BTOR_POP_TAG_SMT2);
  INSERT ("push", BTOR_PUSH_TAG_SMT2);
  INSERT ("set-logic", BTOR_SET_LOGIC_TAG_SMT2);
  INSERT ("set-info", BTOR_SET_INFO_TAG_SMT2);
  INSERT ("set-option", BTOR_SET_OPTION_TAG_SMT2);
}

static void
btor_insert_core_symbols_smt2 (BtorSMT2Parser* parser)
{
  INSERT ("Bool", BTOR_BOOL_TAG_SMT2);
  INSERT ("true", BTOR_TRUE_TAG_SMT2);
  INSERT ("false", BTOR_FALSE_TAG_SMT2);
  INSERT ("not", BTOR_NOT_TAG_SMT2);
  INSERT ("=>", BTOR_IMPLIES_TAG_SMT2);
  INSERT ("and", BTOR_AND_TAG_SMT2);
  INSERT ("or", BTOR_OR_TAG_SMT2);
  INSERT ("xor", BTOR_XOR_TAG_SMT2);
  INSERT ("=", BTOR_EQUAL_TAG_SMT2);
  INSERT ("distinct", BTOR_DISTINCT_TAG_SMT2);
  INSERT ("ite", BTOR_ITE_TAG_SMT2);
}

static void
btor_insert_array_symbols_smt2 (BtorSMT2Parser* parser)
{
  INSERT ("Array", BTOR_ARRAY_TAG_SMT2);
  INSERT ("select", BTOR_SELECT_TAG_SMT2);
  INSERT ("store", BTOR_STORE_TAG_SMT2);
}

static void
btor_insert_bitvec_symbols_smt2 (BtorSMT2Parser* parser)
{
  INSERT ("BitVec", BTOR_BITVEC_TAG_SMT2);
  INSERT ("concat", BTOR_CONCAT_TAG_SMT2);
  INSERT ("extract", BTOR_EXTRACT_TAG_SMT2);
  INSERT ("bvnot", BTOR_BVNOT_TAG_SMT2);
  INSERT ("bvneg", BTOR_BVNEG_TAG_SMT2);
  INSERT ("bvand", BTOR_BVAND_TAG_SMT2);
  INSERT ("bvor", BTOR_BVOR_TAG_SMT2);
  INSERT ("bvadd", BTOR_BVADD_TAG_SMT2);
  INSERT ("bvmul", BTOR_BVMUL_TAG_SMT2);
  INSERT ("bvudiv", BTOR_BVUDIV_TAG_SMT2);
  INSERT ("bvurem", BTOR_BVUREM_TAG_SMT2);
  INSERT ("bvshl", BTOR_BVSHL_TAG_SMT2);
  INSERT ("bvlshr", BTOR_BVLSHR_TAG_SMT2);
  INSERT ("bvult", BTOR_BVULT_TAG_SMT2);
  INSERT ("bvnand", BTOR_BVNAND_TAG_SMT2);
  INSERT ("bvnor", BTOR_BVNOR_TAG_SMT2);
  INSERT ("bvxor", BTOR_BVXOR_TAG_SMT2);
  INSERT ("bvxnor", BTOR_BVXNOR_TAG_SMT2);
  INSERT ("bvcomp", BTOR_BVCOMP_TAG_SMT2);
  INSERT ("bvsub", BTOR_BVSUB_TAG_SMT2);
  INSERT ("bvsdiv", BTOR_BVSDIV_TAG_SMT2);
  INSERT ("bvsrem", BTOR_BVSREM_TAG_SMT2);
  INSERT ("bvsmod", BTOR_BVSMOD_TAG_SMT2);
  INSERT ("bvashr", BTOR_BVASHR_TAG_SMT2);
  INSERT ("repeat", BTOR_REPEAT_TAG_SMT2);
  INSERT ("zero_extend", BTOR_ZERO_EXTEND_TAG_SMT2);
  INSERT ("sign_extend", BTOR_SIGN_EXTEND_TAG_SMT2);
  INSERT ("rotate_left", BTOR_ROTATE_LEFT_TAG_SMT2);
  INSERT ("rotate_right", BTOR_ROTATE_RIGHT_TAG_SMT2);
  INSERT ("bvule", BTOR_BVULE_TAG_SMT2);
  INSERT ("bvugt", BTOR_BVUGT_TAG_SMT2);
  INSERT ("bvuge", BTOR_BVUGE_TAG_SMT2);
  INSERT ("bvslt", BTOR_BVSLT_TAG_SMT2);
  INSERT ("bvsle", BTOR_BVSLE_TAG_SMT2);
  INSERT ("bvsgt", BTOR_BVSGT_TAG_SMT2);
  INSERT ("bvsge", BTOR_BVSGE_TAG_SMT2);
}

static void
btor_insert_logics_smt2 (BtorSMT2Parser* parser)
{
  INSERT ("QF_BV", BTOR_QF_BV_TAG_SMT2);
  INSERT ("QF_ABV", BTOR_QF_ABV_TAG_SMT2);
  INSERT ("QF_UFBV", BTOR_QF_UFBV_TAG_SMT2);
  INSERT ("QF_AUFBV", BTOR_QF_AUFBV_TAG_SMT2);
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

  btor_init_char_classes_smt2 (res);

  btor_insert_keywords_smt2 (res);
  btor_insert_reserved_words_smt2 (res);
  btor_insert_commands_smt2 (res);
  btor_insert_core_symbols_smt2 (res);
  btor_insert_array_symbols_smt2 (res);
  btor_insert_bitvec_symbols_smt2 (res);
  btor_insert_logics_smt2 (res);

  return res;
}

static void
btor_release_item_smt2 (BtorSMT2Parser* parser, BtorSMT2Item* item)
{
  if (item->tag == BTOR_EXP_TAG_SMT2)
  {
    btor_release_exp (parser->btor, item->exp);
  }
  else if (item->tag & BTOR_CONSTANT_TAG_CLASS_SMT2)
    btor_freestr (parser->mem, item->str);
}

static void
btor_release_work_smt2 (BtorSMT2Parser* parser)
{
  BtorSMT2Item item;
  while (!BTOR_EMPTY_STACK (parser->work))
  {
    item = BTOR_POP_STACK (parser->work);
    btor_release_item_smt2 (parser, &item);
  }
  BTOR_RELEASE_STACK (parser->mem, parser->work);
}

static void
btor_delete_smt2_parser (BtorSMT2Parser* parser)
{
  BtorMemMgr* mem = parser->mem;

  btor_release_symbols_smt2 (parser);
  btor_release_work_smt2 (parser);

  if (parser->name) btor_freestr (mem, parser->name);
  if (parser->error) btor_freestr (mem, parser->error);

  while (!BTOR_EMPTY_STACK (parser->inputs))
    btor_release_exp (parser->btor, BTOR_POP_STACK (parser->inputs));
  BTOR_RELEASE_STACK (mem, parser->inputs);

  while (!BTOR_EMPTY_STACK (parser->outputs))
    btor_release_exp (parser->btor, BTOR_POP_STACK (parser->outputs));
  BTOR_RELEASE_STACK (mem, parser->outputs);

  BTOR_RELEASE_STACK (mem, parser->token);

  BTOR_DELETE (mem, parser);
}

static void
btor_msg_smt2 (BtorSMT2Parser* parser, int level, const char* fmt, ...)
{
  va_list ap;
  if (parser->verbosity < level) return;
  printf ("[btorsmt2] ");
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  printf ("\n");
  fflush (stdout);
}

static int
btor_isspace_smt2 (int ch)
{
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

static unsigned
btor_cc_smt2 (BtorSMT2Parser* parser, int ch)
{
  if (ch == EOF) return 0;
  assert (0 <= ch && ch < 256);
  return parser->cc[(unsigned char) ch];
}

static void
btor_pushch_smt2 (BtorSMT2Parser* parser, int ch)
{
  assert (ch != EOF);
  BTOR_PUSH_STACK (parser->mem, parser->token, ch);
}

static int
btor_read_token_aux_smt2 (BtorSMT2Parser* parser)
{
  BtorSMT2Node* node;
  unsigned char cc;
  int ch;
  assert (!BTOR_INVALID_TAG_SMT2);  // error code:		0
  BTOR_RESET_STACK (parser->token);
  parser->last_node = 0;
RESTART:
  do
  {
    if ((ch = btor_nextch_smt2 (parser)) == EOF)
    {
      assert (EOF < 0);
      return EOF;  // end of tokens:	EOF
    }
  } while (btor_isspace_smt2 (ch));
  if (ch == ';')
  {
    while ((ch = btor_nextch_smt2 (parser)) != '\n')
      if (ch == EOF)
      {
        assert (!BTOR_INVALID_TAG_SMT2);
        return !btor_perr_smt2 (parser, "unexpected end-of-file in comment");
      }
    goto RESTART;
  }
  cc = btor_cc_smt2 (parser, ch);
  if (ch == '(')
  {
    btor_pushch_smt2 (parser, '(');
    btor_pushch_smt2 (parser, 0);
    return BTOR_LPAR_TAG_SMT2;
  }
  if (ch == ')')
  {
    btor_pushch_smt2 (parser, ')');
    btor_pushch_smt2 (parser, 0);
    return BTOR_RPAR_TAG_SMT2;
  }
  if (ch == '#')
  {
    btor_pushch_smt2 (parser, '#');
    if ((ch = btor_nextch_smt2 (parser)) == EOF)
      return !btor_perr_smt2 (parser, "unexpected end-of-file after '#'");
    if (ch == 'b')
    {
      btor_pushch_smt2 (parser, 'b');
      if ((ch = btor_nextch_smt2 (parser)) == EOF)
        return !btor_perr_smt2 (parser, "unexpected end-of-file after '#b'");
      if (ch != '0' && ch != '1')
        return !btor_perr_smt2 (parser, "expected '0' or '1' after '#b'");
      btor_pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = btor_nextch_smt2 (parser);
        if (ch != '0' && ch != '1') break;
        btor_pushch_smt2 (parser, ch);
      }
      btor_savech_smt2 (parser, ch);
      btor_pushch_smt2 (parser, 0);
      return BTOR_BINARY_CONSTANT_TAG_SMT2;
    }
    else if (ch == 'x')
    {
      btor_pushch_smt2 (parser, 'x');
      if ((ch = btor_nextch_smt2 (parser)) == EOF)
        return !btor_perr_smt2 (parser, "unexpected end-of-file after '#x'");
      if (!(btor_cc_smt2 (parser, ch) & BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2))
        return !btor_perr_smt2 (parser,
                                "expected hexa-decimal digit after '#x'");
      btor_pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = btor_nextch_smt2 (parser);
        if (!(btor_cc_smt2 (parser, ch)
              & BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2))
          break;
        btor_pushch_smt2 (parser, ch);
      }
      btor_savech_smt2 (parser, ch);
      btor_pushch_smt2 (parser, 0);
      return BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2;
    }
    else
      return !btor_perr_smt2 (parser, "expected 'x' or 'b' after '#'");
  }
  else if (ch == '"')
  {
    btor_pushch_smt2 (parser, '"');
    for (;;)
    {
      if ((ch = btor_nextch_smt2 (parser)) == EOF)
        return !btor_perr_smt2 (parser, "unexpected end-of-file in string");
      if (ch == '"')
      {
        btor_pushch_smt2 (parser, '"');
        btor_pushch_smt2 (parser, 0);
        return BTOR_STRING_CONSTANT_TAG_SMT2;
      }
      if (ch == '\\')
      {
        if ((ch = btor_nextch_smt2 (parser)) == EOF)
          return !btor_perr_smt2 (parser, "unexpected end-of-file after '\\'");
        if (ch != '"' && ch != '\\')
          return !btor_perr_smt2 (parser, "expected '\"' or '\\' after '\\'");
      }
      else if (!(btor_cc_smt2 (parser, ch) & BTOR_STRING_CHAR_CLASS_SMT2))
        return !btor_perr_smt2 (
            parser, "invalid character code %d in string", ch);
      btor_pushch_smt2 (parser, ch);
    }
  }
  else if (ch == '|')
  {
    btor_pushch_smt2 (parser, '|');
    for (;;)
    {
      if ((ch = btor_nextch_smt2 (parser)) == EOF)
        return !btor_perr_smt2 (parser,
                                "unexpected end-of-file in quoted symbol");
      if (ch == '|')
      {
        btor_pushch_smt2 (parser, '|');
        btor_pushch_smt2 (parser, 0);
        if (!(node = btor_find_symbol_smt2 (parser, parser->token.start)))
        {
          node       = btor_new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
          node->name = btor_strdup (parser->mem, parser->token.start);
          btor_insert_symbol_smt2 (parser, node);
        }
        parser->last_node = node;
        return BTOR_SYMBOL_TAG_SMT2;
      }
      if (!(btor_cc_smt2 (parser, ch) & BTOR_QUOTED_SYMBOL_CHAR_CLASS_SMT2))
        return !btor_perr_smt2 (
            parser, "invalid character code %d in quoted symbol", ch);
      btor_pushch_smt2 (parser, ch);
    }
  }
  else if (ch == ':')
  {
    btor_pushch_smt2 (parser, ':');
    if ((ch = btor_nextch_smt2 (parser)) == EOF)
      return !btor_perr_smt2 (parser, "unexpected end-of-file after ':'");
    if (!(btor_cc_smt2 (parser, ch) & BTOR_KEYWORD_CHAR_CLASS_SMT2))
      return !btor_perr_smt2 (
          parser, "unexpected character code %d after ':'", ch);
    btor_pushch_smt2 (parser, ch);
    while ((btor_cc_smt2 (parser, ch = btor_nextch_smt2 (parser))
            & BTOR_KEYWORD_CHAR_CLASS_SMT2))
    {
      assert (ch != EOF);
      btor_pushch_smt2 (parser, ch);
    }
    btor_savech_smt2 (parser, ch);
    btor_pushch_smt2 (parser, 0);
    if (!(node = btor_find_symbol_smt2 (parser, parser->token.start)))
    {
      node       = btor_new_node_smt2 (parser, BTOR_ATTRIBUTE_TAG_SMT2);
      node->name = btor_strdup (parser->mem, parser->token.start);
      btor_insert_symbol_smt2 (parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else if (ch == '0')
  {
    btor_pushch_smt2 (parser, '0');
    ch = btor_nextch_smt2 (parser);
    if (ch == '.')
    {
      btor_pushch_smt2 (parser, '.');
      if ((ch = btor_nextch_smt2 (parser)) == EOF)
        return !btor_perr_smt2 (parser, "unexpected end-of-file after '0.'");
      if (!(btor_cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
        return !btor_perr_smt2 (parser, "expected decimal digit after '0.'");
      btor_pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = btor_nextch_smt2 (parser);
        if (!(btor_cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
          break;
        btor_pushch_smt2 (parser, ch);
      }
    }
    btor_savech_smt2 (parser, ch);
    btor_pushch_smt2 (parser, 0);
    return BTOR_DECIMAL_CONSTANT_TAG_SMT2;
  }
  else if (cc & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2)
  {
    btor_pushch_smt2 (parser, ch);
    for (;;)
    {
      ch = btor_nextch_smt2 (parser);
      if (!(btor_cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
        break;
      btor_pushch_smt2 (parser, ch);
    }
    if (ch == '.')
    {
      btor_pushch_smt2 (parser, '.');
      if ((ch = btor_nextch_smt2 (parser)) == EOF)
      {
        btor_pushch_smt2 (parser, 0);
        return !btor_perr_smt2 (
            parser, "unexpected end-of-file after '%s'", parser->token.start);
      }
      if (!(btor_cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
      {
        btor_pushch_smt2 (parser, 0);
        return !btor_perr_smt2 (
            parser, "expected decimal digit after '%s'", parser->token.start);
      }
      btor_pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = btor_nextch_smt2 (parser);
        if (!(btor_cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
          break;
        btor_pushch_smt2 (parser, ch);
      }
    }
    btor_savech_smt2 (parser, ch);
    btor_pushch_smt2 (parser, 0);
    return BTOR_DECIMAL_CONSTANT_TAG_SMT2;
  }
  else if (cc & BTOR_SYMBOL_CHAR_CLASS_SMT2)
  {
    btor_pushch_smt2 (parser, ch);
    for (;;)
    {
      ch = btor_nextch_smt2 (parser);
      if (!(btor_cc_smt2 (parser, ch) & BTOR_SYMBOL_CHAR_CLASS_SMT2)) break;
      btor_pushch_smt2 (parser, ch);
    }
    btor_savech_smt2 (parser, ch);
    btor_pushch_smt2 (parser, 0);
    if (!strcmp (parser->token.start, "_")) return BTOR_UNDERSCORE_TAG_SMT2;
    if (!(node = btor_find_symbol_smt2 (parser, parser->token.start)))
    {
      node       = btor_new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
      node->name = btor_strdup (parser->mem, parser->token.start);
      btor_insert_symbol_smt2 (parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else
    return !btor_perr_smt2 (parser, "unexpected character code %d", ch);

  // should be dead code ...
  return !btor_perr_smt2 (parser, "internal token reading error");
}

static int
btor_read_token_smt2 (BtorSMT2Parser* parser)
{
  int res = btor_read_token_aux_smt2 (parser);
  if (parser->verbosity >= 3)
  {
    printf ("[btorsmt2] line %08d token %08x %s\n",
            parser->lineno,
            res,
            res == EOF ? "<end-of-file>"
                       : res == BTOR_INVALID_TAG_SMT2 ? "<error>"
                                                      : parser->token.start);
    fflush (stdout);
  }
  return res;
}

#if 0
static void btor_read_tokens_smt2 (BtorSMT2Parser * parser) {
  int tag;
  assert (!BTOR_INVALID_TAG_SMT2);
  while ((tag = btor_read_token_smt2 (parser)) && tag != EOF) {
    assert (!BTOR_EMPTY_STACK (parser->token));
    assert (!parser->token.top[-1]);
    if (parser->verbosity < 2) continue;
    printf ("[btorsmt2] token %08x %s\n", tag, parser->token.start);
    fflush (stdout);
  }
}
#endif

static int
btor_read_rpar_smt2 (BtorSMT2Parser* parser, const char* msg)
{
  int tag = btor_read_token_smt2 (parser);
  if (tag == EOF)
    return !btor_perr_smt2 (
        parser, "expected ')'%s at end-of-file", msg ? msg : "");
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    assert (parser->error);
    return 0;
  }
  if (tag != BTOR_RPAR_TAG_SMT2)
    return !btor_perr_smt2 (
        parser, "expected ')'%s at '%s'", msg ? msg : "", parser->token.start);
  return 1;
}

static int
btor_read_lpar_smt2 (BtorSMT2Parser* parser, const char* msg)
{
  int tag = btor_read_token_smt2 (parser);
  if (tag == EOF)
    return !btor_perr_smt2 (
        parser, "expected '('%s at end-of-file", msg ? msg : "");
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    assert (parser->error);
    return 0;
  }
  if (tag != BTOR_LPAR_TAG_SMT2)
    return !btor_perr_smt2 (
        parser, "expected '('%s at '%s'", msg ? msg : "", parser->token.start);
  return 1;
}

static int
btor_skip_sexprs (BtorSMT2Parser* parser, int initial)
{
  int tag, open = initial;
  while (open > 0)
  {
    tag = btor_read_token_smt2 (parser);
    if (tag == EOF)
    {
      if (open > 0)
        return !btor_perr_smt2 (parser, "')' missing at end-of-file");
      return 1;
    }
    if (tag == BTOR_INVALID_TAG_SMT2)
    {
      assert (parser->error);
      return 0;
    }
    else if (tag == BTOR_LPAR_TAG_SMT2)
      open++;
    else if (tag == BTOR_RPAR_TAG_SMT2)
      open--;
  }
  return 1;
}

static int
btor_read_symbol (BtorSMT2Parser* parser,
                  const char* errmsg,
                  BtorSMT2Node** resptr)
{
  int tag = btor_read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !btor_perr_smt2 (parser,
                            "expected symbol%s but reached end-of-file",
                            errmsg ? errmsg : "");
  if (tag != BTOR_SYMBOL_TAG_SMT2)
    return !btor_perr_smt2 (parser,
                            "expected symbol%s at '%s'",
                            errmsg ? errmsg : "",
                            parser->token.start);
  assert (parser->last_node->tag == BTOR_SYMBOL_TAG_SMT2);
  *resptr = parser->last_node;
  return 1;
}

static int
btor_str2int32_smt2 (BtorSMT2Parser* parser, const char* str, int* resptr)
{
  int res, ch, digit;
  const char* p;
  res = 0;
  assert (sizeof (int) == 4);
  for (p = str; (ch = *p); p++)
  {
    if (res > INT_MAX / 10)
    INVALID:
      return !btor_perr_smt2 (parser, "invalid 32-bit integer '%s'", str);
    assert ('0' <= ch && ch <= '9');
    res *= 10;
    digit = ch - '0';
    if (INT_MAX - digit < res) goto INVALID;
    res += digit;
  }
  *resptr = res;
  return 1;
}

static BtorSMT2Item*
btor_push_item_smt2 (BtorSMT2Parser* parser, BtorSMT2Tag tag)
{
  BtorSMT2Item item;
  BTOR_CLR (&item);
  item.lineno = parser->lineno;
  item.tag    = tag;
  BTOR_PUSH_STACK (parser->mem, parser->work, item);
  return &BTOR_TOP_STACK (parser->work);
}

static BtorSMT2Item*
btor_last_lpar_smt2 (BtorSMT2Parser* parser)
{
  BtorSMT2Item* p = parser->work.top;
  do
  {
    if (p-- == parser->work.start) return 0;
  } while (p->tag != BTOR_LPAR_TAG_SMT2);
  return p;
}

#define BTOR_NODE_TAG_CLASS_MASK_SMT2                         \
  (BTOR_RESERVED_TAG_CLASS_SMT2 | BTOR_COMMAND_TAG_CLASS_SMT2 \
   | BTOR_KEYWORD_TAG_CLASS_SMT2 | BTOR_CORE_TAG_CLASS_SMT2   \
   | BTOR_ARRAY_TAG_CLASS_SMT2 | BTOR_BITVEC_TAG_CLASS_SMT2   \
   | BTOR_LOGIC_TAG_CLASS_SMT2)

static int
btor_item_with_node_smt2 (BtorSMT2Item* item)
{
  if (item->tag == BTOR_SYMBOL_TAG_SMT2) return 1;
  if (item->tag == BTOR_ATTRIBUTE_TAG_SMT2) return 1;
  if (item->tag & BTOR_NODE_TAG_CLASS_MASK_SMT2) return 1;
  return 0;
}

static const char*
btor_item2str_smt2 (BtorSMT2Item* item)
{
  if (btor_item_with_node_smt2 (item))
  {
    assert (item->node);
    assert (item->node->name);
    return item->node->name;
  }
  else if (item->tag & BTOR_CONSTANT_TAG_CLASS_SMT2)
  {
    assert (item->str);
    return item->str;
  }
  else
    return "<non-printable-item>";
}

static int
btor_parse_term_smt2 (BtorSMT2Parser* parser, BtorExp** resptr, int* linenoptr)
{
  int tag, open = 0;
  BtorSMT2Item* p;
  BtorExp* res;
  assert (BTOR_EMPTY_STACK (parser->work));
  do
  {
    tag = btor_read_token_smt2 (parser);
    if (tag == BTOR_INVALID_TAG_SMT2) return 0;
    if (tag == EOF)
    {
      p = btor_last_lpar_smt2 (parser);
      if (!p)
        return !btor_perr_smt2 (parser,
                                "expected term but reached end-of-file");
      return !btor_perr_smt2 (
          parser,
          "unexpected end-of-file since '(' at line %d still open",
          p->lineno);
    }
    if (tag == BTOR_RPAR_TAG_SMT2)
    {
      assert (open > 0);
      open--;
    }
    else
    {
      p = btor_push_item_smt2 (parser, tag);
      if (tag == BTOR_LPAR_TAG_SMT2)
        open++;
      else if (btor_item_with_node_smt2 (p))
      {
        p->node = parser->last_node;
        if (tag & BTOR_COMMAND_TAG_CLASS_SMT2)
          return !btor_perr_smt2 (
              parser, "unexpected command '%s'", p->node->name);
        if (tag & BTOR_KEYWORD_TAG_CLASS_SMT2)
          return !btor_perr_smt2 (
              parser, "unexpected keyword '%s'", p->node->name);
        if (!parser->binding && tag == BTOR_SYMBOL_TAG_SMT2)
          return !btor_perr_smt2 (
              parser, "undeclared function '%s'", p->node->name);
        if (tag == BTOR_TRUE_TAG_SMT2)
        {
          p->tag  = BTOR_EXP_TAG_SMT2;
          p->node = 0;
          p->exp  = btor_true_exp (parser->btor);
        }
        else if (tag == BTOR_FALSE_TAG_SMT2)
        {
          p->tag  = BTOR_EXP_TAG_SMT2;
          p->node = 0;
          p->exp  = btor_false_exp (parser->btor);
        }
      }
      else if (tag & BTOR_CONSTANT_TAG_CLASS_SMT2)
        p->str = btor_strdup (parser->mem, parser->token.start);
    }
  } while (open);
  if (BTOR_COUNT_STACK (parser->work) != 1)
  {
    parser->perrlineno = p->lineno;
    // TODO remove?
    return !btor_perr_smt2 (parser,
                            "internal parse error: worker stack of size %d",
                            BTOR_COUNT_STACK (parser->work));
  }
  p = parser->work.start;
  if (p->tag != BTOR_EXP_TAG_SMT2)
  {
    parser->perrlineno = p->lineno;
    // TODO more specific ...
    return !btor_perr_smt2 (
        parser,
        "internal parse error: failed to parse term at '%s'",
        btor_item2str_smt2 (p));
  }
  res        = btor_copy_exp (parser->btor, p->exp);
  *linenoptr = p->lineno;
  btor_release_work_smt2 (parser);
  *resptr = res;
  return 1;
}

static int
btor_parse_bitvec_sort_smt2 (BtorSMT2Parser* parser, int skiplu, int* resptr)
{
  int tag, res;
  if (!skiplu)
  {
    if (!btor_read_lpar_smt2 (parser, 0)) return 0;
    tag = btor_read_token_smt2 (parser);
    if (tag == BTOR_INVALID_TAG_SMT2) return 0;
    if (tag == EOF)
      return !btor_perr_smt2 (parser, "expected '_' but reached end-of-file");
  }
  tag = btor_read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !btor_perr_smt2 (parser,
                            "expected 'BitVec' but reached end-of-file");
  if (tag != BTOR_BITVEC_TAG_SMT2)
    return !btor_perr_smt2 (
        parser, "expected 'BitVec' at '%s'", parser->token.start);
  tag = btor_read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !btor_perr_smt2 (parser,
                            "expected bit-width but reached end-of-file");
  if (tag != BTOR_DECIMAL_CONSTANT_TAG_SMT2)
    return !btor_perr_smt2 (
        parser, "expected bit-width at '%s'", parser->token.start);
  assert (parser->token.start[0] != '-');
  if (parser->token.start[0] == '0')
  {
    assert (!parser->token.start[1]);
    return !btor_perr_smt2 (parser, "invalid zero bit-width");
  }
  if (strchr (parser->token.start, '.'))
    return !btor_perr_smt2 (
        parser, "invalid floating point bit-width '%s'", parser->token.start);
  res = 0;
  if (!btor_str2int32_smt2 (parser, parser->token.start, &res)) return 0;
  *resptr = res;
  btor_msg_smt2 (parser, 3, "parsed bit-vector sort of width %d", res);
  return btor_read_rpar_smt2 (parser, " to close bit-vector sort");
}

static int
btor_declare_fun_smt2 (BtorSMT2Parser* parser)
{
  BtorSMT2Node* fun;
  int tag;
  fun = 0;
  if (!btor_read_symbol (parser, " after 'declare-fun'", &fun)) return 0;
  assert (fun && fun->tag == BTOR_SYMBOL_TAG_SMT2);
  if (fun->sort.tag != BTOR_UNDEFINED_SORT_SMT2)
    return !btor_perr_smt2 (parser,
                            "symbol '%s' already defined at line %d",
                            fun->name,
                            fun->lineno);
  fun->lineno = parser->lineno;
  if (!btor_read_lpar_smt2 (parser, " after function name")) return 0;
  if (!btor_read_rpar_smt2 (parser, " after '('")) return 0;
  tag = btor_read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !btor_perr_smt2 (parser,
                            "reached end-of-file expecting '(' or 'Bool'");
  if (tag == BTOR_BOOL_TAG_SMT2)
  {
    fun->sort.width = 1;
    goto BITVEC;
  }
  else if (tag != BTOR_LPAR_TAG_SMT2)
    return !btor_perr_smt2 (
        parser, "expected '(' or 'Bool' at '%s'", parser->token.start);
  tag = btor_read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !btor_perr_smt2 (parser,
                            "reached end-of-file expecting '_' or 'Array'");
  if (tag == BTOR_UNDERSCORE_TAG_SMT2)
  {
    if (!btor_parse_bitvec_sort_smt2 (parser, 1, &fun->sort.width)) return 0;
  BITVEC:
    fun->sort.tag = BTOR_BITVEC_SORT_SMT2;
    fun->exp      = btor_var_exp (parser->btor, fun->sort.width, fun->name);
    btor_msg_smt2 (parser,
                   2,
                   "declared '%s' as bit-vector of width %d at line %d",
                   fun->name,
                   fun->sort.width,
                   fun->lineno);
  }
  else if (tag == BTOR_ARRAY_TAG_SMT2)
  {
    if (!btor_parse_bitvec_sort_smt2 (parser, 0, &fun->sort.domain)) return 0;
    if (!btor_parse_bitvec_sort_smt2 (parser, 0, &fun->sort.width)) return 0;
    if (!btor_read_rpar_smt2 (parser, " after element sort")) return 0;
    fun->sort.tag = BTOR_ARRAY_SORT_SMT2;
    fun->exp      = btor_array_exp (
        parser->btor, fun->sort.width, fun->sort.domain, fun->name);
    btor_msg_smt2 (
        parser,
        2,
        "declared bit-vector array '%s' index element width %d %d at line %d",
        fun->name,
        fun->sort.domain,
        fun->sort.width,
        fun->lineno);
    parser->need_arrays = 1;
  }
  else
    return !btor_perr_smt2 (
        parser, "expected '_' or 'Array' at '%s'", parser->token.start);
  (void) btor_copy_exp (parser->btor, fun->exp);
  BTOR_PUSH_STACK (parser->mem, parser->inputs, fun->exp);
  return btor_read_rpar_smt2 (parser, " for closing declaration");
}

static int
btor_set_info_smt2 (BtorSMT2Parser* parser)
{
  int tag = btor_read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !btor_perr_smt2 (parser, "unexpected end-of-file after 'set-info'");
  if (tag == BTOR_RPAR_TAG_SMT2)
    return !btor_perr_smt2 (parser, "keyword after 'set-info' missing");
  if (tag == BTOR_STATUS_TAG_SMT2)
  {
    if ((tag = btor_read_token_smt2 (parser)) == BTOR_INVALID_TAG_SMT2)
      return 0;
    if (tag == EOF)
      return !btor_perr_smt2 (parser, "unexpected end-of-file after ':status'");
    if (tag == BTOR_RPAR_TAG_SMT2)
      return !btor_perr_smt2 (parser, "value after ':status' missing");
    if (tag != BTOR_SYMBOL_TAG_SMT2)
    INVALID_STATUS_VALUE:
      return !btor_perr_smt2 (
          parser, "invalid value '%s' after ':status'", parser->token.start);
    if (!strcmp (parser->token.start, "sat"))
      parser->res->status = BTOR_PARSE_SAT_STATUS_SAT;
    else if (!strcmp (parser->token.start, "unsat"))
      parser->res->status = BTOR_PARSE_SAT_STATUS_UNSAT;
    else if (!strcmp (parser->token.start, "unknown"))
      parser->res->status = BTOR_PARSE_SAT_STATUS_UNKNOWN;
    else
      goto INVALID_STATUS_VALUE;

    btor_msg_smt2 (parser, 2, "parsed status %s", parser->token.start);
    return btor_read_rpar_smt2 (parser, " after 'set-logic'");
  }
  return btor_skip_sexprs (parser, 1);
}

static int
btor_read_command_smt2 (BtorSMT2Parser* parser)
{
  int tag, lineno = 0;
  BtorExp* exp = 0;
  tag          = btor_read_token_smt2 (parser);
  if (tag == EOF || tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag != BTOR_LPAR_TAG_SMT2)
    return !btor_perr_smt2 (
        parser, "expected '(' at '%s'", parser->token.start);
  tag = btor_read_token_smt2 (parser);
  if (tag == EOF)
    return !btor_perr_smt2 (parser, "unexpected end-of-file after '('");
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    assert (parser->error);
    return 0;
  }
  if (!(tag & BTOR_COMMAND_TAG_CLASS_SMT2))
    return !btor_perr_smt2 (
        parser, "expected command at '%s'", parser->token.start);
  switch (tag)
  {
    case BTOR_SET_LOGIC_TAG_SMT2:
      tag = btor_read_token_smt2 (parser);
      if (tag == EOF)
        return !btor_perr_smt2 (parser,
                                "unexpected end-of-file after 'set-logic'");
      if (tag == BTOR_INVALID_TAG_SMT2)
      {
        assert (parser->error);
        return 0;
      }
      if (!(tag & BTOR_LOGIC_TAG_CLASS_SMT2))
        return !btor_perr_smt2 (
            parser, "unsupported logic '%s'", parser->token.start);
      if (tag == BTOR_QF_BV_TAG_SMT2)
        parser->res->logic = BTOR_LOGIC_QF_BV;
      else
      {
        assert (tag == BTOR_QF_AUFBV_TAG_SMT2 || tag == BTOR_QF_UFBV_TAG_SMT2
                || tag == BTOR_QF_ABV_TAG_SMT2);
        parser->res->logic = BTOR_LOGIC_QF_AUFBV;
      }
      btor_msg_smt2 (parser, 2, "logic %s", parser->token.start);
      if (!btor_read_rpar_smt2 (parser, " after logic")) return 0;
      if (parser->set_logic_commands++)
        btor_msg_smt2 (parser, 0, "WARNING additional 'set-logic' command");
      break;

    case BTOR_CHECK_SAT_TAG_SMT2:
      if (!btor_read_rpar_smt2 (parser, " after 'check-sat'")) return 0;
      if (parser->check_sat_commands++)
        btor_msg_smt2 (parser, 0, "WARNING additional 'check-sat' command");
      break;

    case BTOR_DECLARE_FUN_TAG_SMT2:
      if (!btor_declare_fun_smt2 (parser)) return 0;
      break;

    case BTOR_ASSERT_TAG_SMT2:
      if (!btor_parse_term_smt2 (parser, &exp, &lineno)) return 0;
      BTOR_PUSH_STACK (parser->mem, parser->outputs, exp);
      if (btor_is_array_exp (parser->btor, exp))
      {
        parser->perrlineno = lineno;
        return !btor_perr_smt2 (
            parser, "assert argument is an array and not a formula");
      }
      if (btor_get_exp_len (parser->btor, exp) != 1)
      {
        parser->perrlineno = lineno;
        return !btor_perr_smt2 (parser,
                                "assert argument is a bit-vector of length %d",
                                btor_get_exp_len (parser->btor, exp));
      }
      if (!btor_read_rpar_smt2 (parser, " after assert term")) return 0;
      assert (!parser->error);
      parser->assert_commands++;
      break;

    case BTOR_EXIT_TAG_SMT2:
      if (!btor_read_rpar_smt2 (parser, " after 'exit'")) return 0;
      if (parser->exit_commands++)
        btor_msg_smt2 (parser, 0, "WARNING additional 'exit' command");
      break;

    case BTOR_SET_INFO_TAG_SMT2:
      if (!btor_set_info_smt2 (parser)) return 0;
      break;

    default:
      return !btor_perr_smt2 (
          parser, "unsupported command '%s'", parser->token.start);
      break;
  }
  return 1;
}

static const char*
btor_parse_smt2_parser (BtorSMT2Parser* parser,
                        BtorCharStack* prefix,
                        FILE* file,
                        const char* name,
                        BtorParseResult* res)
{
  parser->name    = btor_strdup (parser->mem, name);
  parser->nprefix = 0;
  parser->prefix  = prefix;
  parser->lineno  = 1;
  parser->file    = file;
  parser->saved   = 0;
  BTOR_CLR (res);
  parser->res = res;
  while (btor_read_command_smt2 (parser))
    ;
  if (parser->error) return parser->error;
  if (!parser->set_logic_commands)
    btor_msg_smt2 (
        parser, 0, "WARNING 'set-logic' command missing in '%s'", parser->name);
  if (!parser->check_sat_commands)
    btor_msg_smt2 (
        parser, 0, "WARNING 'check-sat' command missing in '%s'", parser->name);
  if (!parser->assert_commands)
    btor_msg_smt2 (
        parser, 0, "WARNING no 'assert' command in '%s'", parser->name);
  parser->res->inputs   = parser->inputs.start;
  parser->res->outputs  = parser->outputs.start;
  parser->res->ninputs  = BTOR_COUNT_STACK (parser->inputs);
  parser->res->noutputs = BTOR_COUNT_STACK (parser->outputs);
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
