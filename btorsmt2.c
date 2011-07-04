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

typedef enum BtorSMT2TagClass
{
  BTOR_CLASS_BITS_SMT2 = 6,
  BTOR_CLASS_SIZE_SMT2 = (1 << BTOR_CLASS_BITS_SMT2),
  BTOR_CLASS_MASK_SMT2 = (BTOR_CLASS_SIZE_SMT2 - 1),

  BTOR_SYMBOL_TAG_CLASS_SMT2   = 0,
  BTOR_CONSTANT_TAG_CLASS_SMT2 = (BTOR_CLASS_SIZE_SMT2 << 0),
  BTOR_RESERVED_TAG_CLASS_SMT2 = (BTOR_CLASS_SIZE_SMT2 << 1),
  BTOR_COMMAND_TAG_CLASS_SMT2  = (BTOR_CLASS_SIZE_SMT2 << 2),
  BTOR_INSERT_TAG_CLASS_SMT2   = (BTOR_CLASS_SIZE_SMT2 << 3),
  BTOR_CORE_TAG_CLASS_SMT2     = (BTOR_CLASS_SIZE_SMT2 << 4),
  BTOR_ARRAY_TAG_CLASS_SMT2    = (BTOR_CLASS_SIZE_SMT2 << 5),
  BTOR_BITVEC_TAG_CLASS_SMT2   = (BTOR_CLASS_SIZE_SMT2 << 6),
} BtorSMT2TagClass;

typedef enum BtorSMT2Tag
{

  BTOR_PARENT_TAG_SMT2 = 0 + BTOR_SYMBOL_TAG_CLASS_SMT2,
  BTOR_SYMBOL_TAG_SMT2 = 1 + BTOR_SYMBOL_TAG_CLASS_SMT2,

  BTOR_NUMERAL_CONSTANT_TAG_SMT2     = 0 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_DECIMAL_CONSTANT_TAG_SMT2     = 1 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2 = 2 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_BINARY_CONSTANT_TAG_SMT2      = 3 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_STRING_CONSTANT_TAG_SMT2      = 4 + BTOR_CONSTANT_TAG_CLASS_SMT2,

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

  BTOR_ALL_STATISTICS_TAG_SMT2         = 0 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_AUTHORS_TAG_SMT2                = 1 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_AXIOMS_TAG_SMT2                 = 2 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_CHAINABLE_TAG_SMT2              = 3 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_DEFINITION_TAG_SMT2             = 4 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_DIAG_OUTPUT_CHANNEL_TAG_SMT2    = 5 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_ERROR_BEHAVIOR_TAG_SMT2         = 6 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_EXPAND_DEFINITIONS_TAG_SMT2     = 7 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_EXTENSIONS_TAG_SMT2             = 8 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_FUNS_TAG_SMT2                   = 9 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_FUNS_DESCRIPTION_TAG_SMT2       = 10 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_INTERACTIVE_MODE_TAG_SMT2       = 11 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_LANGUAGE_TAG_SMT2               = 12 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_LEFT_ASSOC_TAG_SMT2             = 13 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_NAME_TAG_SMT2                   = 14 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_NAMED_TAG_SMT2                  = 15 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_NOTES_TAG_SMT2                  = 16 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_PRINT_SUCCESS_TAG_SMT2          = 17 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_PRODUCE_ASSIGNMENTS_TAG_SMT2    = 18 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_PRODUCE_MODELS_TAG_SMT2         = 19 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_PRODUCE_PROOFS_TAG_SMT2         = 20 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_PRODUCE_UNSAT_CORES_TAG_SMT2    = 21 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_RANDOM_SEED_TAG_SMT2            = 22 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_REASON_UNKNOWN_TAG_SMT2         = 23 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_REGULAR_OUTPUT_CHANNEL_TAG_SMT2 = 24 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_RIGHT_ASSOC_TAG_SMT2            = 25 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_SORTS_TAG_SMT2                  = 26 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_SORTS_DESCRIPTION_TAG_SMT2      = 27 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_STATUS_TAG_SMT2                 = 28 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_THEORIES_TAG_SMT2               = 29 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_VALUES_TAG_SMT2                 = 30 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_VERBOSITY_TAG_SMT2              = 31 + BTOR_INSERT_TAG_CLASS_SMT2,
  BTOR_VERSION_TAG_SMT2                = 32 + BTOR_INSERT_TAG_CLASS_SMT2,

  BTOR_TRUE_TAG_SMT2     = 0 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_FALSE_TAG_SMT2    = 1 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_NOT_TAG_SMT2      = 2 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_IMPLIES_TAG_SMT2  = 3 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_AND_TAG_SMT2      = 4 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_OR_TAG_SMT2       = 5 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_XOR_TAG_SMT2      = 6 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_EQUAL_TAG_SMT2    = 7 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_DISTINCT_TAG_SMT2 = 8 + BTOR_CORE_TAG_CLASS_SMT2,
  BTOR_ITE_TAG_SMT2      = 9 + BTOR_CORE_TAG_CLASS_SMT2,

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

} BtorSMT2Tag;

typedef struct BtorSMT2Node
{
  BtorSMT2Tag tag;
  int lineno;
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

static const char* btor_printable_ascii_chars_smt2 =
    "!\"#$%&'()*+,-./"
    "0123456789"
    ":;<=>?@"
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "[\\]^_`"
    "abcdefghijklmnopqrstuvwxyz"
    "{|}~";

static const char* btor_letters_smt2 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz";

static const char* btor_decimal_digits_smt2 = "0123456789";

static const char* btor_hexadecimal_digits_smt2 = "0123456789abcdefABCDEF";

static const char* btor_extra_symbol_chars_smt2 = "+-/*=%?!.$~&^<>@";

static const char* btor_extra_keyword_chars_smt2 = "+-/*=%?!.$~&^<>@";

typedef enum BtorSMT2CharClass
{
  BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2     = (1 << 0),
  BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2 = (1 << 1),
  BTOR_STRING_CHAR_CLASS_SMT2            = (1 << 2),
  BTOR_SYMBOL_CHAR_CLASS_SMT2            = (1 << 3),
  BTOR_QUOTED_SYMBOL_CHAR_CLASS_SMT2     = (1 << 4),
  BTOR_INSERT_CHAR_CLASS_SMT2            = (1 << 5),
} BtorSMT2CharClass;

typedef struct BtorSMT2Parser
{
  Btor* btor;
  BtorMemMgr* mem;
  int verbosity, incremental;
  char* name;
  int lineno;
  FILE* file;
  int nprefix;
  BtorCharStack* prefix;
  char* error;
  struct
  {
    unsigned size, count;
    BtorSMT2Node** table;
  } symbol;
  unsigned char cc[256];
  BtorCharStack buffer;
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
  if (parser->symbol.size >= parser->symbol.count)
    btor_enlarge_symbol_table_smt2 (parser);
  p = btor_symbol_position_smt2 (parser, symbol->name);
  assert (!*p);
  *p = symbol;
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
    cc[(unsigned char) *p] |= BTOR_INSERT_CHAR_CLASS_SMT2;
  for (p = btor_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_INSERT_CHAR_CLASS_SMT2;
  for (p = btor_extra_keyword_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BTOR_INSERT_CHAR_CLASS_SMT2;
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

  return res;
}

static void
btor_delete_smt2_parser (BtorSMT2Parser* parser)
{
  BtorMemMgr* mem = parser->mem;
  btor_release_symbols_smt2 (parser);
  if (parser->name) btor_freestr (mem, parser->name);
  if (parser->error) btor_freestr (mem, parser->error);
  BTOR_RELEASE_STACK (mem, parser->buffer);
  BTOR_DELETE (mem, parser);
}

static const char*
btor_parse_smt2_parser (BtorSMT2Parser* parser,
                        BtorCharStack* prefix,
                        FILE* file,
                        const char* name,
                        BtorParseResult* res)
{
  (void) res;
  parser->name    = btor_strdup (parser->mem, name);
  parser->nprefix = 0;
  parser->prefix  = prefix;
  parser->lineno  = 1;
  parser->file    = file;
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
