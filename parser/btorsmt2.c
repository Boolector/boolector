/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2014 Armin Biere.
 *  Copyright (C) 2013-2016 Aina Niemetz.
 *  Copyright (C) 2013-2016 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsmt2.h"
#include "btorconst.h"
#include "btorcore.h"
#include "btormsg.h"
#include "btoropt.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>

//#define BTOR_USE_CLONE_SCOPES

/*------------------------------------------------------------------------*/

void boolector_print_value (
    Btor *btor, BoolectorNode *node, char *node_str, char *format, FILE *file);

/*------------------------------------------------------------------------*/

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
  BTOR_INVALID_TAG_SMT2       = 0 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_PARENT_TAG_SMT2        = 1 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_LPAR_TAG_SMT2          = 2 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_RPAR_TAG_SMT2          = 3 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_SYMBOL_TAG_SMT2        = 4 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_ATTRIBUTE_TAG_SMT2     = 5 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_EXP_TAG_SMT2           = 6 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_LETBIND_TAG_SMT2       = 7 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_PARLETBINDING_TAG_SMT2 = 8 + BTOR_OTHER_TAG_CLASS_SMT2,

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
  BTOR_GET_MODEL_TAG_SMT2      = 19 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_MODEL_TAG_SMT2          = 20 + BTOR_COMMAND_TAG_CLASS_SMT2,

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
  /* ---------------------------------------------------------------------- */

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
  /* Z3 extensions */
  BTOR_BVREDOR_TAG_SMT2          = 36 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_BVREDAND_TAG_SMT2         = 37 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_EXT_ROTATE_LEFT_TAG_SMT2  = 38 + BTOR_BITVEC_TAG_CLASS_SMT2,
  BTOR_EXT_ROTATE_RIGHT_TAG_SMT2 = 39 + BTOR_BITVEC_TAG_CLASS_SMT2,

  BTOR_AUFLIA_TAG_SMT2    = 0 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_AUFLIRA_TAG_SMT2   = 1 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_AUFNIRA_TAG_SMT2   = 2 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LRA_TAG_SMT2       = 3 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_ABV_TAG_SMT2    = 4 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_AUFBV_TAG_SMT2  = 5 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_AUFLIA_TAG_SMT2 = 6 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_AX_TAG_SMT2     = 7 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_BV_TAG_SMT2     = 8 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_IDL_TAG_SMT2    = 9 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_LIA_TAG_SMT2    = 10 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_LRA_TAG_SMT2    = 11 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_NIA_TAG_SMT2    = 12 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_NRA_TAG_SMT2    = 13 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_RDL_TAG_SMT2    = 14 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UF_TAG_SMT2     = 15 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UFBV_TAG_SMT2   = 16 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UFIDL_TAG_SMT2  = 17 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UFLIA_TAG_SMT2  = 18 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UFLRA_TAG_SMT2  = 19 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_QF_UFNRA_TAG_SMT2  = 20 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_UFLRA_TAG_SMT2     = 21 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_UFNIA_TAG_SMT2     = 22 + BTOR_LOGIC_TAG_CLASS_SMT2,

} BtorSMT2Tag;

typedef struct BtorSMT2Coo
{
  int x, y;
} BtorSMT2Coo;

typedef struct BtorSMT2Node
{
  BtorSMT2Tag tag;
  unsigned bound : 1;
  unsigned sort : 1;
  unsigned scope_level;
  BtorSMT2Coo coo;
  char *name;
  BoolectorNode *exp;
  BoolectorSort sort_alias;
  struct BtorSMT2Node *next;
} BtorSMT2Node;

typedef struct BtorSMT2Item
{
  BtorSMT2Tag tag;
  BtorSMT2Coo coo;
  union
  {
    int num;
    struct
    {
      int hi, lo;
    };
  };
  union
  {
    BtorSMT2Node *node;
    BoolectorNode *exp;
    char *str;
  };
} BtorSMT2Item;

BTOR_DECLARE_STACK (BtorSMT2Item, BtorSMT2Item);
BTOR_DECLARE_STACK (BtorPtr, Btor *);
BTOR_DECLARE_STACK (BoolectorSort, BoolectorSort);

/*------------------------------------------------------------------------*/

static const char *btor_printable_ascii_chars_smt2 =
    "!\"#$%&'()*+,-./"
    "0123456789"
    ":;<=>?@"
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "[\\]^_`"
    "abcdefghijklmnopqrstuvwxyz"
    "{|}~"
    " \t\r\n";

static const char *btor_letters_smt2 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz";

static const char *btor_decimal_digits_smt2 = "0123456789";

static const char *btor_hexadecimal_digits_smt2 = "0123456789abcdefABCDEF";

static const char *btor_extra_symbol_chars_smt2 = "+-/*=%?!.$_~&^<>@";

static const char *btor_extra_keyword_chars_smt2 = "+-/*=%?!.$_~&^<>@";

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
  Btor *btor;
  BtorMemMgr *mem;
  int verbosity, incremental, model, need_functions, interactive, done;
  int saved, savedch;
  int last_end_of_line_ycoo;
  int nprefix;
  int binding, expecting_let_body;
  char *error;
  unsigned char cc[256];
  FILE *infile;
  char *infile_name;
  FILE *outfile;
  BtorCharStack *prefix, token;
  BoolectorNodePtrStack outputs, inputs;
  BoolectorSortStack sorts;
  BtorUIntStack outputs_trail, inputs_trail;
  BtorSMT2ItemStack work;
  BtorSMT2Coo coo, lastcoo, nextcoo, perrcoo;
  BtorSMT2Node *last_node;
  BtorParseResult *res;
#ifdef BTOR_USE_CLONE_SCOPES
  BtorPtrStack btor_scopes;
#endif
  BoolectorNodePtrStack assumptions;
  BtorUIntStack assumptions_trail;
  unsigned num_scopes;
  unsigned cur_scope_num_terms;
  struct
  {
    unsigned size, count;
    BtorSMT2Node **table;
  } symbol;
  struct
  {
    int all, set_logic, asserts, check_sat, exits, model;
  } commands;

  /* SMT2 options */
  bool print_success;
} BtorSMT2Parser;

static int
xcoo_smt2 (BtorSMT2Parser *parser)
{
  return parser->perrcoo.x ? parser->perrcoo.x : parser->coo.x;
}

static int
ycoo_smt2 (BtorSMT2Parser *parser)
{
  return parser->perrcoo.x ? parser->perrcoo.y : parser->coo.y;
}

static char *
perr_smt2 (BtorSMT2Parser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;
  if (!parser->error)
  {
    va_start (ap, fmt);
    bytes = btor_parse_error_message_length (parser->infile_name, fmt, ap);
    va_end (ap);
    va_start (ap, fmt);
    parser->error = btor_parse_error_message (parser->mem,
                                              parser->infile_name,
                                              xcoo_smt2 (parser),
                                              ycoo_smt2 (parser),
                                              fmt,
                                              ap,
                                              bytes);
    va_end (ap);
  }
  return parser->error;
}

static void
savech_smt2 (BtorSMT2Parser *parser, char ch)
{
  assert (!parser->saved);
  parser->saved   = 1;
  parser->savedch = ch;
  if (ch == '\n')
  {
    assert (parser->nextcoo.x > 1);
    parser->nextcoo.x--;
    parser->nextcoo.y = parser->last_end_of_line_ycoo;
  }
  else
  {
    assert (parser->nextcoo.y > 1);
    parser->nextcoo.y--;
  }
}

static char *
cerr_smt2 (BtorSMT2Parser *parser, const char *p, int ch, const char *s)
{
  const char *d, *n;

  if (!parser->saved) savech_smt2 (parser, ch);
  parser->perrcoo = parser->nextcoo;

  if (ch == EOF)
    return perr_smt2 (
        parser, "%s end-of-file%s%s", p, (s ? " " : ""), (s ? s : ""));
  if (isprint (ch) && ch != '\\')
    return perr_smt2 (
        parser, "%s character '%c'%s%s", p, ch, (s ? " " : ""), (s ? s : ""));

  switch (ch)
  {
    case '\\':
      n = "backslash";
      d = "\\\\";
      break;
    case '\n':
      n = "new line";
      d = "\\n";
      break;
    case '\t':
      n = "horizontal tabulator";
      d = "\\t";
      break;
    case '\r':
      n = "carriage return";
      d = "\\r";
      break;
    default:
      n = "character";
      d = 0;
      break;
  }

  if (d)
    return perr_smt2 (
        parser, "%s %s '%s'%s%s", p, n, d, (s ? " " : ""), (s ? s : ""));

  return perr_smt2 (parser,
                    "%s (non-printable) character (code %d)%s%s",
                    p,
                    ch,
                    (s ? " " : ""),
                    (s ? s : ""));
}

static unsigned btor_primes_smt2[] = {
    1000000007u, 2000000011u, 3000000019u, 4000000007u};

#define BTOR_NPRIMES_SMT2 (sizeof btor_primes_smt2 / sizeof *btor_primes_smt2)

static unsigned
hash_name_smt2 (BtorSMT2Parser *parser, const char *name)
{
  unsigned res = 0, i = 0;
  unsigned char ch;
  const char *p;
  for (p = name; (ch = *p); p++)
  {
    res += ch;
    res *= btor_primes_smt2[i++];
    if (i == BTOR_NPRIMES_SMT2) i = 0;
  }
  return res & (parser->symbol.size - 1);
}

static BtorSMT2Node **
symbol_position_smt2 (BtorSMT2Parser *parser, const char *name)
{
  unsigned h = hash_name_smt2 (parser, name);
  BtorSMT2Node **p, *s;
  for (p = parser->symbol.table + h; (s = *p) && strcmp (s->name, name);
       p = &s->next)
    ;
  return p;
}

static int
nextch_smt2 (BtorSMT2Parser *parser)
{
  int res;
  if (parser->saved)
    res = parser->savedch, parser->saved = 0;
  else if (parser->prefix
           && parser->nprefix < BTOR_COUNT_STACK (*parser->prefix))
    res = parser->prefix->start[parser->nprefix++];
  else
    res = getc (parser->infile);
  if (res == '\n')
  {
    parser->nextcoo.x++;
    assert (parser->nextcoo.x > 0);
    parser->last_end_of_line_ycoo = parser->nextcoo.y;
    parser->nextcoo.y             = 1;
  }
  else
    parser->nextcoo.y++, assert (parser->nextcoo.y > 0);
  return res;
}

static void
enlarge_symbol_table_smt2 (BtorSMT2Parser *parser)
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
      h       = hash_name_smt2 (parser, p->name);
      p->next = *(q = parser->symbol.table + h);
      *q      = p;
    }
  BTOR_DELETEN (parser->mem, old_table, old_size);
}

static void
insert_symbol_smt2 (BtorSMT2Parser *parser, BtorSMT2Node *symbol)
{
  BtorSMT2Node **p;
  if (parser->symbol.size <= parser->symbol.count)
    enlarge_symbol_table_smt2 (parser);
  p = symbol_position_smt2 (parser, symbol->name);
  assert (!*p);
  *p = symbol;
  parser->symbol.count++;
  assert (parser->symbol.count > 0);
}

static BtorSMT2Node *
find_symbol_smt2 (BtorSMT2Parser *parser, const char *name)
{
  return *symbol_position_smt2 (parser, name);
}

static BtorSMT2Node *
new_node_smt2 (BtorSMT2Parser *parser, BtorSMT2Tag tag)
{
  BtorSMT2Node *res;
  BTOR_NEW (parser->mem, res);
  BTOR_CLR (res);
  res->tag = tag;
#ifdef BTOR_USE_CLONE_SCOPES
  res->scope_level = BTOR_COUNT_STACK (parser->btor_scopes);
#else
  res->scope_level = BTOR_COUNT_STACK (parser->assumptions_trail);
#endif
  return res;
}

static void
release_symbol_smt2 (BtorSMT2Parser *parser, BtorSMT2Node *symbol)
{
  assert (symbol->tag != BTOR_PARENT_TAG_SMT2);
  if (symbol->exp) boolector_release (parser->btor, symbol->exp);
  btor_freestr (parser->mem, symbol->name);
  BTOR_DELETE (parser->mem, symbol);
}

static void
remove_symbol_smt2 (BtorSMT2Parser *parser, BtorSMT2Node *symbol)
{
  BtorSMT2Node **p;
  p = symbol_position_smt2 (parser, symbol->name);
  assert (*p == symbol);
  *p = symbol->next;
  release_symbol_smt2 (parser, symbol);
  assert (parser->symbol.count > 0);
  parser->symbol.count--;
}

static void
release_symbols_smt2 (BtorSMT2Parser *parser)
{
  BtorSMT2Node *p, *next;
  unsigned i;
  for (i = 0; i < parser->symbol.size; i++)
    for (p = parser->symbol.table[i]; p; p = next)
      next = p->next, release_symbol_smt2 (parser, p);
  BTOR_DELETEN (parser->mem, parser->symbol.table, parser->symbol.size);
}

static void
release_item_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *item)
{
  if (item->tag == BTOR_EXP_TAG_SMT2)
  {
    boolector_release (parser->btor, item->exp);
  }
  else if (item->tag & BTOR_CONSTANT_TAG_CLASS_SMT2)
    btor_freestr (parser->mem, item->str);
}

static unsigned
get_current_formula_size (BtorSMT2Parser *parser)
{
  return parser->btor->bv_vars->count + parser->btor->ufs->count
         + parser->btor->nodes_unique_table.num_elements;
}

static void
open_new_scope (BtorSMT2Parser *parser)
{
  double start;
  start = btor_time_stamp ();

  parser->num_scopes++;
  BTOR_PUSH_STACK (parser->mem,
                   parser->assumptions_trail,
                   BTOR_COUNT_STACK (parser->assumptions));
  BTOR_PUSH_STACK (
      parser->mem, parser->inputs_trail, BTOR_COUNT_STACK (parser->inputs));
  parser->cur_scope_num_terms = get_current_formula_size (parser);

  BTOR_MSG (parser->btor->msg,
            2,
            "opened new scope at level %d in %.3f seconds",
            BTOR_COUNT_STACK (parser->assumptions_trail) - 1,
            btor_time_stamp () - start);
}

static void
close_current_scope (BtorSMT2Parser *parser)
{
  assert (!BTOR_EMPTY_STACK (parser->assumptions_trail));

  double start;
  unsigned i, offset, scope_level;
  BtorSMT2Node *node, *next;

  start       = btor_time_stamp ();
  scope_level = BTOR_COUNT_STACK (parser->assumptions_trail);
  offset      = BTOR_POP_STACK (parser->assumptions_trail);
  while (BTOR_COUNT_STACK (parser->assumptions) > offset)
    boolector_release (parser->btor, BTOR_POP_STACK (parser->assumptions));

  /* delete symbols from current scope */
  for (i = 0; i < parser->symbol.size; i++)
  {
    node = parser->symbol.table[i];
    while (node)
    {
      next = node->next;
      if (node->scope_level == scope_level) remove_symbol_smt2 (parser, node);
      node = next;
    }
  }

  /* delete inputs added in current scope */
  offset = BTOR_POP_STACK (parser->inputs_trail);
  assert (offset <= BTOR_COUNT_STACK (parser->inputs));
  while (BTOR_COUNT_STACK (parser->inputs) > offset)
    boolector_release (parser->btor, BTOR_POP_STACK (parser->inputs));

  BTOR_MSG (parser->btor->msg,
            2,
            "closed scope at level %d in %.3f seconds",
            BTOR_COUNT_STACK (parser->assumptions_trail),
            btor_time_stamp () - start);
}

static char *
create_symbol_current_scope (BtorSMT2Parser *parser, char *symbol)
{
  char *symb;
  size_t len;
  if (!BTOR_EMPTY_STACK (parser->assumptions_trail))
  {
    len = strlen (symbol) + 1;
    len += strlen ("BTOR@");
    len += btor_num_digits_util (parser->num_scopes);
    BTOR_CNEWN (parser->mem, symb, len);
    sprintf (symb, "BTOR@%u%s", parser->num_scopes, symbol);
  }
  else
    symb = btor_strdup (parser->mem, symbol);
  return symb;
}

#ifdef BTOR_USE_CLONE_SCOPES
static Btor *
get_current_btor_scope (BtorSMT2Parser *parser)
{
  assert (!BTOR_EMPTY_STACK (parser->btor_scopes));
  return BTOR_TOP_STACK (parser->btor_scopes);
}

static void
open_new_btor_scope (BtorSMT2Parser *parser)
{
  double start;
  unsigned i;
  Btor *scope;
  BtorSMT2Node *node;

  start = btor_time_stamp ();
  /* create new boolector instance (new scope) */
  scope = boolector_clone (get_current_btor_scope (parser));
  //  boolector_set_opt (scope, BTOR_OPT_AUTO_CLEANUP, 1);
  BTOR_PUSH_STACK (parser->mem, parser->btor_scopes, scope);
  BTOR_PUSH_STACK (
      parser->mem, parser->outputs_trail, BTOR_COUNT_STACK (parser->outputs));
  BTOR_PUSH_STACK (
      parser->mem, parser->inputs_trail, BTOR_COUNT_STACK (parser->inputs));

  /* work stack is always empty if a new scope is opened */
  assert (BTOR_EMPTY_STACK (parser->work));

  /* update expressions in symbol table to match current boolector instance */
  for (i = 0; i < parser->symbol.size; i++)
    for (node = parser->symbol.table[i]; node; node = node->next)
    {
      if (!node->exp) continue;
      assert (node->scope_level < BTOR_COUNT_STACK (parser->btor_scopes));
      node->exp = boolector_match_node (scope, node->exp);
      assert (node->exp);
      boolector_release (scope, node->exp);
    }
  BTOR_MSG (parser->btor->msg,
            2,
            "opened new scope at level %d in %.3f seconds",
            BTOR_COUNT_STACK (parser->btor_scopes) - 1,
            btor_time_stamp () - start);
  parser->btor = scope;
}

static void
close_current_btor_scope (BtorSMT2Parser *parser)
{
  assert (BTOR_COUNT_STACK (parser->btor_scopes) > 1);

  double start;
  unsigned i, scope_level, offset;
  Btor *scope;
  BtorSMT2Node *node, *next;
  BtorSMT2Item item;

  start = btor_time_stamp ();
  /* restore previous boolector instance (scope) */
  scope_level = BTOR_COUNT_STACK (parser->btor_scopes);
  /* pop current scope */
  (void) BTOR_POP_STACK (parser->btor_scopes);
  scope = get_current_btor_scope (parser);

  /* in case of an error we have to delete all items on the work stack */
  assert (parser->error || BTOR_EMPTY_STACK (parser->work));
  while (!BTOR_EMPTY_STACK (parser->work))
  {
    item = BTOR_POP_STACK (parser->work);
    release_item_smt2 (parser, &item);
  }

  /* reset outputs added in current scope */
  offset = BTOR_POP_STACK (parser->outputs_trail);
  assert (offset <= BTOR_COUNT_STACK (parser->outputs));
  parser->outputs.top = parser->outputs.start + offset;
  /* reset inputs added in current scope */
  offset = BTOR_POP_STACK (parser->inputs_trail);
  assert (offset <= BTOR_COUNT_STACK (parser->inputs));
  parser->inputs.top = parser->inputs.start + offset;

  /* restore expressions in symbol table to match current boolector instance */
  for (i = 0; i < parser->symbol.size; i++)
  {
    node = parser->symbol.table[i];
    while (node)
    {
      next = node->next;
      if (node->scope_level == scope_level)
        remove_symbol_smt2 (parser, node);
      else if (node->exp)
      {
        node->exp = boolector_match_node (scope, node->exp);
        assert (node->exp);
        boolector_release (scope, node->exp);
      }
      node = next;
    }
  }
  boolector_delete (parser->btor);
  parser->btor = scope;
  BTOR_MSG (parser->btor->msg,
            2,
            "closed scope at level %d in %.3f seconds",
            BTOR_COUNT_STACK (parser->btor_scopes),
            btor_time_stamp () - start);
}
#endif

static void
init_char_classes_smt2 (BtorSMT2Parser *parser)
{
  unsigned char *cc = parser->cc;
  const char *p;

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

#define INSERT(STR, TAG)                                   \
  do                                                       \
  {                                                        \
    BtorSMT2Node *NODE = new_node_smt2 (parser, (TAG));    \
    NODE->name         = btor_strdup (parser->mem, (STR)); \
    insert_symbol_smt2 (parser, NODE);                     \
  } while (0)

static void
insert_keywords_smt2 (BtorSMT2Parser *parser)
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
insert_reserved_words_smt2 (BtorSMT2Parser *parser)
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
insert_commands_smt2 (BtorSMT2Parser *parser)
{
  INSERT ("assert", BTOR_ASSERT_TAG_SMT2);
  INSERT ("check-sat", BTOR_CHECK_SAT_TAG_SMT2);
  INSERT ("declare-sort", BTOR_DECLARE_SORT_TAG_SMT2);
  INSERT ("declare-fun", BTOR_DECLARE_FUN_TAG_SMT2);
  INSERT ("define-sort", BTOR_DEFINE_SORT_TAG_SMT2);
  INSERT ("define-fun", BTOR_DEFINE_FUN_TAG_SMT2);
  INSERT ("exit", BTOR_EXIT_TAG_SMT2);
  INSERT ("get-model", BTOR_GET_MODEL_TAG_SMT2);
  INSERT ("get-assertions", BTOR_GET_ASSERTIONS_TAG_SMT2);
  INSERT ("get-assignment", BTOR_GET_ASSIGNMENT_TAG_SMT2);
  INSERT ("get-info", BTOR_GET_INFO_TAG_SMT2);
  INSERT ("get-option", BTOR_GET_OPTION_TAG_SMT2);
  INSERT ("get-proof", BTOR_GET_PROOF_TAG_SMT2);
  INSERT ("get-unsat-core", BTOR_GET_UNSAT_CORE_TAG_SMT2);
  INSERT ("get-value", BTOR_GET_VALUE_TAG_SMT2);
  INSERT ("model", BTOR_MODEL_TAG_SMT2);
  INSERT ("pop", BTOR_POP_TAG_SMT2);
  INSERT ("push", BTOR_PUSH_TAG_SMT2);
  INSERT ("set-logic", BTOR_SET_LOGIC_TAG_SMT2);
  INSERT ("set-info", BTOR_SET_INFO_TAG_SMT2);
  INSERT ("set-option", BTOR_SET_OPTION_TAG_SMT2);
}

static void
insert_core_symbols_smt2 (BtorSMT2Parser *parser)
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
insert_array_symbols_smt2 (BtorSMT2Parser *parser)
{
  INSERT ("Array", BTOR_ARRAY_TAG_SMT2);
  INSERT ("select", BTOR_SELECT_TAG_SMT2);
  INSERT ("store", BTOR_STORE_TAG_SMT2);
}

static void
insert_bitvec_symbols_smt2 (BtorSMT2Parser *parser)
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
  /* Z3 extensions */
  INSERT ("bvredor", BTOR_BVREDOR_TAG_SMT2);
  INSERT ("bvredand", BTOR_BVREDAND_TAG_SMT2);
  INSERT ("ext_rotate_left", BTOR_EXT_ROTATE_LEFT_TAG_SMT2);
  INSERT ("ext_rotate_right", BTOR_EXT_ROTATE_RIGHT_TAG_SMT2);
}

static void
insert_logics_smt2 (BtorSMT2Parser *parser)
{
  INSERT ("AUFLIA", BTOR_AUFLIA_TAG_SMT2);
  INSERT ("AUFLIRA", BTOR_AUFLIRA_TAG_SMT2);
  INSERT ("AUFNIRA", BTOR_AUFNIRA_TAG_SMT2);
  INSERT ("LRA", BTOR_LRA_TAG_SMT2);
  INSERT ("QF_ABV", BTOR_QF_ABV_TAG_SMT2);
  INSERT ("QF_AUFBV", BTOR_QF_AUFBV_TAG_SMT2);
  INSERT ("QF_AUFLIA", BTOR_QF_AUFLIA_TAG_SMT2);
  INSERT ("QF_AX", BTOR_QF_AX_TAG_SMT2);
  INSERT ("QF_BV", BTOR_QF_BV_TAG_SMT2);
  INSERT ("QF_IDL", BTOR_QF_IDL_TAG_SMT2);
  INSERT ("QF_LIA", BTOR_QF_LIA_TAG_SMT2);
  INSERT ("QF_LRA", BTOR_QF_LRA_TAG_SMT2);
  INSERT ("QF_NIA", BTOR_QF_NIA_TAG_SMT2);
  INSERT ("QF_NRA", BTOR_QF_NRA_TAG_SMT2);
  INSERT ("QF_RDL", BTOR_QF_RDL_TAG_SMT2);
  INSERT ("QF_UF", BTOR_QF_UF_TAG_SMT2);
  INSERT ("QF_UFBV", BTOR_QF_UFBV_TAG_SMT2);
  INSERT ("QF_UFIDL", BTOR_QF_UFIDL_TAG_SMT2);
  INSERT ("QF_UFLIA", BTOR_QF_UFLIA_TAG_SMT2);
  INSERT ("QF_UFLRA", BTOR_QF_UFLRA_TAG_SMT2);
  INSERT ("QF_UFNRA", BTOR_QF_UFNRA_TAG_SMT2);
  INSERT ("UFLRA", BTOR_UFLRA_TAG_SMT2);
  INSERT ("UFNIA", BTOR_UFNIA_TAG_SMT2);
}

static BtorSMT2Parser *
new_smt2_parser (Btor *btor, BtorParseOpt *opts)
{
  BtorSMT2Parser *res;
  BtorMemMgr *mem = btor_new_mem_mgr ();
  BTOR_NEW (mem, res);
  BTOR_CLR (res);
  res->verbosity     = opts->verbosity;
  res->incremental   = opts->incremental;
  res->interactive   = opts->interactive;
  res->model         = opts->need_model;
  res->done          = 0;
  res->btor          = btor;
  res->mem           = mem;
  res->num_scopes    = 0;
  res->print_success = false;

#ifdef BTOR_USE_CLONE_SCOPES
  BTOR_INIT_STACK (res->btor_scopes);
  BTOR_PUSH_STACK (mem, res->btor_scopes, btor);
#endif
  BTOR_INIT_STACK (res->outputs_trail);
  BTOR_INIT_STACK (res->inputs_trail);
  BTOR_INIT_STACK (res->sorts);

  BTOR_INIT_STACK (res->assumptions);
  BTOR_INIT_STACK (res->assumptions_trail);

  init_char_classes_smt2 (res);

  insert_keywords_smt2 (res);
  insert_reserved_words_smt2 (res);
  insert_commands_smt2 (res);
  insert_core_symbols_smt2 (res);
  insert_array_symbols_smt2 (res);
  insert_bitvec_symbols_smt2 (res);
  insert_logics_smt2 (res);

  return res;
}

static void
release_work_smt2 (BtorSMT2Parser *parser)
{
  BtorSMT2Item item;
  while (!BTOR_EMPTY_STACK (parser->work))
  {
    item = BTOR_POP_STACK (parser->work);
    release_item_smt2 (parser, &item);
  }
  BTOR_RELEASE_STACK (parser->mem, parser->work);
}

static void
delete_smt2_parser (BtorSMT2Parser *parser)
{
  BtorMemMgr *mem = parser->mem;

#ifdef BTOR_USE_CLONE_SCOPES
  while (BTOR_COUNT_STACK (parser->btor_scopes) > 1)
    close_current_btor_scope (parser);
#endif

  while (!BTOR_EMPTY_STACK (parser->assumptions_trail))
    close_current_scope (parser);

  release_symbols_smt2 (parser);
  release_work_smt2 (parser);

  if (parser->infile_name) btor_freestr (mem, parser->infile_name);
  if (parser->error) btor_freestr (mem, parser->error);

  while (!BTOR_EMPTY_STACK (parser->inputs))
    boolector_release (parser->btor, BTOR_POP_STACK (parser->inputs));
  BTOR_RELEASE_STACK (mem, parser->inputs);

  while (!BTOR_EMPTY_STACK (parser->outputs))
    boolector_release (parser->btor, BTOR_POP_STACK (parser->outputs));
  BTOR_RELEASE_STACK (mem, parser->outputs);

  while (!BTOR_EMPTY_STACK (parser->sorts))
    boolector_release_sort (parser->btor, BTOR_POP_STACK (parser->sorts));
  BTOR_RELEASE_STACK (mem, parser->sorts);

  BTOR_RELEASE_STACK (mem, parser->outputs_trail);
  BTOR_RELEASE_STACK (mem, parser->inputs_trail);
#ifdef BTOR_USE_CLONE_SCOPES
  BTOR_RELEASE_STACK (mem, parser->btor_scopes);
#endif
  BTOR_RELEASE_STACK (mem, parser->assumptions);
  BTOR_RELEASE_STACK (mem, parser->assumptions_trail);
  BTOR_RELEASE_STACK (mem, parser->token);

  BTOR_DELETE (mem, parser);
  btor_delete_mem_mgr (mem);
}

static bool
isspace_smt2 (int ch)
{
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

static unsigned
cc_smt2 (BtorSMT2Parser *parser, int ch)
{
  if (ch < 0 || ch >= 256) return 0;
  return parser->cc[(unsigned char) ch];
}

static void
pushch_smt2 (BtorSMT2Parser *parser, int ch)
{
  assert (ch != EOF);
  BTOR_PUSH_STACK (parser->mem, parser->token, ch);
}

static int
read_token_aux_smt2 (BtorSMT2Parser *parser)
{
  BtorSMT2Node *node;
  unsigned char cc;
  int ch;
  assert (!BTOR_INVALID_TAG_SMT2);  // error code:          0
  BTOR_RESET_STACK (parser->token);
  parser->last_node = 0;
RESTART:
  do
  {
    parser->coo = parser->nextcoo;
    if ((ch = nextch_smt2 (parser)) == EOF)
    {
      assert (EOF < 0);
      return EOF;  // end of tokens:       EOF
    }
  } while (isspace_smt2 (ch));
  if (ch == ';')
  {
    while ((ch = nextch_smt2 (parser)) != '\n')
      if (ch == EOF)
      {
        assert (!BTOR_INVALID_TAG_SMT2);
        return !perr_smt2 (parser, "unexpected end-of-file in comment");
      }
    goto RESTART;
  }
  cc = cc_smt2 (parser, ch);
  if (ch == '(')
  {
    pushch_smt2 (parser, '(');
    pushch_smt2 (parser, 0);
    return BTOR_LPAR_TAG_SMT2;
  }
  if (ch == ')')
  {
    pushch_smt2 (parser, ')');
    pushch_smt2 (parser, 0);
    return BTOR_RPAR_TAG_SMT2;
  }
  if (ch == '#')
  {
    pushch_smt2 (parser, '#');
    if ((ch = nextch_smt2 (parser)) == EOF)
      return !perr_smt2 (parser, "unexpected end-of-file after '#'");
    if (ch == 'b')
    {
      pushch_smt2 (parser, 'b');
      if ((ch = nextch_smt2 (parser)) == EOF)
        return !perr_smt2 (parser, "unexpected end-of-file after '#b'");
      if (ch != '0' && ch != '1')
        return !perr_smt2 (parser, "expected '0' or '1' after '#b'");
      pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = nextch_smt2 (parser);
        if (ch != '0' && ch != '1') break;
        pushch_smt2 (parser, ch);
      }
      savech_smt2 (parser, ch);
      pushch_smt2 (parser, 0);
      return BTOR_BINARY_CONSTANT_TAG_SMT2;
    }
    else if (ch == 'x')
    {
      pushch_smt2 (parser, 'x');
      if ((ch = nextch_smt2 (parser)) == EOF)
        return !perr_smt2 (parser, "unexpected end-of-file after '#x'");
      if (!(cc_smt2 (parser, ch) & BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2))
        return !perr_smt2 (parser, "expected hexa-decimal digit after '#x'");
      pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = nextch_smt2 (parser);
        if (!(cc_smt2 (parser, ch) & BTOR_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2))
          break;
        pushch_smt2 (parser, ch);
      }
      savech_smt2 (parser, ch);
      pushch_smt2 (parser, 0);
      return BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2;
    }
    else
      return !perr_smt2 (parser, "expected 'x' or 'b' after '#'");
  }
  else if (ch == '"')
  {
    pushch_smt2 (parser, '"');
    for (;;)
    {
      if ((ch = nextch_smt2 (parser)) == EOF)
        return !cerr_smt2 (parser, "unexpected", ch, "in string");
      if (ch == '"')
      {
        pushch_smt2 (parser, '"');
        pushch_smt2 (parser, 0);
        return BTOR_STRING_CONSTANT_TAG_SMT2;
      }
      if (ch == '\\')
      {
        if ((ch = nextch_smt2 (parser)) != '"' && ch != '\\')
          return !cerr_smt2 (
              parser, "unexpected", ch, "after backslash '\\\\' in string");
      }
      else if (!(cc_smt2 (parser, ch) & BTOR_STRING_CHAR_CLASS_SMT2))
      {
        // TODO unreachable?
        return !cerr_smt2 (parser, "invalid", ch, "in string");
      }
      pushch_smt2 (parser, ch);
    }
  }
  else if (ch == '|')
  {
    for (;;)
    {
      if ((ch = nextch_smt2 (parser)) == EOF)
        return !cerr_smt2 (parser, "unexpected", ch, "in quoted symbol");
      if (ch == '|')
      {
        pushch_smt2 (parser, 0);
        if (!(node = find_symbol_smt2 (parser, parser->token.start)))
        {
          node       = new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
          node->name = btor_strdup (parser->mem, parser->token.start);
          insert_symbol_smt2 (parser, node);
        }
        parser->last_node = node;
        return BTOR_SYMBOL_TAG_SMT2;
      }
      if (!(cc_smt2 (parser, ch) & BTOR_QUOTED_SYMBOL_CHAR_CLASS_SMT2))
        return !cerr_smt2 (parser, "invalid", ch, "in quoted symbol");
      pushch_smt2 (parser, ch);
    }
  }
  else if (ch == ':')
  {
    pushch_smt2 (parser, ':');
    if ((ch = nextch_smt2 (parser)) == EOF)
      return !perr_smt2 (parser, "unexpected end-of-file after ':'");
    if (!(cc_smt2 (parser, ch) & BTOR_KEYWORD_CHAR_CLASS_SMT2))
      return !cerr_smt2 (parser, "unexpected", ch, "after ':'");
    pushch_smt2 (parser, ch);
    while ((cc_smt2 (parser, ch = nextch_smt2 (parser))
            & BTOR_KEYWORD_CHAR_CLASS_SMT2))
    {
      assert (ch != EOF);
      pushch_smt2 (parser, ch);
    }
    savech_smt2 (parser, ch);
    pushch_smt2 (parser, 0);
    if (!(node = find_symbol_smt2 (parser, parser->token.start)))
    {
      node       = new_node_smt2 (parser, BTOR_ATTRIBUTE_TAG_SMT2);
      node->name = btor_strdup (parser->mem, parser->token.start);
      insert_symbol_smt2 (parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else if (ch == '0')
  {
    pushch_smt2 (parser, '0');
    ch = nextch_smt2 (parser);
    if (ch == '.')
    {
      pushch_smt2 (parser, '.');
      if ((ch = nextch_smt2 (parser)) == EOF)
        return !perr_smt2 (parser, "unexpected end-of-file after '0.'");
      if (!(cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
        return !perr_smt2 (parser, "expected decimal digit after '0.'");
      pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = nextch_smt2 (parser);
        if (!(cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2)) break;
        pushch_smt2 (parser, ch);
      }
    }
    savech_smt2 (parser, ch);
    pushch_smt2 (parser, 0);
    return BTOR_DECIMAL_CONSTANT_TAG_SMT2;
  }
  else if (cc & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2)
  {
    pushch_smt2 (parser, ch);
    for (;;)
    {
      ch = nextch_smt2 (parser);
      if (!(cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2)) break;
      pushch_smt2 (parser, ch);
    }
    if (ch == '.')
    {
      pushch_smt2 (parser, '.');
      if ((ch = nextch_smt2 (parser)) == EOF)
      {
        pushch_smt2 (parser, 0);
        return !perr_smt2 (
            parser, "unexpected end-of-file after '%s'", parser->token.start);
      }
      if (!(cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
      {
        pushch_smt2 (parser, 0);
        return !perr_smt2 (
            parser, "expected decimal digit after '%s'", parser->token.start);
      }
      pushch_smt2 (parser, ch);
      for (;;)
      {
        ch = nextch_smt2 (parser);
        if (!(cc_smt2 (parser, ch) & BTOR_DECIMAL_DIGIT_CHAR_CLASS_SMT2)) break;
        pushch_smt2 (parser, ch);
      }
    }
    savech_smt2 (parser, ch);
    pushch_smt2 (parser, 0);
    return BTOR_DECIMAL_CONSTANT_TAG_SMT2;
  }
  else if (cc & BTOR_SYMBOL_CHAR_CLASS_SMT2)
  {
    pushch_smt2 (parser, ch);
    for (;;)
    {
      ch = nextch_smt2 (parser);
      if (!(cc_smt2 (parser, ch) & BTOR_SYMBOL_CHAR_CLASS_SMT2)) break;
      pushch_smt2 (parser, ch);
    }
    savech_smt2 (parser, ch);
    pushch_smt2 (parser, 0);
    if (!strcmp (parser->token.start, "_")) return BTOR_UNDERSCORE_TAG_SMT2;
    if (!(node = find_symbol_smt2 (parser, parser->token.start)))
    {
      node       = new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
      node->name = btor_strdup (parser->mem, parser->token.start);
      insert_symbol_smt2 (parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else
    return !cerr_smt2 (parser, "illegal", ch, 0);

  // TODO should be dead code ...?
  return !perr_smt2 (parser, "internal token reading error");
}

static int
read_token_smt2 (BtorSMT2Parser *parser)
{
  int res;
  parser->lastcoo = parser->coo;
  res             = read_token_aux_smt2 (parser);
  if (parser->verbosity >= 4)
  {
    printf ("[btorsmt2] line %-8d column %-4d token %08x %s\n",
            parser->coo.x,
            parser->coo.y,
            res,
            res == EOF ? "<end-of-file>"
                       : res == BTOR_INVALID_TAG_SMT2 ? "<error>"
                                                      : parser->token.start);
    fflush (stdout);
  }
  return res;
}

static int
read_rpar_smt2 (BtorSMT2Parser *parser, const char *msg)
{
  int tag = read_token_smt2 (parser);
  if (tag == EOF)
    return !perr_smt2 (parser, "expected ')'%s at end-of-file", msg ? msg : "");
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    assert (parser->error);
    return 0;
  }
  if (tag != BTOR_RPAR_TAG_SMT2)
    return !perr_smt2 (
        parser, "expected ')'%s at '%s'", msg ? msg : "", parser->token.start);
  return 1;
}

static int
read_lpar_smt2 (BtorSMT2Parser *parser, const char *msg)
{
  int tag = read_token_smt2 (parser);
  if (tag == EOF)
    return !perr_smt2 (parser, "expected '('%s at end-of-file", msg ? msg : "");
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    assert (parser->error);
    return 0;
  }
  if (tag != BTOR_LPAR_TAG_SMT2)
    return !perr_smt2 (
        parser, "expected '('%s at '%s'", msg ? msg : "", parser->token.start);
  return 1;
}

static int
skip_sexprs (BtorSMT2Parser *parser, int initial)
{
  int tag, open = initial;
  while (open > 0)
  {
    tag = read_token_smt2 (parser);
    if (tag == EOF)
    {
      if (open > 0) return !perr_smt2 (parser, "')' missing at end-of-file");
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
read_symbol (BtorSMT2Parser *parser, const char *errmsg, BtorSMT2Node **resptr)
{
  int tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser,
                       "expected symbol%s but reached end-of-file",
                       errmsg ? errmsg : "");
  if (tag != BTOR_SYMBOL_TAG_SMT2)
    return !perr_smt2 (parser,
                       "expected symbol%s at '%s'",
                       errmsg ? errmsg : "",
                       parser->token.start);
  assert (parser->last_node->tag == BTOR_SYMBOL_TAG_SMT2);
  *resptr = parser->last_node;
  return 1;
}

static int
str2int32_smt2 (BtorSMT2Parser *parser,
                int posonly,
                const char *str,
                int *resptr)
{
  int res, ch, digit;
  const char *p;
  res = 0;
  assert (sizeof (int) == 4);
  for (p = str; (ch = *p); p++)
  {
    if (res > INT_MAX / 10 || ch < '0' || ch > '9')
    INVALID:
      return !perr_smt2 (parser, "invalid 32-bit integer '%s'", str);
    assert ('0' <= ch && ch <= '9');
    if (res) res *= 10;
    digit = ch - '0';
    if (INT_MAX - digit < res) goto INVALID;
    res += digit;
  }
  if (posonly && !res)
    return !perr_smt2 (
        parser, "expected positive non-zero 32-bit integer at '%s'", str);
  *resptr = res;
  return 1;
}

static BtorSMT2Item *
push_item_smt2 (BtorSMT2Parser *parser, BtorSMT2Tag tag)
{
  BtorSMT2Item item;
  BTOR_CLR (&item);
  item.coo = parser->coo;
  item.tag = tag;
  BTOR_PUSH_STACK (parser->mem, parser->work, item);
  return parser->work.top - 1;
}

static BtorSMT2Item *
last_lpar_smt2 (BtorSMT2Parser *parser)
{
  BtorSMT2Item *p = parser->work.top;
  do
  {
    if (p-- == parser->work.start) return 0;
  } while (p->tag != BTOR_LPAR_TAG_SMT2);
  return p;
}

#define BTOR_TAG_CLASS_MASK_SMT2                              \
  (BTOR_RESERVED_TAG_CLASS_SMT2 | BTOR_COMMAND_TAG_CLASS_SMT2 \
   | BTOR_KEYWORD_TAG_CLASS_SMT2 | BTOR_CORE_TAG_CLASS_SMT2   \
   | BTOR_ARRAY_TAG_CLASS_SMT2 | BTOR_BITVEC_TAG_CLASS_SMT2   \
   | BTOR_LOGIC_TAG_CLASS_SMT2)

static int
item_with_node_smt2 (BtorSMT2Item *item)
{
  if (item->tag == BTOR_SYMBOL_TAG_SMT2) return 1;
  if (item->tag == BTOR_ATTRIBUTE_TAG_SMT2) return 1;
  if (item->tag & BTOR_TAG_CLASS_MASK_SMT2) return 1;
  return 0;
}

static const char *
item2str_smt2 (BtorSMT2Item *item)
{
  if (item_with_node_smt2 (item))
  {
    if (!item->node) return "<zero-node-item>";
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
bvconst_str_smt2 (const char *str)
{
  const char *p;
  if (str[0] != 'b' || str[1] != 'v') return 0;
  if (!isdigit ((int) str[2])) return 0;
  for (p = str + 3; *p; p++)
    if (!isdigit ((int) *p)) return 0;
  return 1;
}

static int
prev_item_was_lpar_smt2 (BtorSMT2Parser *parser)
{
  if (BTOR_COUNT_STACK (parser->work) >= 2
      && parser->work.top[-2].tag == BTOR_LPAR_TAG_SMT2)
    return 1;
  return !perr_smt2 (parser, "expected '(' before '%s'", parser->token.start);
}

/* Note: we need tokens string only for get-value (for printing the originally
 *	 parsed, non-simplified expression) */
static int
parse_int32_smt2 (BtorSMT2Parser *parser,
                  int posonly,
                  int *resptr,
                  BtorCharStack *tokens)
{
  int i, tag;
  char c, t;

  tag = read_token_smt2 (parser);
  for (i = 0; tokens && i < BTOR_COUNT_STACK (parser->token); i++)
  {
    c = BTOR_PEEK_STACK (parser->token, i);
    t = BTOR_COUNT_STACK (*tokens) ? BTOR_TOP_STACK (*tokens) : 0;
    if (!c && t == '(') continue;
    if (c == ')' && t == ' ') (void) BTOR_POP_STACK (*tokens);
    if (t == ')' && c == '(') BTOR_PUSH_STACK (parser->mem, *tokens, ' ');
    BTOR_PUSH_STACK (parser->mem, *tokens, c ? c : ' ');
  }

  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser,
                       "expected decimal constant but reached end-of-file");
  if (tag != BTOR_DECIMAL_CONSTANT_TAG_SMT2)
    return !perr_smt2 (
        parser, "expected decimal constant at '%s'", parser->token.start);
  return str2int32_smt2 (parser, posonly, parser->token.start, resptr);
}

static bool
check_boolean_args_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *p, int nargs)
{
  int i, width;
  for (i = 1; i <= nargs; i++)
  {
    if (boolector_is_array (parser->btor, p[i].exp))
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2 (
          parser, "argument %d of '%s' is an array term", i, p->node->name);
    }
    if ((width = boolector_get_width (parser->btor, p[i].exp)) != 1)
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2 (parser,
                         "argument %d of '%s' is a bit-vector of width %d",
                         i,
                         p->node->name,
                         width);
    }
  }
  return true;
}

static bool
check_arg_sorts_match_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *p, int nargs)
{
  int i, domain, width, len;
  assert (nargs >= 1);
  width           = boolector_get_width (parser->btor, p[1].exp);
  parser->perrcoo = p->coo;
  if (boolector_is_array (parser->btor, p[1].exp))
  {
    domain = boolector_get_index_width (parser->btor, p[1].exp);
    for (i = 2; i <= nargs; i++)
    {
      if (!boolector_is_array (parser->btor, p[i].exp))
        return !perr_smt2 (
            parser,
            "first argument of '%s' is an array but argument %d not",
            p->node->name,
            i);
      if ((len = boolector_get_width (parser->btor, p[i].exp)) != width)
        return !perr_smt2 (
            parser,
            "first argument of '%s' is an array of bit-vectors of width %d "
            "but argument %d is an array of bit-vectors of width %d",
            p->node->name,
            width,
            i,
            len);
      if ((len = boolector_get_index_width (parser->btor, p[i].exp)) != domain)
        return !perr_smt2 (
            parser,
            "first argument of '%s' is an array with index bit-vectors of "
            "width %d "
            "but argument %d is an array with index bit-vectors of width %d",
            p->node->name,
            domain,
            i,
            len);
    }
  }
  else if (boolector_is_fun (parser->btor, p[1].exp))
  {
    for (i = 2; i <= nargs; i++)
    {
      if (!boolector_is_fun (parser->btor, p[i].exp))
        return !perr_smt2 (
            parser,
            "first argument of '%s' is a function but argument %d not",
            p->node->name,
            i);
      if (!boolector_is_equal_sort (parser->btor, p[1].exp, p[i].exp))
        return !perr_smt2 (
            parser,
            "sort of argument %d does not match with sort of first "
            "argument of '%s'",
            i,
            p->node->name);
    }
  }
  else
  {
    for (i = 1; i <= nargs; i++)
    {
      if (boolector_is_array (parser->btor, p[i].exp))
        return !perr_smt2 (
            parser,
            "argument %d of '%s' is an array but first argument not",
            i,
            p->node->name);
      if (boolector_is_fun (parser->btor, p[i].exp))
        return !perr_smt2 (
            parser,
            "argument %d of '%s' is a function but first argument not",
            i,
            p->node->name);
      if ((len = boolector_get_width (parser->btor, p[i].exp)) != width)
        return !perr_smt2 (parser,
                           "first argument of '%s' is bit-vector of width %d "
                           "but argument %d is a bit-vector of width %d",
                           p->node->name,
                           width,
                           i,
                           len);
    }
  }
  parser->perrcoo.x = 0;
  return true;
}

static bool
check_ite_args_sorts_match_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *p)
{
  int domain, width, len;
  assert (p->tag == BTOR_ITE_TAG_SMT2);
  if (boolector_is_array (parser->btor, p[1].exp))
  {
    parser->perrcoo = p[1].coo;
    return !perr_smt2 (parser, "first argument of 'ite' is an array");
  }
  if (boolector_is_fun (parser->btor, p[1].exp))
  {
    parser->perrcoo = p[1].coo;
    return !perr_smt2 (parser, "first argument of 'ite' is a function");
  }
  if ((len = boolector_get_width (parser->btor, p[1].exp)) != 1)
  {
    parser->perrcoo = p[1].coo;
    return !perr_smt2 (
        parser, "first argument of 'ite' is bit-vector of bit-width %d", len);
  }
  if (boolector_is_array (parser->btor, p[2].exp))
  {
    if (!boolector_is_array (parser->btor, p[3].exp))
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (parser,
                         "second argument of 'ite' is an array but third not");
    }
    width = boolector_get_width (parser->btor, p[2].exp);
    len   = boolector_get_width (parser->btor, p[3].exp);
    if (width != len)
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (
          parser,
          "second argument of 'ite' is array of bit-vectors of width %d and "
          "third argument is array of bit-vectors of width %d",
          width,
          len);
    }
    domain = boolector_get_index_width (parser->btor, p[2].exp);
    len    = boolector_get_index_width (parser->btor, p[3].exp);
    if (domain != len)
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (
          parser,
          "second argument of 'ite' is array with index bit-vectors of width "
          "%d and "
          "third argument is array with index bit-vectors of width %d",
          domain,
          len);
    }
  }
  else
  {
    if (boolector_is_array (parser->btor, p[3].exp))
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (parser,
                         "third argument of 'ite' is an array but second not");
    }
    width = boolector_get_width (parser->btor, p[2].exp);
    len   = boolector_get_width (parser->btor, p[3].exp);
    if (width != len)
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (
          parser,
          "second argument of 'ite' is bit-vector of width %d and "
          "third argument is bit-vector of width %d",
          width,
          len);
    }
  }
  return true;
}

static bool
check_nargs_smt2 (BtorSMT2Parser *parser,
                  BtorSMT2Item *p,
                  int actual,
                  int required)
{
  int diff       = actual - required;
  const char *op = p->node->name;
  if (diff) parser->perrcoo = p->coo;
  if (diff == -1)
    return !perr_smt2 (parser, "one argument to '%s' missing", op);
  if (diff < 0)
    return !perr_smt2 (parser, "%d arguments to '%s' missing", -diff, op);
  if (diff == 1)
    return !perr_smt2 (parser, "'%s' has one argument too much", op);
  if (diff > 0)
    return !perr_smt2 (parser, "'%s' has %d arguments too much", op, diff);
  return true;
}

static bool
check_not_array_or_uf_args_smt2 (BtorSMT2Parser *parser,
                                 BtorSMT2Item *p,
                                 int nargs)
{
  int i;
  for (i = 1; i <= nargs; i++)
  {
    if (boolector_is_array (parser->btor, p[i].exp))
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2 (
          parser, "argument %d of '%s' is an array", i, p->node->name);
    }
    if (boolector_is_fun (parser->btor, p[i].exp))
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2 (
          parser, "argument %d of '%s' is a function", i, p->node->name);
    }
  }
  return true;
}

static BoolectorNode *
translate_shift_smt2 (Btor *btor,
                      BoolectorNode *a0,
                      BoolectorNode *a1,
                      BoolectorNode *(*f) (Btor *,
                                           BoolectorNode *,
                                           BoolectorNode *) )
{
  BoolectorNode *c, *e, *t, *e0, *u, *l, *tmp, *res;
  BoolectorSort s;
  int len, l0, l1, p0, p1;

  len = boolector_get_width (btor, a0);

  assert (len == boolector_get_width (btor, a1));

  l1 = 0;
  for (l0 = 1; l0 < len; l0 *= 2) l1++;

  assert (l0 == (1 << l1));

  if (len == 1)
  {
    assert (l0 == 1);
    assert (l1 == 0);

    if (f != boolector_sra)
    {
      tmp = boolector_not (btor, a1);
      res = boolector_and (btor, a0, tmp);
      boolector_release (btor, tmp);
    }
    else
      res = boolector_copy (btor, a0);
  }
  else
  {
    assert (len >= 1);

    p0 = l0 - len;
    p1 = len - l1;

    assert (p0 >= 0);
    assert (p1 > 0);

    u = boolector_slice (btor, a1, len - 1, len - p1);
    l = boolector_slice (btor, a1, l1 - 1, 0);

    assert (boolector_get_width (btor, u) == p1);
    assert (boolector_get_width (btor, l) == l1);

    if (p1 > 1)
      c = boolector_redor (btor, u);
    else
      c = boolector_copy (btor, u);

    boolector_release (btor, u);

    if (f == boolector_sra)
    {
      tmp = boolector_slice (btor, a0, len - 1, len - 1);
      t   = boolector_sext (btor, tmp, len - 1);
      boolector_release (btor, tmp);
    }
    else
    {
      s = boolector_bitvec_sort (btor, len);
      t = boolector_zero (btor, s);
      boolector_release_sort (btor, s);
    }

    if (!p0)
      e0 = boolector_copy (btor, a0);
    else if (f == boolector_sra)
      e0 = boolector_sext (btor, a0, p0);
    else
      e0 = boolector_uext (btor, a0, p0);

    assert (boolector_get_width (btor, e0) == l0);

    e = f (btor, e0, l);
    boolector_release (btor, e0);
    boolector_release (btor, l);

    if (p0 > 0)
    {
      tmp = boolector_slice (btor, e, len - 1, 0);
      boolector_release (btor, e);
      e = tmp;
    }

    res = boolector_cond (btor, c, t, e);

    boolector_release (btor, c);
    boolector_release (btor, t);
    boolector_release (btor, e);
  }
  return res;
}

static BoolectorNode *
shl_smt2 (Btor *btor, BoolectorNode *a, BoolectorNode *b)
{
  return translate_shift_smt2 (btor, a, b, boolector_sll);
}

static BoolectorNode *
ashr_smt2 (Btor *btor, BoolectorNode *a, BoolectorNode *b)
{
  return translate_shift_smt2 (btor, a, b, boolector_sra);
}

static BoolectorNode *
lshr_smt2 (Btor *btor, BoolectorNode *a, BoolectorNode *b)
{
  return translate_shift_smt2 (btor, a, b, boolector_srl);
}

static BoolectorNode *
translate_rotate_smt2 (Btor *btor, BoolectorNode *exp, int shift, int left)
{
  BoolectorNode *l, *r, *res;
  int len;

  assert (shift >= 0);

  len = boolector_get_width (btor, exp);
  assert (len > 0);
  shift %= len;

  if (shift)
  {
    if (left) shift = len - shift;

    assert (1 <= shift && shift < len);

    l = boolector_slice (btor, exp, shift - 1, 0);
    r = boolector_slice (btor, exp, len - 1, shift);

    res = boolector_concat (btor, l, r);

    boolector_release (btor, l);
    boolector_release (btor, r);
  }
  else
    res = boolector_copy (btor, exp);
  assert (boolector_get_width (btor, res) == len);
  return res;
}

static BoolectorNode *
rotate_left_smt2 (Btor *btor, BoolectorNode *exp, int shift)
{
  return translate_rotate_smt2 (btor, exp, shift, 1);
}

static BoolectorNode *
rotate_right_smt2 (Btor *btor, BoolectorNode *exp, int shift)
{
  return translate_rotate_smt2 (btor, exp, shift, 0);
}

static BoolectorNode *
translate_ext_rotate_smt2 (Btor *btor,
                           BoolectorNode *exp,
                           BoolectorNode *shift,
                           int left)
{
  assert (boolector_is_const (btor, shift));

  char *len;
  int shift_len;

  len = btor_const_to_decimal (btor->mm, boolector_get_bits (btor, shift));
  shift_len = atoi (len);
  assert (shift_len < boolector_get_width (btor, exp));
  btor_freestr (btor->mm, len);
  return translate_rotate_smt2 (btor, exp, shift_len, left);
}

/* Note: we need look ahead and tokens string only for get-value
 *	 (for parsing a term list and printing the originally parsed,
 *	 non-simplified expression) */
static int
parse_term_aux_smt2 (BtorSMT2Parser *parser,
                     int have_look_ahead,
                     int look_ahead,
                     BoolectorNode **resptr,
                     BtorSMT2Coo *cooptr,
                     BtorCharStack *tokens)
{
  char c, t;
  int tag, width, domain, len, nargs, i, j, open = 0, work_cnt;
  BoolectorNode *(*binfun) (Btor *, BoolectorNode *, BoolectorNode *);
  BoolectorNode *(*extfun) (Btor *, BoolectorNode *, int);
  BoolectorNode *(*rotatefun) (Btor *, BoolectorNode *, int);
  BoolectorNode *(*unaryfun) (Btor *, BoolectorNode *);
  BoolectorNode *res, *exp, *tmp, *old;
  BoolectorSort s;
  BtorSMT2Item *l, *p;

  assert (!tokens || !BTOR_COUNT_STACK (*tokens));

  unaryfun = 0;
  binfun   = 0;
  work_cnt = BTOR_COUNT_STACK (parser->work);

  do
  {
    if (have_look_ahead)
    {
      tag             = look_ahead;
      have_look_ahead = 0;
    }
    else
      tag = read_token_smt2 (parser);

    for (i = 0; tokens && i < BTOR_COUNT_STACK (parser->token); i++)
    {
      c = BTOR_PEEK_STACK (parser->token, i);
      t = BTOR_COUNT_STACK (*tokens) ? BTOR_TOP_STACK (*tokens) : 0;
      if (!c && t == '(') continue;
      if (c == ')' && t == ' ') (void) BTOR_POP_STACK (*tokens);
      if (t == ')' && c == '(') BTOR_PUSH_STACK (parser->mem, *tokens, ' ');
      BTOR_PUSH_STACK (parser->mem, *tokens, c ? c : ' ');
    }

    if (tag == BTOR_INVALID_TAG_SMT2)
    {
      assert (parser->error);
      return 0;
    }
    if (tag == EOF)
    {
      l = last_lpar_smt2 (parser);
      if (!l)
        return !perr_smt2 (parser,
                           "expected expression but reached end-of-file");
      return !perr_smt2 (
          parser,
          "unexpected end-of-file since '(' at line %d column %d still open",
          l->coo.x,
          l->coo.y);
    }

    if (tag == BTOR_RPAR_TAG_SMT2)
    {
      if (parser->expecting_let_body)
      {
        l = 0;
        if (open)
        {
          l = last_lpar_smt2 (parser);
          if (++l >= parser->work.top) l = 0;
        }
        if (l)
        {
          assert (l->tag == BTOR_LET_TAG_SMT2);
          return !perr_smt2 (parser,
                             "body to 'let' at line %d column %d missing",
                             l->coo.x,
                             l->coo.y);
        }
        else
        {
          // TODO reachable?
          return !perr_smt2 (parser, "body to 'let' missing");
        }
      }
      assert (open >= 0);
      if (!open) return !perr_smt2 (parser, "expected expression");
      l = last_lpar_smt2 (parser);
      assert (l);
      p = l + 1;
      if (p == parser->work.top) return !perr_smt2 (parser, "unexpected '()'");
      nargs = parser->work.top - p - 1;
      tag   = p->tag;
      if (tag != BTOR_LET_TAG_SMT2 && tag != BTOR_LETBIND_TAG_SMT2
          && tag != BTOR_PARLETBINDING_TAG_SMT2)
      {
        for (i = 1; i <= nargs; i++)
          if (p[i].tag != BTOR_EXP_TAG_SMT2)
          {
            parser->perrcoo = p[i].coo;
            return !perr_smt2 (parser, "expected expression");
          }
      }
      /* function application */
      if (tag == BTOR_EXP_TAG_SMT2 && nargs
          && boolector_is_fun (parser->btor, p[0].exp))
      {
        BoolectorNodePtrStack fargs;
        BTOR_INIT_STACK (fargs);
        for (i = 1; i <= nargs; i++)
        {
          if (p[i].tag != BTOR_EXP_TAG_SMT2)
          {
            BTOR_RELEASE_STACK (parser->mem, fargs);
            parser->perrcoo = p[i].coo;
            return !perr_smt2 (parser, "expected expression");
          }
          BTOR_PUSH_STACK (parser->mem, fargs, p[i].exp);
        }
        tmp = p[0].exp;
        if (nargs != boolector_get_fun_arity (parser->btor, tmp))
        {
          BTOR_RELEASE_STACK (parser->mem, fargs);
          return !perr_smt2 (parser, "invalid number of arguments");
        }
        i = boolector_fun_sort_check (parser->btor, fargs.start, nargs, tmp);
        if (i >= 0)
        {
          BTOR_RELEASE_STACK (parser->mem, fargs);
          return !perr_smt2 (parser, "invalid sort for argument %d", i + 1);
        }
        parser->work.top = p;
        l->tag           = BTOR_EXP_TAG_SMT2;
        l->exp = boolector_apply (parser->btor, fargs.start, nargs, tmp);
        for (i = 0; i <= nargs; i++) boolector_release (parser->btor, p[i].exp);
        BTOR_RELEASE_STACK (parser->mem, fargs);
      }
      else if (tag == BTOR_EXP_TAG_SMT2)
      {
        if (nargs)
        {
          parser->perrcoo = l->coo;
          return !perr_smt2 (parser, "list with %d expressions", nargs + 1);
        }
        p->coo = l->coo;
        *l     = *p;
        parser->work.top--;
        assert (l + 1 == parser->work.top);
      }
      else if (tag == BTOR_NOT_TAG_SMT2)
      {
        if (nargs != 1)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser,
                             "'not' with %d arguments but expected exactly one",
                             nargs);
        }
        tmp = p[1].exp;
        if (boolector_is_array (parser->btor, tmp))
        {
          parser->perrcoo = p[1].coo;
          return !perr_smt2 (
              parser, "unexpected array expression as argument to 'not'");
        }
        if ((width = boolector_get_width (parser->btor, tmp)) != 1)
        {
          parser->perrcoo = p[1].coo;
          return !perr_smt2 (
              parser,
              "unexpected bit-vector of width %d as argument to 'not'",
              width);
        }
        parser->work.top = p;
        l->tag           = BTOR_EXP_TAG_SMT2;
        l->exp           = boolector_not (parser->btor, tmp);
        boolector_release (parser->btor, tmp);
      }
      else if (tag == BTOR_IMPLIES_TAG_SMT2)
      {
        if (!nargs)
          return !perr_smt2 (parser, "argument to '%s' missing", p->node->name);
        if (!check_boolean_args_smt2 (parser, p, nargs)) return 0;
        exp = 0;
        for (i = nargs; i >= 1; i--)
        {
          if (exp)
          {
            old = exp;
            exp = boolector_implies (parser->btor, p[i].exp, old);
            boolector_release (parser->btor, old);
          }
          else
            exp = boolector_copy (parser->btor, p[i].exp);
        }
        assert (exp);
      RELEASE_EXP_AND_OVERWRITE:
        for (i = 1; i <= nargs; i++) boolector_release (parser->btor, p[i].exp);
        parser->work.top = p;
        l->tag           = BTOR_EXP_TAG_SMT2;
        l->exp           = exp;
      }
      else if (tag == BTOR_AND_TAG_SMT2)
      {
        binfun = boolector_and;
      BIN_BOOL_LEFT_ASSOCIATIVE_CORE:
        if (nargs < 2)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser, "argument to '%s' missing", p->node->name);
        }
        if (!check_boolean_args_smt2 (parser, p, nargs)) return 0;
        exp = 0;
        for (i = 1; i <= nargs; i++)
        {
          if (exp)
          {
            old = exp;
            exp = binfun (parser->btor, old, p[i].exp);
            boolector_release (parser->btor, old);
          }
          else
            exp = boolector_copy (parser->btor, p[i].exp);
        }
        assert (exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_OR_TAG_SMT2)
      {
        binfun = boolector_or;
        goto BIN_BOOL_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_XOR_TAG_SMT2)
      {
        binfun = boolector_xor;
        goto BIN_BOOL_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_EQUAL_TAG_SMT2)
      {
        if (!nargs)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser, "arguments to '=' missing");
        }
        if (nargs == 1)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser, "only one argument to '='");
        }
        if (!check_arg_sorts_match_smt2 (parser, p, nargs)) return 0;
        exp = boolector_true (parser->btor);
        for (i = 1; i < nargs; i++)
        {
          tmp = boolector_eq (parser->btor, p[i].exp, p[i + 1].exp);
          old = exp;
          exp = boolector_and (parser->btor, old, tmp);
          boolector_release (parser->btor, old);
          boolector_release (parser->btor, tmp);
        }
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_DISTINCT_TAG_SMT2)
      {
        if (!nargs)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser, "arguments to 'distinct' missing");
        }
        if (nargs == 1)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser, "only one argument to 'distinct'");
        }
        if (!check_arg_sorts_match_smt2 (parser, p, nargs)) return 0;
        exp = boolector_true (parser->btor);
        for (i = 1; i < nargs; i++)
        {
          for (j = i + 1; j <= nargs; j++)
          {
            tmp = boolector_ne (parser->btor, p[i].exp, p[j].exp);
            old = exp;
            exp = boolector_and (parser->btor, old, tmp);
            boolector_release (parser->btor, old);
            boolector_release (parser->btor, tmp);
          }
        }
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_ITE_TAG_SMT2)
      {
        if (!check_nargs_smt2 (parser, p, nargs, 3)) return 0;
        if (!check_ite_args_sorts_match_smt2 (parser, p)) return 0;
        exp = boolector_cond (parser->btor, p[1].exp, p[2].exp, p[3].exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_SELECT_TAG_SMT2)
      {
        if (!check_nargs_smt2 (parser, p, nargs, 2)) return 0;
        if (!boolector_is_array (parser->btor, p[1].exp))
        {
          parser->perrcoo = p[1].coo;
          return !perr_smt2 (parser,
                             "first argument of 'select' is not an array");
        }
        if (boolector_is_array (parser->btor, p[2].exp))
        {
          parser->perrcoo = p[2].coo;
          return !perr_smt2 (parser, "second argument of 'select' is an array");
        }
        width  = boolector_get_width (parser->btor, p[2].exp);
        domain = boolector_get_index_width (parser->btor, p[1].exp);
        if (width != domain)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser,
                             "first (array) argument of 'select' has index "
                             "bit-width %d but the second (index) argument "
                             "has bit-width %d",
                             domain,
                             width);
        }
        exp = boolector_read (parser->btor, p[1].exp, p[2].exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_STORE_TAG_SMT2)
      {
        if (!check_nargs_smt2 (parser, p, nargs, 3)) return 0;
        if (!boolector_is_array (parser->btor, p[1].exp))
        {
          parser->perrcoo = p[1].coo;
          return !perr_smt2 (parser,
                             "first argument of 'store' is not an array");
        }
        if (boolector_is_array (parser->btor, p[2].exp))
        {
          parser->perrcoo = p[2].coo;
          return !perr_smt2 (parser, "second argument of 'store' is an array");
        }
        if (boolector_is_array (parser->btor, p[3].exp))
        {
          parser->perrcoo = p[3].coo;
          return !perr_smt2 (parser, "third argument of 'store' is an array");
        }
        width  = boolector_get_width (parser->btor, p[2].exp);
        domain = boolector_get_index_width (parser->btor, p[1].exp);
        if (width != domain)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser,
                             "first (array) argument of 'store' has index "
                             "bit-width %d but the second (index) argument "
                             "has bit-width %d",
                             domain,
                             width);
        }
        width = boolector_get_width (parser->btor, p[1].exp);
        len   = boolector_get_width (parser->btor, p[3].exp);
        if (width != len)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser,
                             "first (array) argument of 'store' has element "
                             "bit-width %d but the third (stored bit-vector) "
                             "argument has bit-width %d",
                             width,
                             len);
        }
        exp = boolector_write (parser->btor, p[1].exp, p[2].exp, p[3].exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_EXTRACT_TAG_SMT2)
      {
        if (!check_nargs_smt2 (parser, p, nargs, 1)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        width = boolector_get_width (parser->btor, p[1].exp);
        if (width <= p->hi)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser,
                             "first (high) 'extract' parameter %d too large "
                             "for bit-vector argument of bit-width %d",
                             p->hi,
                             width);
        }
        exp = boolector_slice (parser->btor, p[1].exp, p->hi, p->lo);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_BVNOT_TAG_SMT2)
      {
        unaryfun = boolector_not;
      UNARY_BV_FUN:
        if (!check_nargs_smt2 (parser, p, nargs, 1)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        exp = unaryfun (parser->btor, p[1].exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_BVNEG_TAG_SMT2)
      {
        unaryfun = boolector_neg;
        goto UNARY_BV_FUN;
      }
      else if (tag == BTOR_BVREDOR_TAG_SMT2)
      {
        unaryfun = boolector_redor;
        goto UNARY_BV_FUN;
      }
      else if (tag == BTOR_BVREDAND_TAG_SMT2)
      {
        unaryfun = boolector_redand;
        goto UNARY_BV_FUN;
      }
      else if (tag == BTOR_CONCAT_TAG_SMT2)
      {
        binfun = boolector_concat;
      BIN_BV_LEFT_ASSOCIATIVE_CORE:
        if (nargs < 2)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser, "argument to '%s' missing", p->node->name);
        }
        if (tag != BTOR_CONCAT_TAG_SMT2
            && !check_arg_sorts_match_smt2 (parser, p, nargs))
          return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        exp = 0;
        for (i = 1; i <= nargs; i++)
        {
          if (exp)
          {
            old = exp;
            exp = binfun (parser->btor, old, p[i].exp);
            boolector_release (parser->btor, old);
          }
          else
            exp = boolector_copy (parser->btor, p[i].exp);
        }
        assert (exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_BVAND_TAG_SMT2)
      {
        binfun = boolector_and;
        goto BIN_BV_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_BVOR_TAG_SMT2)
      {
        binfun = boolector_or;
        goto BIN_BV_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_BVXOR_TAG_SMT2)
      {
        binfun = boolector_xor;
        goto BIN_BV_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_BVADD_TAG_SMT2)
      {
        binfun = boolector_add;
        goto BIN_BV_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_BVSUB_TAG_SMT2)
      {
        binfun = boolector_sub;
        goto BIN_BV_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_BVMUL_TAG_SMT2)
      {
        binfun = boolector_mul;
        goto BIN_BV_LEFT_ASSOCIATIVE_CORE;
      }
      else if (tag == BTOR_BVUDIV_TAG_SMT2)
      {
        binfun = boolector_udiv;
      BINARY_BV_FUN:
        if (!check_nargs_smt2 (parser, p, nargs, 2)) return 0;
        if (!check_arg_sorts_match_smt2 (parser, p, 2)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        exp = binfun (parser->btor, p[1].exp, p[2].exp);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_BVUREM_TAG_SMT2)
      {
        binfun = boolector_urem;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSHL_TAG_SMT2)
      {
        binfun = shl_smt2;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVLSHR_TAG_SMT2)
      {
        binfun = lshr_smt2;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVULT_TAG_SMT2)
      {
        binfun = boolector_ult;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVNAND_TAG_SMT2)
      {
        binfun = boolector_nand;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVNOR_TAG_SMT2)
      {
        binfun = boolector_nor;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVXNOR_TAG_SMT2)
      {
        binfun = boolector_xnor;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVCOMP_TAG_SMT2)
      {
        binfun = boolector_eq;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSDIV_TAG_SMT2)
      {
        binfun = boolector_sdiv;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSREM_TAG_SMT2)
      {
        binfun = boolector_srem;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSMOD_TAG_SMT2)
      {
        binfun = boolector_smod;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVASHR_TAG_SMT2)
      {
        binfun = ashr_smt2;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_REPEAT_TAG_SMT2)
      {
        if (!check_nargs_smt2 (parser, p, nargs, 1)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        width = boolector_get_width (parser->btor, p[1].exp);
        if (p->num && ((INT_MAX / p->num) < width))
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (parser,
                             "resulting bit-width of 'repeat' too large");
        }
        exp = boolector_copy (parser->btor, p[1].exp);
        for (i = 1; i < p->num; i++)
        {
          old = exp;
          exp = boolector_concat (parser->btor, old, p[1].exp);
          boolector_release (parser->btor, old);
        }
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_ZERO_EXTEND_TAG_SMT2)
      {
        extfun = boolector_uext;
      EXTEND_BV_FUN:
        if (!check_nargs_smt2 (parser, p, nargs, 1)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        width = boolector_get_width (parser->btor, p[1].exp);
        if (INT_MAX - p->num < width)
        {
          parser->perrcoo = p->coo;
          return !perr_smt2 (
              parser, "resulting bit-width of '%s' too large", p->node->name);
        }
        exp = extfun (parser->btor, p[1].exp, p->num);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_SIGN_EXTEND_TAG_SMT2)
      {
        extfun = boolector_sext;
        goto EXTEND_BV_FUN;
      }
      else if (tag == BTOR_ROTATE_LEFT_TAG_SMT2)
      {
        rotatefun = rotate_left_smt2;
      ROTATE_BV_FUN:
        if (!check_nargs_smt2 (parser, p, nargs, 1)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        width = boolector_get_width (parser->btor, p[1].exp);
        exp   = rotatefun (parser->btor, p[1].exp, p->num % width);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_ROTATE_RIGHT_TAG_SMT2)
      {
        rotatefun = rotate_right_smt2;
        goto ROTATE_BV_FUN;
      }
      /* Z3 bit vector extension */
      else if (tag == BTOR_EXT_ROTATE_LEFT_TAG_SMT2
               || tag == BTOR_EXT_ROTATE_RIGHT_TAG_SMT2)
      {
        if (!check_nargs_smt2 (parser, p, nargs, 2)) return 0;
        if (!check_not_array_or_uf_args_smt2 (parser, p, nargs)) return 0;
        if (!boolector_is_const (parser->btor, p[2].exp))
        {
          parser->perrcoo = p[2].coo;
          return !perr_smt2 (
              parser,
              "second argument '%s' of ext_rotate_%s"
              "is not a bit vector constant",
              p[2].node->name,
              tag == BTOR_EXT_ROTATE_LEFT_TAG_SMT2 ? "left" : "right");
        }
        exp = translate_ext_rotate_smt2 (parser->btor,
                                         p[1].exp,
                                         p[2].exp,
                                         tag == BTOR_EXT_ROTATE_LEFT_TAG_SMT2);
        goto RELEASE_EXP_AND_OVERWRITE;
      }
      else if (tag == BTOR_BVULE_TAG_SMT2)
      {
        binfun = boolector_ulte;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVUGT_TAG_SMT2)
      {
        binfun = boolector_ugt;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVUGE_TAG_SMT2)
      {
        binfun = boolector_ugte;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSLT_TAG_SMT2)
      {
        binfun = boolector_slt;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSLE_TAG_SMT2)
      {
        binfun = boolector_slte;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSGT_TAG_SMT2)
      {
        binfun = boolector_sgt;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_BVSGE_TAG_SMT2)
      {
        binfun = boolector_sgte;
        goto BINARY_BV_FUN;
      }
      else if (tag == BTOR_LET_TAG_SMT2)
      {
        BtorSMT2Node *s;
        for (i = 1; i < nargs; i++)
        {
          if (p[i].tag != BTOR_SYMBOL_TAG_SMT2)
          {
            parser->perrcoo = p[i].coo;
            return !perr_smt2 (
                parser, "expected symbol as argument %d of 'let'", i);
          }
        }
        if (p[nargs].tag != BTOR_SYMBOL_TAG_SMT2)
        {
          if (p[i].tag != BTOR_EXP_TAG_SMT2)
          {
            parser->perrcoo = p[i].coo;
            return !perr_smt2 (
                parser, "expected expression as argument %d of 'let'", nargs);
          }
        }
        l[0].tag = BTOR_EXP_TAG_SMT2;
        l[0].exp = p[nargs].exp;
        for (i = 1; i < nargs; i++)
        {
          assert (p[i].tag == BTOR_SYMBOL_TAG_SMT2);
          s = p[i].node;
          assert (s);
          assert (s->coo.x);
          assert (s->tag == BTOR_SYMBOL_TAG_SMT2);
          remove_symbol_smt2 (parser, s);
        }
        parser->work.top = p;
      }
      else if (tag == BTOR_LETBIND_TAG_SMT2)
      {
        assert (p[1].tag == BTOR_SYMBOL_TAG_SMT2);
        if (nargs == 1)
          return !perr_smt2 (
              parser, "term to be bound to '%s' missing", p[1].node->name);
        if (nargs > 2)
        {
          parser->perrcoo = p[3].coo;
          return !perr_smt2 (
              parser, "second term bound to '%s'", p[1].node->name);
        }
        if (p[2].tag != BTOR_EXP_TAG_SMT2)
        {
          parser->perrcoo = p[2].coo;
          return !perr_smt2 (parser, "expected expression in 'let' binding");
        }
        l[0] = p[1];
        assert (!l[0].node->exp);
        assert (p[2].tag == BTOR_EXP_TAG_SMT2);
        l[0].node->exp = p[2].exp;
        assert (!l[0].node->bound);
        l[0].node->bound = 1;
        parser->work.top = p;
        assert (!parser->binding);
        parser->binding = 1;
      }
      else if (tag == BTOR_PARLETBINDING_TAG_SMT2)
      {
        assert (parser->binding);
        parser->binding = 0;
#ifndef NDEBUG
        for (i = 1; i <= nargs; i++) assert (p[i].tag == BTOR_SYMBOL_TAG_SMT2);
#endif
        for (i = 0; i < nargs; i++) l[i] = p[i + 1];
        parser->work.top = l + nargs;
        assert (!parser->expecting_let_body);
        parser->expecting_let_body = 1;
      }
      else
      {
        // TODO unreachable?
        parser->perrcoo = p->coo;
        return !perr_smt2 (
            parser,
            "internal parse error: can not close yet unsupported '%s'",
            item2str_smt2 (p));
      }
      assert (open > 0);
      open--;
    }
    else
    {
      if (parser->expecting_let_body) parser->expecting_let_body = 0;
      p = push_item_smt2 (parser, tag);
      if (tag == BTOR_LPAR_TAG_SMT2)
      {
        if (parser->binding)
        {
          BtorSMT2Node *s;
          BtorSMT2Item *q;
          push_item_smt2 (parser, BTOR_LETBIND_TAG_SMT2);
          parser->binding = 0;

          tag = read_token_smt2 (parser);

          for (i = 0; tokens && i < BTOR_COUNT_STACK (parser->token); i++)
          {
            c = BTOR_PEEK_STACK (parser->token, i);
            BTOR_PUSH_STACK (parser->mem, *tokens, c ? c : ' ');
          }

          if (tag == BTOR_INVALID_TAG_SMT2) return 0;
          if (tag == EOF)
            return !perr_smt2 (
                parser,
                "expected symbol to be bound after '(' at line %d "
                "column %d but reached end-of-file",
                p->coo.x,
                p->coo.y);

          if (tag != BTOR_SYMBOL_TAG_SMT2)
            return !perr_smt2 (
                parser,
                "expected symbol to be bound at '%s' after '(' at "
                "line %d column %d",
                parser->token.start,
                p->coo.x,
                p->coo.y);
          s = parser->last_node;
          assert (s);
          if (s->coo.x)
            return !perr_smt2 (
                parser,
                "symbol '%s' to be bound already %s at line %d "
                "column %d",
                s->name,
                s->bound ? "bound with 'let'" : "declared as function",
                s->coo.x,
                s->coo.y);
          s->coo  = parser->coo;
          q       = push_item_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
          q->node = s;
        }
        open++;
      }
      else if (parser->binding)
      {
        return !perr_smt2 (
            parser, "expected binding at '%s'", parser->token.start);
      }
      else if (item_with_node_smt2 (p))
      {
        p->node = parser->last_node;
        if (tag & BTOR_COMMAND_TAG_CLASS_SMT2)
          return !perr_smt2 (parser, "unexpected command '%s'", p->node->name);
        if (tag & BTOR_KEYWORD_TAG_CLASS_SMT2)
          return !perr_smt2 (parser, "unexpected keyword '%s'", p->node->name);
        if (tag & BTOR_LOGIC_TAG_CLASS_SMT2)
          return !perr_smt2 (parser, "unexpected logic '%s'", p->node->name);
        if (tag & BTOR_RESERVED_TAG_CLASS_SMT2)
        {
          if (tag == BTOR_LET_TAG_SMT2)
          {
            if (!read_lpar_smt2 (parser, " after 'let'")) return 0;
            push_item_smt2 (parser, BTOR_LPAR_TAG_SMT2);
            open++, assert (open > 0);
            push_item_smt2 (parser, BTOR_PARLETBINDING_TAG_SMT2);
            assert (!parser->binding);
            parser->binding = 1;
          }
          else if (tag == BTOR_UNDERSCORE_TAG_SMT2)
          {
            const char *read_rpar_msg = 0;
            BtorSMT2Node *node        = 0;

            if (!prev_item_was_lpar_smt2 (parser)) return 0;

            tag  = read_token_smt2 (parser);
            node = parser->last_node;

            for (i = 0; tokens && i < BTOR_COUNT_STACK (parser->token); i++)
            {
              c = BTOR_PEEK_STACK (parser->token, i);
              BTOR_PUSH_STACK (parser->mem, *tokens, c ? c : ' ');
            }

            if (tag == BTOR_INVALID_TAG_SMT2) return 0;
            if (tag == EOF)
              return !perr_smt2 (parser, "unexpected end-of-file after '_'");

            if (tag == BTOR_REPEAT_TAG_SMT2)
            {
              assert (node && tag == (int) node->tag);
              read_rpar_msg = " to close '(_ repeat'";
            ONE_FIXED_NUM_PARAMETRIC:
              assert (BTOR_COUNT_STACK (parser->work) >= 2);
              if (BTOR_COUNT_STACK (parser->work) < 3)
              {
                assert (BTOR_COUNT_STACK (parser->work) == 2);
                assert (parser->work.start[0].tag == BTOR_LPAR_TAG_SMT2);
                assert (parser->work.start[1].tag == BTOR_UNDERSCORE_TAG_SMT2);
                parser->perrcoo = parser->work.start[0].coo;
                return !perr_smt2 (
                    parser, "expected another '(' before '(_ %s'", node->name);
              }
              if (parser->work.top[-3].tag != BTOR_LPAR_TAG_SMT2)
              {
                parser->perrcoo = parser->work.top[-3].coo;
                return !perr_smt2 (parser,
                                   "expected '(' at '%s' before '(_ %s'",
                                   item2str_smt2 (parser->work.top - 3),
                                   node->name);
              }
              l = p - 1;
              if (!parse_int32_smt2 (parser, 0, &l->num, tokens)) return 0;
              l->tag           = tag;
              l->node          = node;
              parser->work.top = p;
              if (!read_rpar_smt2 (parser, read_rpar_msg)) return 0;
              if (tokens) BTOR_PUSH_STACK (parser->mem, *tokens, ')');
              assert (open > 0);
              open--;
            }
            else if (tag == BTOR_ZERO_EXTEND_TAG_SMT2)
            {
              read_rpar_msg = " to close '(_ zero_extend'";
              goto ONE_FIXED_NUM_PARAMETRIC;
            }
            else if (tag == BTOR_SIGN_EXTEND_TAG_SMT2)
            {
              read_rpar_msg = " to close '(_ sign_extend'";
              goto ONE_FIXED_NUM_PARAMETRIC;
            }
            else if (tag == BTOR_ROTATE_LEFT_TAG_SMT2)
            {
              read_rpar_msg = " to close '(_ rotate_left'";
              goto ONE_FIXED_NUM_PARAMETRIC;
            }
            else if (tag == BTOR_ROTATE_RIGHT_TAG_SMT2)
            {
              read_rpar_msg = " to close '(_ rotate_right'";
              goto ONE_FIXED_NUM_PARAMETRIC;
            }
            else if (tag == BTOR_EXTRACT_TAG_SMT2)
            {
              BtorSMT2Coo firstcoo;
              assert (node && tag == (int) node->tag);
              if (BTOR_COUNT_STACK (parser->work) < 3
                  || parser->work.top[-3].tag != BTOR_LPAR_TAG_SMT2)
                goto ONE_FIXED_NUM_PARAMETRIC;
              l = p - 1;
              if (!parse_int32_smt2 (parser, 0, &l->hi, tokens)) return 0;
              firstcoo = parser->coo;
              if (!parse_int32_smt2 (parser, 0, &l->lo, tokens)) return 0;
              if (l->hi < l->lo)
              {
                parser->perrcoo = firstcoo;
                return !perr_smt2 (parser,
                                   "first parameter '%d' of '(_ extract' "
                                   "smaller than second '%d'",
                                   l->hi,
                                   l->lo);
              }
              l->tag           = tag;
              l->node          = node;
              parser->work.top = p;
              if (!read_rpar_smt2 (parser, " to close '(_ extract'")) return 0;
              if (tokens) BTOR_PUSH_STACK (parser->mem, *tokens, ')');
              assert (open > 0);
              open--;
            }
            else if (tag == BTOR_SYMBOL_TAG_SMT2
                     && bvconst_str_smt2 (parser->token.start))
            {
              char *constr, *decstr;
              BtorSMT2Coo coo;
              int len;
              exp    = 0;
              decstr = btor_strdup (parser->mem, parser->token.start + 2);
              constr =
                  btor_decimal_to_const (parser->mem, parser->token.start + 2);
              coo = parser->coo;
              coo.y += 2;
              if (!parse_int32_smt2 (parser, 1, &width, tokens))
                goto UNDERSCORE_DONE;
              len = (int) strlen (constr);
              if (len > width)
              {
                parser->perrcoo = coo;
                (void) perr_smt2 (parser,
                                  "decimal constant '%s' needs %d bits which "
                                  "exceeds bit-width '%d'",
                                  decstr,
                                  len,
                                  width);
              }
              else if (len == width)
                exp = boolector_const (parser->btor, constr);
              else if (!len)
              {
                s   = boolector_bitvec_sort (parser->btor, width);
                exp = boolector_zero (parser->btor, s);
                boolector_release_sort (parser->btor, s);
              }
              else
              {
                char *uconstr =
                    btor_uext_const (parser->mem, constr, width - len);
                exp = boolector_const (parser->btor, uconstr);
                btor_freestr (parser->mem, uconstr);
              }
            UNDERSCORE_DONE:
              btor_freestr (parser->mem, decstr);
              btor_delete_const (parser->mem, constr);
              if (!exp) return 0;
              assert (boolector_get_width (parser->btor, exp) == width);
              assert (p > parser->work.start);
              p--, parser->work.top--;
              assert (p->tag == BTOR_LPAR_TAG_SMT2);
              assert (open > 0);
              open--;
              p->tag = BTOR_EXP_TAG_SMT2;
              p->exp = exp;
              if (!read_rpar_smt2 (parser, " to close '(_ bv..'")) return 0;
              if (tokens) BTOR_PUSH_STACK (parser->mem, *tokens, ')');
            }
            else
              return !perr_smt2 (parser,
                                 "invalid parametric term '_ %s'",
                                 parser->token.start);
          }
          else
          {
            assert (p->node->name);
            return !perr_smt2 (
                parser, "unsupported reserved word '%s'", p->node->name);
          }
        }
        else if (tag == BTOR_SYMBOL_TAG_SMT2)
        {
          assert (p->node);
          if (!p->node->exp)
            return !perr_smt2 (parser, "undefined symbol '%s'", p->node->name);
          p->tag = BTOR_EXP_TAG_SMT2;
          p->exp = boolector_copy (parser->btor, p->node->exp);
        }
        else if (tag == BTOR_TRUE_TAG_SMT2)
        {
          p->tag = BTOR_EXP_TAG_SMT2;
          p->exp = boolector_true (parser->btor);
        }
        else if (tag == BTOR_FALSE_TAG_SMT2)
        {
          p->tag = BTOR_EXP_TAG_SMT2;
          p->exp = boolector_false (parser->btor);
        }
        else if (tag == BTOR_ATTRIBUTE_TAG_SMT2)
        {
          return !perr_smt2 (
              parser, "unexpected attribute '%s'", parser->token.start);
        }
        else if (tag & BTOR_CORE_TAG_CLASS_SMT2)
        {
          if (tag == BTOR_BOOL_TAG_SMT2)
            return !perr_smt2 (parser, "unexpected 'Bool'");
        }
        else if (tag & BTOR_ARRAY_TAG_CLASS_SMT2)
        {
          if (tag == BTOR_ARRAY_TAG_SMT2)
            return !perr_smt2 (parser, "unexpected 'Array'");
        }
        else if (tag & BTOR_BITVEC_TAG_CLASS_SMT2)
        {
          if (tag == BTOR_BITVEC_TAG_SMT2)
            return !perr_smt2 (parser, "unexpected 'BitVec'");
        }
        else
          return !perr_smt2 (
              parser, "unexpected token '%s'", item2str_smt2 (p));
      }
      else if (tag == BTOR_BINARY_CONSTANT_TAG_SMT2)
      {
        p->tag = BTOR_EXP_TAG_SMT2;
        p->exp = boolector_const (parser->btor, parser->token.start + 2);
      }
      else if (tag == BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2)
      {
        char *constr = btor_hex_to_const (parser->mem, parser->token.start + 2);
        int len      = strlen (constr);
        int width    = strlen (parser->token.start + 2) * 4;
        char *uconstr;
        assert (len <= width);
        if (len == width)
          uconstr = constr;
        else
          uconstr = btor_uext_const (parser->mem, constr, width - len);
        p->tag = BTOR_EXP_TAG_SMT2;
        p->exp = boolector_const (parser->btor, uconstr);
        if (uconstr != constr) btor_delete_const (parser->mem, uconstr);
        btor_delete_const (parser->mem, constr);
      }
      else
        return !perr_smt2 (
            parser, "unexpected token '%s'", parser->token.start);
    }
  } while (open);
  if (BTOR_COUNT_STACK (parser->work) - work_cnt != 1)
  {
    parser->perrcoo = p->coo;
    // This should not occur, but we keep it as a bad style of
    // defensive programming for future extensions of the parser.
    return !perr_smt2 (parser,
                       "internal parse error: worker stack of size %d",
                       BTOR_COUNT_STACK (parser->work));
  }
  parser->work.top -= 1;
  p = parser->work.top;
  if (p->tag != BTOR_EXP_TAG_SMT2)
  {
    parser->perrcoo = p->coo;
    // Ditto, same comment wrt defensive programming an future use.
    return !perr_smt2 (
        parser,
        "internal parse error: failed to translate parsed term at '%s'",
        item2str_smt2 (p));
  }
  res     = boolector_copy (parser->btor, p->exp);
  *cooptr = p->coo;
  release_item_smt2 (parser, p);
  assert (BTOR_COUNT_STACK (parser->work) == work_cnt);
  *resptr = res;
  if (tokens && BTOR_TOP_STACK (*tokens) == ' ')
    tokens->start[BTOR_COUNT_STACK (*tokens) - 1] = 0;
  return 1;
}

static int
parse_term_smt2 (BtorSMT2Parser *parser,
                 BoolectorNode **resptr,
                 BtorSMT2Coo *cooptr)
{
  return parse_term_aux_smt2 (parser, 0, 0, resptr, cooptr, 0);
}

/*
 * skiptokens = 1 -> skip BTOR_LPAR_TAG_SMT2
 * skiptokens = 2 -> skip BTOR_UNDERSCORE_TAG_SMT2
 */
static int
parse_bitvec_sort (BtorSMT2Parser *parser,
                   int skiptokens,
                   BoolectorSort *resptr)
{
  assert (skiptokens >= 0);
  assert (skiptokens <= 2);

  int tag, width;
  if (skiptokens < 1 && !read_lpar_smt2 (parser, 0)) return 0;
  if (skiptokens < 2)
  {
    tag = read_token_smt2 (parser);
    if (tag == EOF)
      return !perr_smt2 (parser, "expected '_' but reached end-of-file");
    if (tag != BTOR_UNDERSCORE_TAG_SMT2)
      return !perr_smt2 (parser, "expected '_' at '%s'", parser->token.start);
  }
  tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser, "expected 'BitVec' but reached end-of-file");
  if (tag != BTOR_BITVEC_TAG_SMT2)
    return !perr_smt2 (
        parser, "expected 'BitVec' at '%s'", parser->token.start);
  tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser, "expected bit-width but reached end-of-file");
  if (tag != BTOR_DECIMAL_CONSTANT_TAG_SMT2)
    return !perr_smt2 (
        parser, "expected bit-width at '%s'", parser->token.start);
  assert (parser->token.start[0] != '-');
  if (strchr (parser->token.start, '.'))
    return !perr_smt2 (
        parser, "invalid floating point bit-width '%s'", parser->token.start);
  if (parser->token.start[0] == '0')
  {
    assert (!parser->token.start[1]);
    return !perr_smt2 (parser, "invalid zero bit-width");
  }
  width = 0;
  if (!str2int32_smt2 (parser, 1, parser->token.start, &width)) return 0;
  BTOR_MSG (boolector_get_btor_msg (parser->btor),
            3,
            "parsed bit-vector sort of width %d",
            width);

  *resptr = boolector_bitvec_sort (parser->btor, width);
  BTOR_PUSH_STACK (parser->mem, parser->sorts, *resptr);
  return read_rpar_smt2 (parser, " to close bit-vector sort");
}

static int parse_sort (BtorSMT2Parser *parser,
                       int tag,
                       bool allow_array_sort,
                       BoolectorSort *sort);

static int
parse_array_sort (BtorSMT2Parser *parser, int tag, BoolectorSort *sort)
{
  BoolectorSort index, value;
  if (tag == BTOR_ARRAY_TAG_SMT2)
  {
    // TODO (ma): check all logics with no arrays?
    if (parser->commands.set_logic && parser->res->logic == BTOR_LOGIC_QF_BV)
      return !perr_smt2 (parser, "'Array' invalid for logic 'QF_BV'");
    tag = read_token_smt2 (parser);
    if (!parse_sort (parser, tag, false, &index)) return 0;
    tag = read_token_smt2 (parser);
    if (!parse_sort (parser, tag, false, &value)) return 0;
    if (!read_rpar_smt2 (parser, " after element sort of Array")) return 0;
    *sort = boolector_array_sort (parser->btor, index, value);
    BTOR_PUSH_STACK (parser->mem, parser->sorts, *sort);
    return 1;
  }
  else if (tag == EOF)
    return !perr_smt2 (parser, "reached end-of-file but expected 'Array'");
  return !perr_smt2 (parser, "expected 'Array' at '%s'", parser->token.start);
}

static int
parse_sort (BtorSMT2Parser *parser,
            int tag,
            bool allow_array_sort,
            BoolectorSort *sort)
{
  BtorSMT2Node *alias;

  if (tag == BTOR_BOOL_TAG_SMT2)
  {
    *sort = boolector_bool_sort (parser->btor);
    BTOR_PUSH_STACK (parser->mem, parser->sorts, *sort);
    return 1;
  }
  else if (tag == BTOR_LPAR_TAG_SMT2)
  {
    if (allow_array_sort)
    {
      tag = read_token_smt2 (parser);
      if (tag == BTOR_ARRAY_TAG_SMT2)
        return parse_array_sort (parser, tag, sort);
      else
      {
        if (tag == EOF)
          return !perr_smt2 (parser,
                             "expected '_' or 'Array' but reached end-of-file");
        if (tag != BTOR_UNDERSCORE_TAG_SMT2)
          return !perr_smt2 (
              parser, "expected '_' or 'Array' at '%s'", parser->token.start);
        return parse_bitvec_sort (parser, 2, sort);
      }
    }
    else
      return parse_bitvec_sort (parser, 1, sort);
  }
  else if (tag == BTOR_SYMBOL_TAG_SMT2)
  {
    alias = find_symbol_smt2 (parser, parser->token.start);
    if (!alias || !alias->sort)
      return !perr_smt2 (parser, "invalid sort '%s'", parser->token.start);
    *sort = alias->sort_alias;
    return 1;
  }
  else if (tag == EOF)
    return !perr_smt2 (parser,
                       "reached end-of-file but expected '(' or 'Bool'");
  return !perr_smt2 (
      parser, "expected '(' or 'Bool' at '%s'", parser->token.start);
}

static int
declare_fun_smt2 (BtorSMT2Parser *parser)
{
  char *symbol;
  int tag;
  BoolectorSortStack args;
  BtorSMT2Node *fun;
  fun = 0;
  BoolectorSort sort, s;

  if (!read_symbol (parser, " after 'declare-fun'", &fun)) return 0;
  assert (fun && fun->tag == BTOR_SYMBOL_TAG_SMT2);
  if (fun->coo.x)
    return !perr_smt2 (parser,
                       "symbol '%s' already defined at line %d column %d",
                       fun->name,
                       fun->coo.x,
                       fun->coo.y);
  fun->coo = parser->coo;
  if (!read_lpar_smt2 (parser, " after function name")) return 0;

  BTOR_INIT_STACK (args);
  do
  {
    tag = read_token_smt2 (parser);
    if (tag != BTOR_RPAR_TAG_SMT2)
    {
      if (!parse_sort (parser, tag, false, &sort))
      {
        BTOR_RELEASE_STACK (parser->mem, args);
        return 0;
      }
      BTOR_PUSH_STACK (parser->mem, args, sort);
    }
  } while (tag != BTOR_RPAR_TAG_SMT2);

  /* parse return sort */
  tag = read_token_smt2 (parser);
  if (!parse_sort (parser, tag, true, &sort))
  {
    BTOR_RELEASE_STACK (parser->mem, args);
    return 0;
  }
  if (boolector_is_array_sort (parser->btor, sort))
  {
    if (!BTOR_EMPTY_STACK (args))
    {
      BTOR_RELEASE_STACK (parser->mem, args);
      return !perr_smt2 (parser, "sort Array is not supported for arity > 0");
    }
    fun->exp = boolector_array (parser->btor, sort, fun->name);
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              2,
              "declared bit-vector array '%s' at line %d column %d",
              fun->name,
              fun->coo.x,
              fun->coo.y);
    parser->need_functions = 1;
  }
  else
  {
    if (BTOR_EMPTY_STACK (args))
    {
      symbol   = create_symbol_current_scope (parser, fun->name);
      fun->exp = boolector_var (parser->btor, sort, symbol);
      btor_freestr (parser->mem, symbol);
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "declared '%s' as bit-vector at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
    }
    else
    {
      s = boolector_fun_sort (
          parser->btor, args.start, BTOR_COUNT_STACK (args), sort);
      symbol   = create_symbol_current_scope (parser, fun->name);
      fun->exp = boolector_uf (parser->btor, s, symbol);
      boolector_release_sort (parser->btor, s);
      btor_freestr (parser->mem, symbol);
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "declared '%s' as uninterpreted function at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
      parser->need_functions = 1;
    }
  }
  (void) boolector_copy (parser->btor, fun->exp);
  BTOR_PUSH_STACK (parser->mem, parser->inputs, fun->exp);
  BTOR_RELEASE_STACK (parser->mem, args);
  return read_rpar_smt2 (parser, " to close declaration");
}

/* Note: if we're currently parsing a model, define-fun for sorted vars
 *	 have to be transformed into assertions of the form
 *       assert (= var assignment), define-funs for funs with args >= 1
 *       have to be built before asserting.
 *       Further, all symbols we parse are already defined -> check sort. */
static int
define_fun_smt2 (BtorSMT2Parser *parser)
{
  int tag, nargs = 0, len;
  BoolectorNode *eq, *tmp, *exp = 0;
  BtorSMT2Coo coo;
  BtorSMT2Item *item;
  BtorSMT2Node *fun, *arg;
  BoolectorNodePtrStack args;
  char *psym, *symbol;
  BoolectorSort sort, s;

  fun   = 0;
  arg   = 0;
  coo.x = coo.y = 0;

  if (!read_symbol (parser, " after 'define-fun'", &fun)) return 0;
  assert (fun && fun->tag == BTOR_SYMBOL_TAG_SMT2);

  if (fun->coo.x && !parser->commands.model)
  {
    return !perr_smt2 (parser,
                       "symbol '%s' already defined at line %d column %d",
                       fun->name,
                       fun->coo.x,
                       fun->coo.y);
  }
  else if (!fun->coo.x && parser->commands.model)
  {
    return !perr_smt2 (parser, "symbol '%s' undefined");
  }
  else /* do not redefine during model parsing */
  {
    fun->coo = parser->coo;
  }

  if (!read_lpar_smt2 (parser, " after function name")) return 0;

  /* parse function arguments */
  do
  {
    tag = read_token_smt2 (parser);

    if (tag != BTOR_RPAR_TAG_SMT2)
    {
      if (tag != BTOR_LPAR_TAG_SMT2) return !perr_smt2 (parser, "expected '('");
      if (!read_symbol (parser, " after '('", &arg)) return 0;
      assert (arg && arg->tag == BTOR_SYMBOL_TAG_SMT2);
      if (arg->coo.x)
        return !perr_smt2 (parser,
                           "symbol '%s' already defined at line %d column %d",
                           arg->name,
                           arg->coo.x,
                           arg->coo.y);
      arg->coo = parser->coo;

      tag = read_token_smt2 (parser);
      if (!parse_sort (parser, tag, false, &s)) return 0;
      nargs++;
      len = strlen (fun->name) + strlen (arg->name) + 3;
      BTOR_CNEWN (parser->mem, psym, len);
      sprintf (psym, "_%s_%s", fun->name, arg->name);
      arg->exp = boolector_param (parser->btor, s, psym);
      BTOR_DELETEN (parser->mem, psym, len);
      item       = push_item_smt2 (parser, arg->tag);
      item->node = arg;

      if (!read_rpar_smt2 (parser, " after argument sort")) return 0;
    }
  } while (tag != BTOR_RPAR_TAG_SMT2);

  /* parse return sort */
  tag = read_token_smt2 (parser);
  if (!parse_sort (parser, tag, true, &sort)) return 0;
  if (boolector_is_array_sort (parser->btor, sort))
  {
    if (nargs)
    {
      return !perr_smt2 (parser, "sort Array is not supported for arity > 0");
    }

    if (!parser->commands.model)
    {
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "defined bit-vector array '%s' at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
      parser->need_functions = 1;
    }
    else
    {
      if (!boolector_is_array (parser->btor, fun->exp))
        return !perr_smt2 (parser, "sort Array expected");
      if (boolector_get_sort (parser->btor, fun->exp) != sort)
        return !perr_smt2 (parser, "array sort mismatch");
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "parsed bit-vector array '%s' at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
      assert (parser->need_functions);
    }
  }
  else
  {
    if (!parser->commands.model)
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "defined '%s' as bit-vector at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
    else
    {
      if (boolector_get_sort (parser->btor, fun->exp) != sort)
        return !perr_smt2 (parser, "invalid sort, expected");
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "parsed '%s' as bit-vector at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
    }
  }

  if (!parse_term_smt2 (parser, &exp, &coo)) return 0;

  // TODO (ma): this temporarily disables the sort check for function models
  //            until we have a api function for retrieving the index/element
  //            sorts of an array sort.
  if (!parser->commands.model && boolector_get_sort (parser->btor, exp) != sort)
  {
    boolector_release (parser->btor, exp);
    return !perr_smt2 (parser, "invalid term sort");
  }

  if (nargs)
  {
    BTOR_INIT_STACK (args);
    item = parser->work.top - nargs;
    /* collect arguments, remove symbols (scope is only this function) */
    while (item < parser->work.top)
    {
      arg = item->node;
      item++;
      assert (arg);
      assert (arg->coo.x);
      assert (arg->tag == BTOR_SYMBOL_TAG_SMT2);
      BTOR_PUSH_STACK (
          parser->mem, args, boolector_copy (parser->btor, arg->exp));
      remove_symbol_smt2 (parser, arg);
    }
    parser->work.top -= nargs;
    assert (BTOR_EMPTY_STACK (parser->work));
    tmp = boolector_fun (parser->btor, args.start, nargs, exp);
    if (parser->commands.model)
    {
      if (!boolector_is_equal_sort (parser->btor, fun->exp, tmp))
      {
        boolector_release (parser->btor, tmp);
        while (!BTOR_EMPTY_STACK (args))
          boolector_release (parser->btor, BTOR_POP_STACK (args));
        boolector_release (parser->btor, exp);
        BTOR_RELEASE_STACK (parser->mem, args);
        return !perr_smt2 (parser, "model must have equal sort");
      }
      eq = boolector_eq (parser->btor, fun->exp, tmp);
      boolector_assert (parser->btor, eq);
      boolector_release (parser->btor, eq);
      boolector_release (parser->btor, tmp);
    }
    else
    {
      fun->exp = tmp;
      symbol   = create_symbol_current_scope (parser, fun->name);
      boolector_set_symbol (parser->btor, fun->exp, symbol);
      btor_freestr (parser->mem, symbol);
      parser->need_functions = 1;
    }
    while (!BTOR_EMPTY_STACK (args))
      boolector_release (parser->btor, BTOR_POP_STACK (args));
    boolector_release (parser->btor, exp);
    BTOR_RELEASE_STACK (parser->mem, args);
  }
  else
  {
    if (parser->commands.model)
    {
      if (!boolector_is_equal_sort (parser->btor, fun->exp, exp))
      {
        boolector_release (parser->btor, exp);
        return !perr_smt2 (parser, "model must have equal sort");
      }
      eq = boolector_eq (parser->btor, fun->exp, exp);
      boolector_assert (parser->btor, eq);
      boolector_release (parser->btor, eq);
      boolector_release (parser->btor, exp);
    }
    else
      fun->exp = exp;
  }
  return read_rpar_smt2 (parser, " to close definition");
}

static int
define_sort_smt2 (BtorSMT2Parser *parser)
{
  int tag;
  BtorSMT2Node *sort_alias;
  BoolectorSort sort;

  if (!read_symbol (parser, " after 'define-sort'", &sort_alias)) return 0;
  assert (sort_alias);
  assert (sort_alias->tag == BTOR_SYMBOL_TAG_SMT2);

  if (sort_alias->coo.x)
  {
    return !perr_smt2 (parser,
                       "sort '%s' already defined at line %d column %d",
                       sort_alias->name,
                       sort_alias->coo.x,
                       sort_alias->coo.y);
  }

  if (!read_lpar_smt2 (parser, " after sort definition")) return 0;
  // TODO (ma): for now we do not support parameterized sort defintions
  if (!read_rpar_smt2 (parser,
                       " parameterized sort definitions not supported yet"))
    return 0;

  tag = read_token_smt2 (parser);
  if (!parse_sort (parser, tag, true, &sort)) return 0;

  sort_alias->sort       = 1;
  sort_alias->sort_alias = sort;
  return read_rpar_smt2 (parser, " to close sort definition");
}

static int
set_info_smt2 (BtorSMT2Parser *parser)
{
  int tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser, "unexpected end-of-file after 'set-info'");
  if (tag == BTOR_RPAR_TAG_SMT2)
    return !perr_smt2 (parser, "keyword after 'set-info' missing");
  if (tag == BTOR_STATUS_TAG_SMT2)
  {
    tag = read_token_smt2 (parser);
    if (tag == BTOR_INVALID_TAG_SMT2) return 0;
    if (tag == EOF)
      return !perr_smt2 (parser, "unexpected end-of-file after ':status'");
    if (tag == BTOR_RPAR_TAG_SMT2)
      return !perr_smt2 (parser, "value after ':status' missing");
    if (tag != BTOR_SYMBOL_TAG_SMT2)
    INVALID_STATUS_VALUE:
      return !perr_smt2 (
          parser, "invalid value '%s' after ':status'", parser->token.start);
    if (!strcmp (parser->token.start, "sat"))
      parser->res->status = BOOLECTOR_SAT;
    else if (!strcmp (parser->token.start, "unsat"))
      parser->res->status = BOOLECTOR_UNSAT;
    else if (!strcmp (parser->token.start, "unknown"))
      parser->res->status = BOOLECTOR_UNKNOWN;
    else
      goto INVALID_STATUS_VALUE;

    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              2,
              "parsed status '%s'",
              parser->token.start);
    return read_rpar_smt2 (parser, " after 'set-info'");
  }
  return skip_sexprs (parser, 1);
}

static int
set_option_smt2 (BtorSMT2Parser *parser)
{
  int tag, val, verb = 0;
  char *opt;
  BtorOption o;

  tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser, "unexpected end-of-file after 'set-option'");
  if (tag == BTOR_RPAR_TAG_SMT2)
    return !perr_smt2 (parser, "keyword after 'set-option' missing");

  /* parser specific options */
  if (tag == BTOR_REGULAR_OUTPUT_CHANNEL_TAG_SMT2)
  {
    assert (parser->outfile != stdin);
    if (parser->outfile != stdout && parser->outfile != stderr)
      fclose (parser->outfile);
    tag = read_token_smt2 (parser);
    if (tag == BTOR_INVALID_TAG_SMT2)
    {
      assert (parser->error);
      return 0;
    }
    parser->outfile = fopen (parser->token.start, "w");
    if (!parser->outfile)
      return !perr_smt2 (parser, "can not create '%s'", parser->token.start);
  }
  else if (tag == BTOR_PRINT_SUCCESS_TAG_SMT2)
  {
    tag = read_token_smt2 (parser);
    if (tag == BTOR_INVALID_TAG_SMT2)
    {
      assert (parser->error);
      return 0;
    }
    else if (tag == BTOR_TRUE_TAG_SMT2)
      parser->print_success = true;
    else if (tag == BTOR_FALSE_TAG_SMT2)
      parser->print_success = false;
    else
      return !perr_smt2 (
          parser, "expected Boolean argument at '%s'", parser->token.start);
  }
  /* boolector specific options */
  else
  {
    if (tag == BTOR_PRODUCE_MODELS_TAG_SMT2)
      o = BTOR_OPT_MODEL_GEN;
    else
    {
      opt = parser->token.start + 1;
      if (!btor_get_ptr_hash_table (parser->btor->str2opt, opt))
        return !perr_smt2 (parser, "unsupported option: '%s'", opt);
      o = btor_get_ptr_hash_table (parser->btor->str2opt, opt)->data.as_int;
    }

    tag = read_token_smt2 (parser);
    if (tag == BTOR_INVALID_TAG_SMT2)
    {
      assert (parser->error);
      return 0;
    }
    val = boolector_get_opt (parser->btor, o);
    if (tag == BTOR_FALSE_TAG_SMT2)
      val = 0;
    else if (tag == BTOR_TRUE_TAG_SMT2)
      val = 1;
    else
      val =
          verb ? val + atoi (parser->token.start) : atoi (parser->token.start);
    boolector_set_opt (parser->btor, o, val);

    /* update parser options */
    if (o == BTOR_OPT_INCREMENTAL)
      parser->incremental = val;
    else if (o == BTOR_OPT_VERBOSITY)
      parser->verbosity = val;
  }
  return skip_sexprs (parser, 1);
}

static void
print_success (BtorSMT2Parser *parser)
{
  if (!parser->print_success) return;
  fprintf (parser->outfile, "success\n");
  fflush (parser->outfile);
}

static int
read_command_smt2 (BtorSMT2Parser *parser)
{
#if 0
  float ratio;
  unsigned fsize
#endif
  unsigned i;
  int tag, width;
  BoolectorNode *exp = 0;
  BtorSMT2Coo coo;
  BtorCharStack tokens; /* for get-value (printing the originally parsed
                           non-simplified expression */

  coo.x = coo.y = 0;
  tag           = read_token_smt2 (parser);

  if (parser->commands.model && tag == BTOR_RPAR_TAG_SMT2)
  {
    parser->commands.model = 0;
    return 0;
  }
  if (parser->commands.model && tag == EOF)
    return !perr_smt2 (parser, "expected ')' after 'model' at end-of-file");

  if (tag == EOF || tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag != BTOR_LPAR_TAG_SMT2)
    return !perr_smt2 (parser, "expected '(' at '%s'", parser->token.start);
  tag = read_token_smt2 (parser);

  if (tag == EOF)
  {
    parser->perrcoo = parser->lastcoo;
    return !perr_smt2 (parser, "unexpected end-of-file after '('");
  }

  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    assert (parser->error);
    return 0;
  }

  if (parser->commands.model && tag != BTOR_DEFINE_FUN_TAG_SMT2)
    return !perr_smt2 (parser, "expected 'define-fun' after 'model'");

  if (!(tag & BTOR_COMMAND_TAG_CLASS_SMT2))
    return !perr_smt2 (parser, "expected command at '%s'", parser->token.start);

  if (parser->commands.model && tag != BTOR_DEFINE_FUN_TAG_SMT2)
    return !perr_smt2 (parser, "'define-fun' command expected");

  switch (tag)
  {
    case BTOR_SET_LOGIC_TAG_SMT2:
      if (parser->commands.all)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING 'set-logic' not first command in '%s'",
                  parser->infile_name);
      tag = read_token_smt2 (parser);
      if (tag == EOF)
      {
        parser->perrcoo = parser->lastcoo;
        return !perr_smt2 (parser, "unexpected end-of-file after 'set-logic'");
      }
      if (tag == BTOR_INVALID_TAG_SMT2)
      {
        assert (parser->error);
        return 0;
      }
      if (!(tag & BTOR_LOGIC_TAG_CLASS_SMT2))
        return !perr_smt2 (
            parser, "expected logic at '%s'", parser->token.start);
      if (tag == BTOR_QF_BV_TAG_SMT2)
        parser->res->logic = BTOR_LOGIC_QF_BV;
      else if (tag == BTOR_QF_AUFBV_TAG_SMT2 || tag == BTOR_QF_UFBV_TAG_SMT2
               || tag == BTOR_QF_ABV_TAG_SMT2)
        parser->res->logic = BTOR_LOGIC_QF_AUFBV;
      else
        return !perr_smt2 (
            parser, "unsupported logic '%s'", parser->token.start);
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "logic %s",
                parser->token.start);
      if (!read_rpar_smt2 (parser, " after logic")) return 0;
      if (parser->commands.set_logic++)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING additional 'set-logic' command");
      print_success (parser);
      break;

    case BTOR_CHECK_SAT_TAG_SMT2:
      if (!read_rpar_smt2 (parser, " after 'check-sat'")) return 0;
      if (parser->commands.check_sat++ && !parser->incremental)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING additional 'check-sat' command");
      if (parser->interactive)
      {
#if 1
        for (i = 0; i < BTOR_COUNT_STACK (parser->assumptions); i++)
          boolector_assume (parser->btor,
                            BTOR_PEEK_STACK (parser->assumptions, i));
#else
        ratio = 0.0f;
        if (!BTOR_EMPTY_STACK (parser->assumptions_trail))
        {
          for (i = 0; i < BTOR_COUNT_STACK (parser->assumptions); i++)
            boolector_assume (parser->btor,
                              BTOR_PEEK_STACK (parser->assumptions, i));
          fsize = get_current_formula_size (parser);
          ratio = (float) (fsize - parser->cur_scope_num_terms) / fsize;
        }

        /* 0.06f is the best factor right now for keeping the cloning
         * overhead as low as possible */
        if (!BTOR_EMPTY_STACK (parser->assumptions_trail) && ratio >= 0.06f)
        {
          Btor *c = boolector_clone (parser->btor);
          boolector_fixate_assumptions (c);
          parser->res->result = boolector_sat (c);
          boolector_delete (c);
          boolector_reset_assumptions (parser->btor);
        }
        else
#endif
        parser->res->result = boolector_sat (parser->btor);
        if (parser->res->result == BOOLECTOR_SAT)
          fprintf (parser->outfile, "sat\n");
        else if (parser->res->result == BOOLECTOR_UNSAT)
          fprintf (parser->outfile, "unsat\n");
        else
          fprintf (parser->outfile, "unknown\n");
        fflush (parser->outfile);
      }
      else
      {
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "parser not interactive, aborted on first "
                  "'check-sat' command");
        parser->done = 1;
      }
      break;

    case BTOR_DECLARE_FUN_TAG_SMT2:
      if (!declare_fun_smt2 (parser)) return 0;
      print_success (parser);
      break;

    case BTOR_DEFINE_FUN_TAG_SMT2:
      if (!define_fun_smt2 (parser)) return 0;
      print_success (parser);
      break;

    case BTOR_DEFINE_SORT_TAG_SMT2:
      if (!define_sort_smt2 (parser)) return 0;
      print_success (parser);
      break;

    case BTOR_ASSERT_TAG_SMT2:
      if (!parse_term_smt2 (parser, &exp, &coo)) return 0;
      assert (!parser->error);
      if (boolector_is_array (parser->btor, exp))
      {
        parser->perrcoo = coo;
        boolector_release (parser->btor, exp);
        return !perr_smt2 (parser,
                           "assert argument is an array and not a formula");
      }
      if (!read_rpar_smt2 (parser, " after asserted expression"))
      {
        boolector_release (parser->btor, exp);
        return 0;
      }
      if ((width = boolector_get_width (parser->btor, exp)) != 1)
      {
        parser->perrcoo = coo;
        boolector_release (parser->btor, exp);
        return !perr_smt2 (
            parser, "assert argument is a bit-vector of length %d", width);
      }
      if (!BTOR_EMPTY_STACK (parser->assumptions_trail))
        BTOR_PUSH_STACK (parser->mem,
                         parser->assumptions,
                         boolector_copy (parser->btor, exp));
      else
        boolector_assert (parser->btor, exp);
      boolector_release (parser->btor, exp);
      assert (!parser->error);
      parser->commands.asserts++;
      print_success (parser);
      break;

    case BTOR_EXIT_TAG_SMT2:
      if (!read_rpar_smt2 (parser, " after 'exit'")) return 0;
      assert (!parser->commands.exits);
      parser->commands.exits++;
      parser->done = 1;
      print_success (parser);
      break;

    case BTOR_GET_MODEL_TAG_SMT2:
      if (!read_rpar_smt2 (parser, " after 'get-model'")) return 0;
      if (!boolector_get_opt (parser->btor, BTOR_OPT_MODEL_GEN))
        return !perr_smt2 (parser, "model generation is not enabled");
      if (parser->res->result != BOOLECTOR_SAT) break;
      boolector_print_model (parser->btor, "smt2", parser->outfile);
      fflush (parser->outfile);
      break;

    case BTOR_GET_VALUE_TAG_SMT2:
      if (!read_lpar_smt2 (parser, " after 'get-value'")) return 0;
      if (!boolector_get_opt (parser->btor, BTOR_OPT_MODEL_GEN))
        return !perr_smt2 (parser, "model generation is not enabled");
      if (parser->res->result != BOOLECTOR_SAT) break;
      tag = 0;
      BTOR_INIT_STACK (tokens);
      if (!parse_term_aux_smt2 (parser, 0, 0, &exp, &coo, &tokens))
      {
        BTOR_RELEASE_STACK (parser->mem, tokens);
        return 0;
      }
      fprintf (parser->outfile, "(");
      boolector_print_value (
          parser->btor, exp, tokens.start, "smt2", parser->outfile);
      BTOR_RESET_STACK (tokens);
      boolector_release (parser->btor, exp);
      tag = read_token_smt2 (parser);
      while (tag != EOF && tag != BTOR_RPAR_TAG_SMT2)
      {
        if (!parse_term_aux_smt2 (parser, 1, tag, &exp, &coo, &tokens))
        {
          BTOR_RELEASE_STACK (parser->mem, tokens);
          return 0;
        }
        fprintf (parser->outfile, "\n ");
        boolector_print_value (
            parser->btor, exp, tokens.start, "smt2", parser->outfile);
        BTOR_RESET_STACK (tokens);
        boolector_release (parser->btor, exp);
        tag = read_token_smt2 (parser);
      }
      fprintf (parser->outfile, ")\n");
      fflush (parser->outfile);
      if (tag != BTOR_RPAR_TAG_SMT2)
      {
        BTOR_RELEASE_STACK (parser->mem, tokens);
        return !perr_smt2 (parser,
                           "expected ')' after 'get-value' at end-of-file");
      }
      if (!read_rpar_smt2 (parser, " after 'get-value'"))
      {
        BTOR_RELEASE_STACK (parser->mem, tokens);
        return 0;
      }
      BTOR_RELEASE_STACK (parser->mem, tokens);
      break;

    case BTOR_MODEL_TAG_SMT2:
      if (parser->commands.model)
        return !perr_smt2 (parser, "nesting models is invalid");
      parser->commands.model = 1;
      while (read_command_smt2 (parser) && !boolector_terminate (parser->btor))
        ;
      print_success (parser);
      break;

    case BTOR_SET_INFO_TAG_SMT2:
      if (!set_info_smt2 (parser)) return 0;
      print_success (parser);
      break;

    case BTOR_SET_OPTION_TAG_SMT2:
      if (!set_option_smt2 (parser)) return 0;
      print_success (parser);
      break;

    case BTOR_PUSH_TAG_SMT2:
      tag = parse_int32_smt2 (parser, 1, &tag, 0);
      if (!read_rpar_smt2 (parser, " after 'push'")) return 0;
        // TODO: open more scopes if tag > 1
#ifdef BTOR_USE_CLONE_SCOPES
      open_new_btor_scope (parser);
#else
      open_new_scope (parser);
#endif
      print_success (parser);
      break;

    case BTOR_POP_TAG_SMT2:
      tag = parse_int32_smt2 (parser, 1, &tag, 0);
      if (!read_rpar_smt2 (parser, " after 'pop'")) return 0;
        // TODO: close more scopes if tag > 1
#ifdef BTOR_USE_CLONE_SCOPES
      close_current_btor_scope (parser);
#else
      close_current_scope (parser);
#endif
      print_success (parser);
      break;

    default:
      return !perr_smt2 (
          parser, "unsupported command '%s'", parser->token.start);
      break;
  }
  parser->commands.all++;
  return 1;
}

static const char *
parse_smt2_parser (BtorSMT2Parser *parser,
                   BtorCharStack *prefix,
                   FILE *infile,
                   const char *infile_name,
                   FILE *outfile,
                   BtorParseResult *res)
{
  double start = btor_time_stamp (), delta;

  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->nextcoo.x   = 1;
  parser->nextcoo.y   = 1;
  parser->infile      = infile;
  parser->infile_name = btor_strdup (parser->mem, infile_name);
  parser->outfile     = outfile;
  parser->saved       = 0;
  BTOR_CLR (res);
  parser->res = res;

  while (read_command_smt2 (parser) && !parser->done
         && !boolector_terminate (parser->btor))
    ;

  if (parser->error) return parser->error;

  if (!boolector_terminate (parser->btor))
  {
    if (!parser->commands.all)
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                1,
                "WARNING no commands in '%s'",
                parser->infile_name);
    else
    {
      if (!parser->commands.set_logic)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING 'set-logic' command missing in '%s'",
                  parser->infile_name);
      if (!parser->commands.asserts)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING no 'assert' command in '%s'",
                  parser->infile_name);
      if (!parser->commands.check_sat)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING 'check-sat' command missing in '%s'",
                  parser->infile_name);
      if (!parser->commands.exits)
        BTOR_MSG (boolector_get_btor_msg (parser->btor),
                  1,
                  "WARNING no 'exit' command at end of '%s'",
                  parser->infile_name);
    }
  }
  parser->res->inputs = parser->inputs.start;
  // TODO (ma): this stack is not used anymore for SMT2
  parser->res->outputs  = parser->outputs.start;
  parser->res->ninputs  = BTOR_COUNT_STACK (parser->inputs);
  parser->res->noutputs = BTOR_COUNT_STACK (parser->outputs);
  delta                 = btor_time_stamp () - start;
  if (delta < 0) delta = 0;
  BTOR_MSG (boolector_get_btor_msg (parser->btor),
            1,
            "parsed %d commands in %.2f seconds",
            parser->commands.all,
            delta);

  if (parser->need_functions && parser->res->logic == BTOR_LOGIC_QF_BV)
  {
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              1,
              "found functions thus using 'QF_AUFBV' logic");
    parser->res->logic = BTOR_LOGIC_QF_AUFBV;
  }
  else if (parser->commands.set_logic)
  {
    assert (!parser->need_functions
            || parser->res->logic == BTOR_LOGIC_QF_AUFBV);
    if (!parser->need_functions && parser->res->logic == BTOR_LOGIC_QF_AUFBV)
    {
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                1,
                "no functions found thus restricting logic to 'QF_BV'");
      parser->res->logic = BTOR_LOGIC_QF_BV;
    }
  }
  return 0;
}

static BtorParserAPI static_btor_smt2_parser_api = {
    (BtorInitParser) new_smt2_parser,
    (BtorResetParser) delete_smt2_parser,
    (BtorParse) parse_smt2_parser};

const BtorParserAPI *
btor_smt2_parser_api ()
{
  return &static_btor_smt2_parser_api;
}
