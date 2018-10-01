/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2011-2017 Armin Biere.
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsmt2.h"

#include "btorbv.h"
#include "btorcore.h"
#include "btormsg.h"
#include "btoropt.h"
#include "utils/btormem.h"
#include "utils/btorutil.h"

#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>

/*------------------------------------------------------------------------*/

BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

/*------------------------------------------------------------------------*/

void boolector_print_value_smt2 (Btor *, BoolectorNode *, char *, FILE *);

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
  BTOR_BV_TAG_CLASS_SMT2       = (BTOR_CLASS_SIZE_SMT2 << 6),
  BTOR_LOGIC_TAG_CLASS_SMT2    = (BTOR_CLASS_SIZE_SMT2 << 7),
} BtorSMT2TagClass;

#define BTOR_TAG_CLASS_MASK_SMT2                              \
  (BTOR_RESERVED_TAG_CLASS_SMT2 | BTOR_COMMAND_TAG_CLASS_SMT2 \
   | BTOR_KEYWORD_TAG_CLASS_SMT2 | BTOR_CORE_TAG_CLASS_SMT2   \
   | BTOR_ARRAY_TAG_CLASS_SMT2 | BTOR_BV_TAG_CLASS_SMT2       \
   | BTOR_LOGIC_TAG_CLASS_SMT2)

typedef enum BtorSMT2Tag
{
  BTOR_INVALID_TAG_SMT2   = 0 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_PARENT_TAG_SMT2    = 1 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_LPAR_TAG_SMT2      = 2 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_RPAR_TAG_SMT2      = 3 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_SYMBOL_TAG_SMT2    = 4 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_ATTRIBUTE_TAG_SMT2 = 5 + BTOR_OTHER_TAG_CLASS_SMT2,
  BTOR_EXP_TAG_SMT2       = 6 + BTOR_OTHER_TAG_CLASS_SMT2,
  /* <var_binding> */
  BTOR_LETBIND_TAG_SMT2 = 7 + BTOR_OTHER_TAG_CLASS_SMT2,
  /* (<var_binding>+) */
  BTOR_PARLETBINDING_TAG_SMT2 = 8 + BTOR_OTHER_TAG_CLASS_SMT2,
  /* <sorted_var> */
  BTOR_SORTED_VAR_TAG_SMT2 = 9 + BTOR_OTHER_TAG_CLASS_SMT2,
  /* (<sorted_var>+) */
  BTOR_SORTED_VARS_TAG_SMT2 = 10 + BTOR_OTHER_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Constants                                                              */

  BTOR_DECIMAL_CONSTANT_TAG_SMT2     = 0 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2 = 1 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_BINARY_CONSTANT_TAG_SMT2      = 2 + BTOR_CONSTANT_TAG_CLASS_SMT2,
  BTOR_STRING_CONSTANT_TAG_SMT2      = 3 + BTOR_CONSTANT_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Reserved Words                                                         */

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

  /* ---------------------------------------------------------------------- */
  /* Commands                                                               */

  BTOR_SET_LOGIC_TAG_SMT2             = 0 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_SET_OPTION_TAG_SMT2            = 1 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_SET_INFO_TAG_SMT2              = 2 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DECLARE_SORT_TAG_SMT2          = 3 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DEFINE_SORT_TAG_SMT2           = 4 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DECLARE_FUN_TAG_SMT2           = 5 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DEFINE_FUN_TAG_SMT2            = 6 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_DECLARE_CONST_TAG_SMT2         = 7 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_PUSH_TAG_SMT2                  = 8 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_POP_TAG_SMT2                   = 9 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_ASSERT_TAG_SMT2                = 10 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_CHECK_SAT_TAG_SMT2             = 11 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_CHECK_SAT_ASSUMING_TAG_SMT2    = 12 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_ASSERTIONS_TAG_SMT2        = 13 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_ASSIGNMENT_TAG_SMT2        = 14 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_INFO_TAG_SMT2              = 15 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_OPTION_TAG_SMT2            = 16 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_PROOF_TAG_SMT2             = 17 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_UNSAT_ASSUMPTIONS_TAG_SMT2 = 18 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_UNSAT_CORE_TAG_SMT2        = 19 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_VALUE_TAG_SMT2             = 20 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_EXIT_TAG_SMT2                  = 21 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_GET_MODEL_TAG_SMT2             = 22 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_MODEL_TAG_SMT2                 = 23 + BTOR_COMMAND_TAG_CLASS_SMT2,
  BTOR_ECHO_TAG_SMT2                  = 24 + BTOR_COMMAND_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Keywords                                                               */

  BTOR_ALL_STATISTICS_TAG_SMT2            = 0 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_AUTHORS_TAG_SMT2                   = 1 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_AXIOMS_TAG_SMT2                    = 2 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_CHAINABLE_TAG_SMT2                 = 3 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_DEFINITION_TAG_SMT2                = 4 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_DIAG_OUTPUT_CHANNEL_TAG_SMT2       = 5 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_ERROR_BEHAVIOR_TAG_SMT2            = 6 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_EXPAND_DEFINITIONS_TAG_SMT2        = 7 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_EXTENSIONS_TAG_SMT2                = 8 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_FUNS_TAG_SMT2                      = 9 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_FUNS_DESCRIPTION_TAG_SMT2          = 10 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_INTERACTIVE_MODE_TAG_SMT2          = 11 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_ASSERTIONS_TAG_SMT2        = 12 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_LANGUAGE_TAG_SMT2                  = 13 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_LEFT_ASSOC_TAG_SMT2                = 14 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_NAME_TAG_SMT2                      = 15 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_NAMED_TAG_SMT2                     = 16 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_NOTES_TAG_SMT2                     = 17 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRINT_SUCCESS_TAG_SMT2             = 18 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_ASSIGNMENTS_TAG_SMT2       = 19 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_MODELS_TAG_SMT2            = 20 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_PROOFS_TAG_SMT2            = 21 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_UNSAT_ASSUMPTIONS_TAG_SMT2 = 22 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_PRODUCE_UNSAT_CORES_TAG_SMT2       = 23 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_RANDOM_SEED_TAG_SMT2               = 24 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_REASON_UNKNOWN_TAG_SMT2            = 25 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_REGULAR_OUTPUT_CHANNEL_TAG_SMT2    = 26 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_RIGHT_ASSOC_TAG_SMT2               = 27 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_SORTS_TAG_SMT2                     = 28 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_SORTS_DESCRIPTION_TAG_SMT2         = 29 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_STATUS_TAG_SMT2                    = 30 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_THEORIES_TAG_SMT2                  = 31 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_VALUES_TAG_SMT2                    = 32 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_VERBOSITY_TAG_SMT2                 = 33 + BTOR_KEYWORD_TAG_CLASS_SMT2,
  BTOR_VERSION_TAG_SMT2                   = 34 + BTOR_KEYWORD_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Theories                                                               */

  /* Core ----------------------------------------------------------------- */
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

  /* Array ---------------------------------------------------------------- */
  BTOR_ARRAY_TAG_SMT2        = 0 + BTOR_ARRAY_TAG_CLASS_SMT2,
  BTOR_ARRAY_SELECT_TAG_SMT2 = 1 + BTOR_ARRAY_TAG_CLASS_SMT2,
  BTOR_ARRAY_STORE_TAG_SMT2  = 2 + BTOR_ARRAY_TAG_CLASS_SMT2,

  /* Bit-Vectors ---------------------------------------------------------- */
  BTOR_BV_BITVEC_TAG_SMT2       = 0 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_CONCAT_TAG_SMT2       = 1 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_EXTRACT_TAG_SMT2      = 2 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_NOT_TAG_SMT2          = 3 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_NEG_TAG_SMT2          = 4 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_AND_TAG_SMT2          = 5 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_OR_TAG_SMT2           = 6 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ADD_TAG_SMT2          = 7 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_MUL_TAG_SMT2          = 8 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_UDIV_TAG_SMT2         = 9 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_UREM_TAG_SMT2         = 10 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SHL_TAG_SMT2          = 11 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_LSHR_TAG_SMT2         = 12 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ULT_TAG_SMT2          = 13 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_NAND_TAG_SMT2         = 14 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_NOR_TAG_SMT2          = 15 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_XOR_TAG_SMT2          = 16 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_XNOR_TAG_SMT2         = 17 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_COMP_TAG_SMT2         = 18 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SUB_TAG_SMT2          = 19 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SDIV_TAG_SMT2         = 20 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SREM_TAG_SMT2         = 21 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SMOD_TAG_SMT2         = 22 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ASHR_TAG_SMT2         = 23 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_REPEAT_TAG_SMT2       = 24 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ZERO_EXTEND_TAG_SMT2  = 25 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SIGN_EXTEND_TAG_SMT2  = 26 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ROTATE_LEFT_TAG_SMT2  = 27 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ROTATE_RIGHT_TAG_SMT2 = 28 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_ULE_TAG_SMT2          = 29 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_UGT_TAG_SMT2          = 30 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_UGE_TAG_SMT2          = 31 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SLT_TAG_SMT2          = 32 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SLE_TAG_SMT2          = 33 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SGT_TAG_SMT2          = 34 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_SGE_TAG_SMT2          = 35 + BTOR_BV_TAG_CLASS_SMT2,
  /* Z3 extensions */
  BTOR_BV_REDOR_TAG_SMT2            = 36 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_REDAND_TAG_SMT2           = 37 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_EXT_ROTATE_LEFT_TAG_SMT2  = 38 + BTOR_BV_TAG_CLASS_SMT2,
  BTOR_BV_EXT_ROTATE_RIGHT_TAG_SMT2 = 39 + BTOR_BV_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Logic                                                                  */

  BTOR_LOGIC_AUFLIA_TAG_SMT2    = 0 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_AUFLIRA_TAG_SMT2   = 1 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_AUFNIRA_TAG_SMT2   = 2 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_LRA_TAG_SMT2       = 3 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_ABV_TAG_SMT2    = 4 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_AUFBV_TAG_SMT2  = 5 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_AUFLIA_TAG_SMT2 = 6 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_AX_TAG_SMT2     = 7 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_BV_TAG_SMT2     = 8 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_IDL_TAG_SMT2    = 9 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_LIA_TAG_SMT2    = 10 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_LRA_TAG_SMT2    = 11 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_NIA_TAG_SMT2    = 12 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_NRA_TAG_SMT2    = 13 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_RDL_TAG_SMT2    = 14 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_UF_TAG_SMT2     = 15 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_UFBV_TAG_SMT2   = 16 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_UFIDL_TAG_SMT2  = 17 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_UFLIA_TAG_SMT2  = 18 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_UFLRA_TAG_SMT2  = 19 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_QF_UFNRA_TAG_SMT2  = 20 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_UFLRA_TAG_SMT2     = 21 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_UFNIA_TAG_SMT2     = 22 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_BV_TAG_SMT2        = 23 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_UFBV_TAG_SMT2      = 24 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_ABV_TAG_SMT2       = 25 + BTOR_LOGIC_TAG_CLASS_SMT2,
  BTOR_LOGIC_ALL_TAG_SMT2       = 26 + BTOR_LOGIC_TAG_CLASS_SMT2,

} BtorSMT2Tag;

typedef struct BtorSMT2Coo
{
  int32_t x, y;
} BtorSMT2Coo;

typedef struct BtorSMT2Node
{
  BtorSMT2Tag tag;
  uint32_t bound : 1;
  uint32_t sort : 1;
  uint32_t scope_level;
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
    int32_t num;
    struct
    {
      int32_t idx0, idx1;
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
  bool done;
  bool need_arrays;
  bool need_functions;
  bool need_quantifiers;
  bool saved;
  int32_t savedch;
  int32_t last_end_of_line_ycoo;
  int32_t open;
  uint32_t nprefix;
  int sorted_var;
  uint32_t bound_vars; /* used for exists/forall vars to enumerate symbols */
  bool isvarbinding;
  const char *expecting_body;
  char *error;
  unsigned char cc[256];
  FILE *infile;
  char *infile_name;
  FILE *outfile;
  double parse_start;
  bool store_tokens; /* needed for parsing terms in get-value */
  BtorCharStack *prefix, token, tokens;
  BoolectorSortStack sorts;
  BtorSMT2ItemStack work;
  BtorSMT2Coo coo, lastcoo, nextcoo, perrcoo;
  BtorSMT2Node *last_node;
  BtorParseResult *res;
  BoolectorNodePtrStack sat_assuming_assumptions;
  uint32_t scope_level;
  uint32_t num_scopes;
  struct
  {
    uint32_t size, count;
    BtorSMT2Node **table;
  } symbol;
  struct
  {
    int32_t all, set_logic, asserts, check_sat, exits, model;
  } commands;

  /* SMT2 options */
  bool print_success;
} BtorSMT2Parser;

static int32_t
xcoo_smt2 (BtorSMT2Parser *parser)
{
  return parser->perrcoo.x ? parser->perrcoo.x : parser->coo.x;
}

static int32_t
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
    bytes = btor_mem_parse_error_msg_length (parser->infile_name, fmt, ap);
    va_end (ap);
    va_start (ap, fmt);
    parser->error = btor_mem_parse_error_msg (parser->mem,
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
  parser->saved   = true;
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
cerr_smt2 (BtorSMT2Parser *parser, const char *p, int32_t ch, const char *s)
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

static uint32_t btor_primes_smt2[] = {
    1000000007u, 2000000011u, 3000000019u, 4000000007u};

#define BTOR_NPRIMES_SMT2 (sizeof btor_primes_smt2 / sizeof *btor_primes_smt2)

static uint32_t
hash_name_smt2 (BtorSMT2Parser *parser, const char *name)
{
  uint32_t res = 0, i = 0;
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

static int32_t
nextch_smt2 (BtorSMT2Parser *parser)
{
  int32_t res;
  if (parser->saved)
    res = parser->savedch, parser->saved = false;
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
  uint32_t old_size        = parser->symbol.size;
  uint32_t new_size        = old_size ? 2 * old_size : 1;
  BtorSMT2Node **old_table = parser->symbol.table, *p, *next, **q;
  uint32_t h, i;
  BTOR_CNEWN (parser->mem, parser->symbol.table, new_size);
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

static BtorSMT2Node *
find_symbol_smt2 (BtorSMT2Parser *parser, const char *name)
{
  unsigned h;
  BtorSMT2Node *s;

  if (parser->symbol.size == 0) return 0;

  h = hash_name_smt2 (parser, name);
  for (s = parser->symbol.table[h]; s && strcmp (s->name, name); s = s->next)
    ;
  return s;
}

static void
insert_symbol_smt2 (BtorSMT2Parser *parser, BtorSMT2Node *symbol)
{
  unsigned h;
  BtorSMT2Node *p;

  if (parser->symbol.size <= parser->symbol.count)
    enlarge_symbol_table_smt2 (parser);

  /* always add new symbol as first element to collision chain (required for
   * scoping) */
  h = hash_name_smt2 (parser, symbol->name);
  p = parser->symbol.table[h];

  parser->symbol.table[h] = symbol;
  symbol->next            = p;
  parser->symbol.count++;
  assert (parser->symbol.count > 0);
  BTOR_MSG (parser->btor->msg,
            2,
            "insert symbol '%s' at scope level %u",
            symbol->name,
            parser->scope_level);
}

static BtorSMT2Node *
new_node_smt2 (BtorSMT2Parser *parser, BtorSMT2Tag tag)
{
  BtorSMT2Node *res;
  BTOR_CNEW (parser->mem, res);
  res->tag         = tag;
  res->scope_level = parser->scope_level;
  return res;
}

static void
release_symbol_smt2 (BtorSMT2Parser *parser, BtorSMT2Node *symbol)
{
  assert (symbol->tag != BTOR_PARENT_TAG_SMT2);
  if (symbol->exp) boolector_release (parser->btor, symbol->exp);
  btor_mem_freestr (parser->mem, symbol->name);
  BTOR_DELETE (parser->mem, symbol);
}

static void
remove_symbol_smt2 (BtorSMT2Parser *parser, BtorSMT2Node *symbol)
{
  BtorSMT2Node **p, *s;
  unsigned h;

  BTOR_MSG (parser->btor->msg,
            2,
            "remove symbol '%s' at scope level %u",
            symbol->name,
            parser->scope_level);

  h = hash_name_smt2 (parser, symbol->name);
  for (p = parser->symbol.table + h;
       (s = *p) && (strcmp (s->name, symbol->name) || s != symbol);
       p = &s->next)
    ;
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
  uint32_t i;
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
    btor_mem_freestr (parser->mem, item->str);
}

static void
open_new_scope (BtorSMT2Parser *parser)
{
  parser->scope_level++;
  parser->num_scopes++;

  BTOR_MSG (parser->btor->msg,
            2,
            "opened new scope at level %d",
            parser->scope_level);
}

static void
close_current_scope (BtorSMT2Parser *parser)
{
  double start;
  uint32_t i;
  BtorSMT2Node *node, *next;

  start = btor_util_time_stamp ();

  /* delete symbols from current scope */
  for (i = 0; i < parser->symbol.size; i++)
  {
    node = parser->symbol.table[i];
    while (node)
    {
      next = node->next;
      if (node->scope_level == parser->scope_level)
        remove_symbol_smt2 (parser, node);
      node = next;
    }
  }

  BTOR_MSG (parser->btor->msg,
            2,
            "closed scope at level %d in %.3f seconds",
            parser->scope_level,
            btor_util_time_stamp () - start);
  parser->scope_level--;
}

static char *
create_symbol_current_scope (BtorSMT2Parser *parser, char *symbol)
{
  char *symb;
  size_t len;
  if (parser->scope_level)
  {
    len = strlen (symbol) + 1;
    len += strlen ("BTOR@");
    len += btor_util_num_digits (parser->num_scopes);
    BTOR_CNEWN (parser->mem, symb, len);
    sprintf (symb, "BTOR@%u%s", parser->num_scopes, symbol);
  }
  else
    symb = btor_mem_strdup (parser->mem, symbol);
  return symb;
}

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

#define INSERT(STR, TAG)                                       \
  do                                                           \
  {                                                            \
    BtorSMT2Node *NODE = new_node_smt2 (parser, (TAG));        \
    NODE->name         = btor_mem_strdup (parser->mem, (STR)); \
    assert (!find_symbol_smt2 (parser, NODE->name));           \
    insert_symbol_smt2 (parser, NODE);                         \
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
  INSERT (":produce-assertions", BTOR_PRODUCE_ASSERTIONS_TAG_SMT2);
  INSERT (":language", BTOR_LANGUAGE_TAG_SMT2);
  INSERT (":left-assoc", BTOR_LEFT_ASSOC_TAG_SMT2);
  INSERT (":name", BTOR_NAME_TAG_SMT2);
  INSERT (":named", BTOR_NAMED_TAG_SMT2);
  INSERT (":notes", BTOR_NOTES_TAG_SMT2);
  INSERT (":print-success", BTOR_PRINT_SUCCESS_TAG_SMT2);
  INSERT (":produce-assignments", BTOR_PRODUCE_ASSIGNMENTS_TAG_SMT2);
  INSERT (":produce-models", BTOR_PRODUCE_MODELS_TAG_SMT2);
  INSERT (":produce-proofs", BTOR_PRODUCE_PROOFS_TAG_SMT2);
  INSERT (":produce-unsat-assumptions",
          BTOR_PRODUCE_UNSAT_ASSUMPTIONS_TAG_SMT2);
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
  INSERT ("check-sat-assuming", BTOR_CHECK_SAT_ASSUMING_TAG_SMT2);
  INSERT ("declare-sort", BTOR_DECLARE_SORT_TAG_SMT2);
  INSERT ("declare-fun", BTOR_DECLARE_FUN_TAG_SMT2);
  INSERT ("declare-const", BTOR_DECLARE_CONST_TAG_SMT2);
  INSERT ("define-sort", BTOR_DEFINE_SORT_TAG_SMT2);
  INSERT ("define-fun", BTOR_DEFINE_FUN_TAG_SMT2);
  INSERT ("echo", BTOR_ECHO_TAG_SMT2);
  INSERT ("exit", BTOR_EXIT_TAG_SMT2);
  INSERT ("get-model", BTOR_GET_MODEL_TAG_SMT2);
  INSERT ("get-assertions", BTOR_GET_ASSERTIONS_TAG_SMT2);
  INSERT ("get-assignment", BTOR_GET_ASSIGNMENT_TAG_SMT2);
  INSERT ("get-info", BTOR_GET_INFO_TAG_SMT2);
  INSERT ("get-option", BTOR_GET_OPTION_TAG_SMT2);
  INSERT ("get-proof", BTOR_GET_PROOF_TAG_SMT2);
  INSERT ("get-unsat-core", BTOR_GET_UNSAT_CORE_TAG_SMT2);
  INSERT ("get-unsat-assumptions", BTOR_GET_UNSAT_ASSUMPTIONS_TAG_SMT2);
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
  INSERT ("select", BTOR_ARRAY_SELECT_TAG_SMT2);
  INSERT ("store", BTOR_ARRAY_STORE_TAG_SMT2);
}

static void
insert_bitvec_symbols_smt2 (BtorSMT2Parser *parser)
{
  INSERT ("BitVec", BTOR_BV_BITVEC_TAG_SMT2);
  INSERT ("concat", BTOR_BV_CONCAT_TAG_SMT2);
  INSERT ("extract", BTOR_BV_EXTRACT_TAG_SMT2);
  INSERT ("bvnot", BTOR_BV_NOT_TAG_SMT2);
  INSERT ("bvneg", BTOR_BV_NEG_TAG_SMT2);
  INSERT ("bvand", BTOR_BV_AND_TAG_SMT2);
  INSERT ("bvor", BTOR_BV_OR_TAG_SMT2);
  INSERT ("bvadd", BTOR_BV_ADD_TAG_SMT2);
  INSERT ("bvmul", BTOR_BV_MUL_TAG_SMT2);
  INSERT ("bvudiv", BTOR_BV_UDIV_TAG_SMT2);
  INSERT ("bvurem", BTOR_BV_UREM_TAG_SMT2);
  INSERT ("bvshl", BTOR_BV_SHL_TAG_SMT2);
  INSERT ("bvlshr", BTOR_BV_LSHR_TAG_SMT2);
  INSERT ("bvult", BTOR_BV_ULT_TAG_SMT2);
  INSERT ("bvnand", BTOR_BV_NAND_TAG_SMT2);
  INSERT ("bvnor", BTOR_BV_NOR_TAG_SMT2);
  INSERT ("bvxor", BTOR_BV_XOR_TAG_SMT2);
  INSERT ("bvxnor", BTOR_BV_XNOR_TAG_SMT2);
  INSERT ("bvcomp", BTOR_BV_COMP_TAG_SMT2);
  INSERT ("bvsub", BTOR_BV_SUB_TAG_SMT2);
  INSERT ("bvsdiv", BTOR_BV_SDIV_TAG_SMT2);
  INSERT ("bvsrem", BTOR_BV_SREM_TAG_SMT2);
  INSERT ("bvsmod", BTOR_BV_SMOD_TAG_SMT2);
  INSERT ("bvashr", BTOR_BV_ASHR_TAG_SMT2);
  INSERT ("repeat", BTOR_BV_REPEAT_TAG_SMT2);
  INSERT ("zero_extend", BTOR_BV_ZERO_EXTEND_TAG_SMT2);
  INSERT ("sign_extend", BTOR_BV_SIGN_EXTEND_TAG_SMT2);
  INSERT ("rotate_left", BTOR_BV_ROTATE_LEFT_TAG_SMT2);
  INSERT ("rotate_right", BTOR_BV_ROTATE_RIGHT_TAG_SMT2);
  INSERT ("bvule", BTOR_BV_ULE_TAG_SMT2);
  INSERT ("bvugt", BTOR_BV_UGT_TAG_SMT2);
  INSERT ("bvuge", BTOR_BV_UGE_TAG_SMT2);
  INSERT ("bvslt", BTOR_BV_SLT_TAG_SMT2);
  INSERT ("bvsle", BTOR_BV_SLE_TAG_SMT2);
  INSERT ("bvsgt", BTOR_BV_SGT_TAG_SMT2);
  INSERT ("bvsge", BTOR_BV_SGE_TAG_SMT2);
  /* Z3 extensions */
  INSERT ("bvredor", BTOR_BV_REDOR_TAG_SMT2);
  INSERT ("bvredand", BTOR_BV_REDAND_TAG_SMT2);
  INSERT ("ext_rotate_left", BTOR_BV_EXT_ROTATE_LEFT_TAG_SMT2);
  INSERT ("ext_rotate_right", BTOR_BV_EXT_ROTATE_RIGHT_TAG_SMT2);
}

static void
insert_logics_smt2 (BtorSMT2Parser *parser)
{
  INSERT ("AUFLIA", BTOR_LOGIC_AUFLIA_TAG_SMT2);
  INSERT ("AUFLIRA", BTOR_LOGIC_AUFLIRA_TAG_SMT2);
  INSERT ("AUFNIRA", BTOR_LOGIC_AUFNIRA_TAG_SMT2);
  INSERT ("LRA", BTOR_LOGIC_LRA_TAG_SMT2);
  INSERT ("QF_ABV", BTOR_LOGIC_QF_ABV_TAG_SMT2);
  INSERT ("QF_AUFBV", BTOR_LOGIC_QF_AUFBV_TAG_SMT2);
  INSERT ("QF_AUFLIA", BTOR_LOGIC_QF_AUFLIA_TAG_SMT2);
  INSERT ("QF_AX", BTOR_LOGIC_QF_AX_TAG_SMT2);
  INSERT ("QF_BV", BTOR_LOGIC_QF_BV_TAG_SMT2);
  INSERT ("QF_IDL", BTOR_LOGIC_QF_IDL_TAG_SMT2);
  INSERT ("QF_LIA", BTOR_LOGIC_QF_LIA_TAG_SMT2);
  INSERT ("QF_LRA", BTOR_LOGIC_QF_LRA_TAG_SMT2);
  INSERT ("QF_NIA", BTOR_LOGIC_QF_NIA_TAG_SMT2);
  INSERT ("QF_NRA", BTOR_LOGIC_QF_NRA_TAG_SMT2);
  INSERT ("QF_RDL", BTOR_LOGIC_QF_RDL_TAG_SMT2);
  INSERT ("QF_UF", BTOR_LOGIC_QF_UF_TAG_SMT2);
  INSERT ("QF_UFBV", BTOR_LOGIC_QF_UFBV_TAG_SMT2);
  INSERT ("QF_UFIDL", BTOR_LOGIC_QF_UFIDL_TAG_SMT2);
  INSERT ("QF_UFLIA", BTOR_LOGIC_QF_UFLIA_TAG_SMT2);
  INSERT ("QF_UFLRA", BTOR_LOGIC_QF_UFLRA_TAG_SMT2);
  INSERT ("QF_UFNRA", BTOR_LOGIC_QF_UFNRA_TAG_SMT2);
  INSERT ("UFLRA", BTOR_LOGIC_UFLRA_TAG_SMT2);
  INSERT ("UFNIA", BTOR_LOGIC_UFNIA_TAG_SMT2);
  INSERT ("BV", BTOR_LOGIC_BV_TAG_SMT2);
  INSERT ("UFBV", BTOR_LOGIC_UFBV_TAG_SMT2);
  INSERT ("ABV", BTOR_LOGIC_ABV_TAG_SMT2);
  INSERT ("ALL", BTOR_LOGIC_ALL_TAG_SMT2);
}

static BtorSMT2Parser *
new_smt2_parser (Btor *btor)
{
  BtorSMT2Parser *res;
  BtorMemMgr *mem = btor_mem_mgr_new ();
  BTOR_CNEW (mem, res);
  res->done          = false;
  res->btor          = btor;
  res->mem           = mem;
  res->scope_level   = 0;
  res->print_success = false;
  res->store_tokens  = false;

  BTOR_INIT_STACK (mem, res->work);
  BTOR_INIT_STACK (mem, res->sorts);

  BTOR_INIT_STACK (mem, res->sat_assuming_assumptions);
  BTOR_INIT_STACK (mem, res->token);
  BTOR_INIT_STACK (mem, res->tokens);

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
  BTOR_RELEASE_STACK (parser->work);
}

static void
delete_smt2_parser (BtorSMT2Parser *parser)
{
  BtorMemMgr *mem = parser->mem;

  while (parser->scope_level) close_current_scope (parser);

  release_symbols_smt2 (parser);
  release_work_smt2 (parser);

  if (parser->infile_name) btor_mem_freestr (mem, parser->infile_name);
  if (parser->error) btor_mem_freestr (mem, parser->error);

  while (!BTOR_EMPTY_STACK (parser->sorts))
    boolector_release_sort (parser->btor, BTOR_POP_STACK (parser->sorts));
  BTOR_RELEASE_STACK (parser->sorts);

  while (!BTOR_EMPTY_STACK (parser->sat_assuming_assumptions))
  {
    boolector_release (parser->btor,
                       BTOR_POP_STACK (parser->sat_assuming_assumptions));
  }
  BTOR_RELEASE_STACK (parser->sat_assuming_assumptions);
  BTOR_RELEASE_STACK (parser->token);
  BTOR_RELEASE_STACK (parser->tokens);

  BTOR_DELETE (mem, parser);
  btor_mem_mgr_delete (mem);
}

static bool
isspace_smt2 (int32_t ch)
{
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

static uint32_t
cc_smt2 (BtorSMT2Parser *parser, int32_t ch)
{
  if (ch < 0 || ch >= 256) return 0;
  return parser->cc[(unsigned char) ch];
}

/* this is only needed for storing the parsed tokens for get-value */
static void
storech_smt2 (BtorSMT2Parser *parser, int32_t ch)
{
  char t;
  if (!parser->store_tokens) return;

  t = BTOR_EMPTY_STACK (parser->tokens) ? 0 : BTOR_TOP_STACK (parser->tokens);
  if (!ch && t == '(') return;
  if (ch == ')' && t == ' ')
  {
    (void) BTOR_POP_STACK (parser->tokens);
  }
  BTOR_PUSH_STACK (parser->tokens, ch ? ch : ' ');
}

static void
pushch_smt2 (BtorSMT2Parser *parser, int32_t ch)
{
  assert (ch != EOF);
  BTOR_PUSH_STACK (parser->token, ch);
  storech_smt2 (parser, ch);
}

static int32_t
read_token_aux_smt2 (BtorSMT2Parser *parser)
{
  BtorSMT2Node *node;
  unsigned char cc;
  int32_t ch;
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
    storech_smt2 (parser, ch);
    for (;;)
    {
      if ((ch = nextch_smt2 (parser)) == EOF)
        return !cerr_smt2 (parser, "unexpected", ch, "in quoted symbol");
      if (ch == '|')
      {
        storech_smt2 (parser, ch);
        pushch_smt2 (parser, 0);
        if (!(node = find_symbol_smt2 (parser, parser->token.start)))
        {
          node       = new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
          node->name = btor_mem_strdup (parser->mem, parser->token.start);
          assert (!find_symbol_smt2 (parser, node->name));
          insert_symbol_smt2 (parser, node);
        }
        parser->last_node = node;
        return BTOR_SYMBOL_TAG_SMT2;
      }
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
      node->name = btor_mem_strdup (parser->mem, parser->token.start);
      assert (!find_symbol_smt2 (parser, node->name));
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
      node->name = btor_mem_strdup (parser->mem, parser->token.start);
      assert (!find_symbol_smt2 (parser, node->name));
      insert_symbol_smt2 (parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else
    return !cerr_smt2 (parser, "illegal", ch, 0);

  return !perr_smt2 (parser, "internal token reading error");
}

static int32_t
read_token_smt2 (BtorSMT2Parser *parser)
{
  int32_t res;
  parser->lastcoo = parser->coo;
  res             = read_token_aux_smt2 (parser);
  if (boolector_get_opt (parser->btor, BTOR_OPT_VERBOSITY) >= 4)
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

static int32_t
read_rpar_smt2 (BtorSMT2Parser *parser, const char *msg)
{
  int32_t tag = read_token_smt2 (parser);
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

static int32_t
read_lpar_smt2 (BtorSMT2Parser *parser, const char *msg)
{
  int32_t tag = read_token_smt2 (parser);
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

static int32_t
skip_sexprs (BtorSMT2Parser *parser, int32_t initial)
{
  int32_t tag, open = initial;
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

static int32_t
read_symbol (BtorSMT2Parser *parser, const char *errmsg, BtorSMT2Node **resptr)
{
  int32_t tag = read_token_smt2 (parser);
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

static int32_t
str2int32_smt2 (BtorSMT2Parser *parser,
                bool posonly,
                const char *str,
                int32_t *resptr)
{
  int32_t res;
  int32_t ch, digit;
  const char *p;
  res = 0;
  assert (sizeof (int32_t) == 4);
  for (p = str; (ch = *p); p++)
  {
    if (res > INT32_MAX / 10 || ch < '0' || ch > '9')
    INVALID:
      return !perr_smt2 (parser, "invalid 32-bit integer '%s'", str);
    assert ('0' <= ch && ch <= '9');
    if (res) res *= 10;
    digit = ch - '0';
    if (INT32_MAX - digit < res) goto INVALID;
    res += digit;
  }
  if (posonly && !res)
    return !perr_smt2 (
        parser, "expected positive non-zero 32-bit integer at '%s'", str);
  *resptr = res;
  return 1;
}

static int32_t
str2uint32_smt2 (BtorSMT2Parser *parser,
                 bool posonly,
                 const char *str,
                 uint32_t *resptr)
{
  int32_t res, rint = 0;
  res     = str2int32_smt2 (parser, posonly, str, &rint);
  *resptr = (uint32_t) rint;
  return res;
}

static BtorSMT2Item *
push_item_smt2 (BtorSMT2Parser *parser, BtorSMT2Tag tag)
{
  BtorSMT2Item item;
  BTOR_CLR (&item);
  item.coo = parser->coo;
  item.tag = tag;
  BTOR_PUSH_STACK (parser->work, item);
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

static bool
is_item_with_node_smt2 (BtorSMT2Item *item)
{
  if (item->tag == BTOR_SYMBOL_TAG_SMT2) return true;
  if (item->tag == BTOR_ATTRIBUTE_TAG_SMT2) return true;
  if (item->tag & BTOR_TAG_CLASS_MASK_SMT2) return true;
  return false;
}

static const char *
item2str_smt2 (BtorSMT2Item *item)
{
  if (is_item_with_node_smt2 (item))
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

static bool
is_bvconst_str_smt2 (const char *str)
{
  const char *p;
  if (str[0] != 'b' || str[1] != 'v') return false;
  if (!isdigit ((int32_t) str[2])) return false;
  for (p = str + 3; *p; p++)
    if (!isdigit ((int32_t) *p)) return false;
  return true;
}

static bool
prev_item_was_lpar_smt2 (BtorSMT2Parser *parser)
{
  if (BTOR_COUNT_STACK (parser->work) >= 2
      && parser->work.top[-2].tag == BTOR_LPAR_TAG_SMT2)
    return true;
  return !perr_smt2 (parser, "expected '(' before '%s'", parser->token.start);
}

static int32_t
parse_int32_smt2 (BtorSMT2Parser *parser, bool posonly, int32_t *resptr)
{
  int32_t tag = read_token_smt2 (parser);
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
is_boolean_exp_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *p)
{
  return !boolector_is_array (parser->btor, p->exp)
         && !boolector_is_fun (parser->btor, p->exp)
         && boolector_get_width (parser->btor, p->exp) == 1;
}

static int32_t
parse_uint32_smt2 (BtorSMT2Parser *parser, bool posonly, uint32_t *resptr)
{
  int32_t res, rint = 0;
  res     = parse_int32_smt2 (parser, posonly, &rint);
  *resptr = (uint32_t) rint;
  return res;
}

static bool
check_boolean_args_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *p, int32_t nargs)
{
  int32_t i;
  uint32_t width;
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
check_arg_sorts_match_smt2 (BtorSMT2Parser *parser,
                            BtorSMT2Item *p,
                            int32_t nargs)
{
  int32_t i;
  uint32_t domain, width, width2;
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
            "first argument of '%s' is an array but argument %d is not",
            p->node->name,
            i);
      if ((width2 = boolector_get_width (parser->btor, p[i].exp)) != width)
        return !perr_smt2 (
            parser,
            "first argument of '%s' is an array of bit-vectors of width %d "
            "but argument %d is an array of bit-vectors of width %d",
            p->node->name,
            width,
            i,
            width2);
      if ((width2 = boolector_get_index_width (parser->btor, p[i].exp))
          != domain)
        return !perr_smt2 (
            parser,
            "first argument of '%s' is an array with index bit-vectors of "
            "width %d "
            "but argument %d is an array with index bit-vectors of width %d",
            p->node->name,
            domain,
            i,
            width2);
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
      if ((width2 = boolector_get_width (parser->btor, p[i].exp)) != width)
        return !perr_smt2 (parser,
                           "first argument of '%s' is bit-vector of width %d "
                           "but argument %d is a bit-vector of width %d",
                           p->node->name,
                           width,
                           i,
                           width2);
    }
  }
  parser->perrcoo.x = 0;
  return true;
}

static bool
check_ite_args_sorts_match_smt2 (BtorSMT2Parser *parser, BtorSMT2Item *p)
{
  uint32_t domain, width, width2;
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
  if ((width2 = boolector_get_width (parser->btor, p[1].exp)) != 1)
  {
    parser->perrcoo = p[1].coo;
    return !perr_smt2 (parser,
                       "first argument of 'ite' is bit-vector of bit-width %u",
                       width2);
  }
  if (boolector_is_array (parser->btor, p[2].exp))
  {
    if (!boolector_is_array (parser->btor, p[3].exp))
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (parser,
                         "second argument of 'ite' is an array but third not");
    }
    width  = boolector_get_width (parser->btor, p[2].exp);
    width2 = boolector_get_width (parser->btor, p[3].exp);
    if (width != width2)
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (
          parser,
          "second argument of 'ite' is array of bit-vectors of width %u and "
          "third argument is array of bit-vectors of width %u",
          width,
          width2);
    }
    domain = boolector_get_index_width (parser->btor, p[2].exp);
    width2 = boolector_get_index_width (parser->btor, p[3].exp);
    if (domain != width2)
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (
          parser,
          "second argument of 'ite' is array with index bit-vectors of width "
          "%u and "
          "third argument is array with index bit-vectors of width %u",
          domain,
          width2);
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
    width  = boolector_get_width (parser->btor, p[2].exp);
    width2 = boolector_get_width (parser->btor, p[3].exp);
    if (width != width2)
    {
      parser->perrcoo = p->coo;
      return !perr_smt2 (
          parser,
          "second argument of 'ite' is bit-vector of width %d and "
          "third argument is bit-vector of width %d",
          width,
          width2);
    }
  }
  return true;
}

static bool
check_nargs_smt2 (BtorSMT2Parser *parser,
                  BtorSMT2Item *p,
                  int32_t actual,
                  int32_t required)
{
  int32_t diff   = actual - required;
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
                                 int32_t nargs)
{
  int32_t i;
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
translate_rotate_smt2 (Btor *btor,
                       BoolectorNode *exp,
                       uint32_t shift,
                       uint32_t left)
{
  BoolectorNode *l, *r, *res;
  uint32_t width;

  width = boolector_get_width (btor, exp);
  assert (width > 0);
  shift %= width;

  if (shift)
  {
    if (left) shift = width - shift;

    assert (1 <= shift && shift < width);

    l = boolector_slice (btor, exp, shift - 1, 0);
    r = boolector_slice (btor, exp, width - 1, shift);

    res = boolector_concat (btor, l, r);

    boolector_release (btor, l);
    boolector_release (btor, r);
  }
  else
    res = boolector_copy (btor, exp);
  assert (boolector_get_width (btor, res) == width);
  return res;
}

static BoolectorNode *
rotate_left_smt2 (Btor *btor, BoolectorNode *exp, int32_t shift)
{
  return translate_rotate_smt2 (btor, exp, shift, 1);
}

static BoolectorNode *
rotate_right_smt2 (Btor *btor, BoolectorNode *exp, int32_t shift)
{
  return translate_rotate_smt2 (btor, exp, shift, 0);
}

static BoolectorNode *
translate_ext_rotate_smt2 (Btor *btor,
                           BoolectorNode *exp,
                           BoolectorNode *shift,
                           int32_t left)
{
  assert (boolector_is_const (btor, shift));

  BtorBitVector *shift_width_bv;
  uint32_t shift_width;

  /* max width of a bit vector is uint32_t -> conversion not a problem */
  shift_width_bv =
      btor_bv_char_to_bv (btor->mm, (char *) boolector_get_bits (btor, shift));
  shift_width = (uint32_t) btor_bv_to_uint64 (shift_width_bv);
  btor_bv_free (btor->mm, shift_width_bv);

  assert (shift_width < boolector_get_width (btor, exp));

  return translate_rotate_smt2 (btor, exp, shift_width, left);
}

static int parse_sort (BtorSMT2Parser *parser,
                       int tag,
                       bool allow_array_sort,
                       BoolectorSort *sort);

/* -------------------------------------------------------------------------- */

static void
release_exp_and_overwrite (BtorSMT2Parser *parser,
                           BtorSMT2Item *item_open,
                           BtorSMT2Item *item_cur,
                           uint32_t nargs,
                           BoolectorNode *exp)
{
  uint32_t i;

  for (i = 1; i <= nargs; i++)
    boolector_release (parser->btor, item_cur[i].exp);
  parser->work.top = item_cur;
  item_open->tag   = BTOR_EXP_TAG_SMT2;
  item_open->exp   = exp;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_bin_bool (BtorSMT2Parser *parser,
                     BtorSMT2Item *item_open,
                     BtorSMT2Item *item_cur,
                     uint32_t nargs,
                     BoolectorNode *(*fun) (Btor *,
                                            BoolectorNode *,
                                            BoolectorNode *) )
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_IMPLIES_TAG_SMT2
          || item_cur->tag == BTOR_AND_TAG_SMT2
          || item_cur->tag == BTOR_OR_TAG_SMT2
          || item_cur->tag == BTOR_XOR_TAG_SMT2);

  BoolectorNode *old, *exp;
  Btor *btor;
  uint32_t i;

  btor = parser->btor;

  if (nargs < 2)
  {
    parser->perrcoo = item_cur->coo;
    return !perr_smt2 (
        parser, "argument to '%s' missing", item_cur->node->name);
  }

  if (!check_boolean_args_smt2 (parser, item_cur, nargs)) return 0;

  if (item_cur->tag == BTOR_IMPLIES_TAG_SMT2) /* right-associative */
  {
    for (i = nargs, exp = 0; i >= 1; i--)
    {
      if (exp)
      {
        old = exp;
        exp = fun (btor, item_cur[i].exp, old);
        boolector_release (btor, old);
      }
      else
      {
        exp = boolector_copy (btor, item_cur[i].exp);
      }
    }
  }
  else
  {
    for (i = 1, exp = 0; i <= nargs; i++)
    {
      if (exp)
      {
        old = exp;
        exp = fun (btor, old, item_cur[i].exp);
        boolector_release (btor, old);
      }
      else
      {
        exp = boolector_copy (btor, item_cur[i].exp);
      }
    }
  }
  assert (exp);

  release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);

  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_unary_bv_fun (BtorSMT2Parser *parser,
                         BtorSMT2Item *item_open,
                         BtorSMT2Item *item_cur,
                         uint32_t nargs,
                         BoolectorNode *(*fun) (Btor *, BoolectorNode *) )
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_BV_NOT_TAG_SMT2
          || item_cur->tag == BTOR_BV_NEG_TAG_SMT2
          || item_cur->tag == BTOR_BV_REDOR_TAG_SMT2
          || item_cur->tag == BTOR_BV_REDAND_TAG_SMT2);

  BoolectorNode *exp;

  if (!check_nargs_smt2 (parser, item_cur, nargs, 1)) return 0;
  if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
  exp = fun (parser->btor, item_cur[1].exp);
  release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_bin_bv_left_associative (BtorSMT2Parser *parser,
                                    BtorSMT2Item *item_open,
                                    BtorSMT2Item *item_cur,
                                    uint32_t nargs,
                                    BoolectorNode *(*fun) (Btor *,
                                                           BoolectorNode *,
                                                           BoolectorNode *) )
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_BV_CONCAT_TAG_SMT2
          || item_cur->tag == BTOR_BV_AND_TAG_SMT2
          || item_cur->tag == BTOR_BV_OR_TAG_SMT2
          || item_cur->tag == BTOR_BV_XOR_TAG_SMT2
          || item_cur->tag == BTOR_BV_ADD_TAG_SMT2
          || item_cur->tag == BTOR_BV_SUB_TAG_SMT2
          || item_cur->tag == BTOR_BV_MUL_TAG_SMT2);

  BoolectorNode *old, *exp;
  uint32_t i;

  if (nargs < 2)
  {
    parser->perrcoo = item_cur->coo;
    return !perr_smt2 (
        parser, "argument to '%s' missing", item_cur->node->name);
  }

  if (item_cur->tag != BTOR_BV_CONCAT_TAG_SMT2
      && !check_arg_sorts_match_smt2 (parser, item_cur, nargs))
  {
    return 0;
  }

  if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs))
  {
    return 0;
  }

  for (i = 1, exp = 0; i <= nargs; i++)
  {
    if (exp)
    {
      old = exp;
      exp = fun (parser->btor, old, item_cur[i].exp);
      boolector_release (parser->btor, old);
    }
    else
      exp = boolector_copy (parser->btor, item_cur[i].exp);
  }
  assert (exp);
  release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);

  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_bin_bv_fun (BtorSMT2Parser *parser,
                       BtorSMT2Item *item_open,
                       BtorSMT2Item *item_cur,
                       uint32_t nargs,
                       BoolectorNode *(*fun) (Btor *,
                                              BoolectorNode *,
                                              BoolectorNode *) )
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_BV_UDIV_TAG_SMT2
          || item_cur->tag == BTOR_BV_UREM_TAG_SMT2
          || item_cur->tag == BTOR_BV_SHL_TAG_SMT2
          || item_cur->tag == BTOR_BV_LSHR_TAG_SMT2
          || item_cur->tag == BTOR_BV_ASHR_TAG_SMT2
          || item_cur->tag == BTOR_BV_NAND_TAG_SMT2
          || item_cur->tag == BTOR_BV_NOR_TAG_SMT2
          || item_cur->tag == BTOR_BV_XNOR_TAG_SMT2
          || item_cur->tag == BTOR_BV_COMP_TAG_SMT2
          || item_cur->tag == BTOR_BV_SDIV_TAG_SMT2
          || item_cur->tag == BTOR_BV_SREM_TAG_SMT2
          || item_cur->tag == BTOR_BV_SMOD_TAG_SMT2
          || item_cur->tag == BTOR_BV_ULT_TAG_SMT2
          || item_cur->tag == BTOR_BV_ULE_TAG_SMT2
          || item_cur->tag == BTOR_BV_UGT_TAG_SMT2
          || item_cur->tag == BTOR_BV_UGE_TAG_SMT2
          || item_cur->tag == BTOR_BV_SLT_TAG_SMT2
          || item_cur->tag == BTOR_BV_SLE_TAG_SMT2
          || item_cur->tag == BTOR_BV_SGT_TAG_SMT2
          || item_cur->tag == BTOR_BV_SGE_TAG_SMT2);

  BoolectorNode *exp;

  if (!check_nargs_smt2 (parser, item_cur, nargs, 2)) return 0;
  if (!check_arg_sorts_match_smt2 (parser, item_cur, 2)) return 0;
  if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
  exp = fun (parser->btor, item_cur[1].exp, item_cur[2].exp);
  release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_extend_bv_fun (BtorSMT2Parser *parser,
                          BtorSMT2Item *item_open,
                          BtorSMT2Item *item_cur,
                          uint32_t nargs,
                          BoolectorNode *(*fun) (Btor *,
                                                 BoolectorNode *,
                                                 uint32_t))
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_BV_ZERO_EXTEND_TAG_SMT2
          || item_cur->tag == BTOR_BV_SIGN_EXTEND_TAG_SMT2);

  BoolectorNode *exp;
  uint32_t width;

  if (!check_nargs_smt2 (parser, item_cur, nargs, 1)) return 0;
  if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
  width = boolector_get_width (parser->btor, item_cur[1].exp);
  if ((uint32_t) (INT32_MAX - item_cur->num) < width)
  {
    parser->perrcoo = item_cur->coo;
    return !perr_smt2 (
        parser, "resulting bit-width of '%s' too large", item_cur->node->name);
  }
  exp = fun (parser->btor, item_cur[1].exp, item_cur->num);
  release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_rotate_bv_fun (BtorSMT2Parser *parser,
                          BtorSMT2Item *item_open,
                          BtorSMT2Item *item_cur,
                          uint32_t nargs,
                          BoolectorNode *(*fun) (Btor *,
                                                 BoolectorNode *,
                                                 int32_t))
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_BV_ROTATE_LEFT_TAG_SMT2
          || item_cur->tag == BTOR_BV_ROTATE_RIGHT_TAG_SMT2);

  BoolectorNode *exp;
  uint32_t width;

  if (!check_nargs_smt2 (parser, item_cur, nargs, 1)) return 0;
  if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
  width = boolector_get_width (parser->btor, item_cur[1].exp);
  exp   = fun (parser->btor, item_cur[1].exp, item_cur->num % width);
  release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_quant (BtorSMT2Parser *parser,
                  BtorSMT2Item *item_open,
                  BtorSMT2Item *item_cur,
                  uint32_t nargs,
                  BoolectorNode *(*fun) (
                      Btor *, BoolectorNode *[], int32_t, BoolectorNode *) )
{
  assert (parser);
  assert (item_open);
  assert (item_cur);
  assert (fun);

  assert (item_cur->tag == BTOR_FORALL_TAG_SMT2
          || item_cur->tag == BTOR_EXISTS_TAG_SMT2);

  BoolectorNodePtrStack params;
  uint32_t i;
  char *msg;
  BtorSMT2Node *sym;

  msg = item_cur->tag == BTOR_FORALL_TAG_SMT2 ? "forall" : "exists";

  for (i = 1; i < nargs; i++)
  {
    if (item_cur[i].tag != BTOR_SYMBOL_TAG_SMT2)
    {
      parser->perrcoo = item_cur[i].coo;
      return !perr_smt2 (
          parser, "expected symbol as argument %d of '%s'", i, msg);
    }
  }
  if (item_cur[nargs].tag != BTOR_SYMBOL_TAG_SMT2
      && item_cur[nargs].tag != BTOR_EXP_TAG_SMT2)
  {
    parser->perrcoo = item_cur[nargs].coo;
    return !perr_smt2 (
        parser, "expected expression as argument %d of '%s'", nargs, msg);
  }
  if (!is_boolean_exp_smt2 (parser, item_cur + nargs))
  {
    parser->perrcoo = item_cur[nargs].coo;
    return !perr_smt2 (parser, "body of '%s' is not a boolean term", msg);
  }
  BTOR_INIT_STACK (parser->mem, params);
  for (i = 1; i < nargs; i++)
  {
    assert (item_cur[i].tag == BTOR_SYMBOL_TAG_SMT2);
    sym = item_cur[i].node;
    assert (sym);
    assert (sym->coo.x);
    assert (sym->tag);
    assert (sym->tag == BTOR_SYMBOL_TAG_SMT2);
    assert (sym->exp);
    BTOR_PUSH_STACK (params, boolector_copy (parser->btor, sym->exp));
    remove_symbol_smt2 (parser, sym);
  }
  item_open[0].tag = BTOR_EXP_TAG_SMT2;
  item_open[0].exp = fun (parser->btor,
                          params.start,
                          BTOR_COUNT_STACK (params),
                          item_cur[nargs].exp);
  while (!BTOR_EMPTY_STACK (params))
    boolector_release (parser->btor, BTOR_POP_STACK (params));
  boolector_release (parser->btor, item_cur[nargs].exp);
  BTOR_RELEASE_STACK (params);
  parser->work.top = item_cur;
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term (BtorSMT2Parser *parser)
{
  assert (parser);

  Btor *btor;
  BoolectorNode *exp, *tmp, *old;
  int32_t open, tag, k;
  uint32_t i, j, width, width2, domain, nargs;
  BtorSMT2Item *item_open;
  BtorSMT2Item *item_cur;
  BtorSMT2Node *sym;

  open = parser->open;
  btor = parser->btor;

  if (parser->expecting_body)
  {
    item_open = 0;
    if (open)
    {
      item_open = last_lpar_smt2 (parser);
      if (++item_open >= parser->work.top) item_open = 0;
    }
    if (item_open)
    {
      assert (item_open->tag == BTOR_LET_TAG_SMT2);
      return !perr_smt2 (parser,
                         "body to '%s' at line %d column %d missing",
                         parser->expecting_body,
                         item_open->coo.x,
                         item_open->coo.y);
    }
    else
    {
      return !perr_smt2 (parser, "body to 'let' missing");
    }
  }
  assert (open >= 0);
  if (!open) return !perr_smt2 (parser, "expected expression");
  item_open = last_lpar_smt2 (parser);
  assert (item_open);
  item_cur = item_open + 1;
  if (item_cur == parser->work.top)
    return !perr_smt2 (parser, "unexpected '()'");
  nargs = parser->work.top - item_cur - 1;
  tag   = item_cur->tag;

  /* check if operands are expressions -------------------------------------- */
  if (tag != BTOR_LET_TAG_SMT2 && tag != BTOR_LETBIND_TAG_SMT2
      && tag != BTOR_PARLETBINDING_TAG_SMT2 && tag != BTOR_SORTED_VAR_TAG_SMT2
      && tag != BTOR_SORTED_VARS_TAG_SMT2 && tag != BTOR_FORALL_TAG_SMT2
      && tag != BTOR_EXISTS_TAG_SMT2)
  {
    for (i = 1; i <= nargs; i++)
      if (item_cur[i].tag != BTOR_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2 (parser, "expected expression");
      }
  }

  /* expression ------------------------------------------------------------- */
  if (tag == BTOR_EXP_TAG_SMT2)
  {
    /* function application */
    if (nargs && boolector_is_fun (btor, item_cur[0].exp))
    {
      BoolectorNodePtrStack fargs;
      BTOR_INIT_STACK (parser->mem, fargs);
      for (i = 1; i <= nargs; i++)
      {
        if (item_cur[i].tag != BTOR_EXP_TAG_SMT2)
        {
          BTOR_RELEASE_STACK (fargs);
          parser->perrcoo = item_cur[i].coo;
          return !perr_smt2 (parser, "expected expression");
        }
        BTOR_PUSH_STACK (fargs, item_cur[i].exp);
      }
      tmp = item_cur[0].exp;
      if (nargs != boolector_get_fun_arity (btor, tmp))
      {
        BTOR_RELEASE_STACK (fargs);
        return !perr_smt2 (parser, "invalid number of arguments");
      }
      k = boolector_fun_sort_check (btor, fargs.start, nargs, tmp);
      if (k >= 0)
      {
        BTOR_RELEASE_STACK (fargs);
        return !perr_smt2 (parser, "invalid sort for argument %d", k + 1);
      }
      parser->work.top = item_cur;
      item_open->tag   = BTOR_EXP_TAG_SMT2;
      item_open->exp   = boolector_apply (btor, fargs.start, nargs, tmp);
      for (i = 0; i <= nargs; i++) boolector_release (btor, item_cur[i].exp);
      BTOR_RELEASE_STACK (fargs);
    }
    else
    {
      if (nargs)
      {
        parser->perrcoo = item_open->coo;
        return !perr_smt2 (parser, "list with %d expressions", nargs + 1);
      }
      item_cur->coo = item_open->coo;
      *item_open    = *item_cur;
      parser->work.top--;
      assert (item_open + 1 == parser->work.top);
    }
  }
  /* CORE: NOT -------------------------------------------------------------- */
  else if (tag == BTOR_NOT_TAG_SMT2)
  {
    if (nargs != 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (
          parser, "'not' with %d arguments but expected exactly one", nargs);
    }
    tmp = item_cur[1].exp;
    if (boolector_is_array (btor, tmp))
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2 (parser,
                         "unexpected array expression as argument to 'not'");
    }
    if ((width = boolector_get_width (btor, tmp)) != 1)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2 (
          parser,
          "unexpected bit-vector of width %d as argument to 'not'",
          width);
    }
    parser->work.top = item_cur;
    item_open->tag   = BTOR_EXP_TAG_SMT2;
    item_open->exp   = boolector_not (btor, tmp);
    boolector_release (btor, tmp);
  }
  /* CORE: IMPLIES ---------------------------------------------------------- */
  else if (tag == BTOR_IMPLIES_TAG_SMT2)
  {
    if (!close_term_bin_bool (
            parser, item_open, item_cur, nargs, boolector_implies))
    {
      return 0;
    }
  }
  /* CORE: AND -------------------------------------------------------------- */
  else if (tag == BTOR_AND_TAG_SMT2)
  {
    if (!close_term_bin_bool (
            parser, item_open, item_cur, nargs, boolector_and))
    {
      return 0;
    }
  }
  /* CORE: OR --------------------------------------------------------------- */
  else if (tag == BTOR_OR_TAG_SMT2)
  {
    if (!close_term_bin_bool (parser, item_open, item_cur, nargs, boolector_or))
    {
      return 0;
    }
  }
  /* CORE: XOR -------------------------------------------------------------- */
  else if (tag == BTOR_XOR_TAG_SMT2)
  {
    if (!close_term_bin_bool (
            parser, item_open, item_cur, nargs, boolector_xor))
    {
      return 0;
    }
  }
  /* CORE: EQUAL ------------------------------------------------------------ */
  else if (tag == BTOR_EQUAL_TAG_SMT2)
  {
    if (!nargs)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser, "arguments to '=' missing");
    }
    if (nargs == 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser, "only one argument to '='");
    }
    if (!check_arg_sorts_match_smt2 (parser, item_cur, nargs)) return 0;
    exp = boolector_eq (btor, item_cur[1].exp, item_cur[2].exp);
    for (i = 3; i < nargs; i++)
    {
      tmp = boolector_eq (btor, item_cur[i - 1].exp, item_cur[i].exp);
      old = exp;
      exp = boolector_and (btor, old, tmp);
      boolector_release (btor, old);
      boolector_release (btor, tmp);
    }
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* CORE: DISTINCT --------------------------------------------------------- */
  else if (tag == BTOR_DISTINCT_TAG_SMT2)
  {
    if (!nargs)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser, "arguments to 'distinct' missing");
    }
    if (nargs == 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser, "only one argument to 'distinct'");
    }
    if (!check_arg_sorts_match_smt2 (parser, item_cur, nargs)) return 0;
    exp = 0;
    for (i = 1; i < nargs; i++)
    {
      for (j = i + 1; j <= nargs; j++)
      {
        tmp = boolector_ne (btor, item_cur[i].exp, item_cur[j].exp);
        if (exp)
        {
          old = exp;
          exp = boolector_and (btor, old, tmp);
          boolector_release (btor, old);
          boolector_release (btor, tmp);
        }
        else
        {
          exp = tmp;
        }
      }
    }
    assert (exp);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* CORE: ITE -------------------------------------------------------------- */
  else if (tag == BTOR_ITE_TAG_SMT2)
  {
    if (!check_nargs_smt2 (parser, item_cur, nargs, 3)) return 0;
    if (!check_ite_args_sorts_match_smt2 (parser, item_cur)) return 0;
    exp = boolector_cond (
        btor, item_cur[1].exp, item_cur[2].exp, item_cur[3].exp);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* ARRAY: SELECT ---------------------------------------------------------- */
  else if (tag == BTOR_ARRAY_SELECT_TAG_SMT2)
  {
    if (!check_nargs_smt2 (parser, item_cur, nargs, 2)) return 0;
    if (!boolector_is_array (btor, item_cur[1].exp))
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2 (parser, "first argument of 'select' is not an array");
    }
    if (boolector_is_array (btor, item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2 (parser, "second argument of 'select' is an array");
    }
    width  = boolector_get_width (btor, item_cur[2].exp);
    domain = boolector_get_index_width (btor, item_cur[1].exp);
    if (width != domain)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser,
                         "first (array) argument of 'select' has index "
                         "bit-width %u but the second (index) argument "
                         "has bit-width %u",
                         domain,
                         width);
    }
    exp = boolector_read (btor, item_cur[1].exp, item_cur[2].exp);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* ARRAY: STORE ----------------------------------------------------------- */
  else if (tag == BTOR_ARRAY_STORE_TAG_SMT2)
  {
    if (!check_nargs_smt2 (parser, item_cur, nargs, 3)) return 0;
    if (!boolector_is_array (btor, item_cur[1].exp))
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2 (parser, "first argument of 'store' is not an array");
    }
    if (boolector_is_array (btor, item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2 (parser, "second argument of 'store' is an array");
    }
    if (boolector_is_array (btor, item_cur[3].exp))
    {
      parser->perrcoo = item_cur[3].coo;
      return !perr_smt2 (parser, "third argument of 'store' is an array");
    }
    width  = boolector_get_width (btor, item_cur[2].exp);
    domain = boolector_get_index_width (btor, item_cur[1].exp);
    if (width != domain)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser,
                         "first (array) argument of 'store' has index "
                         "bit-width %u but the second (index) argument "
                         "has bit-width %u",
                         domain,
                         width);
    }
    width  = boolector_get_width (btor, item_cur[1].exp);
    width2 = boolector_get_width (btor, item_cur[3].exp);
    if (width != width2)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser,
                         "first (array) argument of 'store' has element "
                         "bit-width %u but the third (stored bit-vector) "
                         "argument has bit-width %u",
                         width,
                         width2);
    }
    exp = boolector_write (
        btor, item_cur[1].exp, item_cur[2].exp, item_cur[3].exp);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* BV: EXTRACT ------------------------------------------------------------ */
  else if (tag == BTOR_BV_EXTRACT_TAG_SMT2)
  {
    if (!check_nargs_smt2 (parser, item_cur, nargs, 1)) return 0;
    if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
    width = boolector_get_width (btor, item_cur[1].exp);
    if (width <= (uint32_t) item_cur->idx0)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser,
                         "first (high) 'extract' parameter %u too large "
                         "for bit-vector argument of bit-width %u",
                         item_cur->idx0,
                         width);
    }
    exp =
        boolector_slice (btor, item_cur[1].exp, item_cur->idx0, item_cur->idx1);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* BV: NOT ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_NOT_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun (
            parser, item_open, item_cur, nargs, boolector_not))
    {
      return 0;
    }
  }
  /* BV: NEG ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_NEG_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun (
            parser, item_open, item_cur, nargs, boolector_neg))
    {
      return 0;
    }
  }
  /* BV: REDOR -------------------------------------------------------------- */
  else if (tag == BTOR_BV_REDOR_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun (
            parser, item_open, item_cur, nargs, boolector_redor))
    {
      return 0;
    }
  }
  /* BV: REDAND ------------------------------------------------------------- */
  else if (tag == BTOR_BV_REDAND_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun (
            parser, item_open, item_cur, nargs, boolector_redand))
    {
      return 0;
    }
  }
  /* BV: CONCAT ------------------------------------------------------------- */
  else if (tag == BTOR_BV_CONCAT_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_concat))
    {
      return 0;
    }
  }
  /* BV: AND ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_AND_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_and))
    {
      return 0;
    }
  }
  /* BV: OR ----------------------------------------------------------------- */
  else if (tag == BTOR_BV_OR_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_or))
    {
      return 0;
    }
  }
  /* BV: XOR ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_XOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_xor))
    {
      return 0;
    }
  }
  /* BV: ADD ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_ADD_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_add))
    {
      return 0;
    }
  }
  /* BV: SUB ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_SUB_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_sub))
    {
      return 0;
    }
  }
  /* BV: MUL ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_MUL_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative (
            parser, item_open, item_cur, nargs, boolector_mul))
    {
      return 0;
    }
  }
  /* BV: UDIV --------------------------------------------------------------- */
  else if (tag == BTOR_BV_UDIV_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_udiv))
    {
      return 0;
    }
  }
  /* BV: UREM --------------------------------------------------------------- */
  else if (tag == BTOR_BV_UREM_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_urem))
    {
      return 0;
    }
  }
  /* BV: SHL ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_SHL_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_sll))
    {
      return 0;
    }
  }
  /* BV: LSHR --------------------------------------------------------------- */
  else if (tag == BTOR_BV_LSHR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_srl))
    {
      return 0;
    }
  }
  /* BV: ULT ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_ULT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_ult))
    {
      return 0;
    }
  }
  /* BV: NAND --------------------------------------------------------------- */
  else if (tag == BTOR_BV_NAND_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_nand))
    {
      return 0;
    }
  }
  /* BV: NOR ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_NOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_nor))
    {
      return 0;
    }
  }
  /* BV: XNOR --------------------------------------------------------------- */
  else if (tag == BTOR_BV_XNOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_xnor))
    {
      return 0;
    }
  }
  /* BV: COMP --------------------------------------------------------------- */
  else if (tag == BTOR_BV_COMP_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_eq))
    {
      return 0;
    }
  }
  /* BV: SDIV --------------------------------------------------------------- */
  else if (tag == BTOR_BV_SDIV_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_sdiv))
    {
      return 0;
    }
  }
  /* BV: SREM --------------------------------------------------------------- */
  else if (tag == BTOR_BV_SREM_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_srem))
    {
      return 0;
    }
  }
  /* BV: SMOD --------------------------------------------------------------- */
  else if (tag == BTOR_BV_SMOD_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_smod))
    {
      return 0;
    }
  }
  /* BV: ASHR --------------------------------------------------------------- */
  else if (tag == BTOR_BV_ASHR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_sra))
    {
      return 0;
    }
  }
  /* BV: REPEAT ------------------------------------------------------------- */
  else if (tag == BTOR_BV_REPEAT_TAG_SMT2)
  {
    if (!check_nargs_smt2 (parser, item_cur, nargs, 1)) return 0;
    if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
    width = boolector_get_width (btor, item_cur[1].exp);
    if (item_cur->num && ((uint32_t) (INT32_MAX / item_cur->num) < width))
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2 (parser, "resulting bit-width of 'repeat' too large");
    }
    exp = boolector_repeat (btor, item_cur[1].exp, item_cur->num);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* BV: ZERO EXTEND -------------------------------------------------------- */
  else if (tag == BTOR_BV_ZERO_EXTEND_TAG_SMT2)
  {
    if (!close_term_extend_bv_fun (
            parser, item_open, item_cur, nargs, boolector_uext))
    {
      return 0;
    }
  }
  /* BV: SIGN EXTEND -------------------------------------------------------- */
  else if (tag == BTOR_BV_SIGN_EXTEND_TAG_SMT2)
  {
    if (!close_term_extend_bv_fun (
            parser, item_open, item_cur, nargs, boolector_sext))
    {
      return 0;
    }
  }
  /* BV: ROTATE LEFT -------------------------------------------------------- */
  else if (tag == BTOR_BV_ROTATE_LEFT_TAG_SMT2)
  {
    if (!close_term_rotate_bv_fun (
            parser, item_open, item_cur, nargs, rotate_left_smt2))
    {
      return 0;
    }
  }
  /* BV: ROTATE RIGHT ------------------------------------------------------- */
  else if (tag == BTOR_BV_ROTATE_RIGHT_TAG_SMT2)
  {
    if (!close_term_rotate_bv_fun (
            parser, item_open, item_cur, nargs, rotate_right_smt2))
    {
      return 0;
    }
  }
  /* BV: Z3 extensions ------------------------------------------------------ */
  else if (tag == BTOR_BV_EXT_ROTATE_LEFT_TAG_SMT2
           || tag == BTOR_BV_EXT_ROTATE_RIGHT_TAG_SMT2)
  {
    if (!check_nargs_smt2 (parser, item_cur, nargs, 2)) return 0;
    if (!check_not_array_or_uf_args_smt2 (parser, item_cur, nargs)) return 0;
    if (!boolector_is_const (btor, item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2 (
          parser,
          "second argument '%s' of ext_rotate_%s"
          "is not a bit vector constant",
          item_cur[2].node->name,
          tag == BTOR_BV_EXT_ROTATE_LEFT_TAG_SMT2 ? "left" : "right");
    }
    exp = translate_ext_rotate_smt2 (btor,
                                     item_cur[1].exp,
                                     item_cur[2].exp,
                                     tag == BTOR_BV_EXT_ROTATE_LEFT_TAG_SMT2);
    release_exp_and_overwrite (parser, item_open, item_cur, nargs, exp);
  }
  /* BV: ULE ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_ULE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_ulte))
    {
      return 0;
    }
  }
  /* BV: UGT ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_UGT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_ugt))
    {
      return 0;
    }
  }
  /* BV: UGE ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_UGE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_ugte))
    {
      return 0;
    }
  }
  /* BV: SLT ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_SLT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_slt))
    {
      return 0;
    }
  }
  /* BV: SLE ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_SLE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_slte))
    {
      return 0;
    }
  }
  /* BV: SGT ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_SGT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_sgt))
    {
      return 0;
    }
  }
  /* BV: SGE ---------------------------------------------------------------- */
  else if (tag == BTOR_BV_SGE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun (
            parser, item_open, item_cur, nargs, boolector_sgte))
    {
      return 0;
    }
  }
  /* let (<var_binding>+) <term> -------------------------------------------- */
  else if (tag == BTOR_LET_TAG_SMT2)
  {
    for (i = 1; i < nargs; i++)
    {
      if (item_cur[i].tag != BTOR_SYMBOL_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2 (
            parser, "expected symbol as argument %d of 'let'", i);
      }
    }
    if (item_cur[nargs].tag != BTOR_SYMBOL_TAG_SMT2)
    {
      if (item_cur[i].tag != BTOR_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2 (
            parser, "expected expression as argument %d of 'let'", nargs);
      }
    }
    item_open[0].tag = BTOR_EXP_TAG_SMT2;
    item_open[0].exp = item_cur[nargs].exp;
    for (i = 1; i < nargs; i++)
    {
      assert (item_cur[i].tag == BTOR_SYMBOL_TAG_SMT2);
      sym = item_cur[i].node;
      assert (sym);
      assert (sym->coo.x);
      assert (sym->tag == BTOR_SYMBOL_TAG_SMT2);
      remove_symbol_smt2 (parser, sym);
    }
    parser->work.top = item_cur;
  }
  /* <var_binding> ---------------------------------------------------------- */
  else if (tag == BTOR_LETBIND_TAG_SMT2)
  {
    assert (item_cur[1].tag == BTOR_SYMBOL_TAG_SMT2);
    if (nargs == 1)
      return !perr_smt2 (
          parser, "term to be bound to '%s' missing", item_cur[1].node->name);
    if (nargs > 2)
    {
      parser->perrcoo = item_cur[3].coo;
      return !perr_smt2 (
          parser, "second term bound to '%s'", item_cur[1].node->name);
    }
    if (item_cur[2].tag != BTOR_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2 (parser, "expected expression in 'let' var binding");
    }
    item_open[0] = item_cur[1];
    assert (!item_open[0].node->exp);
    assert (item_cur[2].tag == BTOR_EXP_TAG_SMT2);
    item_open[0].node->exp = item_cur[2].exp;
    assert (!item_open[0].node->bound);
    item_open[0].node->bound = 1;
    parser->work.top         = item_cur;
    assert (!parser->isvarbinding);
    parser->isvarbinding = true;
  }
  /* (<var_binding>+) ------------------------------------------------------- */
  else if (tag == BTOR_PARLETBINDING_TAG_SMT2)
  {
    assert (parser->isvarbinding);
    parser->isvarbinding = false;
#ifndef NDEBUG
    for (i = 1; i <= nargs; i++)
      assert (item_cur[i].tag == BTOR_SYMBOL_TAG_SMT2);
#endif
    for (i = 0; i < nargs; i++) item_open[i] = item_cur[i + 1];
    parser->work.top = item_open + nargs;
    assert (!parser->expecting_body);
    parser->expecting_body = "let";
  }
  /* forall (<sorted_var>+) <term> ------------------------------------------ */
  else if (tag == BTOR_FORALL_TAG_SMT2)
  {
    if (!close_term_quant (
            parser, item_open, item_cur, nargs, boolector_forall))
    {
      return 0;
    }
  }
  /* exists (<sorted_var>+) <term> ------------------------------------------ */
  else if (tag == BTOR_EXISTS_TAG_SMT2)
  {
    if (!close_term_quant (
            parser, item_open, item_cur, nargs, boolector_exists))
    {
      return 0;
    }
  }
  /* <sorted_var> ----------------------------------------------------------- */
  else if (tag == BTOR_SORTED_VAR_TAG_SMT2)
  {
    assert (item_cur[1].tag == BTOR_SYMBOL_TAG_SMT2);
    if (nargs != 1)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2 (parser,
                         "expected only one variable at sorted var '%s'",
                         item_cur[1].node->name);
    }
    parser->work.top = item_cur;
    item_open->tag   = BTOR_SYMBOL_TAG_SMT2;
    item_open->node  = item_cur[1].node;
    assert (boolector_is_param (btor, item_open->node->exp));
    assert (!parser->sorted_var);
    parser->sorted_var = 1;
  }
  /* (<sorted_var>+) -------------------------------------------------------- */
  else if (tag == BTOR_SORTED_VARS_TAG_SMT2)
  {
    assert (parser->sorted_var);
    parser->sorted_var = 0;
#ifndef NDEBUG
    for (i = 1; i <= nargs; i++)
    {
      assert (item_cur[i].tag == BTOR_SYMBOL_TAG_SMT2);
      assert (boolector_is_param (btor, item_cur[i].node->exp));
    }
#endif
    for (i = 0; i < nargs; i++) item_open[i] = item_cur[i + 1];
    parser->work.top = item_open + nargs;
    assert (!parser->expecting_body);
    parser->expecting_body = "quantifier";
  }
  /* DEFAULT: unsupported --------------------------------------------------- */
  else
  {
    // This should not occur, but we keep it as a bad style of
    // defensive programming for future extensions of the parser.
    parser->perrcoo = item_cur->coo;
    return !perr_smt2 (
        parser,
        "internal parse error: can not close yet unsupported '%s'",
        item2str_smt2 (item_cur));
  }
  assert (open > 0);
  parser->open = open - 1;

  return 1;
}

static int32_t
parse_open_term_quant (BtorSMT2Parser *parser, const char *msg)
{
  assert (parser);
  assert (msg);

  if (!read_lpar_smt2 (parser, msg)) return 0;
  push_item_smt2 (parser, BTOR_LPAR_TAG_SMT2);
  parser->open++, assert (parser->open > 0);
  push_item_smt2 (parser, BTOR_SORTED_VARS_TAG_SMT2);
  assert (!parser->sorted_var);
  parser->sorted_var       = 1;
  parser->need_quantifiers = true;
  return 1;
}

static int32_t
check_open_term_indexed_one_fixed_num_parametric (BtorSMT2Parser *parser,
                                                     BtorSMT2Node *node)
{
  assert (parser);

  if (BTOR_COUNT_STACK (parser->work) < 3)
  {
    assert (BTOR_COUNT_STACK (parser->work) == 2);
    assert (parser->work.start[0].tag == BTOR_LPAR_TAG_SMT2);
    assert (parser->work.start[1].tag == BTOR_UNDERSCORE_TAG_SMT2);
    parser->perrcoo = parser->work.start[0].coo;
    return !perr_smt2 (parser, "expected '(' before '(_ %s'", node->name);
  }
  if (parser->work.top[-3].tag != BTOR_LPAR_TAG_SMT2)
  {
    parser->perrcoo = parser->work.top[-3].coo;
    return !perr_smt2 (parser,
                       "expected '(' at '%s' before '(_ %s'",
                       item2str_smt2 (parser->work.top - 3),
                       node->name);
  }
  return 1;
}

static int32_t
parse_open_term_indexed_one_fixed_num_parametric (BtorSMT2Parser *parser,
                                                     BtorSMT2Item *item_cur,
                                                     int32_t tag,
                                                     BtorSMT2Node *node,
                                                     const char *msg)
{
  assert (parser);
  assert (item_cur);
  assert (node);
  assert (msg);

  assert (BTOR_COUNT_STACK (parser->work) >= 2);

  BtorSMT2Item *item_open;

  if (!check_open_term_indexed_one_fixed_num_parametric (parser, node))
    return 0;
  item_open = item_cur - 1;
  if (!parse_int32_smt2 (parser, false, &item_open->num)) return 0;
  item_open->tag   = tag;
  item_open->node  = node;
  parser->work.top = item_cur;
  if (!read_rpar_smt2 (parser, msg)) return 0;
  assert (parser->open > 0);
  parser->open--;
  return 1;
}

static int32_t
parse_open_term_indexed (BtorSMT2Parser *parser, BtorSMT2Item *item_cur)
{
  assert (parser);
  assert (item_cur);

  uint32_t width, width2;
  int32_t tag;
  BtorSMT2Node *node;
  BoolectorNode *exp;
  BoolectorSort s;
  Btor *btor;

  btor = parser->btor;

  if (!prev_item_was_lpar_smt2 (parser)) return 0;

  tag  = read_token_smt2 (parser);
  node = parser->last_node;

  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser, "unexpected end-of-file after '_'");

  if (tag == BTOR_BV_REPEAT_TAG_SMT2)
  {
    assert (node && tag == (int32_t) node->tag);
    if (!parse_open_term_indexed_one_fixed_num_parametric (
            parser, item_cur, tag, node, " to close '(_ repeat'"))
    {
      return 0;
    }
  }
  else if (tag == BTOR_BV_ZERO_EXTEND_TAG_SMT2)
  {
    if (!parse_open_term_indexed_one_fixed_num_parametric (
            parser, item_cur, tag, node, " to close '(_ zero_extend'"))
    {
      return 0;
    }
  }
  else if (tag == BTOR_BV_SIGN_EXTEND_TAG_SMT2)
  {
    if (!parse_open_term_indexed_one_fixed_num_parametric (
            parser, item_cur, tag, node, " to close '(_ sign_extend'"))
    {
      return 0;
    }
  }
  else if (tag == BTOR_BV_ROTATE_LEFT_TAG_SMT2)
  {
    if (!parse_open_term_indexed_one_fixed_num_parametric (
            parser, item_cur, tag, node, " to close '(_ rotate_left'"))
    {
      return 0;
    }
  }
  else if (tag == BTOR_BV_ROTATE_RIGHT_TAG_SMT2)
  {
    if (!parse_open_term_indexed_one_fixed_num_parametric (
            parser, item_cur, tag, node, " to close '(_ rotate_right'"))
    {
      return 0;
    }
  }
  else if (tag == BTOR_BV_EXTRACT_TAG_SMT2)
  {
    BtorSMT2Coo firstcoo;
    BtorSMT2Item *item_open = item_cur - 1;
    assert (node && tag == (int32_t) node->tag);
    if (!check_open_term_indexed_one_fixed_num_parametric (parser, node))
      return 0;
    if (!parse_int32_smt2 (parser, false, &item_open->idx0)) return 0;
    firstcoo = parser->coo;
    if (!parse_int32_smt2 (parser, false, &item_open->idx1)) return 0;
    if (item_open->idx0 < item_open->idx1)
    {
      parser->perrcoo = firstcoo;
      return !perr_smt2 (parser,
                         "first parameter '%u' of '(_ extract' "
                         "smaller than second '%u'",
                         item_open->idx0,
                         item_open->idx1);
    }
    item_open->tag           = tag;
    item_open->node          = node;
    parser->work.top = item_cur;
    if (!read_rpar_smt2 (parser, " to close '(_ extract'")) return 0;
    assert (parser->open > 0);
    parser->open--;
  }
  else if (tag == BTOR_SYMBOL_TAG_SMT2
           && is_bvconst_str_smt2 (parser->token.start))
  {
    char *constr, *decstr;
    BtorSMT2Coo coo;
    exp    = 0;
    decstr = btor_mem_strdup (parser->mem, parser->token.start + 2);
    constr = btor_util_dec_to_bin_str (parser->mem,
                                       parser->token.start + 2);
    coo    = parser->coo;
    coo.y += 2;
    if (parse_uint32_smt2 (parser, true, &width))
    {
      width2 = strlen (constr);
      if (width2 > width)
      {
        parser->perrcoo = coo;
        (void) perr_smt2 (parser,
                          "decimal constant '%s' needs %d bits which "
                          "exceeds bit-width '%d'",
                          decstr,
                          width2,
                          width);
      }
      else if (width2 == width)
        exp = boolector_const (btor, constr);
      else if (!width2)
      {
        s   = boolector_bitvec_sort (btor, width);
        exp = boolector_zero (btor, s);
        boolector_release_sort (btor, s);
      }
      else
      {
        BtorBitVector *constrbv = 0, *uconstrbv;
        char *uconstr;
        if (!strcmp (constr, ""))
          uconstrbv = btor_bv_new (parser->mem, width - width2);
        else
        {
          constrbv  = btor_bv_char_to_bv (parser->mem, constr);
          uconstrbv = btor_bv_uext (parser->mem, constrbv, width - width2);
        }
        uconstr = btor_bv_to_char (parser->mem, uconstrbv);
        exp     = boolector_const (btor, uconstr);
        btor_mem_freestr (parser->mem, uconstr);
        btor_bv_free (parser->mem, uconstrbv);
        if (constrbv) btor_bv_free (parser->mem, constrbv);
      }
    }
    btor_mem_freestr (parser->mem, decstr);
    btor_mem_freestr (parser->mem, constr);
    if (!exp) return 0;
    assert (boolector_get_width (btor, exp) == width);
    assert (item_cur > parser->work.start);
    item_cur--, parser->work.top--;
    assert (item_cur->tag == BTOR_LPAR_TAG_SMT2);
    assert (parser->open > 0);
    parser->open--;
    item_cur->tag = BTOR_EXP_TAG_SMT2;
    item_cur->exp = exp;
    if (!read_rpar_smt2 (parser, " to close '(_ bv..'")) return 0;
  }
  else
  {

    return !perr_smt2 (parser,
                       "invalid parametric term '_ %s'",
                       parser->token.start);
  }
  return 1;
}

static int32_t
parse_open_term (BtorSMT2Parser *parser, int32_t tag)
{
  assert (parser);

  uint32_t width, width2;
  BtorSMT2Item *item_cur;
  BtorSMT2Node *sym, *new_sym;
  BoolectorSort s;
  Btor *btor;

  btor = parser->btor;
  sym  = 0;
  new_sym = 0;

  if (parser->expecting_body) parser->expecting_body = 0;

  item_cur = push_item_smt2 (parser, tag);

  if (tag == BTOR_LPAR_TAG_SMT2)
  {
    BtorSMT2Item *q;
    if (parser->isvarbinding)
    {
      push_item_smt2 (parser, BTOR_LETBIND_TAG_SMT2);
      parser->isvarbinding = false;

      tag = read_token_smt2 (parser);

      if (tag == BTOR_INVALID_TAG_SMT2) return 0;
      if (tag == EOF)
        return !perr_smt2 (
            parser,
            "expected symbol to be bound after '(' at line %d "
            "column %d but reached end-of-file",
            item_cur->coo.x,
            item_cur->coo.y);

      if (tag != BTOR_SYMBOL_TAG_SMT2)
        return !perr_smt2 (
            parser,
            "expected symbol to be bound at '%s' after '(' at "
            "line %d column %d",
            parser->token.start,
            item_cur->coo.x,
            item_cur->coo.y);
      sym = parser->last_node;
      assert (sym);
      /* shadow previously defined symbols */
      if (sym->coo.x)
      {
        new_sym       = new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
        new_sym->name = btor_mem_strdup (parser->mem, sym->name);
        /* symbol may already be in symbol table */
        insert_symbol_smt2 (parser, new_sym);
        sym = new_sym;
      }
      sym->coo = parser->coo;
      q        = push_item_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
      q->node  = sym;
    }
    /* parse <sorted_var>: <symbol> <sort> */
    else if (parser->sorted_var)
    {
      push_item_smt2 (parser, BTOR_SORTED_VAR_TAG_SMT2);
      parser->sorted_var = 0;
      s                  = 0;
      if (!read_symbol (parser, " in sorted var after '('", &sym)) return 0;
      assert (sym && sym->tag == BTOR_SYMBOL_TAG_SMT2);
      /* shadow previously defined symbols */
      if (sym->coo.x)
      {
        new_sym       = new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
        new_sym->name = btor_mem_strdup (parser->mem, sym->name);
        /* symbol may already be in symbol table */
        insert_symbol_smt2 (parser, new_sym);
        sym = new_sym;
      }
      sym->coo = parser->coo;

      tag = read_token_smt2 (parser);
      if (!parse_sort (parser, tag, false, &s)) return 0;

      q       = push_item_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
      q->node = sym;
      char buf[strlen (sym->name)
               + btor_util_num_digits (parser->bound_vars) + 2];
      sprintf (buf, "%s!%d", sym->name, parser->bound_vars++);
      sym->exp = boolector_param (btor, s, buf);
    }
    parser->open++;
  }
  else if (parser->isvarbinding)
  {
    return !perr_smt2 (
        parser, "expected var binding at '%s'", parser->token.start);
  }
  else if (parser->sorted_var)
  {
    return !perr_smt2 (
        parser, "expected sorted variable at '%s'", parser->token.start);
  }
  else if (is_item_with_node_smt2 (item_cur))
  {
    item_cur->node = parser->last_node;
    if (tag & BTOR_COMMAND_TAG_CLASS_SMT2)
      return !perr_smt2 (parser, "unexpected command '%s'", item_cur->node->name);
    if (tag & BTOR_KEYWORD_TAG_CLASS_SMT2)
      return !perr_smt2 (parser, "unexpected keyword '%s'", item_cur->node->name);
    if (tag & BTOR_LOGIC_TAG_CLASS_SMT2)
      return !perr_smt2 (parser, "unexpected logic '%s'", item_cur->node->name);
    if (tag & BTOR_RESERVED_TAG_CLASS_SMT2)
    {
      if (tag == BTOR_LET_TAG_SMT2)
      {
        if (!read_lpar_smt2 (parser, " after 'let'")) return 0;
        push_item_smt2 (parser, BTOR_LPAR_TAG_SMT2);
        parser->open++, assert (parser->open > 0);
        push_item_smt2 (parser, BTOR_PARLETBINDING_TAG_SMT2);
        assert (!parser->isvarbinding);
        parser->isvarbinding = true;
      }
      else if (tag == BTOR_FORALL_TAG_SMT2)
      {
        if (!parse_open_term_quant (parser, " after 'forall'")) return 0;
      }
      else if (tag == BTOR_EXISTS_TAG_SMT2)
      {
        if (!parse_open_term_quant (parser, " after 'exists'")) return 0;
      }
      else if (tag == BTOR_UNDERSCORE_TAG_SMT2)
      {
        if (!parse_open_term_indexed(parser, item_cur)) return 0;
      }
      else
      {
        assert (item_cur->node->name);
        return !perr_smt2 (
            parser, "unsupported reserved word '%s'", item_cur->node->name);
      }
    }
    else if (tag == BTOR_SYMBOL_TAG_SMT2)
    {
      assert (item_cur->node);
      if (!item_cur->node->exp)
        return !perr_smt2 (parser, "undefined symbol '%s'", item_cur->node->name);
      item_cur->tag = BTOR_EXP_TAG_SMT2;
      item_cur->exp = boolector_copy (btor, item_cur->node->exp);
    }
    else if (tag == BTOR_TRUE_TAG_SMT2)
    {
      item_cur->tag = BTOR_EXP_TAG_SMT2;
      item_cur->exp = boolector_true (btor);
    }
    else if (tag == BTOR_FALSE_TAG_SMT2)
    {
      item_cur->tag = BTOR_EXP_TAG_SMT2;
      item_cur->exp = boolector_false (btor);
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
    else if (tag & BTOR_BV_TAG_CLASS_SMT2)
    {
      if (tag == BTOR_BV_BITVEC_TAG_SMT2)
        return !perr_smt2 (parser, "unexpected 'BitVec'");
    }
    else
      return !perr_smt2 (
          parser, "unexpected token '%s'", item2str_smt2 (item_cur));
  }
  else if (tag == BTOR_BINARY_CONSTANT_TAG_SMT2)
  {
    item_cur->tag = BTOR_EXP_TAG_SMT2;
    item_cur->exp = boolector_const (btor, parser->token.start + 2);
  }
  else if (tag == BTOR_HEXADECIMAL_CONSTANT_TAG_SMT2)
  {
    char *constr, *uconstr;
    BtorBitVector *constrbv = 0, *uconstrbv;
    constr =
        btor_util_hex_to_bin_str (parser->mem, parser->token.start + 2);
    width2 = strlen (constr);
    width  = strlen (parser->token.start + 2) * 4;
    assert (width2 <= width);
    if (width2 == width)
      uconstr = btor_mem_strdup (parser->mem, constr);
    else
    {
      if (!strcmp (constr, ""))
        uconstrbv = btor_bv_new (parser->mem, width - width2);
      else
      {
        constrbv  = btor_bv_char_to_bv (parser->mem, constr);
        uconstrbv = btor_bv_uext (parser->mem, constrbv, width - width2);
      }
      uconstr = btor_bv_to_char (parser->mem, uconstrbv);
      btor_bv_free (parser->mem, uconstrbv);
      if (constrbv) btor_bv_free (parser->mem, constrbv);
    }
    item_cur->tag = BTOR_EXP_TAG_SMT2;
    item_cur->exp = boolector_const (btor, uconstr);
    btor_mem_freestr (parser->mem, uconstr);
    btor_mem_freestr (parser->mem, constr);
  }
  else
  {
    return !perr_smt2 (
        parser, "unexpected token '%s'", parser->token.start);
  }

  return 1;
}

/* Note: we need look ahead and tokens string only for get-value
 *       (for parsing a term list and printing the originally parsed,
 *       non-simplified expression) */
static int32_t
parse_term_aux_smt2 (BtorSMT2Parser *parser,
                     bool have_look_ahead,
                     int32_t look_ahead,
                     BoolectorNode **resptr,
                     BtorSMT2Coo *cooptr)
{
  size_t work_cnt;
  int32_t tag;
  BoolectorNode *res;
  BtorSMT2Item *l, *p;
  Btor *btor;

  btor         = parser->btor;
  parser->open = 0;

  work_cnt = BTOR_COUNT_STACK (parser->work);

  do
  {
    if (have_look_ahead)
    {
      tag             = look_ahead;
      have_look_ahead = false;
    }
    else
      tag = read_token_smt2 (parser);

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
          "unexpected end-of-file, '(' at line %d column %d not closed",
          l->coo.x,
          l->coo.y);
    }

    /* ------------------------------------------------------------------- */
    /* close term                                                          */
    /* ------------------------------------------------------------------- */
    if (tag == BTOR_RPAR_TAG_SMT2)
    {
      if (!close_term (parser)) return 0;
    }
    /* ------------------------------------------------------------------- */
    /* parse term                                                          */
    /* ------------------------------------------------------------------- */
    else
    {
      if (!parse_open_term(parser, tag)) return 0;
    }
  } while (parser->open);
  if (BTOR_COUNT_STACK (parser->work) - work_cnt != 1)
  {
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
  res     = boolector_copy (btor, p->exp);
  *cooptr = p->coo;
  release_item_smt2 (parser, p);
  assert (BTOR_COUNT_STACK (parser->work) == work_cnt);
  *resptr = res;
  return 1;
}

/* -------------------------------------------------------------------------- */

static int32_t
parse_term_smt2 (BtorSMT2Parser *parser,
                 BoolectorNode **resptr,
                 BtorSMT2Coo *cooptr)
{
  return parse_term_aux_smt2 (parser, false, 0, resptr, cooptr);
}

static int32_t
parse_bit_width_smt2 (BtorSMT2Parser *parser, uint32_t *width)
{
  int32_t tag;

  tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    return 0;
  }
  if (tag == EOF)
  {
    return !perr_smt2 (parser, "expected bit-width but reached end-of-file");
  }
  if (tag != BTOR_DECIMAL_CONSTANT_TAG_SMT2)
  {
    return !perr_smt2 (
        parser, "expected bit-width at '%s'", parser->token.start);
  }
  assert (parser->token.start[0] != '-');
  if (strchr (parser->token.start, '.'))
  {
    return !perr_smt2 (parser,
                       "invalid bit-width '%s', expected integer",
                       parser->token.start);
  }
  if (parser->token.start[0] == '0')
  {
    assert (!parser->token.start[1]);
    return !perr_smt2 (parser, "invalid zero bit-width");
  }
  *width = 0;
  return str2uint32_smt2 (parser, true, parser->token.start, width) ? 1 : 0;
}

/*
 * skiptokens = 1 -> skip BTOR_LPAR_TAG_SMT2
 * skiptokens = 2 -> skip BTOR_UNDERSCORE_TAG_SMT2
 */
static int32_t
parse_bitvec_sort (BtorSMT2Parser *parser,
                   uint32_t skiptokens,
                   BoolectorSort *resptr)
{
  assert (skiptokens <= 2);

  int32_t tag;
  uint32_t width;

  if (skiptokens < 1 && !read_lpar_smt2 (parser, 0))
  {
    return 0;
  }
  if (skiptokens < 2)
  {
    tag = read_token_smt2 (parser);
    if (tag == EOF)
      return !perr_smt2 (parser, "expected '_' but reached end-of-file");
    if (tag != BTOR_UNDERSCORE_TAG_SMT2)
      return !perr_smt2 (parser, "expected '_' at '%s'", parser->token.start);
  }

  tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2)
  {
    return 0;
  }
  if (tag == EOF)
  {
    return !perr_smt2 (parser, "expected 'BitVec' but reached end-of-file");
  }
  if (tag != BTOR_BV_BITVEC_TAG_SMT2)
  {
    return !perr_smt2 (
        parser, "expected 'BitVec' at '%s'", parser->token.start);
  }

  if (!parse_bit_width_smt2 (parser, &width))
  {
    return 0;
  }
  BTOR_MSG (boolector_get_btor_msg (parser->btor),
            3,
            "parsed bit-vector sort of width %d",
            width);
  *resptr = boolector_bitvec_sort (parser->btor, width);
  BTOR_PUSH_STACK (parser->sorts, *resptr);

  return read_rpar_smt2 (parser, " to close bit-vector sort");
}

static int32_t
parse_array_sort (BtorSMT2Parser *parser, int32_t tag, BoolectorSort *sort)
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
    BTOR_PUSH_STACK (parser->sorts, *sort);
    return 1;
  }
  else if (tag == EOF)
    return !perr_smt2 (parser, "reached end-of-file but expected 'Array'");
  return !perr_smt2 (parser, "expected 'Array' at '%s'", parser->token.start);
}

static int32_t
parse_sort (BtorSMT2Parser *parser,
            int32_t tag,
            bool allow_array_sort,
            BoolectorSort *sort)
{
  BtorSMT2Node *alias;

  if (tag == BTOR_BOOL_TAG_SMT2)
  {
    *sort = boolector_bool_sort (parser->btor);
    BTOR_PUSH_STACK (parser->sorts, *sort);
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

static int32_t
declare_fun_smt2 (BtorSMT2Parser *parser, bool isconst)
{
  char *symbol;
  uint32_t i;
  int32_t tag;
  BoolectorSortStack args;
  BtorSMT2Node *fun;
  fun = 0;
  BoolectorSort sort, s;

  if (!read_symbol (parser,
                    isconst ? " after 'declare-const'" : " after 'declare-fun'",
                    &fun))
  {
    return 0;
  }

  assert (fun && fun->tag == BTOR_SYMBOL_TAG_SMT2);

  if (fun->coo.x)
    return !perr_smt2 (parser,
                       "symbol '%s' already defined at line %d column %d",
                       fun->name,
                       fun->coo.x,
                       fun->coo.y);
  fun->coo = parser->coo;

  BTOR_INIT_STACK (parser->mem, args);

  if (!isconst)
  {
    if (!read_lpar_smt2 (
            parser, isconst ? " after const name" : " after function name"))
    {
      BTOR_RELEASE_STACK (args);
      return 0;
    }

    do
    {
      tag = read_token_smt2 (parser);
      if (tag != BTOR_RPAR_TAG_SMT2)
      {
        if (!parse_sort (parser, tag, false, &sort))
        {
          BTOR_RELEASE_STACK (args);
          return 0;
        }
        BTOR_PUSH_STACK (args, sort);
      }
    } while (tag != BTOR_RPAR_TAG_SMT2);
  }

  /* parse return sort */
  tag = read_token_smt2 (parser);
  if (!parse_sort (parser, tag, true, &sort))
  {
    BTOR_RELEASE_STACK (args);
    return 0;
  }
  /* bit-vector/array variable */
  if (BTOR_EMPTY_STACK (args))
  {
    if (boolector_is_fun_sort (parser->btor, sort))
    {
      fun->exp = boolector_array (parser->btor, sort, fun->name);
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "declared bit-vector array '%s' at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
      parser->need_arrays = true;
    }
    else
    {
      symbol   = create_symbol_current_scope (parser, fun->name);
      fun->exp = boolector_var (parser->btor, sort, symbol);
      btor_mem_freestr (parser->mem, symbol);
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                2,
                "declared '%s' as bit-vector at line %d column %d",
                fun->name,
                fun->coo.x,
                fun->coo.y);
    }
  }
  else
  {
    /* check if arguments have bit-vector sort, all other sorts are not
     * supported for uninterpreted functions */
    for (i = 0; i < BTOR_COUNT_STACK (args); i++)
    {
      s = BTOR_PEEK_STACK (args, i);
      if (!boolector_is_bitvec_sort (parser->btor, s))
      {
        BTOR_RELEASE_STACK (args);
        return !perr_smt2 (parser,
                           "only bit-vector sorts "
                           "supported for arity > 0");
      }
    }
    if (!boolector_is_bitvec_sort (parser->btor, sort))
    {
      BTOR_RELEASE_STACK (args);
      return !perr_smt2 (parser,
                         "only bit-vector sorts supported as return sort "
                         "for arity > 0");
    }

    s = boolector_fun_sort (
        parser->btor, args.start, BTOR_COUNT_STACK (args), sort);
    symbol   = create_symbol_current_scope (parser, fun->name);
    fun->exp = boolector_uf (parser->btor, s, symbol);
    boolector_release_sort (parser->btor, s);
    btor_mem_freestr (parser->mem, symbol);
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              2,
              "declared '%s' as uninterpreted function at line %d column %d",
              fun->name,
              fun->coo.x,
              fun->coo.y);
    parser->need_functions = true;
  }
  BTOR_RELEASE_STACK (args);
  return read_rpar_smt2 (parser, " to close declaration");
}

/* Note: if we're currently parsing a model, define-fun for sorted vars
 *       have to be transformed into assertions of the form
 *       assert (= var assignment), define-funs for funs with args >= 1
 *       have to be built before asserting.
 *       Further, all symbols we parse are already defined -> check sort. */
static int32_t
define_fun_smt2 (BtorSMT2Parser *parser)
{
  int32_t tag, nargs = 0, len;
  BoolectorNode *eq, *tmp, *exp = 0;
  BtorSMT2Coo coo;
  BtorSMT2Item *item;
  BtorSMT2Node *fun, *arg, *new_arg;
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
      {
        new_arg       = new_node_smt2 (parser, BTOR_SYMBOL_TAG_SMT2);
        new_arg->name = btor_mem_strdup (parser->mem, arg->name);
        /* symbol may already be in symbol table */
        insert_symbol_smt2 (parser, new_arg);
        arg = new_arg;
      }
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
      parser->need_arrays = true;
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
      assert (parser->need_arrays);
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
      if ((boolector_is_fun (parser->btor, fun->exp)
           && boolector_fun_get_codomain_sort (parser->btor, fun->exp) != sort)
          || (!boolector_is_fun (parser->btor, fun->exp)
              && boolector_get_sort (parser->btor, fun->exp) != sort))
      {
        return !perr_smt2 (parser, "invalid sort, expected");
      }
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
    BTOR_INIT_STACK (parser->mem, args);
    item = parser->work.top - nargs;
    /* collect arguments, remove symbols (scope is only this function) */
    while (item < parser->work.top)
    {
      arg = item->node;
      item++;
      assert (arg);
      assert (arg->coo.x);
      assert (arg->tag == BTOR_SYMBOL_TAG_SMT2);
      BTOR_PUSH_STACK (args, boolector_copy (parser->btor, arg->exp));
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
        BTOR_RELEASE_STACK (args);
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
      btor_mem_freestr (parser->mem, symbol);
      parser->need_functions = true;
    }
    while (!BTOR_EMPTY_STACK (args))
      boolector_release (parser->btor, BTOR_POP_STACK (args));
    boolector_release (parser->btor, exp);
    BTOR_RELEASE_STACK (args);
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

static int32_t
define_sort_smt2 (BtorSMT2Parser *parser)
{
  int32_t tag;
  BtorSMT2Node *sort_alias;
  BoolectorSort sort;

  sort_alias = 0;
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

static int32_t
declare_sort_smt2 (BtorSMT2Parser *parser)
{
  uint32_t arity, opt_bit_width = 0;
  BtorSMT2Node *sort_alias;
  BoolectorSort sort;

  opt_bit_width = boolector_get_opt (parser->btor, BTOR_OPT_DECLSORT_BV_WIDTH);
  if (!opt_bit_width)
    return !perr_smt2 (parser,
                       "'declare-sort' not supported if it is not interpreted "
                       " as a bit-vector");

  sort_alias = 0;
  if (!read_symbol (parser, " after 'declare-sort'", &sort_alias)) return 0;
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

  if (!parse_uint32_smt2 (parser, false, &arity)) return 0;
  if (arity != 0)
    return !perr_smt2 (parser, "sort arity other than 0 not supported");

  sort                   = boolector_bitvec_sort (parser->btor, opt_bit_width);
  sort_alias->sort       = 1;
  sort_alias->sort_alias = sort;
  BTOR_PUSH_STACK (parser->sorts, sort);
  return read_rpar_smt2 (parser, " to close sort declaration");
}

static int32_t
echo_smt2 (BtorSMT2Parser *parser)
{
  int32_t tag;

  tag = read_token_smt2 (parser);

  if (tag == BTOR_INVALID_TAG_SMT2) return 0;

  if (tag == EOF)
    return !perr_smt2 (parser, "unexpected end-of-file after 'echo'");

  if (tag == BTOR_RPAR_TAG_SMT2)
    return !perr_smt2 (parser, "string after 'echo' missing");

  if (tag != BTOR_STRING_CONSTANT_TAG_SMT2)
    return !perr_smt2 (parser, "expected string after 'echo'");

  fprintf (parser->outfile, "%s", parser->token.start);
  return skip_sexprs (parser, 1);
}

static int32_t
set_info_smt2 (BtorSMT2Parser *parser)
{
  int32_t tag = read_token_smt2 (parser);
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

static int32_t
set_option_smt2 (BtorSMT2Parser *parser)
{
  int32_t tag, val, verb = 0;
  char *opt;
  BtorOption o;

  tag = read_token_smt2 (parser);
  if (tag == BTOR_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2 (parser, "unexpected end-of-file after 'set-option'");
  if (tag == BTOR_RPAR_TAG_SMT2)
    return !perr_smt2 (parser, "keyword after 'set-option' missing");

  /* parser specific options */
  if (tag == BTOR_PRODUCE_UNSAT_ASSUMPTIONS_TAG_SMT2)
  {
    /* do nothing, enabled by default */
  }
  else if (tag == BTOR_REGULAR_OUTPUT_CHANNEL_TAG_SMT2)
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
      if (!btor_hashptr_table_get (parser->btor->str2opt, opt))
        return !perr_smt2 (parser, "unsupported option: '%s'", opt);
      o = btor_hashptr_table_get (parser->btor->str2opt, opt)->data.as_int;
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

static void
check_sat (BtorSMT2Parser *parser)
{
  assert (!parser->error);
  while (!BTOR_EMPTY_STACK (parser->sat_assuming_assumptions))
  {
    boolector_release (parser->btor,
                       BTOR_POP_STACK (parser->sat_assuming_assumptions));
  }
  if (parser->commands.check_sat++
      && !boolector_get_opt (parser->btor, BTOR_OPT_INCREMENTAL))
  {
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              1,
              "WARNING additional 'check-sat' command");
  }
  if (boolector_get_opt (parser->btor, BTOR_OPT_PARSE_INTERACTIVE))
  {
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              1,
              "parsed %d commands in %.2f seconds",
              parser->commands.all,
              btor_util_time_stamp () - parser->parse_start);
    parser->res->result = boolector_sat (parser->btor);
    parser->res->nsatcalls += 1;
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
    parser->done = true;
  }
}

static int32_t
read_exp_list (BtorSMT2Parser *parser,
               BoolectorNodePtrStack *exps,
               BtorSMT2Coo *coo)
{
  int32_t tag        = 0;
  BoolectorNode *exp = 0;

  /* parse list of symbols/terms */
  BTOR_INIT_STACK (parser->mem, *exps);
  parser->store_tokens = true;
  if (!parse_term_aux_smt2 (parser, false, 0, &exp, coo))
  {
    while (!BTOR_EMPTY_STACK (*exps))
      boolector_release (parser->btor, BTOR_POP_STACK (*exps));
    BTOR_RELEASE_STACK (*exps);
    return 0;
  }
  if (BTOR_TOP_STACK (parser->tokens) == ' ')
    (void) BTOR_POP_STACK (parser->tokens);
  BTOR_PUSH_STACK (parser->tokens, 0);
  BTOR_PUSH_STACK (*exps, exp);
  tag = read_token_smt2 (parser);
  while (tag != EOF && tag != BTOR_RPAR_TAG_SMT2)
  {
    if (!parse_term_aux_smt2 (parser, true, tag, &exp, coo))
    {
      while (!BTOR_EMPTY_STACK (*exps))
        boolector_release (parser->btor, BTOR_POP_STACK (*exps));
      BTOR_RELEASE_STACK (*exps);
      return 0;
    }
    if (BTOR_TOP_STACK (parser->tokens) == ' ')
      (void) BTOR_POP_STACK (parser->tokens);
    BTOR_PUSH_STACK (parser->tokens, 0);
    BTOR_PUSH_STACK (*exps, exp);
    tag = read_token_smt2 (parser);
  }
  parser->store_tokens = false;
  return 1;
}

static int32_t
read_command_smt2 (BtorSMT2Parser *parser)
{
  uint32_t i, width, level;
  int32_t tag;
  BoolectorNode *exp = 0;
  BtorSMT2Coo coo;
  BoolectorNodePtrStack exps;
  BoolectorNode **failed_assumptions;

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
      switch (tag)
      {
        case BTOR_LOGIC_QF_BV_TAG_SMT2:
          parser->res->logic = BTOR_LOGIC_QF_BV;
          break;
        case BTOR_LOGIC_QF_AUFBV_TAG_SMT2:
        case BTOR_LOGIC_QF_UFBV_TAG_SMT2:
        case BTOR_LOGIC_QF_ABV_TAG_SMT2:
          parser->res->logic = BTOR_LOGIC_QF_AUFBV;
          break;
        case BTOR_LOGIC_ABV_TAG_SMT2:
          parser->res->logic = BTOR_LOGIC_QF_ABV;
          break;
        case BTOR_LOGIC_BV_TAG_SMT2: parser->res->logic = BTOR_LOGIC_BV; break;
        case BTOR_LOGIC_UFBV_TAG_SMT2:
          parser->res->logic = BTOR_LOGIC_QF_UFBV;
          break;
        case BTOR_LOGIC_ALL_TAG_SMT2:
          parser->res->logic = BTOR_LOGIC_ALL;
          break;
        default:
          return !perr_smt2 (
              parser, "unsupported logic '%s'", parser->token.start);
      }
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
      check_sat (parser);
      break;

    case BTOR_CHECK_SAT_ASSUMING_TAG_SMT2:
      if (!read_lpar_smt2 (parser, " after 'check-sat-assuming'")) return 0;
      if (!boolector_get_opt (parser->btor, BTOR_OPT_INCREMENTAL))
        return !perr_smt2 (parser, "incremental solving is not enabled");
      if (!read_exp_list (parser, &exps, &coo))
      {
        while (!BTOR_EMPTY_STACK (exps))
          boolector_release (parser->btor, BTOR_POP_STACK (exps));
        BTOR_RELEASE_STACK (exps);
        return 0;
      }
      for (i = 0; i < BTOR_COUNT_STACK (exps); i++)
      {
        exp = BTOR_PEEK_STACK (exps, i);
        if (boolector_is_array (parser->btor, exp))
        {
          parser->perrcoo = coo;
          while (!BTOR_EMPTY_STACK (exps))
            boolector_release (parser->btor, BTOR_POP_STACK (exps));
          BTOR_RELEASE_STACK (exps);
          return !perr_smt2 (
              parser, "assumption argument is an array and not a formula");
        }
        boolector_assume (parser->btor, exp);
      }
      if (!read_rpar_smt2 (parser, " after 'check-sat-assuming'"))
      {
        BTOR_RELEASE_STACK (exps);
        return 0;
      }
      check_sat (parser);
      for (i = 0; i < BTOR_COUNT_STACK (exps); i++)
      {
        exp = BTOR_PEEK_STACK (exps, i);
        BTOR_PUSH_STACK (parser->sat_assuming_assumptions, exp);
      }
      BTOR_RELEASE_STACK (exps);
      BTOR_RESET_STACK (parser->tokens);
      break;

    case BTOR_DECLARE_FUN_TAG_SMT2:
      if (!declare_fun_smt2 (parser, false)) return 0;
      print_success (parser);
      break;

    case BTOR_DECLARE_CONST_TAG_SMT2:
      if (!declare_fun_smt2 (parser, true)) return 0;
      print_success (parser);
      break;

    case BTOR_DEFINE_FUN_TAG_SMT2:
      if (!define_fun_smt2 (parser)) return 0;
      print_success (parser);
      break;

    case BTOR_DECLARE_SORT_TAG_SMT2:
      if (!declare_sort_smt2 (parser)) return 0;
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
      boolector_assert (parser->btor, exp);
      boolector_release (parser->btor, exp);
      assert (!parser->error);
      parser->commands.asserts++;
      print_success (parser);
      break;

    case BTOR_ECHO_TAG_SMT2:
      if (!echo_smt2 (parser)) return 0;
      break;

    case BTOR_EXIT_TAG_SMT2:
      if (!read_rpar_smt2 (parser, " after 'exit'")) return 0;
      assert (!parser->commands.exits);
      parser->commands.exits++;
      parser->done = true;
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

    case BTOR_GET_UNSAT_ASSUMPTIONS_TAG_SMT2:
      if (!read_rpar_smt2 (parser, " after 'get-unsat-assumptions'")) return 0;
      if (parser->res->result != BOOLECTOR_UNSAT) break;
      fputc ('(', parser->outfile);
      failed_assumptions = boolector_get_failed_assumptions (parser->btor);
      for (i = 0; failed_assumptions[i] != 0; i++)
      {
        boolector_dump_smt2_node (
            parser->btor, parser->outfile, failed_assumptions[i]);
      }
      free (failed_assumptions);
      failed_assumptions = 0;
      fputc (')', parser->outfile);
      fflush (parser->outfile);
      break;

    case BTOR_GET_VALUE_TAG_SMT2:
      if (!read_lpar_smt2 (parser, " after 'get-value'")) return 0;
      if (!boolector_get_opt (parser->btor, BTOR_OPT_MODEL_GEN))
        return !perr_smt2 (parser, "model generation is not enabled");
      if (parser->res->result != BOOLECTOR_SAT) break;
      if (!read_exp_list (parser, &exps, &coo))
      {
        while (!BTOR_EMPTY_STACK (exps))
          boolector_release (parser->btor, BTOR_POP_STACK (exps));
        BTOR_RELEASE_STACK (exps);
        return 0;
      }
      if (!read_rpar_smt2 (parser, " after 'get-value'"))
      {
        while (!BTOR_EMPTY_STACK (exps))
          boolector_release (parser->btor, BTOR_POP_STACK (exps));
        BTOR_RELEASE_STACK (exps);
        return 0;
      }
      fputc ('(', parser->outfile);
      char *symbols = parser->tokens.start;
      for (i = 0; i < BTOR_COUNT_STACK (exps); i++)
      {
        if (BTOR_COUNT_STACK (exps) > 1) fputs ("\n ", parser->outfile);
        exp = BTOR_PEEK_STACK (exps, i);
        boolector_print_value_smt2 (
            parser->btor, exp, symbols, parser->outfile);
        boolector_release (parser->btor, exp);
        symbols += strlen (symbols) + 1;
        assert (symbols <= parser->tokens.top);
      }
      if (BTOR_COUNT_STACK (exps) > 1) fputc ('\n', parser->outfile);
      fprintf (parser->outfile, ")\n");
      fflush (parser->outfile);
      BTOR_RELEASE_STACK (exps);
      BTOR_RESET_STACK (parser->tokens);
      break;

    case BTOR_MODEL_TAG_SMT2:
      // FIXME model parsing for arrays currently disabled
      if (parser->need_arrays)
        return !perr_smt2 (parser,
                           "model parsing for arrays currently not supported");
      ///////////
      if (parser->commands.model)
        return !perr_smt2 (parser, "nesting models is invalid");
      parser->commands.model = 1;
      while (read_command_smt2 (parser) && !boolector_terminate (parser->btor))
        ;
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
      (void) parse_uint32_smt2 (parser, true, &level);
      if (!read_rpar_smt2 (parser, " after 'push'")) return 0;
      for (i = 0; i < level; i++) open_new_scope (parser);
      boolector_push (parser->btor, level);
      print_success (parser);
      break;

    case BTOR_POP_TAG_SMT2:
      (void) parse_uint32_smt2 (parser, true, &level);
      if (!read_rpar_smt2 (parser, " after 'pop'")) return 0;
      if (level > parser->scope_level)
      {
        return !perr_smt2 (
            parser,
            "popping more scopes (%u) than created via push (%u)",
            level,
            parser->scope_level);
      }
      for (i = 0; i < level; i++) close_current_scope (parser);
      boolector_pop (parser->btor, level);
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
  double start = btor_util_time_stamp (), delta;

  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->nextcoo.x   = 1;
  parser->nextcoo.y   = 1;
  parser->infile      = infile;
  parser->infile_name = btor_mem_strdup (parser->mem, infile_name);
  parser->outfile     = outfile;
  parser->saved       = false;
  parser->parse_start = start;
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
  delta = btor_util_time_stamp () - start;
  if (delta < 0) delta = 0;
  BTOR_MSG (boolector_get_btor_msg (parser->btor),
            1,
            "parsed %d commands in %.2f seconds",
            parser->commands.all,
            delta);

  if (parser->need_functions
      && parser->need_arrays
      && parser->res->logic == BTOR_LOGIC_QF_BV)
  {
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              1,
              "found functions thus using 'QF_AUFBV' logic");
    parser->res->logic = BTOR_LOGIC_QF_AUFBV;
  }
  else if (parser->need_functions && parser->res->logic == BTOR_LOGIC_QF_BV)
  {
    BTOR_MSG (boolector_get_btor_msg (parser->btor),
              1,
              "found functions thus using 'QF_UFBV' logic");
    parser->res->logic = BTOR_LOGIC_QF_UFBV;
  }
  /* determine logic to use */
  else if (parser->res->logic == BTOR_LOGIC_ALL)
  {
    if (!parser->need_quantifiers)
    {
      if (parser->need_functions || parser->need_arrays)
        parser->res->logic = BTOR_LOGIC_QF_AUFBV;
      else
        parser->res->logic = BTOR_LOGIC_QF_BV;
    }
    else
    {
      /* we only support quantifiers with pure bit-vectors for now */
      parser->res->logic = BTOR_LOGIC_BV;
    }
  }
  else if (parser->commands.set_logic)
  {
    if (!parser->need_functions
        && !parser->need_arrays
        && !parser->need_quantifiers
        && parser->res->logic == BTOR_LOGIC_QF_AUFBV)
    {
      BTOR_MSG (boolector_get_btor_msg (parser->btor),
                1,
                "no functions found thus restricting logic to 'QF_BV'");
      parser->res->logic = BTOR_LOGIC_QF_BV;
    }
  }
  return 0;
}

static BtorParserAPI parsesmt2_parser_api = {
    (BtorInitParser) new_smt2_parser,
    (BtorResetParser) delete_smt2_parser,
    (BtorParse) parse_smt2_parser};

const BtorParserAPI *
btor_parsesmt2_parser_api ()
{
  return &parsesmt2_parser_api;
}
