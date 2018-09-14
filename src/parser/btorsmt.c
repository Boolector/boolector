/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorsmt.h"
#include "btorbv.h"
#include "btoropt.h"
#include "utils/btorhashptr.h"
#include "utils/btormem.h"
#include "utils/btorstack.h"
#include "utils/btorutil.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>

BTOR_DECLARE_STACK (BoolectorNodePtr, BoolectorNode *);

/*------------------------------------------------------------------------*/

typedef struct BtorSMTParser BtorSMTParser;
typedef struct BtorSMTNode BtorSMTNode;
typedef struct BtorSMTNodes BtorSMTNodes;
typedef struct BtorSMTSymbol BtorSMTSymbol;

enum BtorSMTCharacterClass
{
  BTOR_SMTCC_IDENTIFIER_START    = 1,
  BTOR_SMTCC_IDENTIFIER_MIDDLE   = 2,
  BTOR_SMTCC_ARITHMETIC_OPERATOR = 4,
  BTOR_SMTCC_NUMERAL_START       = 8,
  BTOR_SMTCC_DIGIT               = 16,
  BTOR_SMTCC_SPACE               = 32,
  BTOR_SMTCC_IDENTIFIER_PREFIX   = 64,
};

enum BtorSMTToken
{
  BTOR_SMTOK_ERR = 0,
  BTOR_SMTOK_EOF = EOF,

  BTOR_SMTOK_IDENTIFIER = 'a',
  BTOR_SMTOK_NUMERAL    = '0',
  BTOR_SMTOK_RATIONAL   = '.',
  BTOR_SMTOK_USERVAL    = '{',
  BTOR_SMTOK_LP         = '(',
  BTOR_SMTOK_RP         = ')',
  BTOR_SMTOK_STRING     = '"',
  BTOR_SMTOK_VAR        = '?',
  BTOR_SMTOK_FVAR       = '$',
  BTOR_SMTOK_ATTR       = ':',
  BTOR_SMTOK_ARITH      = '=',

  BTOR_SMTOK_KEYWORD      = 256, /* above ASCII codes */
  BTOR_SMTOK_AND          = 256,
  BTOR_SMTOK_ASSUMPTION   = 257,
  BTOR_SMTOK_BENCHMARK    = 258,
  BTOR_SMTOK_DISTINCT     = 259,
  BTOR_SMTOK_EXTRAFUNS    = 260,
  BTOR_SMTOK_EXTRAPREDS   = 261,
  BTOR_SMTOK_EXTRASORTS   = 262,
  BTOR_SMTOK_FALSE        = 263,
  BTOR_SMTOK_FLET         = 264,
  BTOR_SMTOK_FORMULA      = 265,
  BTOR_SMTOK_IFF          = 266,
  BTOR_SMTOK_IF_THEN_ELSE = 267,
  BTOR_SMTOK_IMPLIES      = 268,
  BTOR_SMTOK_ITE          = 269,
  BTOR_SMTOK_LET          = 270,
  BTOR_SMTOK_LOGICATTR    = 271,
  BTOR_SMTOK_NOT          = 272,
  BTOR_SMTOK_NOTES        = 273,
  BTOR_SMTOK_OR           = 274,
  BTOR_SMTOK_SAT          = 275,
  BTOR_SMTOK_STATUS       = 276,
  BTOR_SMTOK_TRUE         = 277,
  BTOR_SMTOK_UNKNOWN      = 278,
  BTOR_SMTOK_UNSAT        = 279,
  BTOR_SMTOK_XOR          = 280,

  BTOR_SMTOK_CONCAT  = 281, /* QF_BV specific symbols */
  BTOR_SMTOK_EQ      = 282,
  BTOR_SMTOK_EXTRACT = 283,
  BTOR_SMTOK_BIT0    = 284,
  BTOR_SMTOK_BIT1    = 285,
  BTOR_SMTOK_BVADD   = 286,
  BTOR_SMTOK_BVNOT   = 287,
  BTOR_SMTOK_BVMUL   = 288,
  BTOR_SMTOK_BVULE   = 289,
  BTOR_SMTOK_BVAND   = 290,
  BTOR_SMTOK_BVLSHR  = 291,
  BTOR_SMTOK_BVSLT   = 292,
  BTOR_SMTOK_BVULT   = 293,
  BTOR_SMTOK_BVNEG   = 294,
  BTOR_SMTOK_BVSLE   = 295,
  BTOR_SMTOK_BVSHL   = 296,
  BTOR_SMTOK_BVSUB   = 297,
  BTOR_SMTOK_BVSDIV  = 298,
  BTOR_SMTOK_BVASHR  = 299,
  BTOR_SMTOK_BVOR    = 300,
  BTOR_SMTOK_BVUDIV  = 301,
  BTOR_SMTOK_BVUREM  = 302,
  BTOR_SMTOK_BVNAND  = 303,
  BTOR_SMTOK_BVNOR   = 304,
  BTOR_SMTOK_BVUGT   = 305,
  BTOR_SMTOK_BVUGE   = 306,
  BTOR_SMTOK_BVSGT   = 307,
  BTOR_SMTOK_BVSGE   = 308,
  BTOR_SMTOK_BVCOMP  = 309,

  BTOR_SMTOK_REPEAT       = 310,
  BTOR_SMTOK_ZERO_EXTEND  = 311,
  BTOR_SMTOK_SIGN_EXTEND  = 312,
  BTOR_SMTOK_ROTATE_LEFT  = 313,
  BTOR_SMTOK_ROTATE_RIGHT = 314,

  BTOR_SMTOK_BVXOR  = 315,
  BTOR_SMTOK_BVSREM = 316,
  BTOR_SMTOK_BVSMOD = 317,
  BTOR_SMTOK_BVXNOR = 318,

  BTOR_SMTOK_SELECT = 319,
  BTOR_SMTOK_STORE  = 320,

  BTOR_SMTOK_UNSUPPORTED_KEYWORD = 512,
  BTOR_SMTOK_AXIOMS              = 512,
  BTOR_SMTOK_DEFINITIONS         = 513,
  BTOR_SMTOK_EXISTS              = 514,
  BTOR_SMTOK_EXTENSIONS          = 515,
  BTOR_SMTOK_FORALL              = 516,
  BTOR_SMTOK_FUNS                = 517,
  BTOR_SMTOK_LANGUAGE            = 518,
  BTOR_SMTOK_LOGIC               = 519,
  BTOR_SMTOK_PREDS               = 520,
  BTOR_SMTOK_SORTS               = 521,
  BTOR_SMTOK_THEORY              = 522,
  BTOR_SMTOK_THEORYATTR          = 523,

  BTOR_SMTOK_INTERNAL   = 1024,
  BTOR_SMTOK_BIND       = 1024,
  BTOR_SMTOK_TRANSLATED = 1025,  // TODO ...
};

typedef enum BtorSMTToken BtorSMTToken;

struct BtorSMTNode
{
  void *head;
  void *tail;
  BoolectorNode *exp;  // TODO overlay with tail/head?
};

BTOR_DECLARE_STACK (BtorSMTNodePtr, BtorSMTNode *);

struct BtorSMTSymbol
{
  char *name;
  BtorSMTToken token;
  BtorSMTSymbol *next;
  BtorSMTNode *last;
  BoolectorNode *exp;
};

struct BtorSMTParser
{
  BtorMemMgr *mem;
  Btor *btor;
  bool parsed;

  uint32_t verbosity;
  uint32_t modelgen;
  uint32_t incremental;
  BtorOptIncrementalSMT1 incremental_smt1;

  struct
  {
    uint32_t nparsed, handled;
  } assumptions;
  struct
  {
    uint32_t nparsed, handled, nchecked;
  } formulas;

  uint32_t nprefix;
  BtorCharStack *prefix;
  FILE *infile;
  const char *infile_name;
  FILE *outfile;
  uint32_t lineno;
  bool saved;
  int32_t saved_char;

  uint_least64_t bytes;

  BtorLogic required_logic;

  char *error;
  BtorCharStack buffer;

  unsigned char types[256];

  BtorSMTSymbol *symbol;
  BtorSMTSymbol **symtab;
  uint32_t szsymtab;
  uint32_t symbols;

  uint32_t constants;

  BtorSMTNode *bind;
  BtorSMTNode *translated;

  BtorPtrHashTable *nodes;
  BtorSMTNodePtrStack stack;
  BtorSMTNodePtrStack work;
  BtorSMTNodePtrStack delete;
  BtorIntStack heads;
};

/*------------------------------------------------------------------------*/

static uint32_t btor_smt_primes[] = {1001311, 2517041, 3543763, 4026227};
#define BTOR_SMT_PRIMES ((sizeof btor_smt_primes) / sizeof *btor_smt_primes)

static void *
car (BtorSMTNode *node)
{
  assert (node);
  return node->head;
}

static void *
cdr (BtorSMTNode *node)
{
  assert (node);
  return node->tail;
}

#define isleaf(l) (1lu & (unsigned long) (l))
#define leaf(l) ((void *) (1lu | (unsigned long) (l)))
#define strip(l) ((BtorSMTSymbol *) ((~1lu) & (unsigned long) (l)))

static BtorSMTNode *
cons (BtorSMTParser *parser, void *h, void *t)
{
  BtorSMTNode *res;

  BTOR_NEW (parser->mem, res);
  BTOR_CLR (res);

  btor_hashptr_table_add (parser->nodes, res);
  assert (parser->nodes->count > 0);

  res->head = h;
  res->tail = t;

  return res;
}

static uint32_t
hash_name (const char *name)
{
  uint32_t i, res;
  const char *p;
  char ch;

  i   = 0;
  res = 0;

  for (p = name; (ch = *p); p++)
  {
    res += btor_smt_primes[i++] * (uint32_t) ch;

    if (i == BTOR_SMT_PRIMES) i = 0;

    res = (res << 4) | (res >> 28);
  }

  return res;
}

static BtorSMTSymbol **
find_symbol_position (BtorSMTParser *parser, const char *name)
{
  uint32_t h = hash_name (name) & (parser->szsymtab - 1);
  BtorSMTSymbol **p, *s;

  for (p = parser->symtab + h; (s = *p) && strcmp (name, s->name); p = &s->next)
    ;

  return p;
}

static void
delete_symbol (BtorSMTParser *parser, BtorSMTSymbol *symbol)
{
  BoolectorNode *exp;

  assert (parser->symbols > 0);
  parser->symbols--;

  btor_mem_freestr (parser->mem, symbol->name);

  if ((exp = symbol->exp)) boolector_release (parser->btor, exp);

  BTOR_DELETE (parser->mem, symbol);
}

static void
remove_and_delete_symbol (BtorSMTParser *parser, BtorSMTSymbol *symbol)
{
  BtorSMTSymbol **p;

  p = find_symbol_position (parser, symbol->name);
  assert (*p == symbol);

  *p = symbol->next;
  delete_symbol (parser, symbol);
}

static void
delete_smt_node (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTSymbol *s;

  if (!node) return;

  assert (parser->nodes->count > 0);
  assert (btor_hashptr_table_get (parser->nodes, node));
  btor_hashptr_table_remove (parser->nodes, node, 0, 0);

  if (node->exp) boolector_release (parser->btor, node->exp);

  if (!parser->modelgen && isleaf (car (node)))
  {
    s = strip (car (node));
    if (s->last == node) remove_and_delete_symbol (parser, s);
  }

  BTOR_DELETE (parser->mem, node);
}

static void
smt_message (BtorSMTParser *parser, uint32_t level, const char *fmt, ...)
{
  va_list ap;

  if (parser->verbosity < level) return;

  fflush (stdout);
  fprintf (stdout, "[btorsmt] ");
  if (parser->incremental) printf ("%d : ", parser->formulas.nchecked);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fprintf (stdout, " after %.2f seconds\n", btor_util_time_stamp ());
  fflush (stdout);
}

static void
recursively_delete_smt_node (BtorSMTParser *parser, BtorSMTNode *root)
{
  BtorSMTNode *node;

  assert (BTOR_EMPTY_STACK (parser->delete));

  BTOR_PUSH_STACK (parser->delete, root);
  while (!BTOR_EMPTY_STACK (parser->delete))
  {
    node = BTOR_POP_STACK (parser->delete);

    if (!node) continue;

    if (isleaf (node)) continue;

    if (car (node) == parser->bind)
    {
      /* NOTE: assignment == cdr (node) shared, so do not delete here */
      assert (cdr (node));
    }
    else
    {
      BTOR_PUSH_STACK (parser->delete, cdr (node));
      BTOR_PUSH_STACK (parser->delete, car (node));
    }

    delete_smt_node (parser, node);
  }
}

static uint32_t
length (BtorSMTNode *node)
{
  BtorSMTNode *p;
  uint32_t res;

  assert (!isleaf (node));

  res = 0;
  for (p = node; p; p = cdr (p)) res++;

  return res;
}

static bool
is_list_of_length (BtorSMTNode *node, uint32_t l)
{
  if (isleaf (node)) return false;

  return length (node) == l;
}

static void
release_smt_symbols (BtorSMTParser *parser)
{
  BtorSMTSymbol *p, *next;
  uint32_t i;

  for (i = 0; i < parser->szsymtab; i++)
  {
    for (p = parser->symtab[i]; p; p = next)
    {
      next = p->next;
      delete_symbol (parser, p);
    }
  }
  BTOR_DELETEN (parser->mem, parser->symtab, parser->szsymtab);
  parser->symtab   = 0;
  parser->szsymtab = 0;
}

static void
release_smt_nodes (BtorSMTParser *parser)
{
  while (parser->nodes && parser->nodes->count)
    recursively_delete_smt_node (parser, parser->nodes->first->key);
}

static void
release_smt_internals (BtorSMTParser *parser)
{
  release_smt_nodes (parser);
  release_smt_symbols (parser);

  if (parser->nodes)
  {
    btor_hashptr_table_delete (parser->nodes);
    parser->nodes = 0;
  }
  BTOR_RELEASE_STACK (parser->stack);
  BTOR_RELEASE_STACK (parser->work);
  BTOR_RELEASE_STACK (parser->delete);
  BTOR_RELEASE_STACK (parser->heads);
  BTOR_RELEASE_STACK (parser->buffer);
}

static void
delete_smt_parser (BtorSMTParser *parser)
{
  BtorMemMgr *mm;

  mm = parser->mem;

  release_smt_internals (parser);

  btor_mem_freestr (mm, parser->error);

  BTOR_DELETE (mm, parser);
  btor_mem_mgr_delete (mm);
}

static char *
perr_smt (BtorSMTParser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start (ap, fmt);
    bytes = btor_mem_parse_error_msg_length (parser->infile_name, fmt, ap);
    va_end (ap);

    va_start (ap, fmt);
    parser->error = btor_mem_parse_error_msg (
        parser->mem, parser->infile_name, parser->lineno, -1, fmt, ap, bytes);
    va_end (ap);
  }

  return parser->error;
}

static void
enlarge_symtab (BtorSMTParser *parser)
{
  BtorSMTSymbol *p, *next, **old_symtab, **new_symtab;
  uint32_t h, i, old_size, new_size;

  old_symtab = parser->symtab;
  old_size   = parser->szsymtab;

  new_size = old_size ? 2 * old_size : 1;
  BTOR_NEWN (parser->mem, new_symtab, new_size);
  BTOR_CLRN (new_symtab, new_size);

  for (i = 0; i < old_size; i++)
  {
    for (p = old_symtab[i]; p; p = next)
    {
      next          = p->next;
      h             = hash_name (p->name) & (new_size - 1);
      p->next       = new_symtab[h];
      new_symtab[h] = p;
    }
  }

  BTOR_DELETEN (parser->mem, old_symtab, old_size);

  parser->symtab   = new_symtab;
  parser->szsymtab = new_size;
}

static BtorSMTSymbol *
insert_symbol (BtorSMTParser *parser, const char *name)
{
  BtorSMTSymbol **p, *res;

  if (parser->szsymtab == parser->symbols) enlarge_symtab (parser);

  p = find_symbol_position (parser, name);
  if (!(res = *p))
  {
    BTOR_NEW (parser->mem, res);
    BTOR_CLR (res);

    res->token = BTOR_SMTOK_IDENTIFIER;
    res->name  = btor_mem_strdup (parser->mem, name);

    parser->symbols++;
    *p = res;
  }

  return res;
}

static BtorSMTParser *
new_smt_parser (Btor *btor)
{
  BtorSMTSymbol *bind, *translated;
  BtorMemMgr *mem;
  BtorSMTParser *res;
  unsigned char type;
  int32_t ch;

  mem = btor_mem_mgr_new ();
  BTOR_NEW (mem, res);
  BTOR_CLR (res);

  res->verbosity        = boolector_get_opt (btor, BTOR_OPT_VERBOSITY);
  res->modelgen         = boolector_get_opt (btor, BTOR_OPT_MODEL_GEN);
  res->incremental      = boolector_get_opt (btor, BTOR_OPT_INCREMENTAL);
  res->incremental_smt1 = boolector_get_opt (btor, BTOR_OPT_INCREMENTAL_SMT1);

  smt_message (res, 2, "initializing SMT parser");
  if (res->incremental)
  {
    smt_message (res, 2, "incremental checking of SMT benchmark");
    if (res->incremental_smt1 == BTOR_INCREMENTAL_SMT1_BASIC)
      smt_message (res, 2, "stop after first satisfiable ':formula'");
    else if (res->incremental_smt1 == BTOR_INCREMENTAL_SMT1_CONTINUE)
      smt_message (res, 2, "check all ':formula' for satisfiability");
  }

  res->mem  = mem;
  res->btor = btor;

  res->nodes = btor_hashptr_table_new (mem, 0, 0);
  BTOR_INIT_STACK (mem, res->stack);
  BTOR_INIT_STACK (mem, res->work);
  BTOR_INIT_STACK (mem, res->delete);
  BTOR_INIT_STACK (mem, res->heads);
  BTOR_INIT_STACK (mem, res->buffer);

  res->required_logic = BTOR_LOGIC_QF_BV;

  type = BTOR_SMTCC_IDENTIFIER_START | BTOR_SMTCC_IDENTIFIER_MIDDLE;

  for (ch = 'a'; ch <= 'z'; ch++) res->types[ch] |= type;
  for (ch = 'A'; ch <= 'Z'; ch++) res->types[ch] |= type;

  res->types['_'] |= type;
  res->types['.'] |= BTOR_SMTCC_IDENTIFIER_MIDDLE;
  res->types['\''] |= BTOR_SMTCC_IDENTIFIER_MIDDLE;

  type = BTOR_SMTCC_IDENTIFIER_MIDDLE;
  type |= BTOR_SMTCC_DIGIT;

  res->types['0'] |= type;

  type |= BTOR_SMTCC_NUMERAL_START;
  for (ch = '1'; ch <= '9'; ch++) res->types[ch] |= type;

  res->types['='] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['<'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['>'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['&'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['@'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['#'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['+'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['-'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['*'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['/'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['%'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['|'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;
  res->types['~'] |= BTOR_SMTCC_ARITHMETIC_OPERATOR;

  res->types[' '] |= BTOR_SMTCC_SPACE;
  res->types['\t'] |= BTOR_SMTCC_SPACE;
  res->types['\n'] |= BTOR_SMTCC_SPACE;
  res->types[0xd] |= BTOR_SMTCC_SPACE;

  res->types[':'] |= BTOR_SMTCC_IDENTIFIER_PREFIX;
  res->types['?'] |= BTOR_SMTCC_IDENTIFIER_PREFIX;
  res->types['$'] |= BTOR_SMTCC_IDENTIFIER_PREFIX;

  insert_symbol (res, "and")->token          = BTOR_SMTOK_AND;
  insert_symbol (res, ":assumption")->token  = BTOR_SMTOK_ASSUMPTION;
  insert_symbol (res, ":axioms")->token      = BTOR_SMTOK_AXIOMS;
  insert_symbol (res, "benchmark")->token    = BTOR_SMTOK_BENCHMARK;
  insert_symbol (res, ":definitions")->token = BTOR_SMTOK_DEFINITIONS;
  insert_symbol (res, "distinct")->token     = BTOR_SMTOK_DISTINCT;
  insert_symbol (res, "exists")->token       = BTOR_SMTOK_EXISTS;
  insert_symbol (res, ":extensions")->token  = BTOR_SMTOK_EXTENSIONS;
  insert_symbol (res, ":extrafuns")->token   = BTOR_SMTOK_EXTRAFUNS;
  insert_symbol (res, ":extrapreds")->token  = BTOR_SMTOK_EXTRAPREDS;
  insert_symbol (res, ":extrasorts")->token  = BTOR_SMTOK_EXTRASORTS;
  insert_symbol (res, "false")->token        = BTOR_SMTOK_FALSE;
  insert_symbol (res, "flet")->token         = BTOR_SMTOK_FLET;
  insert_symbol (res, "forall")->token       = BTOR_SMTOK_FORALL;
  insert_symbol (res, ":formula")->token     = BTOR_SMTOK_FORMULA;
  insert_symbol (res, ":funs")->token        = BTOR_SMTOK_FUNS;
  insert_symbol (res, "iff")->token          = BTOR_SMTOK_IFF;
  insert_symbol (res, "if_then_else")->token = BTOR_SMTOK_IF_THEN_ELSE;
  insert_symbol (res, "implies")->token      = BTOR_SMTOK_IMPLIES;
  insert_symbol (res, "ite")->token          = BTOR_SMTOK_ITE;
  insert_symbol (res, ":language")->token    = BTOR_SMTOK_LANGUAGE;
  insert_symbol (res, "let")->token          = BTOR_SMTOK_LET;
  insert_symbol (res, "logic")->token        = BTOR_SMTOK_LOGIC;
  insert_symbol (res, ":logic")->token       = BTOR_SMTOK_LOGICATTR;
  insert_symbol (res, ":notes")->token       = BTOR_SMTOK_NOTES;
  insert_symbol (res, "not")->token          = BTOR_SMTOK_NOT;
  insert_symbol (res, "or")->token           = BTOR_SMTOK_OR;
  insert_symbol (res, ":preds")->token       = BTOR_SMTOK_PREDS;
  insert_symbol (res, "sat")->token          = BTOR_SMTOK_SAT;
  insert_symbol (res, ":sorts")->token       = BTOR_SMTOK_SORTS;
  insert_symbol (res, ":status")->token      = BTOR_SMTOK_STATUS;
  insert_symbol (res, "theory")->token       = BTOR_SMTOK_THEORY;
  insert_symbol (res, ":theory")->token      = BTOR_SMTOK_THEORYATTR;
  insert_symbol (res, "true")->token         = BTOR_SMTOK_TRUE;
  insert_symbol (res, "unknown")->token      = BTOR_SMTOK_UNKNOWN;
  insert_symbol (res, "unsat")->token        = BTOR_SMTOK_UNSAT;
  insert_symbol (res, "xor")->token          = BTOR_SMTOK_XOR;

  bind        = insert_symbol (res, "<internal bind symbol>");
  bind->token = BTOR_SMTOK_BIND;
  res->bind   = leaf (bind);

  translated        = insert_symbol (res, "<internal translated symbol>");
  translated->token = BTOR_SMTOK_TRANSLATED;
  res->translated   = leaf (translated);

  insert_symbol (res, "=")->token      = BTOR_SMTOK_EQ;
  insert_symbol (res, "concat")->token = BTOR_SMTOK_CONCAT;
  insert_symbol (res, "bit0")->token   = BTOR_SMTOK_BIT0;
  insert_symbol (res, "bit1")->token   = BTOR_SMTOK_BIT1;
  insert_symbol (res, "bvadd")->token  = BTOR_SMTOK_BVADD;
  insert_symbol (res, "bvnot")->token  = BTOR_SMTOK_BVNOT;
  insert_symbol (res, "bvmul")->token  = BTOR_SMTOK_BVMUL;
  insert_symbol (res, "bvule")->token  = BTOR_SMTOK_BVULE;
  insert_symbol (res, "bvand")->token  = BTOR_SMTOK_BVAND;
  insert_symbol (res, "bvlshr")->token = BTOR_SMTOK_BVLSHR;
  insert_symbol (res, "bvslt")->token  = BTOR_SMTOK_BVSLT;
  insert_symbol (res, "bvult")->token  = BTOR_SMTOK_BVULT;
  insert_symbol (res, "bvneg")->token  = BTOR_SMTOK_BVNEG;
  insert_symbol (res, "bvsle")->token  = BTOR_SMTOK_BVSLE;
  insert_symbol (res, "bvshl")->token  = BTOR_SMTOK_BVSHL;
  insert_symbol (res, "bvsub")->token  = BTOR_SMTOK_BVSUB;
  insert_symbol (res, "bvsdiv")->token = BTOR_SMTOK_BVSDIV;
  insert_symbol (res, "bvashr")->token = BTOR_SMTOK_BVASHR;
  insert_symbol (res, "bvor")->token   = BTOR_SMTOK_BVOR;
  insert_symbol (res, "bvudiv")->token = BTOR_SMTOK_BVUDIV;
  insert_symbol (res, "bvurem")->token = BTOR_SMTOK_BVUREM;
  insert_symbol (res, "bvnor")->token  = BTOR_SMTOK_BVNOR;
  insert_symbol (res, "bvnand")->token = BTOR_SMTOK_BVNAND;
  insert_symbol (res, "bvugt")->token  = BTOR_SMTOK_BVUGT;
  insert_symbol (res, "bvuge")->token  = BTOR_SMTOK_BVUGE;
  insert_symbol (res, "bvsgt")->token  = BTOR_SMTOK_BVSGT;
  insert_symbol (res, "bvsge")->token  = BTOR_SMTOK_BVSGE;
  insert_symbol (res, "bvcomp")->token = BTOR_SMTOK_BVCOMP;
  insert_symbol (res, "bvxor")->token  = BTOR_SMTOK_BVXOR;
  insert_symbol (res, "bvsrem")->token = BTOR_SMTOK_BVSREM;
  insert_symbol (res, "bvsmod")->token = BTOR_SMTOK_BVSMOD;
  insert_symbol (res, "bvxnor")->token = BTOR_SMTOK_BVXNOR;
  insert_symbol (res, "select")->token = BTOR_SMTOK_SELECT;
  insert_symbol (res, "store")->token  = BTOR_SMTOK_STORE;

  return res;
}

static int32_t
nextch_smt (BtorSMTParser *parser)
{
  int32_t res;

  if (parser->saved)
  {
    res           = parser->saved_char;
    parser->saved = false;
  }
  else if (parser->prefix
           && parser->nprefix < BTOR_COUNT_STACK (*parser->prefix))
  {
    parser->bytes++;
    res = parser->prefix->start[parser->nprefix++];
  }
  else
  {
    parser->bytes++;
    res = getc (parser->infile);
  }

  if (res == '\n') parser->lineno++;

  return res;
}

static void
savech_smt (BtorSMTParser *parser, int32_t ch)
{
  assert (!parser->saved);

  parser->saved_char = ch;
  parser->saved      = true;

  if (ch == '\n')
  {
    assert (parser->lineno > 1);
    parser->lineno--;
  }
}

static unsigned char
int2type (BtorSMTParser *parser, int32_t ch)
{
  if (0 > ch || ch >= 256) return 0;
  return parser->types[ch];
}

static bool
has_prefix (const char *str, const char *prefix)
{
  const char *p, *q;

  for (p = str, q = prefix; *q && *p == *q; p++, q++)
    ;
  return *q == 0;
}

static BtorSMTToken
nextok (BtorSMTParser *parser)
{
  unsigned char type;
  BtorSMTToken res;
  int32_t ch;
  uint32_t count;

  parser->symbol = 0;
  BTOR_RESET_STACK (parser->buffer);

SKIP_WHITE_SPACE:

  ch = nextch_smt (parser);
  if (ch == EOF) return EOF;

  type = int2type (parser, ch);
  if (type & BTOR_SMTCC_SPACE) goto SKIP_WHITE_SPACE;

  if (type & BTOR_SMTCC_IDENTIFIER_START)
  {
    BTOR_PUSH_STACK (parser->buffer, ch);

    while (int2type (parser, (ch = nextch_smt (parser)))
           & BTOR_SMTCC_IDENTIFIER_MIDDLE)
      BTOR_PUSH_STACK (parser->buffer, ch);

    count = 0;

    if (ch == '[')
    {
      BTOR_PUSH_STACK (parser->buffer, ch);

      ch = nextch_smt (parser);

      for (;;)
      {
        if (int2type (parser, ch) & BTOR_SMTCC_NUMERAL_START)
        {
          BTOR_PUSH_STACK (parser->buffer, ch);

          while (int2type (parser, (ch = nextch_smt (parser)))
                 & BTOR_SMTCC_DIGIT)
            BTOR_PUSH_STACK (parser->buffer, ch);

        COUNT_AND_CONTINUE_WITH_NEXT_INDEX:

          count++;

          if (ch == ']') break;

          if (ch != ':') goto UNEXPECTED_CHARACTER;

          BTOR_PUSH_STACK (parser->buffer, ':');
          ch = nextch_smt (parser);
        }
        else if (ch == '0')
        {
          BTOR_PUSH_STACK (parser->buffer, ch);
          ch = nextch_smt (parser);
          goto COUNT_AND_CONTINUE_WITH_NEXT_INDEX;
        }
        else
          goto UNEXPECTED_CHARACTER;
      }

      if (!count) return !perr_smt (parser, "empty index list");

      assert (ch == ']');
      BTOR_PUSH_STACK (parser->buffer, ch);
    }
    else
    {
      if (!ch) goto UNEXPECTED_CHARACTER;

      savech_smt (parser, ch);
    }

    BTOR_PUSH_STACK (parser->buffer, 0);

    parser->symbol = insert_symbol (parser, parser->buffer.start);

    if (count == 2 && has_prefix (parser->symbol->name, "extract["))
      parser->symbol->token = BTOR_SMTOK_EXTRACT;

    if (count == 1)
    {
      if (has_prefix (parser->symbol->name, "repeat["))
        parser->symbol->token = BTOR_SMTOK_REPEAT;

      if (has_prefix (parser->symbol->name, "zero_extend["))
        parser->symbol->token = BTOR_SMTOK_ZERO_EXTEND;

      if (has_prefix (parser->symbol->name, "sign_extend["))
        parser->symbol->token = BTOR_SMTOK_SIGN_EXTEND;

      if (has_prefix (parser->symbol->name, "rotate_left["))
        parser->symbol->token = BTOR_SMTOK_ROTATE_LEFT;

      if (has_prefix (parser->symbol->name, "rotate_right["))
        parser->symbol->token = BTOR_SMTOK_ROTATE_RIGHT;
    }

  CHECK_FOR_UNSUPPORTED_KEYWORD:

    if (parser->symbol->token >= BTOR_SMTOK_UNSUPPORTED_KEYWORD)
      return !perr_smt (
          parser, "unsupported keyword '%s'", parser->buffer.start);

    return parser->symbol->token;
  }

  if (ch == '(') return BTOR_SMTOK_LP;

  if (ch == ')') return BTOR_SMTOK_RP;

  if (type & BTOR_SMTCC_IDENTIFIER_PREFIX)
  {
    res = ch;

    assert (ch == '?' || ch == '$' || ch == ':');

    assert ((ch == '?') == (res == BTOR_SMTOK_VAR));
    assert ((ch == '$') == (res == BTOR_SMTOK_FVAR));
    assert ((ch == ':') == (res == BTOR_SMTOK_ATTR));

    BTOR_PUSH_STACK (parser->buffer, ch);

    ch = nextch_smt (parser);
    if (!(int2type (parser, ch) & BTOR_SMTCC_IDENTIFIER_START))
      return !perr_smt (parser, "expected identifier after '%c'", res);

    BTOR_PUSH_STACK (parser->buffer, ch);

    while (int2type (parser, (ch = nextch_smt (parser)))
           & BTOR_SMTCC_IDENTIFIER_MIDDLE)
      BTOR_PUSH_STACK (parser->buffer, ch);

    if (!ch) goto UNEXPECTED_CHARACTER;

    savech_smt (parser, ch);
    BTOR_PUSH_STACK (parser->buffer, 0);

    parser->symbol = insert_symbol (parser, parser->buffer.start);

    if (res == BTOR_SMTOK_VAR || res == BTOR_SMTOK_FVAR)
      parser->symbol->token = res;

    goto CHECK_FOR_UNSUPPORTED_KEYWORD;
  }

  if (type & BTOR_SMTCC_NUMERAL_START)
  {
    BTOR_PUSH_STACK (parser->buffer, ch);

    while (int2type (parser, (ch = nextch_smt (parser))) & BTOR_SMTCC_DIGIT)
      BTOR_PUSH_STACK (parser->buffer, ch);

  CHECK_FOR_FRACTIONAL_PART:

    if (ch == '.')
    {
      res = BTOR_SMTOK_RATIONAL;

      BTOR_PUSH_STACK (parser->buffer, ch);
      ch = nextch_smt (parser);

      if (int2type (parser, ch) & BTOR_SMTCC_NUMERAL_START)
      {
        BTOR_PUSH_STACK (parser->buffer, ch);

        while (int2type (parser, (ch = nextch_smt (parser)))
               & BTOR_SMTCC_NUMERAL_START)
          BTOR_PUSH_STACK (parser->buffer, ch);
      }
      else if (ch == '0')
      {
        BTOR_PUSH_STACK (parser->buffer, ch);

        ch = nextch_smt (parser);
        if (int2type (parser, ch) & BTOR_SMTCC_DIGIT)
          goto UNEXPECTED_DIGIT_AFTER_ZERO;
      }
      else
        goto UNEXPECTED_CHARACTER;
    }
    else
      res = BTOR_SMTOK_NUMERAL;

    if (!ch) goto UNEXPECTED_CHARACTER;

    savech_smt (parser, ch);
    BTOR_PUSH_STACK (parser->buffer, 0);

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = res;

    return res;
  }

  if (ch == '0')
  {
    BTOR_PUSH_STACK (parser->buffer, ch);

    ch = nextch_smt (parser);
    if (int2type (parser, ch) & BTOR_SMTCC_DIGIT)
    {
    UNEXPECTED_DIGIT_AFTER_ZERO:
      return !perr_smt (parser, "unexpected digit after '0'");
    }

    goto CHECK_FOR_FRACTIONAL_PART;
  }

  if (type & BTOR_SMTCC_ARITHMETIC_OPERATOR)
  {
    BTOR_PUSH_STACK (parser->buffer, ch);

    while (int2type (parser, (ch = nextch_smt (parser)))
           & BTOR_SMTCC_ARITHMETIC_OPERATOR)
      BTOR_PUSH_STACK (parser->buffer, ch);

    if (!ch) goto UNEXPECTED_CHARACTER;

    BTOR_PUSH_STACK (parser->buffer, 0);

    parser->symbol = insert_symbol (parser, parser->buffer.start);
    if (parser->symbol->token == BTOR_SMTOK_IDENTIFIER)
      parser->symbol->token = BTOR_SMTOK_ARITH;

    return parser->symbol->token;
  }

  if (ch == ';')
  {
    while ((ch = nextch_smt (parser)) != '\n')
      if (ch == EOF) return BTOR_SMTOK_EOF;

    goto SKIP_WHITE_SPACE;
  }

  if (ch == '{')
  {
    BTOR_PUSH_STACK (parser->buffer, ch);

    while ((ch = nextch_smt (parser)) != '}')
    {
      if (ch == '{') return !perr_smt (parser, "unescaped '{' after '{'");

      if (ch == '\\')
      {
        BTOR_PUSH_STACK (parser->buffer, ch);
        ch = nextch_smt (parser);
      }

      if (ch == EOF) return !perr_smt (parser, "unexpected EOF after '{'");

      BTOR_PUSH_STACK (parser->buffer, ch);
    }

    assert (ch == '}');
    BTOR_PUSH_STACK (parser->buffer, ch);
    BTOR_PUSH_STACK (parser->buffer, 0);

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = BTOR_SMTOK_USERVAL;

    return BTOR_SMTOK_USERVAL;
  }

  if (ch == '"')
  {
    while ((ch = nextch_smt (parser)) != '"')
    {
      if (ch == '\\')
      {
        BTOR_PUSH_STACK (parser->buffer, ch);
        ch = nextch_smt (parser);
      }

      if (ch == EOF) return !perr_smt (parser, "unexpected EOF after '\"'");

      BTOR_PUSH_STACK (parser->buffer, ch);
    }

    BTOR_PUSH_STACK (parser->buffer, 0);

    parser->symbol        = insert_symbol (parser, parser->buffer.start);
    parser->symbol->token = BTOR_SMTOK_STRING;

    return BTOR_SMTOK_STRING;
  }

UNEXPECTED_CHARACTER:
  if (isprint (ch)) return !perr_smt (parser, "unexpected character '%c'", ch);

  return !perr_smt (parser, "unexpected character with ASCII code %d", ch);
}

static void
btorsmtppaux (FILE *file, BtorSMTNode *node, uint32_t indent)
{
  uint32_t i;

  if (isleaf (node))
    fprintf (file, "%s", ((BtorSMTSymbol *) strip (node))->name);
  else
  {
    fputc ('(', file);

    for (;;)
    {
      btorsmtppaux (file, car (node), indent + 1);
      if (!(node = cdr (node))) break;

      fputc ('\n', file);
      for (i = 0; i <= indent; i++) fputc (' ', file);
    }

    fputc (')', file);
  }
}

void
btorsmtpp (BtorSMTNode *node)
{
  btorsmtppaux (stdout, node, 0);
  fputc ('\n', stdout);
  fflush (stdout);
}

static const char *
next_numeral (const char *str)
{
  const char *p = str;
  int32_t ch;

  assert (str);

  if (isdigit ((int32_t) *p++))
  {
    while (isdigit (ch = *p++))
      ;

    if (ch == ':')
    {
      assert (isdigit ((int32_t) *p));
      return p;
    }

    assert (ch == ']');
  }
  else
  {
    while ((ch = *p++))
      if (ch == '[')
      {
        assert (isdigit ((int32_t) *p));
        return p;
      }
  }

  return 0;
}

static int32_t
extrafun (BtorSMTParser *parser, BtorSMTNode *fdecl)
{
  BtorSMTSymbol *symbol, *sortsymbol;
  BtorSMTNode *node, *sort;
  int32_t addrlen, datalen;
  const char *p;
  BoolectorSort s, is, es;

  if (!fdecl || !cdr (fdecl) || isleaf (fdecl) || !isleaf (node = car (fdecl))
      || (symbol = strip (node))->token != BTOR_SMTOK_IDENTIFIER)
    return !perr_smt (parser, "invalid function declaration");

  if (cdr (cdr (fdecl)))
    return !perr_smt (parser,
                      "no support for function declaration "
                      "with more than one argument");

  sort = car (cdr (fdecl));
  if (!sort || !isleaf (sort)
      || (sortsymbol = strip (sort))->token != BTOR_SMTOK_IDENTIFIER)
  {
  INVALID_SORT:
    return !perr_smt (parser,
                      "invalid or unsupported sort "
                      "in function declaration");
  }

  if (symbol->exp)
    return !perr_smt (parser, "multiple definitions for '%s'", symbol->name);

  p = sortsymbol->name;

  if (!strcmp (p, "Bool"))
  {
    s           = boolector_bool_sort (parser->btor);
    symbol->exp = boolector_var (parser->btor, s, symbol->name);
    boolector_release_sort (parser->btor, s);
  }
  else if (has_prefix (p, "BitVec"))
  {
    if (!(p = next_numeral (p)) || next_numeral (p)) goto INVALID_SORT;

    datalen = atoi (p); /* TODO Overflow? */
    if (!datalen) goto INVALID_SORT;

    s           = boolector_bitvec_sort (parser->btor, datalen);
    symbol->exp = boolector_var (parser->btor, s, symbol->name);
    boolector_release_sort (parser->btor, s);
  }
  else if (has_prefix (p, "Array"))
  {
    if (!(p = next_numeral (p))) goto INVALID_SORT;

    addrlen = atoi (p); /* TODO Overflow? */
    if (!addrlen) goto INVALID_SORT;

    if (!(p = next_numeral (p)) || next_numeral (p)) goto INVALID_SORT;

    datalen = atoi (p); /* TODO Overflow? */
    if (!datalen) goto INVALID_SORT;

    es          = boolector_bitvec_sort (parser->btor, datalen);
    is          = boolector_bitvec_sort (parser->btor, addrlen);
    s           = boolector_array_sort (parser->btor, is, es);
    symbol->exp = boolector_array (parser->btor, s, symbol->name);
    boolector_release_sort (parser->btor, is);
    boolector_release_sort (parser->btor, es);
    boolector_release_sort (parser->btor, s);

    if (parser->required_logic == BTOR_LOGIC_QF_BV)
    {
      smt_message (parser, 2, "requires QF_AUFBV");
      parser->required_logic = BTOR_LOGIC_QF_AUFBV;
    }

    /* TODO what about 'symbol->name' back annotation? */
  }
  else
    goto INVALID_SORT;

  return 1;
}

static bool
extrafuns (BtorSMTParser *parser, BtorSMTNode *list)
{
  BtorSMTNode *p;

  if (!list || isleaf (list))
    return !perr_smt (parser,
                      "expected non empty list as argument to ':extrafuns'");

  for (p = list; p; p = cdr (p))
    if (!extrafun (parser, car (p))) return 0;

  return parser->error == 0;
}

static bool
extrapred (BtorSMTParser *parser, BtorSMTNode *pdecl)
{
  BtorSMTSymbol *symbol;
  BtorSMTNode *node;
  BoolectorSort s;

  if (!pdecl || isleaf (pdecl) || !isleaf (node = car (pdecl))
      || (symbol = strip (node))->token != BTOR_SMTOK_IDENTIFIER)
    return !perr_smt (parser, "invalid predicate declaration");

  if (cdr (pdecl))
    return !perr_smt (parser,
                      "no support for predicate declarations with arguments");

  if (symbol->exp)
    return !perr_smt (parser, "multiple definitions for '%s'", symbol->name);

  s           = boolector_bool_sort (parser->btor);
  symbol->exp = boolector_var (parser->btor, s, symbol->name);
  boolector_release_sort (parser->btor, s);

  return true;
}

static bool
extrapreds (BtorSMTParser *parser, BtorSMTNode *list)
{
  BtorSMTNode *p;

  if (!list || isleaf (list))
    return !perr_smt (parser,
                      "expected non empty list as argument to ':extrapreds'");

  for (p = list; p; p = cdr (p))
    if (!extrapred (parser, car (p))) return false;

  return !parser->error;
}

static BtorSMTToken
node2token (BtorSMTNode *node)
{
  return (node && isleaf (node)) ? strip (node)->token : BTOR_SMTOK_ERR;
}

static bool
is_let_or_flet (BtorSMTNode *node)
{
  BtorSMTToken token = node2token (node);
  return token == BTOR_SMTOK_LET || token == BTOR_SMTOK_FLET;
}

static BoolectorNode *
node2exp (BtorSMTParser *parser, BtorSMTNode *node)
{
  const char *p, *start, *end;
  char *tmp, *ext, ch;
  BtorBitVector *tmpbv, *extbv;
  BtorSMTSymbol *symbol;
  int32_t len, tlen;
  BtorSMTToken token;

  if (isleaf (node))
  {
    symbol = strip (node);
    if (symbol->exp) return symbol->exp;

    token = symbol->token;
    if (token == BTOR_SMTOK_TRUE || token == BTOR_SMTOK_BIT1)
      return symbol->exp = boolector_const (parser->btor, "1");

    if (token == BTOR_SMTOK_FALSE || token == BTOR_SMTOK_BIT0)
      return symbol->exp = boolector_const (parser->btor, "0");

    p = symbol->name;
    if (*p++ == 'b' && *p++ == 'v')
    {
      if (isdigit ((int32_t) *p))
      {
        start = p++;
        for (end = p; isdigit ((int32_t) *end); end++)
          ;

        if (*end == '[')
        {
          for (p = end + 1; isdigit ((int32_t) *p); p++)
            ;

          if (*p == ']')
          {
            len = atoi (end + 1);
            if (len)
            {
              tmp =
                  btor_util_dec_to_bin_str_n (parser->mem, start, end - start);

              tlen = (int32_t) strlen (tmp);

              if (tlen <= len)
              {
                if (tlen < len)
                {
                  tmpbv = 0;
                  if (!strcmp (tmp, ""))
                    extbv = btor_bv_new (parser->mem, len - tlen);
                  else
                  {
                    tmpbv = btor_bv_char_to_bv (parser->mem, tmp);
                    extbv = btor_bv_uext (parser->mem, tmpbv, len - tlen);
                  }
                  ext = btor_bv_to_char (parser->mem, extbv);
                  btor_mem_freestr (parser->mem, tmp);
                  btor_bv_free (parser->mem, extbv);
                  if (tmpbv) btor_bv_free (parser->mem, tmpbv);
                  tmp = ext;
                }

                symbol->exp = boolector_const (parser->btor, tmp);
                parser->constants++;
              }

              btor_mem_freestr (parser->mem, tmp);
            }
          }
        }
      }
      else if (*p == 'b')
      {
        if (*++p == 'i' && *++p == 'n')
        {
          for (start = ++p; (ch = *p) == '0' || ch == '1'; p++)
            ;

          if (start < p && !*p)
          {
            symbol->exp = boolector_const (parser->btor, start);
            parser->constants++;
          }
        }
      }
      else if (*p++ == 'h' && *p++ == 'e' && *p++ == 'x')
      {
        for (start = p; isxdigit ((int32_t) *p); p++)
          ;

        if (start < p && !*p)
        {
          len  = 4 * (p - start);
          tmp  = btor_util_hex_to_bin_str (parser->mem, start);
          tlen = (int32_t) strlen (tmp);
          assert (tlen <= len);
          if (tlen < len)
          {
            tmpbv = 0;
            if (!strcmp (tmp, ""))
              extbv = btor_bv_new (parser->mem, len - tlen);
            else
            {
              tmpbv = btor_bv_char_to_bv (parser->mem, tmp);
              extbv = btor_bv_uext (parser->mem, tmpbv, len - tlen);
            }
            ext = btor_bv_to_char (parser->mem, extbv);
            btor_mem_freestr (parser->mem, tmp);
            btor_bv_free (parser->mem, extbv);
            if (tmpbv) btor_bv_free (parser->mem, tmpbv);
            tmp = ext;
          }
          symbol->exp = boolector_const (parser->btor, tmp);
          btor_mem_freestr (parser->mem, tmp);
          parser->constants++;
        }
      }
      else
      {
        /* DO NOT ADD ANYTHING HERE BECAUSE 'p' CHANGED */
      }
    }

    if (symbol->exp) return symbol->exp;

    (void) perr_smt (parser, "'%s' undefined", strip (node)->name);
    return 0;
  }
  else
  {
    assert (node->exp);
    return node->exp;
  }

  return 0;
}

static BoolectorNode *
node2nonarrayexp (BtorSMTParser *parser, BtorSMTNode *node)
{
  BoolectorNode *res;

  res = node2exp (parser, node);
  if (res && boolector_is_array (parser->btor, res))
  {
    (void) perr_smt (parser, "unexpected array argument");
    res = 0;
  }

  return res;
}

static void
translate_node (BtorSMTParser *parser, BtorSMTNode *node, BoolectorNode *exp)
{
  (void) parser;
  assert (!isleaf (node));
  assert (!node->exp);
  node->exp = exp;
}

static void
translate_symbol (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c;
  BoolectorNode *a;

  assert (!node->exp);
  if (!is_list_of_length (node, 1))
  {
    (void) perr_smt (parser, "symbolic head with argument");
    return;
  }

  c = car (node);
  if ((a = node2nonarrayexp (parser, c)))
    translate_node (parser, node, boolector_copy (parser->btor, a));
}

static void
translate_unary (BtorSMTParser *parser,
                 BtorSMTNode *node,
                 const char *name,
                 BoolectorNode *(*f) (Btor *, BoolectorNode *) )
{
  BtorSMTNode *c;
  BoolectorNode *a;

  assert (!node->exp);

  if (!is_list_of_length (node, 2))
  {
    (void) perr_smt (parser, "expected exactly one argument to '%s'", name);
    return;
  }

  c = car (cdr (node));
  if ((a = node2nonarrayexp (parser, c)))
    translate_node (parser, node, f (parser->btor, a));
}

static void
translate_binary (BtorSMTParser *parser,
                  BtorSMTNode *node,
                  const char *name,
                  BoolectorNode *(*f) (Btor *,
                                       BoolectorNode *,
                                       BoolectorNode *) )
{
  BtorSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) perr_smt (parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if ((a0 = node2nonarrayexp (parser, c0)))
    if ((a1 = node2nonarrayexp (parser, c1)))
    {
      if (boolector_get_width (parser->btor, a0)
          != boolector_get_width (parser->btor, a1))
        (void) perr_smt (parser, "expression width mismatch");
      else
        translate_node (parser, node, f (parser->btor, a0, a1));
    }
}

static void
translate_eq (BtorSMTParser *parser, BtorSMTNode *node)
{
  bool isarray0, isarray1;
  uint32_t len0, len1;
  BtorSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) perr_smt (parser, "expected exactly two arguments to '='");
    return;
  }

  c0 = car (cdr (node));
  a0 = node2exp (parser, c0);
  if (!a0) return;

  c1 = car (cdr (cdr (node)));
  a1 = node2exp (parser, c1);
  if (!a1) return;

  len0 = boolector_get_width (parser->btor, a0);
  len1 = boolector_get_width (parser->btor, a1);

  if (len0 != len1)
  {
    (void) perr_smt (parser, "expression width mismatch in '='");
    return;
  }

  isarray0 = boolector_is_array (parser->btor, a0);
  isarray1 = boolector_is_array (parser->btor, a1);

  if (isarray0 != isarray1)
  {
    (void) perr_smt (parser, "'=' between array and non array expression");
    return;
  }

  if (isarray0 && isarray1)
  {
    len0 = boolector_get_index_width (parser->btor, a0);
    len1 = boolector_get_index_width (parser->btor, a1);

    if (len0 != len1)
    {
      (void) perr_smt (parser, "index width mismatch in '='");
      return;
    }
  }

  assert (!parser->error);
  translate_node (parser, node, boolector_eq (parser->btor, a0, a1));
}

static void
translate_associative_binary (BtorSMTParser *parser,
                              BtorSMTNode *node,
                              const char *name,
                              BoolectorNode *(*f) (Btor *,
                                                   BoolectorNode *,
                                                   BoolectorNode *) )
{
  BoolectorNode *res, *tmp, *exp;
  BtorSMTNode *child, *p;
  uint32_t width;

  assert (!node->exp);

  child = car (cdr (node));

  if (!(exp = node2nonarrayexp (parser, child)))
  {
  CHECK_FOR_PARSE_ERROR_AND_RETURN:
    assert (parser->error);
    return;
  }

  width = boolector_get_width (parser->btor, exp);
  res   = boolector_copy (parser->btor, exp);

  for (p = cdr (cdr (node)); p; p = cdr (p))
  {
    child = car (p);
    if (!(exp = node2nonarrayexp (parser, child)))
    {
    RELEASE_RES_CHECK_FOR_PARSE_ERROR_AND_RETURN:
      boolector_release (parser->btor, res);
      assert (parser->error);
      goto CHECK_FOR_PARSE_ERROR_AND_RETURN;
    }

    if (boolector_get_width (parser->btor, exp) != width)
    {
      perr_smt (parser, "mismatched width of arguments of '%s'", name);
      goto RELEASE_RES_CHECK_FOR_PARSE_ERROR_AND_RETURN;
    }

    tmp = f (parser->btor, res, exp); /* left associative ? */
    boolector_release (parser->btor, res);
    res = tmp;
  }

  translate_node (parser, node, res);
}

static void
translate_cond (BtorSMTParser *parser, BtorSMTNode *node, const char *name)
{
  bool isarray1, isarray2;
  uint32_t width1, width2;
  BtorSMTNode *c0, *c1, *c2;
  BoolectorNode *a0, *a1, *a2;

  assert (!node->exp);

  if (!is_list_of_length (node, 4))
  {
    (void) perr_smt (parser, "expected exactly three arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));
  c2 = car (cdr (cdr (cdr (node))));

  a0 = node2nonarrayexp (parser, c0);
  if (!a0) return;

  if (boolector_get_width (parser->btor, a0) != 1)
  {
    (void) perr_smt (parser, "non boolean conditional");
    return;
  }

  a1 = node2exp (parser, c1);
  if (!a1) return;

  a2 = node2exp (parser, c2);
  if (!a2) return;

  width1 = boolector_get_width (parser->btor, a1);
  width2 = boolector_get_width (parser->btor, a2);

  if (width1 != width2)
  {
    (void) perr_smt (parser, "expression width mismatch in conditional");
    return;
  }

  isarray1 = boolector_is_array (parser->btor, a1);
  isarray2 = boolector_is_array (parser->btor, a2);

  if (isarray1 != isarray2)
  {
    (void) perr_smt (parser,
                     "conditional between array and non array expression");
    return;
  }

  if (isarray1 && isarray2)
  {
    width1 = boolector_get_index_width (parser->btor, a1);
    width2 = boolector_get_index_width (parser->btor, a2);

    if (width1 != width2)
    {
      (void) perr_smt (parser, "index width mismatch in conditional");
      return;
    }
  }

  translate_node (parser, node, boolector_cond (parser->btor, a0, a1, a2));
}

static void
translate_extract (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTSymbol *symbol;
  uint32_t upper, lower, len;
  const char *p;
  BoolectorNode *exp;

  assert (!node->exp);

  symbol = strip (car (node));
  assert (symbol->token == BTOR_SMTOK_EXTRACT);
  p = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) perr_smt (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  len = boolector_get_width (parser->btor, exp);

  p = next_numeral (p);
  assert (p);
  upper = (uint32_t) strtol (p, 0, 10); /* TODO Overflow? */
  p     = next_numeral (p);
  lower = (uint32_t) strtol (p, 0, 10); /* TODO Overflow? */
  assert (!next_numeral (p));

  if (len <= upper || upper < lower)
  {
    (void) perr_smt (parser, "invalid '%s' on expression of width %d", p, len);
    return;
  }

  translate_node (
      parser, node, boolector_slice (parser->btor, exp, upper, lower));
}

static void
translate_repeat (BtorSMTParser *parser, BtorSMTNode *node)
{
  BoolectorNode *tmp, *exp, *res;
  BtorSMTSymbol *symbol;
  const char *p;
  int32_t i, count;

  assert (!node->exp);

  symbol = strip (car (node));
  assert (symbol->token == BTOR_SMTOK_REPEAT);

  p = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) perr_smt (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  p = next_numeral (p);
  assert (p);
  assert (!next_numeral (p));
  count = atoi (p); /* TODO Overflow? */

  if (!count)
  {
    (void) perr_smt (parser, "can not handle 'repeat[0]'");
    return;
  }

  res = boolector_copy (parser->btor, exp);

  for (i = 1; i < count; i++)
  {
    tmp = boolector_concat (parser->btor, exp, res);
    boolector_release (parser->btor, res);
    res = tmp;
  }

  translate_node (parser, node, res);
}

static void
translate_extend (BtorSMTParser *parser,
                  BtorSMTNode *node,
                  BoolectorNode *(*f) (Btor *, BoolectorNode *, uint32_t))
{
  BtorSMTSymbol *symbol;
  const char *p;
  BoolectorNode *exp;
  int32_t pad;

  assert (!node->exp);

  symbol = strip (car (node));
  p      = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) perr_smt (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  p = next_numeral (p);
  assert (p);
  assert (!next_numeral (p));
  pad = atoi (p); /* TODO Overflow? */

  translate_node (parser, node, f (parser->btor, exp, pad));
}

static void
translate_rotate (BtorSMTParser *parser, BtorSMTNode *node)
{
  BoolectorNode *exp, *l, *r;
  BtorSMTSymbol *symbol;
  BtorSMTToken token;
  uint32_t shift, width;
  const char *p;

  assert (!node->exp);

  symbol = strip (car (node));
  token  = symbol->token;
  assert (token == BTOR_SMTOK_ROTATE_LEFT || token == BTOR_SMTOK_ROTATE_RIGHT);

  p = symbol->name;

  if (!is_list_of_length (node, 2))
  {
    (void) perr_smt (parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp (parser, car (cdr (node)))))
  {
    assert (parser->error);
    return;
  }

  p = next_numeral (p);
  assert (p);
  assert (!next_numeral (p));
  shift = (uint32_t) strtol (p, 0, 10); /* TODO Overflow? */

  width = boolector_get_width (parser->btor, exp);
  assert (width > 0);
  shift %= width;

  if (shift)
  {
    if (token == BTOR_SMTOK_ROTATE_LEFT) shift = width - shift;

    assert (1 <= shift && shift < width);

    l = boolector_slice (parser->btor, exp, shift - 1, 0);
    r = boolector_slice (parser->btor, exp, width - 1, shift);

    translate_node (parser, node, boolector_concat (parser->btor, l, r));
    assert (boolector_get_width (parser->btor, node->exp) == width);

    boolector_release (parser->btor, l);
    boolector_release (parser->btor, r);
  }
  else
    translate_node (parser, node, boolector_copy (parser->btor, exp));
}

static void
translate_concat (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) perr_smt (parser, "expected exactly two arguments to 'concat'");
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if ((a0 = node2nonarrayexp (parser, c0)))
    if ((a1 = node2nonarrayexp (parser, c1)))
      translate_node (parser, node, boolector_concat (parser->btor, a0, a1));
}

static void
translate_shift (BtorSMTParser *parser,
                 BtorSMTNode *node,
                 const char *name,
                 BoolectorNode *(*f) (Btor *,
                                      BoolectorNode *,
                                      BoolectorNode *) )
{
  BoolectorNode *a0, *a1, *c, *e, *t, *e0, *u, *l, *tmp;
  uint32_t width, l0, l1, p0, p1;
  BtorSMTNode *c0, *c1;
  BoolectorSort s;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) perr_smt (parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if (!(a0 = node2nonarrayexp (parser, c0)))
  {
    assert (parser->error);
    return;
  }

  if (!(a1 = node2nonarrayexp (parser, c1)))
  {
    assert (parser->error);
    return;
  }

  width = boolector_get_width (parser->btor, a0);

  if (width != boolector_get_width (parser->btor, a1))
  {
    (void) perr_smt (parser, "expression width mismatch");
    return;
  }

  l1 = 0;
  for (l0 = 1; l0 < width; l0 *= 2) l1++;

  assert (l0 == (1u << l1));

  if (width == 1)
  {
    assert (l0 == 1);
    assert (l1 == 0);

    if (f == boolector_sra)
      translate_node (parser, node, boolector_copy (parser->btor, a0));
    else
    {
      tmp = boolector_not (parser->btor, a1);
      translate_node (parser, node, boolector_and (parser->btor, a0, tmp));
      boolector_release (parser->btor, tmp);
    }
  }
  else
  {
    assert (width >= 1);
    assert (width <= l0);

    p0 = l0 - width;
    p1 = width - l1;

    assert (p1 > 0);

    u = boolector_slice (parser->btor, a1, width - 1, width - p1);
    l = boolector_slice (parser->btor, a1, l1 - 1, 0);

    assert (boolector_get_width (parser->btor, u) == p1);
    assert (boolector_get_width (parser->btor, l) == l1);

    if (p1 > 1)
      c = boolector_redor (parser->btor, u);
    else
      c = boolector_copy (parser->btor, u);

    boolector_release (parser->btor, u);

    if (f == boolector_sra)
    {
      tmp = boolector_slice (parser->btor, a0, width - 1, width - 1);
      t   = boolector_sext (parser->btor, tmp, width - 1);
      boolector_release (parser->btor, tmp);
    }
    else
    {
      s = boolector_bitvec_sort (parser->btor, width);
      t = boolector_zero (parser->btor, s);
      boolector_release_sort (parser->btor, s);
    }

    if (!p0)
      e0 = boolector_copy (parser->btor, a0);
    else if (f == boolector_sra)
      e0 = boolector_sext (parser->btor, a0, p0);
    else
      e0 = boolector_uext (parser->btor, a0, p0);

    assert (boolector_get_width (parser->btor, e0) == l0);

    e = f (parser->btor, e0, l);
    boolector_release (parser->btor, e0);
    boolector_release (parser->btor, l);

    if (p0 > 0)
    {
      tmp = boolector_slice (parser->btor, e, width - 1, 0);
      boolector_release (parser->btor, e);
      e = tmp;
    }

    translate_node (parser, node, boolector_cond (parser->btor, c, t, e));

    boolector_release (parser->btor, c);
    boolector_release (parser->btor, t);
    boolector_release (parser->btor, e);
  }
}

static void
translate_select (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert (!node->exp);

  if (!is_list_of_length (node, 3))
  {
    (void) perr_smt (parser, "expected exactly two arguments to 'select'");
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));

  if (!(a0 = node2exp (parser, c0)))
  {
    assert (parser->error);
    return;
  }

  if (!boolector_is_array (parser->btor, a0))
  {
    (void) perr_smt (parser, "invalid first argument to 'select'");
    return;
  }

  if (!(a1 = node2nonarrayexp (parser, c1)))
  {
    assert (parser->error);
    return;
  }

  if (boolector_get_index_width (parser->btor, a0)
      != boolector_get_width (parser->btor, a1))
  {
    (void) perr_smt (parser, "mismatched bit width of 'select' index");
    return;
  }

  translate_node (parser, node, boolector_read (parser->btor, a0, a1));
}

static void
translate_store (BtorSMTParser *parser, BtorSMTNode *node)
{
  BtorSMTNode *c0, *c1, *c2;
  BoolectorNode *a0, *a1, *a2;

  assert (!node->exp);

  if (!is_list_of_length (node, 4))
  {
    (void) perr_smt (parser, "expected exactly three arguments to 'store'");
    return;
  }

  c0 = car (cdr (node));
  c1 = car (cdr (cdr (node)));
  c2 = car (cdr (cdr (cdr (node))));

  if (!(a0 = node2exp (parser, c0)))
  {
    assert (parser->error);
    return;
  }

  if (!boolector_is_array (parser->btor, a0))
  {
    (void) perr_smt (parser, "invalid first argument to 'store'");
    return;
  }

  if (!(a1 = node2nonarrayexp (parser, c1)))
  {
    assert (parser->error);
    return;
  }

  if (boolector_get_index_width (parser->btor, a0)
      != boolector_get_width (parser->btor, a1))
  {
    (void) perr_smt (parser, "mismatched bit width of 'store' index");
    return;
  }

  if (!(a2 = node2nonarrayexp (parser, c2)))
  {
    assert (parser->error);
    return;
  }

  if (boolector_get_width (parser->btor, a2)
      != boolector_get_width (parser->btor, a0))
  {
    (void) perr_smt (parser, "mismatched bit width of 'store' value");
    return;
  }

  translate_node (parser, node, boolector_write (parser->btor, a0, a1, a2));
}

static BoolectorNode *
translate_formula (BtorSMTParser *parser, BtorSMTNode *root)
{
  BtorSMTNode *node, *child, *p, **s, **t, *tmp;
  BtorSMTNode *assignment, *body;
  BtorSMTSymbol *symbol;
  BtorSMTToken token;
  uint32_t start, end;
  BoolectorNode *exp;

  assert (BTOR_EMPTY_STACK (parser->work));
  assert (BTOR_EMPTY_STACK (parser->stack));

  assert (root);
  BTOR_PUSH_STACK (parser->stack, root);

  while (!BTOR_EMPTY_STACK (parser->stack))
  {
    node = BTOR_POP_STACK (parser->stack);

    if (node)
    {
      if (isleaf (node))
      {
        /* DO NOTHING HERE */
      }
      else if (car (node) == parser->bind)
      {
        BTOR_PUSH_STACK (parser->work, node);
      }
      else if (is_let_or_flet (car (node)))
      {
        /* node       == ([f]let assignment body)
         * assignment == (var term)
         */
        if (!cdr (node) || !(assignment = car (cdr (node)))
            || isleaf (assignment) || !(token = node2token (car (assignment)))
            || (token != BTOR_SMTOK_FVAR && token != BTOR_SMTOK_VAR)
            || !cdr (assignment) || cdr (cdr (assignment)) || !cdr (cdr (node))
            || cdr (cdr (cdr (node))))
          return perr_smt (parser, "illformed 'let' or 'flet'"),
                 (BoolectorNode *) 0;

        body = car (cdr (cdr (node)));

        BTOR_PUSH_STACK (parser->stack, node);
        BTOR_PUSH_STACK (parser->stack, 0);

        BTOR_PUSH_STACK (parser->stack, body);

        BTOR_PUSH_STACK (parser->stack,
                         cons (parser, parser->bind, assignment));

        BTOR_PUSH_STACK (parser->stack, car (cdr (assignment)));
      }
      else
      {
        BTOR_PUSH_STACK (parser->stack, node);
        BTOR_PUSH_STACK (parser->stack, 0);

        start = BTOR_COUNT_STACK (parser->stack);

        for (p = node; p; p = cdr (p))
        {
          child = car (p);
          assert (child);
          BTOR_PUSH_STACK (parser->stack, child);
        }

        end = BTOR_COUNT_STACK (parser->stack);

        if (start < end)
        {
          s = parser->stack.start + start;
          t = parser->stack.start + end - 1;

          while (s < t)
          {
            tmp = *s;
            *s  = *t;
            *t  = tmp;

            s++;
            t--;
          }
        }
      }
    }
    else
    {
      assert (!BTOR_EMPTY_STACK (parser->stack));

      node = BTOR_POP_STACK (parser->stack);

      assert (node);
      assert (!isleaf (node));

      BTOR_PUSH_STACK (parser->work, node);
    }
  }

  node = 0;
  for (s = parser->work.start; s < parser->work.top; s++)
  {
    node = *s;

    assert (node);
    assert (!isleaf (node));

    child = car (node);

    if (!child) return perr_smt (parser, "empty list"), (BoolectorNode *) 0;

    if (isleaf (child))
    {
      symbol = strip (child);

      switch (symbol->token)
      {
        case BTOR_SMTOK_NOT:
          translate_unary (parser, node, "not", boolector_not);
          break;
        case BTOR_SMTOK_AND:
          translate_associative_binary (parser, node, "and", boolector_and);
          break;
        case BTOR_SMTOK_OR:
          translate_associative_binary (parser, node, "or", boolector_or);
          break;
        case BTOR_SMTOK_IMPLIES:
          translate_binary (parser, node, "implies", boolector_implies);
          break;
        case BTOR_SMTOK_XOR:
          translate_associative_binary (parser, node, "xor", boolector_xor);
          break;
        case BTOR_SMTOK_IFF:
          translate_associative_binary (parser, node, "iff", boolector_xnor);
          break;

        case BTOR_SMTOK_EQ: translate_eq (parser, node); break;

        case BTOR_SMTOK_DISTINCT:
          translate_binary (parser, node, "distinct", boolector_ne);
          break;
        case BTOR_SMTOK_ITE: translate_cond (parser, node, "ite"); break;
        case BTOR_SMTOK_IF_THEN_ELSE:
          translate_cond (parser, node, "if_then_else");
          break;
        case BTOR_SMTOK_BIND:
          assert (cdr (node));
          assert (cdr (cdr (node)));
          assert (!cdr (cdr (cdr (node))));
          assert (isleaf (car (cdr (node))));
          symbol = strip (car (cdr (node)));
          if (symbol->exp)
            return perr_smt (parser, "unsupported nested '[f]let'"),
                   (BoolectorNode *) 0;
          body = car (cdr (cdr (node)));
          if ((exp = node2exp (parser, body)))
          {
            if (symbol->token == BTOR_SMTOK_FVAR)
            {
              if (boolector_get_width (parser->btor, exp) != 1)
              {
                return perr_smt (parser, "flet assignment width not one"),
                       (BoolectorNode *) 0;
              }
            }
            else
              assert (symbol->token == BTOR_SMTOK_VAR);

            assert (!symbol->exp);
            symbol->exp = boolector_copy (parser->btor, exp);
          }
          /* Prevent leaking of 'bind' nodes.  */
          *s = 0;
          delete_smt_node (parser, node);
          break;
        case BTOR_SMTOK_LET:
        case BTOR_SMTOK_FLET:
          symbol = strip (car (car (cdr (node))));
          assert (symbol->token == BTOR_SMTOK_FVAR
                  || symbol->token == BTOR_SMTOK_VAR);
          assert (symbol->exp);
          body = car (cdr (cdr (node)));
          if ((exp = node2exp (parser, body)))
            node->exp = boolector_copy (parser->btor, exp);
          boolector_release (parser->btor, symbol->exp);
          symbol->exp = 0;
          break;
        case BTOR_SMTOK_EXTRACT: translate_extract (parser, node); break;
        case BTOR_SMTOK_REPEAT: translate_repeat (parser, node); break;
        case BTOR_SMTOK_ZERO_EXTEND:
          translate_extend (parser, node, boolector_uext);
          break;
        case BTOR_SMTOK_SIGN_EXTEND:
          translate_extend (parser, node, boolector_sext);
          break;
        case BTOR_SMTOK_ROTATE_RIGHT:
        case BTOR_SMTOK_ROTATE_LEFT: translate_rotate (parser, node); break;
        case BTOR_SMTOK_CONCAT: translate_concat (parser, node); break;
        case BTOR_SMTOK_BVNOT:
          translate_unary (parser, node, "bvnot", boolector_not);
          break;
        case BTOR_SMTOK_BVNEG:
          translate_unary (parser, node, "bvneg", boolector_neg);
          break;
        case BTOR_SMTOK_BVADD:
          translate_associative_binary (parser, node, "bvadd", boolector_add);
          break;
        case BTOR_SMTOK_BVSUB:
          translate_binary (parser, node, "bvsub", boolector_sub);
          break;
        case BTOR_SMTOK_BVSDIV:
          translate_binary (parser, node, "bvsdiv", boolector_sdiv);
          break;
        case BTOR_SMTOK_BVUDIV:
          translate_binary (parser, node, "bvudiv", boolector_udiv);
          break;
        case BTOR_SMTOK_BVUREM:
          translate_binary (parser, node, "bvurem", boolector_urem);
          break;
        case BTOR_SMTOK_BVSREM:
          translate_binary (parser, node, "bvsrem", boolector_srem);
          break;
        case BTOR_SMTOK_BVSMOD:
          translate_binary (parser, node, "bvsmod", boolector_smod);
          break;
        case BTOR_SMTOK_BVMUL:
          translate_associative_binary (parser, node, "bvmul", boolector_mul);
          break;
        case BTOR_SMTOK_BVULE:
          translate_binary (parser, node, "bvule", boolector_ulte);
          break;
        case BTOR_SMTOK_BVSLE:
          translate_binary (parser, node, "bvsle", boolector_slte);
          break;
        case BTOR_SMTOK_BVSGT:
          translate_binary (parser, node, "bvsgt", boolector_sgt);
          break;
        case BTOR_SMTOK_BVSGE:
          translate_binary (parser, node, "bvsge", boolector_sgte);
          break;
        case BTOR_SMTOK_BVCOMP:
          translate_binary (parser, node, "bvcomp", boolector_eq);
          break;
        case BTOR_SMTOK_BVULT:
          translate_binary (parser, node, "bvult", boolector_ult);
          break;
        case BTOR_SMTOK_BVUGT:
          translate_binary (parser, node, "bvugt", boolector_ugt);
          break;
        case BTOR_SMTOK_BVUGE:
          translate_binary (parser, node, "bvuge", boolector_ugte);
          break;
        case BTOR_SMTOK_BVSLT:
          translate_binary (parser, node, "bvslt", boolector_slt);
          break;
        case BTOR_SMTOK_BVAND:
          translate_binary (parser, node, "bvand", boolector_and);
          break;
        case BTOR_SMTOK_BVOR:
          translate_binary (parser, node, "bvor", boolector_or);
          break;
        case BTOR_SMTOK_BVXOR:
          translate_binary (parser, node, "bvxor", boolector_xor);
          break;
        case BTOR_SMTOK_BVXNOR:
          translate_binary (parser, node, "bvxnor", boolector_xnor);
          break;
        case BTOR_SMTOK_BVNOR:
          translate_binary (parser, node, "bvnor", boolector_nor);
          break;
        case BTOR_SMTOK_BVNAND:
          translate_binary (parser, node, "bvnand", boolector_nand);
          break;
        case BTOR_SMTOK_BVLSHR:
          translate_shift (parser, node, "bvlshr", boolector_srl);
          break;
        case BTOR_SMTOK_BVASHR:
          translate_shift (parser, node, "bvashr", boolector_sra);
          break;
        case BTOR_SMTOK_BVSHL:
          translate_shift (parser, node, "bvshl", boolector_sll);
          break;
        case BTOR_SMTOK_SELECT: translate_select (parser, node); break;
        case BTOR_SMTOK_STORE: translate_store (parser, node); break;
        default:
          assert (symbol->token != BTOR_SMTOK_TRANSLATED);
          translate_symbol (parser, node);
          break;
      }
    }
    else
    {
      if (is_list_of_length (node, 1))
      {
        if ((exp = node2exp (parser, child)))
          translate_node (parser, node, boolector_copy (parser->btor, exp));
      }
      else
        (void) perr_smt (parser, "invalid list expression");
    }

    if (parser->error) return (BoolectorNode *) 0;
  }

  BTOR_RESET_STACK (parser->work);

  if (!(exp = node2exp (parser, root)))
  {
    assert (parser->error);
    return (BoolectorNode *) 0;
  }

  if (boolector_get_width (parser->btor, exp) != 1)
    return perr_smt (parser, "non boolean formula"), (BoolectorNode *) 0;

  assert (!parser->error);

  assert (exp);

  return boolector_copy (parser->btor, exp);
}

static void
smt_parser_inc_add_release_sat (BtorSMTParser *parser,
                                BtorParseResult *res,
                                BoolectorNode *exp)
{
  char *prefix;
  int32_t satres, nchecked, ndigits;
  uint32_t formula;
  assert (parser->formulas.nchecked < parser->formulas.nparsed);
  formula = parser->formulas.nchecked;
  nchecked = 1;

  if (parser->formulas.nchecked + 1 == parser->formulas.nparsed)
  {
    smt_message (parser, 3, "adding last ':formula' %d permanently", formula);
    boolector_assert (parser->btor, exp);
  }
  else
  {
    smt_message (parser, 3, "adding ':formula' %d as assumption", formula);
    boolector_assume (parser->btor, exp);
  }
  boolector_release (parser->btor, exp);

  satres = boolector_sat (parser->btor);
  res->nsatcalls += 1;
  if (satres == BOOLECTOR_SAT)
  {
    smt_message (parser, 1, "':formula' %d SAT", formula);
    res->result = BOOLECTOR_SAT;
    fprintf (parser->outfile, "sat\n");
  }
  else
  {
    assert (satres == BOOLECTOR_UNSAT);
    smt_message (parser, 1, "':formula' %d UNSAT", formula);
    if (res->result == BOOLECTOR_UNKNOWN) res->result = BOOLECTOR_UNSAT;
    fprintf (parser->outfile, "unsat\n");
  }
  if (parser->verbosity >= 2) boolector_print_stats (parser->btor);

  parser->formulas.nchecked += nchecked;

  ndigits = btor_util_num_digits (parser->formulas.nchecked) + 3;
  BTOR_NEWN (parser->mem, prefix, ndigits);
  sprintf (prefix, "%d:", parser->formulas.nchecked);
  boolector_set_msg_prefix (parser->btor, prefix);
  BTOR_DELETEN (parser->mem, prefix, ndigits);

  if (parser->formulas.nchecked == parser->formulas.nparsed)
    boolector_set_msg_prefix (parser->btor, 0);
}

static bool
continue_parsing (BtorSMTParser *parser, BtorParseResult *res)
{
  if (res->result != BOOLECTOR_SAT) return true;
  return parser->incremental
         && parser->incremental_smt1 == BTOR_INCREMENTAL_SMT1_CONTINUE;
}

static char *
translate_benchmark (BtorSMTParser *parser,
                     BtorSMTNode *top,
                     BtorParseResult *res)
{
  BtorSMTSymbol *symbol, *logic, *benchmark;
  BtorSMTNode *p, *node, *q;
  BoolectorNode *exp;
  BtorSMTToken status;

  smt_message (parser, 2, "extracting expressions");

  p = top;

  if (!p || !(node = car (p)) || !isleaf (node)
      || strip (node)->token != BTOR_SMTOK_BENCHMARK)
    return perr_smt (parser, "expected 'benchmark' keyword");

  p = cdr (p);

  if (!p || !(benchmark = car (p)) || !isleaf (benchmark)
      || strip (benchmark)->token != BTOR_SMTOK_IDENTIFIER)
    return perr_smt (parser, "expected benchmark name");

  benchmark = strip (benchmark);

  smt_message (parser, 2, "benchmark %s", benchmark->name);

  symbol = 0;

  for (p = top; p; p = cdr (p))
  {
    node = car (p);
    if (!isleaf (node)) continue;

    symbol = strip (node);

    if (symbol->token == BTOR_SMTOK_EXTRASORTS
        || symbol->token == BTOR_SMTOK_EXTRAFUNS
        || symbol->token == BTOR_SMTOK_EXTRAPREDS
        || symbol->token == BTOR_SMTOK_ASSUMPTION
        || symbol->token == BTOR_SMTOK_FORMULA)
      return perr_smt (parser, "'%s' before ':logic'", symbol->name);

    if (symbol->token == BTOR_SMTOK_LOGICATTR) break;
  }

  if (!p) return perr_smt (parser, "no ':logic' attribute found");

  p = cdr (p);
  if (!p) return perr_smt (parser, "argument to ':logic' missing");

  node = car (p);
  if (!isleaf (node)) return perr_smt (parser, "invalid argument to ':logic'");

  logic = strip (node);
  if (!strcmp (logic->name, "QF_BV"))
    res->logic = BTOR_LOGIC_QF_BV;
  else if (!strcmp (logic->name, "QF_AUFBV") || !strcmp (logic->name, "QF_ABV"))
    res->logic = BTOR_LOGIC_QF_AUFBV;
  else
    return perr_smt (parser, "unsupported logic '%s'", logic->name);

  for (p = top; p; p = cdr (p))
  {
    node = car (p);
    if (!isleaf (node)) continue;

    symbol = strip (node);
    if (symbol->token == BTOR_SMTOK_STATUS) break;
  }

  if (p)
  {
    p = cdr (p);
    if (!p) return perr_smt (parser, "argument to ':status' missing");

    node = car (p);
    if (!isleaf (node))
    {
    INVALID_STATUS_ARGUMENT:
      return perr_smt (parser, "invalid ':status' argument");
    }

    symbol = strip (node);
    status = symbol->token;

    if (status == BTOR_SMTOK_SAT)
      res->status = BOOLECTOR_SAT;
    else if (status == BTOR_SMTOK_UNSAT)
      res->status = BOOLECTOR_UNSAT;
    else if (status == BTOR_SMTOK_UNKNOWN)
      res->status = BOOLECTOR_UNKNOWN;
    else
      goto INVALID_STATUS_ARGUMENT;
  }

  for (p = top; p && continue_parsing (parser, res); p = cdr (p))
  {
    q    = p;
    node = car (p);
    if (!isleaf (node)) goto CONTINUE;

    symbol = strip (node);

    switch (symbol->token)
    {
      case BTOR_SMTOK_EXTRAFUNS:
        p = cdr (p);
        if (!p) return perr_smt (parser, "argument to ':extrafuns' missing");

        if (!extrafuns (parser, car (p)))
        {
          assert (parser->error);
          return parser->error;
        }

        break;

      case BTOR_SMTOK_EXTRAPREDS:

        p = cdr (p);
        if (!p) return perr_smt (parser, "argument to ':extrapreds' missing");

        if (!extrapreds (parser, car (p)))
        {
          assert (parser->error);
          return parser->error;
        }

        break;

      case BTOR_SMTOK_ASSUMPTION:

        p = cdr (p);
        if (!p) return perr_smt (parser, "argument to ':assumption' missing");

        exp = translate_formula (parser, car (p));
        if (!exp)
        {
          assert (parser->error);
          return parser->error;
        }

        recursively_delete_smt_node (parser, p->head);
        p->head = 0;

        if (parser->incremental)
        {
          smt_message (parser,
                       3,
                       "adding ':assumption' %d",
                       parser->assumptions.handled);
        }
        boolector_assert (parser->btor, exp);
        boolector_release (parser->btor, exp);

        parser->assumptions.handled++;

        break;

      case BTOR_SMTOK_FORMULA:

        p = cdr (p);
        if (!p) return perr_smt (parser, "argument to ':formula' missing");

        exp = translate_formula (parser, car (p));
        if (!exp)
        {
          assert (parser->error);
          return parser->error;
        }

        recursively_delete_smt_node (parser, p->head);
        p->head = 0;

        if (!parser->incremental)
        {
          boolector_assert (parser->btor, exp);
          boolector_release (parser->btor, exp);
        }
        else
          smt_parser_inc_add_release_sat (parser, res, exp);

        parser->formulas.handled++;

        break;

      case BTOR_SMTOK_EXTRASORTS:
        return perr_smt (parser, "':extrasorts' unsupported");

      default: break;
    }
  CONTINUE:
    for (;;)
    {
      node    = q->head;
      q->head = 0;
      recursively_delete_smt_node (parser, node);
      if (q == p) break;
      q = cdr (q);
    }
  }

  if (parser->required_logic == BTOR_LOGIC_QF_AUFBV
      && res->logic == BTOR_LOGIC_QF_BV)
  {
    if (parser->incremental)
    {
      smt_message (
          parser,
          1,
          "need QF_AUFBV but only QF_BV specified in incremental mode");
      res->logic = BTOR_LOGIC_QF_AUFBV;
    }
    else
      return perr_smt (
          parser,
          "need QF_AUFBV but only QF_BV specified in non-incremental mode");
  }

  if (parser->required_logic == BTOR_LOGIC_QF_BV
      && res->logic == BTOR_LOGIC_QF_AUFBV)
  {
    smt_message (
        parser,
        1,
        "no arrays found: only need QF_BV (even though QF_AUFBV specified)");
    res->logic = BTOR_LOGIC_QF_BV;
  }

  assert (!parser->error);

  return 0;
}

static void
count_assumptions_and_formulas (BtorSMTParser *parser, BtorSMTNode *top)
{
  BtorSMTNode *p, *n;
  BtorSMTSymbol *s;

  parser->formulas.nparsed = parser->assumptions.nparsed = 0;

  for (p = top; p; p = cdr (p))
  {
    n = car (p);

    if (!isleaf (n)) continue;

    s = strip (n);

    if (s->token == BTOR_SMTOK_FORMULA) parser->formulas.nparsed++;

    if (s->token == BTOR_SMTOK_ASSUMPTION) parser->assumptions.nparsed++;
  }
}

static void
set_last_occurrence_of_symbols (BtorSMTParser *parser, BtorSMTNode *top)
{
  BtorSMTNode *n, *h, *t;
  BtorSMTSymbol *s;
  uint32_t occs = 0;

  assert (BTOR_EMPTY_STACK (parser->stack));

  BTOR_PUSH_STACK (parser->stack, top);
  while (!BTOR_EMPTY_STACK (parser->stack))
  {
    n = BTOR_POP_STACK (parser->stack);
    if (isleaf (n)) continue;

    h = car (n);
    t = cdr (n);

    if (t)
    {
      assert (!isleaf (t));
      BTOR_PUSH_STACK (parser->stack, t);
    }

    assert (h);
    if (isleaf (h))
    {
      s = strip (h);
      if (s->token == BTOR_SMTOK_IDENTIFIER)
      {
        s->last = n;
        occs++;
      }
    }
    else
      BTOR_PUSH_STACK (parser->stack, h);
  }

  smt_message (parser, 1, "found %u occurrences of symbols", occs);
}

/* Note: we need prefix in case of stdin as input (also applies to compressed
 * input files). */
static const char *
parse (BtorSMTParser *parser,
       BtorCharStack *prefix,
       FILE *infile,
       const char *infile_name,
       FILE *outfile,
       BtorParseResult *res)
{
  BtorSMTNode *node, *top, **p, **first;
  BtorSMTToken token;
  const char *err;
  int32_t head;

  assert (!parser->parsed);
  parser->parsed = true;

  smt_message (parser, 1, "parsing SMT file %s", infile_name);

  parser->infile_name = infile_name;
  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->infile      = infile;
  parser->outfile     = outfile;
  parser->lineno      = 1;
  parser->saved       = false;

  BTOR_CLR (res);

  res->status = BOOLECTOR_UNKNOWN;
  res->result = BOOLECTOR_UNKNOWN;

  assert (BTOR_EMPTY_STACK (parser->stack));
  assert (BTOR_EMPTY_STACK (parser->heads));

NEXT_TOKEN:

  token = nextok (parser);

  if (token == BTOR_SMTOK_LP)
  {
    head = BTOR_COUNT_STACK (parser->stack);
    BTOR_PUSH_STACK (parser->heads, head);
    goto NEXT_TOKEN;
  }

  if (token == BTOR_SMTOK_RP)
  {
    if (BTOR_EMPTY_STACK (parser->heads))
      return perr_smt (parser, "too many closing ')'");

    node = 0;
    head = BTOR_POP_STACK (parser->heads);
    assert ((size_t) head <= BTOR_COUNT_STACK (parser->stack));
    first = parser->stack.start + head;
    p     = parser->stack.top;
    while (first < p) node = cons (parser, *--p, node);

    parser->stack.top = first;
    BTOR_PUSH_STACK (parser->stack, node);

    if (!BTOR_EMPTY_STACK (parser->heads)) goto NEXT_TOKEN;

    token = nextok (parser);
    if (token != BTOR_SMTOK_EOF) return perr_smt (parser, "expected EOF");

    assert (BTOR_COUNT_STACK (parser->stack) == 1);
    top = parser->stack.start[0];
    BTOR_RESET_STACK (parser->stack);

    smt_message (parser, 2, "read %llu bytes", parser->bytes);
    smt_message (parser, 2, "found %u symbols", parser->symbols);
    smt_message (parser, 2, "generated %u nodes", parser->nodes->count);

    count_assumptions_and_formulas (parser, top);

    smt_message (
        parser, 1, "found %d assumptions", parser->assumptions.nparsed);

    smt_message (parser, 1, "found %d formulas", parser->formulas.nparsed);

    set_last_occurrence_of_symbols (parser, top);

    err = translate_benchmark (parser, top, res);
    recursively_delete_smt_node (parser, top);

    if (err)
    {
      assert (parser->error);
      return parser->error;
    }

    smt_message (parser, 2, "found %u constants", parser->constants);

    return 0; /* DONE */
  }

  if (token == BTOR_SMTOK_ERR)
  {
    assert (parser->error);
    return parser->error;
  }

  if (token == BTOR_SMTOK_EOF) return perr_smt (parser, "unexpected EOF");

  if (BTOR_EMPTY_STACK (parser->heads))
    return perr_smt (parser, "expected '('");

  assert (parser->symbol);
  BTOR_PUSH_STACK (parser->stack, leaf (parser->symbol));

  goto NEXT_TOKEN;
}

static const char *
parse_smt_parser (BtorSMTParser *parser,
                  BtorCharStack *prefix,
                  FILE *infile,
                  const char *infile_name,
                  FILE *outfile,
                  BtorParseResult *res)
{
  (void) parse (parser, prefix, infile, infile_name, outfile, res);
  release_smt_internals (parser);
  return parser->error;
}

static BtorParserAPI parsesmt_parser_api = {
    (BtorInitParser) new_smt_parser,
    (BtorResetParser) delete_smt_parser,
    (BtorParse) parse_smt_parser,
};

const BtorParserAPI *
btor_parsesmt_parser_api ()
{
  return &parsesmt_parser_api;
}
