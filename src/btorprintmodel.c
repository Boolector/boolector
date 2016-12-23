/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorprintmodel.h"
#include "btormodel.h"
#include "dumper/btordumpsmt.h"
#include "utils/btormisc.h"

/*------------------------------------------------------------------------*/
/* print model                                                            */
/*------------------------------------------------------------------------*/

static void
print_fmt_bv_model_btor (Btor *btor,
                         int base,
                         const BtorBitVector *assignment,
                         FILE *file)
{
  assert (btor);
  assert (assignment);
  assert (file);

  char *ass;

  if (base == BTOR_OUTPUT_BASE_HEX)
    ass = btor_bv_to_hex_char_bv (btor->mm, assignment);
  else if (base == BTOR_OUTPUT_BASE_DEC)
    ass = btor_bv_to_dec_char_bv (btor->mm, assignment);
  else
    ass = btor_bv_to_char_bv (btor->mm, assignment);
  fprintf (file, "%s", ass);
  btor_freestr (btor->mm, ass);
}

static void
print_fmt_bv_model_tuple_btor (Btor *btor,
                               int base,
                               const BtorBitVectorTuple *assignments,
                               FILE *file)
{
  assert (btor);
  assert (assignments);
  assert (file);

  uint32_t i;

  if (assignments->arity > 1)
  {
    for (i = 0; i < assignments->arity; i++)
    {
      if (i > 0) fprintf (file, " ");
      print_fmt_bv_model_btor (btor, base, assignments->bv[i], file);
    }
  }
  else
    print_fmt_bv_model_btor (btor, base, assignments->bv[0], file);
}

/*------------------------------------------------------------------------*/

static void
print_bv_model (Btor *btor, BtorNode *node, char *format, int base, FILE *file)
{
  assert (btor);
  assert (format);
  assert (node);
  assert (BTOR_IS_REGULAR_NODE (node));

  int id;
  char *symbol;
  const BtorBitVector *ass;

  ass    = btor_get_bv_model (btor, node);
  symbol = btor_get_symbol_exp (btor, node);

  if (!strcmp (format, "btor"))
  {
    id = ((BtorBVVarNode *) node)->btor_id;
    fprintf (file, "%d ", id ? id : node->id);
    print_fmt_bv_model_btor (btor, base, ass, file);
    fprintf (file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
  }
  else
  {
    if (symbol)
      fprintf (file, "%2c(define-fun %s () ", ' ', symbol);
    else
      fprintf (file,
               "%2c(define-fun v%d () ",
               ' ',
               ((BtorBVVarNode *) node)->btor_id
                   ? ((BtorBVVarNode *) node)->btor_id
                   : node->id);

    btor_dump_sort_smt_node (node, file);
    fprintf (file, " ");
    btor_dump_const_value_smt (btor, ass, base, file);
    fprintf (file, ")\n");
  }
}

/*------------------------------------------------------------------------*/

static void
print_param_smt2 (char *symbol, int param_index, BtorSort *sort, FILE *file)
{
  assert (symbol);
  assert (sort);
  assert (file);

  fprintf (file, "(%s_x%d ", symbol, param_index);
  btor_dump_sort_smt (sort, file);
  fprintf (file, ")");
}

static void
print_fun_model_smt2 (Btor *btor, BtorNode *node, int base, FILE *file)
{
  assert (btor);
  assert (node);
  assert (BTOR_IS_REGULAR_NODE (node));
  assert (file);

  char *s, *symbol;
  uint32_t i, x, n;
  BtorPtrHashTable *fun_model;
  BtorPtrHashTableIterator it;
  BtorBitVectorTuple *args;
  BtorBitVector *assignment, *tmp;
  BtorSortId sort;
  BtorTupleSortIterator iit;

  fun_model = (BtorPtrHashTable *) btor_get_fun_model (
      btor, btor_simplify_exp (btor, node));
  if (!fun_model) return;

  if ((symbol = btor_get_symbol_exp (btor, node)))
    s = symbol;
  else
  {
    BTOR_NEWN (btor->mm, s, 40);
    sprintf (s,
             "%s%d",
             btor_is_uf_array_node (node) ? "a" : "uf",
             ((BtorUFNode *) node)->btor_id ? ((BtorUFNode *) node)->btor_id
                                            : node->id);
  }

  fprintf (file, "%2c(define-fun %s (", ' ', s);

  /* fun param sorts */
  node = btor_simplify_exp (btor, node);
  assert (BTOR_IS_REGULAR_NODE (node));
  assert (btor_is_fun_node (node));
  btor_init_tuple_sort_iterator (
      &iit, btor, btor_get_domain_fun_sort (btor, btor_exp_get_sort_id (node)));
  x = 0;
  while (btor_has_next_tuple_sort_iterator (&iit))
  {
    sort = btor_next_tuple_sort_iterator (&iit);
    fprintf (file, "\n%3c", ' ');
    print_param_smt2 (s, x, btor_get_sort_by_id (btor, sort), file);
    x++;
  }
  fprintf (file, ") ");
  sort = btor_get_codomain_fun_sort (btor, btor_exp_get_sort_id (node));
  btor_dump_sort_smt (btor_get_sort_by_id (btor, sort), file);
  fprintf (file, "\n");

  /* fun model as ite over args and assignments */
  n          = 0;
  assignment = 0;
  btor_init_ptr_hash_table_iterator (&it, fun_model);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    fprintf (file, "%4c(ite ", ' ');
    assignment = it.bucket->data.as_ptr;
    args       = btor_next_ptr_hash_table_iterator (&it);
    x          = 0;
    if (args->arity > 1)
    {
      fprintf (file, "\n%6c(and ", ' ');
      for (i = 0; i < args->arity; i++, x++)
      {
        fprintf (file, "\n%8c(= %s_x%d ", ' ', s, x);
        btor_dump_const_value_smt (btor, args->bv[i], base, file);
        fprintf (file, ")%s", i + 1 == args->arity ? "" : " ");
      }
      fprintf (file, ") ");
      fprintf (file, "\n%6c", ' ');
    }
    else
    {
      fprintf (file, "(= %s_x%d ", s, x);
      btor_dump_const_value_smt (btor, args->bv[0], base, file);
      fprintf (file, ") ");
    }
    btor_dump_const_value_smt (btor, assignment, base, file);
    fprintf (file, "\n");
    n += 1;
  }

  /* print default value */
  assert (assignment);
  if (assignment) /* get rid of compiler warning */
  {
    fprintf (file, "%6c", ' ');
    tmp = btor_new_bv (btor->mm, assignment->width);
    btor_dump_const_value_smt (btor, tmp, base, file);
    btor_free_bv (btor->mm, tmp);
  }

  for (i = 0; i < n; i++) fprintf (file, ")");
  fprintf (file, ")\n");

  if (!symbol) BTOR_DELETEN (btor->mm, s, 40);
}

static void
print_fun_model_btor (Btor *btor, BtorNode *node, int base, FILE *file)
{
  assert (btor);
  assert (node);
  assert (BTOR_IS_REGULAR_NODE (node));
  assert (file);

  char *symbol;
  int id;
  BtorBitVector *assignment;
  BtorBitVectorTuple *args;
  BtorPtrHashTable *fun_model;
  BtorPtrHashTableIterator it;

  fun_model = (BtorPtrHashTable *) btor_get_fun_model (
      btor, btor_simplify_exp (btor, node));
  if (!fun_model) return;

  symbol = btor_get_symbol_exp (btor, node);
  id     = ((BtorUFNode *) node)->btor_id;

  btor_init_ptr_hash_table_iterator (&it, fun_model);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    assignment = it.bucket->data.as_ptr;
    args       = btor_next_ptr_hash_table_iterator (&it);
    // TODO: distinguish between functions and arrays (ma)
    //       needs proper sort handling
    fprintf (file, "%d[", id ? id : node->id);
    print_fmt_bv_model_tuple_btor (btor, base, args, file);
    fprintf (file, "] ");
    print_fmt_bv_model_btor (btor, base, assignment, file);
    fprintf (file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
  }
}

static void
print_fun_model (Btor *btor, BtorNode *node, char *format, int base, FILE *file)
{
  assert (btor);
  assert (node);
  assert (format);
  assert (file);
  assert (BTOR_IS_REGULAR_NODE (node));

  if (!strcmp (format, "btor"))
    print_fun_model_btor (btor, node, base, file);
  else
    print_fun_model_smt2 (btor, node, base, file);
}

/*------------------------------------------------------------------------*/

void
btor_print_model (Btor *btor, char *format, FILE *file)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_RESULT_SAT);
  assert (format);
  assert (!strcmp (format, "btor") || !strcmp (format, "smt2"));
  assert (file);

  BtorNode *cur;
  BtorPtrHashTableIterator it;
  int base;

  base = btor_get_opt (btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT);

  if (!strcmp (format, "smt2"))
    fprintf (file, "(model%s", btor->inputs->count ? "\n" : " ");

  btor_init_ptr_hash_table_iterator (&it, btor->inputs);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    cur = btor_next_ptr_hash_table_iterator (&it);
    if (btor_is_fun_node (btor_simplify_exp (btor, cur)))
      print_fun_model (btor, cur, format, base, file);
    else
      print_bv_model (btor, cur, format, base, file);
  }

  if (!strcmp (format, "smt2")) fprintf (file, ")\n");
}

/*------------------------------------------------------------------------*/
/* print value                                                            */
/*------------------------------------------------------------------------*/

static void
print_bv_value (Btor *btor,
                BtorNode *node,
                char *symbol_str,
                char *format,
                int base,
                FILE *file)
{
  assert (btor);
  assert (format);
  assert (node);
  assert (BTOR_IS_REGULAR_NODE (node));

  char *symbol;
  const BtorBitVector *ass;

  ass    = btor_get_bv_model (btor, node);
  symbol = symbol_str ? symbol_str : btor_get_symbol_exp (btor, node);

  if (!strcmp (format, "btor"))
    print_bv_model (btor, node, format, base, file);
  else
  {
    if (symbol)
      fprintf (file, "(%s ", symbol);
    else
      fprintf (file,
               "(v%d ",
               ((BtorBVVarNode *) node)->btor_id
                   ? ((BtorBVVarNode *) node)->btor_id
                   : node->id);

    btor_dump_const_value_smt (btor, ass, base, file);
    fprintf (file, ")");
  }
}

/*------------------------------------------------------------------------*/

static void
print_fun_value_smt2 (
    Btor *btor, BtorNode *node, char *symbol_str, int base, FILE *file)
{
  assert (btor);
  assert (node);
  assert (BTOR_IS_REGULAR_NODE (node));
  assert (file);

  uint32_t i, n;
  char *s, *symbol;
  BtorPtrHashTable *fun_model;
  BtorPtrHashTableIterator it;
  BtorBitVectorTuple *args;
  BtorBitVector *assignment;

  fun_model = (BtorPtrHashTable *) btor_get_fun_model (btor, node);
  if (!fun_model) return;

  if (symbol_str)
    symbol = symbol_str;
  else if ((symbol = btor_get_symbol_exp (btor, node)))
    s = symbol;
  else
  {
    BTOR_NEWN (btor->mm, s, 40);
    sprintf (s,
             "%s%d",
             btor_is_uf_array_node (node) ? "a" : "uf",
             ((BtorUFNode *) node)->btor_id ? ((BtorUFNode *) node)->btor_id
                                            : node->id);
  }

  fprintf (file, "(");

  n = 0;
  btor_init_ptr_hash_table_iterator (&it, fun_model);
  while (btor_has_next_ptr_hash_table_iterator (&it))
  {
    fprintf (file, "%s((%s ", n++ ? "\n  " : "", symbol);
    assignment = it.bucket->data.as_ptr;
    args       = btor_next_ptr_hash_table_iterator (&it);
    if (args->arity > 1)
    {
      for (i = 0; i < args->arity; i++)
      {
        btor_dump_const_value_smt (btor, args->bv[i], base, file);
        fprintf (file, ")%s", i + 1 == args->arity ? "" : " ");
      }
      fprintf (file, ") ");
    }
    else
    {
      btor_dump_const_value_smt (btor, args->bv[0], base, file);
      fprintf (file, ") ");
    }
    btor_dump_const_value_smt (btor, assignment, base, file);
    fprintf (file, ")");
  }

  fprintf (file, ")");
}

static void
print_fun_value_btor (Btor *btor, BtorNode *node, int base, FILE *file)
{
  print_fun_model_btor (btor, node, base, file);
}

static void
print_fun_value (Btor *btor,
                 BtorNode *node,
                 char *symbol_str,
                 char *format,
                 int base,
                 FILE *file)
{
  assert (btor);
  assert (node);
  assert (format);
  assert (file);

  if (!strcmp (format, "btor"))
    print_fun_value_btor (btor, BTOR_REAL_ADDR_NODE (node), base, file);
  else
    print_fun_value_smt2 (
        btor, BTOR_REAL_ADDR_NODE (node), symbol_str, base, file);
}

/*------------------------------------------------------------------------*/

void
btor_print_value (
    Btor *btor, BtorNode *exp, char *symbol_str, char *format, FILE *file)
{
  assert (btor);
  assert (btor->last_sat_result == BTOR_RESULT_SAT);
  assert (exp);
  assert (format);
  assert (!strcmp (format, "btor") || !strcmp (format, "smt2"));
  assert (file);

  int base;

  base = btor_get_opt (btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT);
  if (btor_is_fun_node (btor_simplify_exp (btor, exp)))
    print_fun_value (btor, exp, symbol_str, format, base, file);
  else
    print_bv_value (btor, exp, symbol_str, format, base, file);
}
