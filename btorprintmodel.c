/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014 Mathias Preiner.
 *  Copyright (C) 2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorprintmodel.h"
#include "btorconst.h"
#include "btorhash.h"
#include "btoriter.h"
#include "btormodel.h"

const char *
btor_get_bv_model_str (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);

  const char *res;
  const BitVector *bv;

  exp = btor_simplify_exp (btor, exp);
  if (!(bv = btor_get_bv_model (btor, exp)))
    return btor_x_const_3vl (btor->mm, BTOR_REAL_ADDR_NODE (exp)->len);
  res = btor_bv_to_char_bv (btor, bv);
  return res;
}

void
btor_get_fun_model_str (
    Btor *btor, BtorNode *exp, char ***args, char ***values, int *size)
{
  assert (btor);
  assert (exp);
  assert (args);
  assert (values);
  assert (size);
  assert (BTOR_IS_REGULAR_NODE (exp));

  char *arg, *tmp, *bv;
  int i, j, len;
  BtorHashTableIterator it;
  const BtorPtrHashTable *model;
  BitVector *value;
  BitVectorTuple *t;

  exp = btor_simplify_exp (btor, exp);
  assert (BTOR_IS_FUN_NODE (exp));

  model = btor_get_fun_model (btor, exp);
  assert (model->count > 0);

  if ((BTOR_IS_LAMBDA_NODE (exp) && ((BtorLambdaNode *) exp)->num_params > 1)
      || !btor->fun_model || !model)
  {
    *size = 0;
    return;
  }

  *size = (int) model->count;
  BTOR_NEWN (btor->mm, *args, *size);
  BTOR_NEWN (btor->mm, *values, *size);

  i = 0;
  init_hash_table_iterator (&it, (BtorPtrHashTable *) model);
  while (has_next_hash_table_iterator (&it))
  {
    value = (BitVector *) it.bucket->data.asPtr;

    /* build assignment string for all arguments */
    t   = (BitVectorTuple *) next_hash_table_iterator (&it);
    len = t->arity;
    for (j = 0; j < t->arity; j++) len += t->bv[j]->width;
    BTOR_NEWN (btor->mm, arg, len);
    tmp = arg;

    bv = (char *) btor_bv_to_char_bv (btor, t->bv[0]);
    strcpy (tmp, bv);
    btor_release_bv_assignment_str (btor, bv);

    for (j = 1; j < t->arity; j++)
    {
      bv = (char *) btor_bv_to_char_bv (btor, t->bv[j]);
      strcat (tmp, " ");
      strcat (tmp, bv);
      btor_release_bv_assignment_str (btor, bv);
    }
    assert ((int) strlen (arg) == len - 1);

    (*args)[i]   = arg;
    (*values)[i] = (char *) btor_bv_to_char_bv (btor, value);
    i++;
  }
}

static void
print_formatted_bv_btor (Btor *btor, int base, char *assignment, FILE *file)
{
  assert (btor);
  assert (assignment);
  assert (file);

  BtorCharPtrStack values;
  char *fmt, *ground, *tok;
  int i, len, orig_len;

  BTOR_INIT_STACK (values);

  /* assignment may contain multiple values (in case of function args) */
  len      = 0;
  fmt      = btor_strdup (btor->mm, assignment);
  orig_len = strlen (fmt) + 1;
  tok      = strtok (fmt, " ");
  do
  {
    if (base == BTOR_OUTPUT_BASE_HEX || base == BTOR_OUTPUT_BASE_DEC)
    {
      ground = btor_ground_const_3vl (btor->mm, tok);
      if (base == BTOR_OUTPUT_BASE_HEX)
        tok = btor_const_to_hex (btor->mm, ground);
      else
      {
        assert (base == BTOR_OUTPUT_BASE_DEC);
        tok = btor_const_to_decimal (btor->mm, ground);
      }
      btor_delete_const (btor->mm, ground);
    }
    else
      tok = btor_copy_const (btor->mm, tok);
    len += strlen (tok) + 1;
    BTOR_PUSH_STACK (btor->mm, values, tok);
  } while ((tok = strtok (0, " ")));
  btor_free (btor->mm, fmt, orig_len * sizeof (char));

  /* concat formatted assignment strings */
  BTOR_NEWN (btor->mm, fmt, len);
  assert (!BTOR_EMPTY_STACK (values));
  for (i = 0; i < BTOR_COUNT_STACK (values); i++)
  {
    tok = BTOR_PEEK_STACK (values, i);
    if (i == 0)
      strcpy (fmt, tok);
    else
    {
      strcat (fmt, " ");
      strcat (fmt, tok);
    }
    btor_freestr (btor->mm, tok);
  }
  BTOR_RELEASE_STACK (btor->mm, values);
  fprintf (file, "%s", fmt);
  btor_freestr (btor->mm, fmt);
}

static void
print_formatted_bv_smt2 (
    Btor *btor, int len, int base, char *assignment, FILE *file)
{
  assert (btor);
  assert (len);
  assert (assignment);
  assert (file);

  char *fmt = 0;

  if (base == BTOR_OUTPUT_BASE_HEX)
  {
    if (len % 4) goto BASE_BIN;
    fmt = btor_const_to_hex (btor->mm, assignment);
    fprintf (file, "#x%s", fmt);
  }
  else if (base == BTOR_OUTPUT_BASE_DEC)
  {
    fmt = btor_const_to_decimal (btor->mm, assignment);
    fprintf (file, "(_ bv%s %d)", fmt, len);
  }
  else
  BASE_BIN:
    fprintf (file, "#b%s", assignment);

  if (fmt) btor_freestr (btor->mm, fmt);
}

static void
print_bv_assignment (
    Btor *btor, BtorNode *node, char *format, int base, FILE *file)
{
  assert (btor);
  assert (format);
  assert (node);

  int id;
  char *symbol;
  char *assignment;

  assignment = (char *) btor_get_bv_model_str (btor, node);
  symbol     = btor_get_symbol_exp (btor, node);

  if (!strcmp (format, "btor"))
  {
    id = ((BtorBVVarNode *) node)->btor_id;
    fprintf (file, "%d ", id ? id : node->id);
    print_formatted_bv_btor (btor, base, assignment, file);
    fprintf (file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
  }
  else
  {
    fprintf (file, "  (define-fun ");
    fprintf (file, "%s () (_ BitVec %d) ", symbol, node->len);
    print_formatted_bv_smt2 (btor, node->len, base, assignment, file);
    fprintf (file, ")\n");
  }
  btor_release_bv_assignment_str (btor, (char *) assignment);
}

static void
print_uf_assignment_btor (Btor *btor, BtorNode *node, int base, FILE *file)
{
  char **args, **val, *symbol;
  int i, size, id;

  btor_get_fun_model_str (btor, node, &args, &val, &size);

  if (size > 0)
  {
    for (i = 0; i < size; i++)
    {
      symbol = btor_get_symbol_exp (btor, node);
      id     = ((BtorUFNode *) node)->btor_id;
      // TODO: distinguish between functions and arrays (ma)
      //       needs proper sort handling
      fprintf (file, "%d[", id ? id : node->id);
      print_formatted_bv_btor (btor, base, args[i], file);
      fprintf (file, "] ");
      print_formatted_bv_btor (btor, base, val[i], file);
      fprintf (file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
      btor_freestr (btor->mm, args[i]);
      btor_freestr (btor->mm, val[i]);
    }
    btor_free (btor->mm, args, size * sizeof (*args));
    btor_free (btor->mm, val, size * sizeof (*val));
  }
}

static void
print_bv_or_bool_sort (BtorSort *sort, FILE *file)
{
  int len;

  if (BTOR_IS_BITVEC_SORT (sort))
    len = sort->bitvec.len;
  else
  {
    assert (BTOR_IS_BOOL_SORT (sort));
    len = 1;
  }
  fprintf (file, "(_ BitVec %d)", len);
}

static void
print_bv_or_bool_param (char *symbol,
                        int param_index,
                        BtorSort *sort,
                        FILE *file)
{
  fprintf (file, "(%s_x%d ", symbol, param_index);
  print_bv_or_bool_sort (sort, file);
  fprintf (file, ")");
}

static void
print_uf_assignment_smt2 (Btor *btor, BtorNode *node, int base, FILE *file)
{
  // FIXME: dumper currently too messy to be used for dumping the model
  // use dumper as soon as this is fixed?
  // BtorNode *lambda;
  // lambda = btor_generate_lambda_model_from_fun_model (
  //     btor, node, btor_get_fun_model (btor, node));
  // btor_dump_smt2_nodes (btor, file, &lambda, 1);

  assert (btor);
  assert (node);
  assert (((BtorUFNode *) node)->num_params >= 1);
  assert (file);

  BtorPtrHashTable *fun_model;
  BtorHashTableIterator it;
  BitVectorTuple *args;
  BitVector *val;
  BtorSort *sort;
  int x, i, n, len;
  char *symbol, *tmp;

  x         = 0;
  symbol    = btor_get_symbol_exp (btor, node);
  fun_model = (BtorPtrHashTable *) btor_get_fun_model (btor, node);

  fprintf (file, "  (define-fun ");
  fprintf (file, "%s (", symbol);

  /* args sorts */
  sort = ((BtorUFNode *) node)->sort;
  if (sort->fun.domain->kind != BTOR_TUPLE_SORT)
  {
    fprintf (file, "\n   ");
    print_bv_or_bool_param (symbol, x, sort->fun.domain, file);
  }
  else
  {
    for (i = 0; i < sort->fun.domain->tuple.num_elements; i++, x++)
    {
      fprintf (file, "\n   ");
      print_bv_or_bool_param (
          symbol, x, sort->fun.domain->tuple.elements[i], file);
    }
  }
  fprintf (file, ") ");
  print_bv_or_bool_sort (sort->fun.codomain, file);
  fprintf (file, "\n");

  /* model as ite over args -> assignments */
  n = 0;
  init_hash_table_iterator (&it, fun_model);
  while (has_next_hash_table_iterator (&it))
  {
    val  = it.bucket->data.asPtr;
    args = next_hash_table_iterator (&it);

    fprintf (file, "    (ite ");

    x = 0;
    if (args->arity > 1)
    {
      fprintf (file, "\n      (and ");
      for (i = 0; i < args->arity; i++, x++)
      {
        tmp = btor_bv_to_char_bv (btor, args->bv[i]);
        fprintf (file, "\n        (= %s_x%d ", symbol, x);
        print_formatted_bv_smt2 (btor, args->bv[i]->width, base, tmp, file);
        fprintf (file, ")%s", i + 1 == args->arity ? "" : " ");
        btor_freestr (btor->mm, tmp);
      }
      fprintf (file, ") ");
      fprintf (file, "\n      ");
    }
    else
    {
      tmp = btor_bv_to_char_bv (btor, args->bv[0]);
      fprintf (file, "(= %s_x%d ", symbol, x);
      print_formatted_bv_smt2 (btor, args->bv[0]->width, base, tmp, file);
      fprintf (file, ") ");
      btor_freestr (btor->mm, tmp);
    }
    tmp = btor_bv_to_char_bv (btor, val);
    print_formatted_bv_smt2 (btor, val->width, base, tmp, file);
    fprintf (file, "\n");
    btor_freestr (btor->mm, tmp);
    n += 1;
  }

  fprintf (file, "      ");
  len = val->width + 1;
  BTOR_NEWN (btor->mm, tmp, len);
  memset (tmp, '0', len - 1);
  tmp[len - 1] = 0;
  print_formatted_bv_smt2 (btor, val->width, base, tmp, file);
  BTOR_DELETEN (btor->mm, tmp, len);

  for (i = 0; i < n; i++) fprintf (file, ")");
  fprintf (file, ")\n");
}

static void
print_uf_assignment (
    Btor *btor, BtorNode *node, char *format, int base, FILE *file)
{
  assert (btor);
  assert (node);
  assert (format);

  if (!strcmp (format, "btor"))
    print_uf_assignment_btor (btor, node, base, file);
  else
    print_uf_assignment_smt2 (btor, node, base, file);
}

void
btor_print_model (Btor *btor, char *format, FILE *file)
{
  assert (btor);
  assert (format);
  assert (!strcmp (format, "btor") || !strcmp (format, "smt2"));
  assert (btor->last_sat_result == BTOR_SAT);
  assert (file);

  BtorNode *cur, *simp;
  BtorHashTableIterator it;
  int base;

  base = btor_get_opt_val (btor, BTOR_OPT_OUTPUT_NUMBER_FORMAT);

  if (!strcmp (format, "smt2")) fprintf (file, "(model\n");

  init_node_hash_table_iterator (&it, btor->inputs);
  while (has_next_node_hash_table_iterator (&it))
  {
    cur  = next_node_hash_table_iterator (&it);
    simp = btor_simplify_exp (btor, cur);
    if (BTOR_IS_FUN_NODE (BTOR_REAL_ADDR_NODE (simp)))
      print_uf_assignment (btor, cur, format, base, file);
    else
      print_bv_assignment (btor, cur, format, base, file);
  }

  if (!strcmp (format, "smt2")) fprintf (file, ")\n");
}
