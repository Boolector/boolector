/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz, Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btordump.h"
#include "btorconst.h"
#include "btorexit.h"

#include <ctype.h>
#include <limits.h>

#define BTOR_ABORT_DUMP(cond, msg)                   \
  do                                                 \
  {                                                  \
    if (cond)                                        \
    {                                                \
      printf ("[btordump] %s: %s\n", __func__, msg); \
      fflush (stdout);                               \
      exit (BTOR_ERR_EXIT);                          \
    }                                                \
  } while (0)

#define BTOR_PUSH_NODE_IF_NOT_MARKED(e)          \
  do                                             \
  {                                              \
    BtorNode *child = BTOR_REAL_ADDR_NODE ((e)); \
    if (child->mark) break;                      \
    child->mark = 1;                             \
    BTOR_PUSH_STACK (mm, stack, child);          \
  } while (0)

static int
btor_cmp_node_id (const void *p, const void *q)
{
  BtorNode *a = *(BtorNode **) p;
  BtorNode *b = *(BtorNode **) q;
  return a->id - b->id;
}

/*------------------------------------------------------------------------*/
/* BTOR                                                                   */
/*------------------------------------------------------------------------*/

static void
dump_node (FILE *file, BtorNode *node)
{
  int i;
  char idbuffer[20];
  const char *op;

  node = BTOR_REAL_ADDR_NODE (node);

  switch (node->kind)
  {
    case BTOR_ADD_NODE: op = "add"; break;
    case BTOR_AND_NODE: op = "and"; break;
    case BTOR_CONCAT_NODE: op = "concat"; break;
    case BTOR_BCOND_NODE: op = "cond"; break;
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE: op = "eq"; break;
    case BTOR_MUL_NODE: op = "mul"; break;
    case BTOR_PROXY_NODE: op = "proxy"; break;
    case BTOR_READ_NODE: op = "read"; break;
    case BTOR_SLL_NODE: op = "sll"; break;
    case BTOR_SRL_NODE: op = "srl"; break;
    case BTOR_UDIV_NODE: op = "udiv"; break;
    case BTOR_ULT_NODE: op = "ult"; break;
    case BTOR_UREM_NODE: op = "urem"; break;
    case BTOR_SLICE_NODE: op = "slice"; break;
    case BTOR_ARRAY_VAR_NODE:
      op = "array";
      break;
      // NOTE: do not exist anymore
      //      case BTOR_WRITE_NODE:     op = "write"; break;
      //      case BTOR_ACOND_NODE:	op = "acond"; break;
    case BTOR_BV_CONST_NODE: op = "const"; break;
    case BTOR_PARAM_NODE: op = "param"; break;
    case BTOR_LAMBDA_NODE: op = "lambda"; break;
    case BTOR_APPLY_NODE: op = "apply"; break;
    case BTOR_ARGS_NODE: op = "args"; break;
    default: assert (node->kind == BTOR_BV_VAR_NODE); op = "var";
  }

  fprintf (file, "%d %s %d", node->id, op, node->len);

  /* print index bit width of arrays */
  if (BTOR_IS_ARRAY_NODE (node)) fprintf (file, " %d", node->index_len);

  /* print children or const values */
  if (BTOR_IS_BV_CONST_NODE (node))
    fprintf (file, " %s", node->bits);
  else if (BTOR_IS_PROXY_NODE (node))
    fprintf (file, " %d", BTOR_GET_ID_NODE (node->simplified));
  else
    for (i = 0; i < node->arity; i++)
      fprintf (file, " %d", BTOR_GET_ID_NODE (node->e[i]));

  /* print slice limits/var symbols */
  if (node->kind == BTOR_SLICE_NODE)
    fprintf (file, " %d %d", node->upper, node->lower);
  else if (BTOR_IS_BV_VAR_NODE (node) || BTOR_IS_ARRAY_VAR_NODE (node))
  {
    sprintf (idbuffer, "%d", node->id);
    assert (node->symbol);
    if (strcmp (node->symbol, idbuffer)) fprintf (file, " %s", node->symbol);
  }
  fputc ('\n', file);
}

#if 0
static void
dump_node (FILE *file, BtorNode *node)
{
  int j;
  char idbuffer[20];
  const char *op;
  BtorNode *n;


  n = BTOR_REAL_ADDR_NODE (node);
  fprintf (file, "%d ", n->id);

  switch (n->kind)
    {
    case BTOR_ADD_NODE:
      op = "add";
      goto PRINT;
    case BTOR_AND_NODE:
      op = "and";
      goto PRINT;
    case BTOR_CONCAT_NODE:
      op = "concat";
      goto PRINT;
    case BTOR_BCOND_NODE:
      op = "cond";
      goto PRINT;
    case BTOR_BEQ_NODE:
    case BTOR_AEQ_NODE:
      op = "eq";
      goto PRINT;
    case BTOR_MUL_NODE:
      op = "mul";
      goto PRINT;
    case BTOR_PROXY_NODE:
      op = "proxy";
      goto PRINT;
    case BTOR_READ_NODE:
      op = "read";
      goto PRINT;
    case BTOR_SLL_NODE:
      op = "sll";
      goto PRINT;
    case BTOR_SRL_NODE:
      op = "srl";
      goto PRINT;
    case BTOR_UDIV_NODE:
      op = "udiv";
      goto PRINT;
    case BTOR_ULT_NODE:
      op = "ult";
      goto PRINT;
    case BTOR_UREM_NODE:
      op = "urem";
    PRINT:
      fputs (op, file);
      fprintf (file, " %d", n->len);

      if (n->kind == BTOR_PROXY_NODE)
	fprintf (file, " %d", BTOR_GET_ID_NODE (n->simplified));
      else
	for (j = 0; j < n->arity; j++)
	  fprintf (file, " %d", BTOR_GET_ID_NODE (n->e[j]));
      break;

    case BTOR_SLICE_NODE:
      fprintf (file,
	       "slice %d %d %d %d",
	       n->len,
	       BTOR_GET_ID_NODE (n->e[0]), n->upper, n->lower);
      break;

    case BTOR_ARRAY_VAR_NODE:
      fprintf (file, "array %d %d", n->len, n->index_len);
      break;

    case BTOR_WRITE_NODE:
      fprintf (file, "write %d %d %d %d %d", n->len, n->index_len,
	       BTOR_GET_ID_NODE (n->e[0]), BTOR_GET_ID_NODE (n->e[1]),
	       BTOR_GET_ID_NODE (n->e[2]));
      break;

    case BTOR_ACOND_NODE:
      fprintf (file, "acond %d %d %d %d %d", n->len, n->index_len,
	       BTOR_GET_ID_NODE (n->e[0]), BTOR_GET_ID_NODE (n->e[1]),
	       BTOR_GET_ID_NODE (n->e[2]));
      break;

    case BTOR_BV_CONST_NODE:
      fprintf (file, "const %d %s", n->len, n->bits);
      break;

    case BTOR_PARAM_NODE:
      fprintf (file, "param %d", n->len);
      break;

    case BTOR_LAMBDA_NODE:
      fprintf (file, "lambda %d %d %d %d", n->len, n->index_len,
	       BTOR_GET_ID_NODE (n->e[0]), BTOR_GET_ID_NODE (n->e[1]));
      break;

    default:
      assert (n->kind == BTOR_BV_VAR_NODE);
      fprintf (file, "var %d", n->len);
      sprintf (idbuffer, "%d", n->id);
      assert (n->symbol);
      if (strcmp (n->symbol, idbuffer))
	fprintf (file, " %s", n->symbol);
      break;
    }

  fputc ('\n', file);
}
#endif

static void
dump_exps (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  BtorMemMgr *mm = btor->mm;
  int i, id = 0, maxid;
  BtorNodePtrStack work_stack, stack;
  BtorNodePtrStack const_stack, param_stack, bvvar_stack, avar_stack;
  BtorIntStack id_stack;
  BtorNode *root, *cur = 0;

  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots > 0);
  assert (mm);

  BTOR_INIT_STACK (work_stack);
  BTOR_INIT_STACK (stack);

  maxid = 0;

  if (btor->pprint)
  {
    BTOR_INIT_STACK (const_stack);
    BTOR_INIT_STACK (bvvar_stack);
    BTOR_INIT_STACK (avar_stack);
    BTOR_INIT_STACK (param_stack);
    BTOR_INIT_STACK (id_stack);
  }

  for (i = 0; i < nroots; i++)
  {
    root = roots[i];
    assert (root);
    BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (root));
  }

  while (!BTOR_EMPTY_STACK (work_stack))
  {
    cur = BTOR_POP_STACK (work_stack);
    assert (BTOR_IS_REGULAR_NODE (cur));

    if (cur->mark == 2) continue;

    if (cur->mark == 0)
    {
      cur->mark = 1;
      BTOR_PUSH_STACK (mm, work_stack, cur);
      for (i = 0; i < cur->arity; i++)
        BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (cur->e[i]));
      // TODO: debug
      if (cur->simplified)
        BTOR_PUSH_STACK (mm, work_stack, BTOR_REAL_ADDR_NODE (cur->simplified));
    }
    else
    {
      cur->mark = 2;
      if (btor->pprint)
      {
        switch (cur->kind)
        {
          case BTOR_BV_CONST_NODE:
            BTOR_PUSH_STACK (mm, const_stack, cur);
            break;
          case BTOR_BV_VAR_NODE: BTOR_PUSH_STACK (mm, bvvar_stack, cur); break;
          case BTOR_ARRAY_VAR_NODE:
            BTOR_PUSH_STACK (mm, avar_stack, cur);
            break;
          case BTOR_PARAM_NODE: BTOR_PUSH_STACK (mm, param_stack, cur); break;
          default: BTOR_PUSH_STACK (mm, stack, cur);
        }
      }
      else
        BTOR_PUSH_STACK (mm, stack, cur);
    }
  }

  BTOR_RELEASE_STACK (mm, work_stack);

  if (btor->pprint)
  {
    /* unmark and assign ids in order of DFS traversal - var, const and param
     * nodes are sorted by original id and dumped first */
    if (const_stack.start)
      qsort (const_stack.start,
             BTOR_COUNT_STACK (const_stack),
             sizeof cur,
             btor_cmp_node_id);
    if (bvvar_stack.start)
      qsort (bvvar_stack.start,
             BTOR_COUNT_STACK (bvvar_stack),
             sizeof cur,
             btor_cmp_node_id);
    if (avar_stack.start)
      qsort (avar_stack.start,
             BTOR_COUNT_STACK (avar_stack),
             sizeof cur,
             btor_cmp_node_id);
    if (param_stack.start)
      qsort (param_stack.start,
             BTOR_COUNT_STACK (param_stack),
             sizeof cur,
             btor_cmp_node_id);

    for (i = 0; i < BTOR_COUNT_STACK (const_stack); i++)
    {
      const_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, const_stack.start[i]->id);
      const_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (bvvar_stack); i++)
    {
      bvvar_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, bvvar_stack.start[i]->id);
      bvvar_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (avar_stack); i++)
    {
      avar_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, avar_stack.start[i]->id);
      avar_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (param_stack); i++)
    {
      param_stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, param_stack.start[i]->id);
      param_stack.start[i]->id = ++id;
    }
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
    {
      stack.start[i]->mark = 0;
      BTOR_PUSH_STACK (mm, id_stack, stack.start[i]->id);
      stack.start[i]->id = ++id;
    }

    maxid = id;
  }
  else
  {
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;
    if (stack.start)
      qsort (
          stack.start, BTOR_COUNT_STACK (stack), sizeof cur, btor_cmp_node_id);
    if (BTOR_COUNT_STACK (stack))
      maxid = stack.start[BTOR_COUNT_STACK (stack) - 1]->id;
  }

  if (btor->pprint)
  {
    for (i = 0; i < BTOR_COUNT_STACK (const_stack); i++)
    {
      cur = const_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
    for (i = 0; i < BTOR_COUNT_STACK (bvvar_stack); i++)
    {
      cur = bvvar_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
    for (i = 0; i < BTOR_COUNT_STACK (avar_stack); i++)
    {
      cur = avar_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
    for (i = 0; i < BTOR_COUNT_STACK (param_stack); i++)
    {
      cur = param_stack.start[i];
      assert (BTOR_IS_REGULAR_NODE (cur));
      dump_node (file, cur);
    }
  }
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    cur = stack.start[i];
    assert (BTOR_IS_REGULAR_NODE (cur));
    dump_node (file, cur);
  }

  for (i = 0; i < nroots; i++)
  {
    id = maxid + i;
    BTOR_ABORT_DUMP (id == INT_MAX, "expression id overflow");
    fprintf (
        file, "%d root %d %d\n", id + 1, cur->len, BTOR_GET_ID_NODE (roots[i]));
  }

  if (btor->pprint)
  {
    /* reassign original ids */
    for (i = 0; i < BTOR_COUNT_STACK (const_stack); i++)
      const_stack.start[i]->id = id_stack.start[const_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (bvvar_stack); i++)
      bvvar_stack.start[i]->id = id_stack.start[bvvar_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (avar_stack); i++)
      avar_stack.start[i]->id = id_stack.start[avar_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (param_stack); i++)
      param_stack.start[i]->id = id_stack.start[param_stack.start[i]->id - 1];
    for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
      stack.start[i]->id = id_stack.start[stack.start[i]->id - 1];
  }

  BTOR_RELEASE_STACK (mm, stack);
  if (btor->pprint)
  {
    BTOR_RELEASE_STACK (mm, const_stack);
    BTOR_RELEASE_STACK (mm, bvvar_stack);
    BTOR_RELEASE_STACK (mm, avar_stack);
    BTOR_RELEASE_STACK (mm, param_stack);
    BTOR_RELEASE_STACK (mm, id_stack);
  }
}

void
btor_dump_exps (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
#ifndef NDEBUG
  int i;
  assert (btor);
  assert (file);
  for (i = 0; i < nroots; i++) assert (roots[i]);
#endif

  BtorNode *tmp;

  if (nroots == 0)
  {
    tmp = btor_true_exp (btor);
    btor_dump_exp (btor, file, tmp);
    btor_release_exp (btor, tmp);
  }
  else
    dump_exps (btor, file, roots, nroots);
}

void
btor_dump_exp (Btor *btor, FILE *file, BtorNode *root)
{
  assert (btor);
  assert (file);
  assert (root);
  dump_exps (btor, file, &root, 1);
}

/*------------------------------------------------------------------------*/
/* SMT                                                                    */
/*------------------------------------------------------------------------*/

static void
btor_dump_smt_id (BtorNode *e, const char *symgenprefix, FILE *file)
{
  const char *type, *sym;
  BtorNode *u;

  u = BTOR_REAL_ADDR_NODE (e);

  if (u != e) fputs ("(bvnot ", file);

  if (BTOR_IS_BV_VAR_NODE (u) || BTOR_IS_PARAM_NODE (u))
  {
    sym = u->symbol;
    if (!isdigit (sym[0]))
    {
      fputs (sym, file);
      goto CLOSE;
    }

    type = "v";
  }
  else if (BTOR_IS_ARRAY_VAR_NODE (u))
    type = "a";
  else
    type = symgenprefix;

  fprintf (file, "%s%d", type, u ? u->id : -1);

CLOSE:
  if (u != e) fputc (')', file);
}

static void
btor_dump_bit_smt (int format, int bit, FILE *file)
{
  assert (bit == 0 || bit == 1);
  if (format < 2)
    fprintf (file, "bv%d[1]", bit);
  else
    fprintf (file, "#b%d", bit);
}

static void
btor_dump_exp_smt (
    Btor *btor, BtorNode *e, const char *sgp, int format, FILE *file)
{
  assert (btor);
  assert (e);
  assert (sgp);

  int pad, i;
  char *tmp;
  const char *op;
  BtorMemMgr *mm = btor->mm;

  // TODO: function application handling
  if (BTOR_IS_PARAM_NODE (e) || BTOR_IS_LAMBDA_NODE (e))
  {
    btor_dump_smt_id (e, sgp, file);
  }
  else if (e->kind == BTOR_BV_CONST_NODE)
  {
    tmp = btor_const_to_decimal (mm, e->bits);
    if (format < 2)
      fprintf (file, "bv%s[%d]", tmp, e->len);
    else
      fprintf (file, "(_ bv%s %d)", tmp, e->len);
    btor_freestr (mm, tmp);
  }
  else if (e->kind == BTOR_SLICE_NODE)
  {
    if (format < 2)
      fprintf (file, "(extract[%d:%d] ", e->upper, e->lower);
    else
      fprintf (file, "((_ extract %d %d) ", e->upper, e->lower);

    btor_dump_smt_id (e->e[0], sgp, file);
    fputc (')', file);
  }
  else if (e->kind == BTOR_SLL_NODE || e->kind == BTOR_SRL_NODE)
  {
    fputc ('(', file);

    if (e->kind == BTOR_SRL_NODE)
      fputs ("bvlshr", file);
    else
      fputs ("bvshl", file);

    fputc (' ', file);
    btor_dump_smt_id (e->e[0], sgp, file);
    fputc (' ', file);

    assert (e->len > 1);
    pad = e->len - BTOR_REAL_ADDR_NODE (e->e[1])->len;

    if (format < 2)
      fprintf (file, " (zero_extend[%d] ", pad);
    else
      fprintf (file, " ((_ zero_extend %d) ", pad);

    btor_dump_smt_id (e->e[1], sgp, file);

    fputs ("))", file);
  }
  else if (BTOR_IS_ARRAY_OR_BV_COND_NODE (e))
  {
    fputs ("(ite (= ", file);
    btor_dump_bit_smt (format, 1, file);
    fputc (' ', file);
    btor_dump_smt_id (e->e[0], sgp, file);
    fputs (") ", file);
    btor_dump_smt_id (e->e[1], sgp, file);
    fputc (' ', file);
    btor_dump_smt_id (e->e[2], sgp, file);
    fputc (')', file);
  }
  else if (BTOR_IS_ARRAY_OR_BV_EQ_NODE (e) || e->kind == BTOR_ULT_NODE)
  {
    fputs ("(ite (", file);
    if (e->kind == BTOR_ULT_NODE)
      fputs ("bvult", file);
    else
      fputc ('=', file);
    fputc (' ', file);
    btor_dump_smt_id (e->e[0], sgp, file);
    fputc (' ', file);
    btor_dump_smt_id (e->e[1], sgp, file);
    fputs (") ", file);
    btor_dump_bit_smt (format, 1, file);
    fputc (' ', file);
    btor_dump_bit_smt (format, 0, file);
    fputc (')', file);
  }
  else
  {
    fputc ('(', file);

    switch (e->kind)
    {
      case BTOR_AND_NODE: op = "bvand"; break;
      case BTOR_ADD_NODE: op = "bvadd"; break;
      case BTOR_MUL_NODE: op = "bvmul"; break;
      case BTOR_UDIV_NODE: op = "bvudiv"; break;
      case BTOR_UREM_NODE: op = "bvurem"; break;
      case BTOR_CONCAT_NODE: op = "concat"; break;
      case BTOR_READ_NODE: op = "select"; break;

      default:
      case BTOR_WRITE_NODE:
        assert (e->kind == BTOR_WRITE_NODE);
        op = "store";
        break;
    }

    fputs (op, file);

    for (i = 0; i < e->arity; i++)
    {
      fputc (' ', file);
      btor_dump_smt_id (e->e[i], sgp, file);
    }

    fputc (')', file);
  }
}

static void
btor_dump_sort_smt2 (BtorNode *e, FILE *file)
{
  assert (e);
  assert (file);

  e = BTOR_REAL_ADDR_NODE (e);

  if (BTOR_IS_ARRAY_NODE (e) && !BTOR_IS_LAMBDA_NODE (e))
    fprintf (file, "(Array (_ BitVec %d) (_ BitVec %d))", e->index_len, e->len);
  //  else if (e->len == 1)
  //    fprintf (file, "Bool");
  else if (e)
    fprintf (file, "(_ BitVec %d)", e->len);
}

static void
btor_dump_fun_let_smt2 (Btor *btor, BtorNode *e, const char *sgp, FILE *file)
{
  assert (btor);
  assert (e);
  assert (sgp);
  assert (file);

  fputs ("(define-fun ", file);
  btor_dump_smt_id (e, sgp, file);
  fputs (" () ", file);
  btor_dump_sort_smt2 (e, file);
  fputc (' ', file);
  btor_dump_exp_smt (btor, e, sgp, 2, file);
  fputs (")\n", file);
}

static void
btor_dump_declare_fun_smt2 (BtorNode *e, const char *sgp, FILE *file)
{
  fputs ("(declare-fun ", file);
  btor_dump_smt_id (e, sgp, file);
  fputs (" () ", file);
  btor_dump_sort_smt2 (e, file);
  fputs (")\n", file);
}

static void
btor_dump_let_smt (
    Btor *btor, BtorNode *e, const char *sgp, int format, FILE *file)
{
  assert (btor);
  assert (e);
  assert (sgp);
  assert (file);

  fputs ("(let (", file);
  if (format >= 2) fputc ('(', file);
  btor_dump_smt_id (e, sgp, file);
  fputc (' ', file);

  btor_dump_exp_smt (btor, e, sgp, format, file);

  if (format >= 2) fputc (')', file);
  fputs (")\n", file);
}

static void
btor_dump_fun_smt2 (Btor *btor, FILE *file, BtorNode *fun)
{
  assert (btor);
  assert (file);
  assert (fun);

  int i, next, lets;
  const char *sgp = "$e";
  BtorNode *e, *child;
  BtorMemMgr *mm = btor->mm;
  BtorNodePtrStack stack, params, not_param;

  next = 0;
  BTOR_INIT_STACK (stack);
  BTOR_INIT_STACK (params);
  BTOR_INIT_STACK (not_param);
  BTOR_PUSH_STACK (mm, stack, fun);
  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];
    assert (BTOR_IS_REGULAR_NODE (e));

    for (i = 0; i < e->arity; i++)
    {
      child = BTOR_REAL_ADDR_NODE (e->e[i]);

      if (child->aux_mark || child->mark) continue;

      if (!child->parameterized && child->arity > 0)
      {
        BTOR_PUSH_STACK (mm, not_param, child);
      }

      child->aux_mark = 1;
      BTOR_PUSH_STACK (mm, stack, child);
    }
  }

  if (not_param.start)
    qsort (not_param.start,
           BTOR_COUNT_STACK (not_param),
           sizeof e,
           btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (not_param); i++)
  {
    e = not_param.start[i];
    assert (!e->mark);

    btor_dump_fun_let_smt2 (btor, e, sgp, file);
    e->mark = 1;
  }

  fputs ("(define-fun ", file);
  btor_dump_smt_id (fun, sgp, file);
  fputs (" (", file);
  /* dump parameters */
  e = fun;
  while (BTOR_IS_LAMBDA_NODE (e))
  {
    child = e->e[0];
    assert (BTOR_IS_REGULAR_NODE (child));
    assert (BTOR_IS_PARAM_NODE (child));
    fputc ('(', file);
    btor_dump_smt_id (child, sgp, file);
    fputc (' ', file);
    btor_dump_sort_smt2 (child, file);
    e = BTOR_REAL_ADDR_NODE (e->e[1]);
    fputc (')', file);
    if (BTOR_IS_LAMBDA_NODE (e)) fputc (' ', file);
    child->mark = 1;
  }
  fputs (") ", file);
  btor_dump_sort_smt2 (fun, file);
  fputs ("\n", file);

  lets = 0;
  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof e, btor_cmp_node_id);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];
    assert (e);
    assert (BTOR_IS_REGULAR_NODE (e));

    if (BTOR_IS_PARAM_NODE (e) || e->mark || BTOR_IS_LAMBDA_NODE (e)) continue;

    if (e == BTOR_REAL_ADDR_NODE (fun->e[1])) break;

    lets++;
    btor_dump_let_smt (btor, e, sgp, 2, file);
    e->mark = 1;
  }

  btor_dump_exp_smt (btor, fun->e[1], sgp, 2, file);
  BTOR_REAL_ADDR_NODE (fun->e[1])->mark = 1;

  for (i = 0; i < lets; i++) fputc (')', file);

  fputs (")\n", file);

  fun->mark = 1;

  BTOR_RELEASE_STACK (mm, not_param);
  BTOR_RELEASE_STACK (mm, params);
  BTOR_RELEASE_STACK (mm, stack);
}

void
btor_dump_smt2_fun (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots);

  const char *sgp = "$e";
  int next, i;
  BtorMemMgr *mm = btor->mm;
  BtorNodePtrStack stack, consts, vars, arrays, lambdas;
  BtorNode *e;
  char *tmp;

  BTOR_INIT_STACK (stack);
  for (i = 0; i < nroots; i++) BTOR_PUSH_NODE_IF_NOT_MARKED (roots[i]);

  next = 0;

  BTOR_INIT_STACK (consts);
  BTOR_INIT_STACK (vars);
  BTOR_INIT_STACK (arrays);
  BTOR_INIT_STACK (lambdas);

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_NODE (e));
    assert (e->mark);

    if (BTOR_IS_BV_CONST_NODE (e))
    {
      BTOR_PUSH_STACK (mm, consts, e);
      continue;
    }

    if (BTOR_IS_BV_VAR_NODE (e))
    {
      BTOR_PUSH_STACK (mm, vars, e);
      continue;
    }

    if (BTOR_IS_ARRAY_VAR_NODE (e))
    {
      BTOR_PUSH_STACK (mm, arrays, e);
      continue;
    }

    if (BTOR_IS_LAMBDA_NODE (e)) BTOR_PUSH_STACK (mm, lambdas, e);

    for (i = 0; i < e->arity; i++) BTOR_PUSH_NODE_IF_NOT_MARKED (e->e[i]);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;

  if (BTOR_COUNT_STACK (arrays))
    fputs ("(set-logic QF_AUFBV)\n", file);
  else
    fputs ("(set-logic QF_BV)\n", file);

  if (consts.start)
    qsort (consts.start, BTOR_COUNT_STACK (consts), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (consts); i++)
  {
    e = consts.start[i];
    assert (!e->mark);
    tmp = btor_const_to_decimal (mm, e->bits);
    fputs ("(define-fun ", file);
    btor_dump_smt_id (e, sgp, file);
    fprintf (file, " () ");
    btor_dump_sort_smt2 (e, file);
    fprintf (file, " (_ bv%s %d))\n", tmp, e->len);
    btor_freestr (mm, tmp);
    e->mark = 1;
  }

  if (vars.start)
    qsort (vars.start, BTOR_COUNT_STACK (vars), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (vars); i++)
  {
    e = vars.start[i];
    assert (!e->mark);
    btor_dump_declare_fun_smt2 (e, sgp, file);
    e->mark = 1;
  }

  if (arrays.start)
    qsort (arrays.start, BTOR_COUNT_STACK (arrays), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (arrays); i++)
  {
    e = arrays.start[i];
    assert (!e->mark);
    btor_dump_declare_fun_smt2 (e, sgp, file);
    e->mark = 1;
  }

  if (lambdas.start)
    qsort (
        lambdas.start, BTOR_COUNT_STACK (lambdas), sizeof e, btor_cmp_node_id);

  for (i = 0; i < BTOR_COUNT_STACK (lambdas); i++)
  {
    e = lambdas.start[i];
    assert (!e->mark);
    btor_dump_fun_smt2 (btor, file, e);
    e->mark = 1;
  }

  if (stack.start)
    qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof e, btor_cmp_node_id);
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_NODE (e));

    if (!e || BTOR_IS_BV_VAR_NODE (e) || BTOR_IS_ARRAY_VAR_NODE (e) || e->mark)
      continue;

    btor_dump_fun_let_smt2 (btor, e, sgp, file);
  }

  /* dump asserts */
  for (i = 0; i < nroots; i++)
  {
    assert (BTOR_REAL_ADDR_NODE (roots[i])->len == 1);
    fputs ("(assert ", file);
    btor_dump_smt_id (roots[i], sgp, file);
    fputs (")\n", file);
  }

  BTOR_RELEASE_STACK (mm, stack);
  BTOR_RELEASE_STACK (mm, consts);
  BTOR_RELEASE_STACK (mm, vars);
  BTOR_RELEASE_STACK (mm, arrays);
  BTOR_RELEASE_STACK (mm, lambdas);

  fputs ("(check-sat)\n", file);
  fputs ("(exit)\n", file);

  fflush (file);
}

#define WRAP_NON_BOOL_ROOT(e)                                     \
  do                                                              \
  {                                                               \
    fputs ("(not (= ", file);                                     \
    btor_dump_smt_id (e, sgp, file);                              \
    if (format < 2)                                               \
      fprintf (file, " bv0[%d]))", BTOR_REAL_ADDR_NODE (e)->len); \
    else                                                          \
      fprintf (file, " #b0))");                                   \
  } while (0)

static void
btor_dump_smt (Btor *btor, int format, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor);
  assert (file);
  assert (roots);
  assert (nroots >= 1);
  assert (format == 1 || format == 2);

  const char *sgp = (format < 2) ? "?e" : "$e";
  int next, i, arrays, open_left_par;
  BtorMemMgr *mm = btor->mm;
  BtorNodePtrStack stack;
  BtorNode *e, **p;

  BTOR_INIT_STACK (stack);
  for (i = 0; i < nroots; i++) BTOR_PUSH_NODE_IF_NOT_MARKED (roots[i]);

  arrays = 0;
  next   = 0;

  while (next < BTOR_COUNT_STACK (stack))
  {
    e = stack.start[next++];

    assert (BTOR_IS_REGULAR_NODE (e));
    assert (e->mark);

    if (BTOR_IS_BV_CONST_NODE (e)) continue;

    if (BTOR_IS_BV_VAR_NODE (e)) continue;

    if (BTOR_IS_ARRAY_VAR_NODE (e))
    {
      arrays = 1;
      continue;
    }

    for (i = 0; i < e->arity; i++) BTOR_PUSH_NODE_IF_NOT_MARKED (e->e[i]);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++) stack.start[i]->mark = 0;

  qsort (stack.start, BTOR_COUNT_STACK (stack), sizeof e, btor_cmp_node_id);

  if (format < 2)
  {
    fputs ("(benchmark ", file);
    if (BTOR_IS_INVERTED_NODE (roots[0])) fputs ("not", file);
    fprintf (file, "root%d\n", BTOR_REAL_ADDR_NODE (roots[0])->id);

    if (arrays)
      fputs (":logic QF_AUFBV\n", file);
    else
      fputs (":logic QF_BV\n", file);
  }
  else
  {
    if (arrays)
      fputs ("(set-logic QF_AUFBV)\n", file);
    else
      fputs ("(set-logic QF_BV)\n", file);
  }

  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_NODE (e));

    if (!BTOR_IS_BV_VAR_NODE (e) && !BTOR_IS_ARRAY_VAR_NODE (e)) continue;

    if (format < 2)
    {
      fputs (":extrafuns ((", file);

      btor_dump_smt_id (e, sgp, file);

      if (BTOR_IS_BV_VAR_NODE (e))
        fprintf (file, " BitVec[%d]))\n", e->len);
      else
        fprintf (file, " Array[%d:%d]))\n", e->index_len, e->len);
    }
    else
      btor_dump_declare_fun_smt2 (e, sgp, file);
  }

  if (format < 2)
    fputs (":formula\n", file);
  else
    fputs ("(assert\n", file);

  open_left_par = 0;
  for (i = 0; i < BTOR_COUNT_STACK (stack); i++)
  {
    e = stack.start[i];

    assert (BTOR_IS_REGULAR_NODE (e));

    if (!e || BTOR_IS_BV_VAR_NODE (e) || BTOR_IS_ARRAY_VAR_NODE (e)) continue;

    open_left_par++;
    btor_dump_let_smt (btor, e, sgp, format, file);
  }

  for (i = 0; i < nroots - 1; i++)
  {
    e = roots[i];
    fputs (" (and ", file);
    if (BTOR_REAL_ADDR_NODE (e)->len > 1)
      WRAP_NON_BOOL_ROOT (e);
    else
      btor_dump_smt_id (e, sgp, file);
    open_left_par++;
  }
  fputc (' ', file);

  e = roots[nroots - 1];
  WRAP_NON_BOOL_ROOT (e);

  for (i = 0; i < open_left_par + 1; i++) fputc (')', file);

  fputc ('\n', file);

  for (p = stack.start; p < stack.top; p++)
  {
    e = *p;
    assert (e);
    e->mark     = 0;
    e->aux_mark = 0;
  }

  BTOR_RELEASE_STACK (mm, stack);

  if (format >= 2)
  {
    fputs ("(check-sat)\n", file);
    fputs ("(exit)\n", file);
  }

  fflush (file);
}

void
btor_dump_smt1 (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  BtorNode *tmp;

  if (nroots == 0)
  {
    tmp = btor_true_exp (btor);
    btor_dump_smt (btor, 1, file, &tmp, 1);
    btor_release_exp (btor, tmp);
  }
  else
    btor_dump_smt (btor, 1, file, roots, nroots);
}

void
btor_dump_smt2 (Btor *btor, FILE *file, BtorNode **roots, int nroots)
{
  assert (btor->lambdas->count == 0u);  // TODO: force define-fun dumps?
  BtorNode *tmp;

  if (nroots == 0)
  {
    tmp = btor_true_exp (btor);
    btor_dump_smt (btor, 2, file, &tmp, 1);
    btor_release_exp (btor, tmp);
  }
  else
    btor_dump_smt (btor, 2, file, roots, nroots);
}
