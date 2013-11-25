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
