#include "simplifier/btorfeq.h"
#include "btorsort.h"
#include "utils/btoriter.h"
#include "utils/btormem.h"

BtorNode *
btor_rewrite_function_inequality (Btor *btor, BtorNode *feq)
{
  assert (BTOR_IS_REGULAR_NODE (feq));
  assert (BTOR_IS_FEQ_NODE (feq));

  BtorMemMgr *mm;
  BtorNode *var, *app0, *app1, *eq;
  BtorSortUniqueTable *sorts;
  BtorSortId funsort, sort;
  BtorNodePtrStack args;
  BtorTupleSortIterator it;

  BTOR_INIT_STACK (args);

  mm      = btor->mm;
  sorts   = &btor->sorts_unique_table;
  funsort = btor_get_domain_fun_sort (sorts, feq->e[0]->sort_id);

  btor_init_tuple_sort_iterator (&it, sorts, funsort);
  while (btor_has_next_tuple_sort_iterator (&it))
  {
    sort = btor_next_tuple_sort_iterator (&it);
    assert (btor_is_bitvec_sort (sorts, sort));
    var = btor_var_exp (btor, btor_get_width_bitvec_sort (sorts, sort), 0);
    BTOR_PUSH_STACK (mm, args, var);
  }

  app0 = btor_apply_exps (btor, BTOR_COUNT_STACK (args), args.start, feq->e[0]);
  app1 = btor_apply_exps (btor, BTOR_COUNT_STACK (args), args.start, feq->e[1]);
  eq   = btor_eq_exp (btor, app0, app1);

  btor_release_exp (btor, app0);
  btor_release_exp (btor, app1);
  while (!BTOR_EMPTY_STACK (args))
    btor_release_exp (btor, BTOR_POP_STACK (args));
  BTOR_RELEASE_STACK (mm, args);

  return BTOR_INVERT_NODE (eq);
}

void
btor_rewrite_function_inequalities (Btor *btor)
{
  assert (btor->varsubst_constraints->count == 0);
  assert (btor->embedded_constraints->count == 0);

  unsigned num_pos = 0, num_neg = 0;
  int i, pos;
  BtorNode *cur, *par, *real_par, *eq, *e[3], *subst;
  BtorNodeIterator it, pit;
  BtorNodePtrStack feqs;
  BtorPtrHashTable *ctable;

  BTOR_INIT_STACK (feqs);

  init_unique_table_iterator (btor, &it);
  while (has_next_unique_table_iterator (&it))
  {
    cur = next_unique_table_iterator (&it);
    if (!BTOR_IS_FEQ_NODE (cur)) continue;
    BTOR_PUSH_STACK (btor->mm, feqs, cur);
  }

  btor_init_substitutions (btor);
  while (!BTOR_EMPTY_STACK (feqs))
  {
    cur = BTOR_POP_STACK (feqs);

    init_full_parent_iterator (&pit, cur);
    while (has_next_parent_full_parent_iterator (&pit))
    {
      par      = pit.cur;
      real_par = next_parent_full_parent_iterator (&pit);
      pos      = BTOR_GET_TAG_NODE (par);
      assert (cur == BTOR_REAL_ADDR_NODE (real_par->e[pos]));

      /* occurs positively */
      if (!BTOR_IS_INVERTED_NODE (real_par->e[pos]))
      {
        num_pos++;
        continue;
      }

      eq = btor_rewrite_function_inequality (btor, cur);
      for (i = 0; i < real_par->arity; i++) e[i] = real_par->e[i];
      e[pos] = eq;
      subst  = btor_create_exp (btor, real_par->kind, real_par->arity, e);
      /* real_par may be inserted multiple times if more than one negative
       * function eq is in real_par->e */
      btor_insert_substitution (btor, real_par, subst, 1);
      btor_release_exp (btor, eq);
      btor_release_exp (btor, subst);
    }

    if (!cur->constraint) continue;

    /* occurs as positive constraint */
    if (btor_find_in_ptr_hash_table (btor->unsynthesized_constraints, cur)
        || btor_find_in_ptr_hash_table (btor->synthesized_constraints, cur))
    {
      num_pos++;
      continue;
    }

    eq = btor_rewrite_function_inequality (btor, cur);
    if (btor_find_in_ptr_hash_table (btor->unsynthesized_constraints,
                                     BTOR_INVERT_NODE (cur)))
    {
      ctable = btor->unsynthesized_constraints;
    }
    else
    {
      assert (btor_find_in_ptr_hash_table (btor->synthesized_constraints,
                                           BTOR_INVERT_NODE (cur)));
      ctable = btor->synthesized_constraints;
    }
    btor_remove_from_ptr_hash_table (ctable, BTOR_INVERT_NODE (cur), 0, 0);
    btor_insert_in_ptr_hash_table (ctable, eq);
    BTOR_REAL_ADDR_NODE (eq)->constraint = 1;
    btor_release_exp (btor, cur);
  }

  BTOR_RELEASE_STACK (btor->mm, feqs);
  num_neg = btor->substitutions->count;
  btor_substitute_and_rebuild (btor, btor->substitutions, 0);
  btor_delete_substitutions (btor);
  BTOR_MSG (btor->msg,
            1,
            "eliminated %u function inequalities (%u positive)",
            num_neg,
            num_pos);
}
