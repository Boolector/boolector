/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2014-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btornodeiter.h"

/*------------------------------------------------------------------------*/
/* node iterators					                  */
/*------------------------------------------------------------------------*/

void
btor_iter_apply_parent_init (BtorNodeIterator *it, const BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = btor_node_real_addr (btor_node_real_addr (exp)->last_parent);
}

bool
btor_iter_apply_parent_has_next (const BtorNodeIterator *it)
{
  assert (it);
  assert (btor_node_is_regular (it->cur));
  /* function child of apply is at position 0, so cur is not tagged */
  return it->cur && btor_node_is_apply (it->cur);
}

BtorNode *
btor_iter_apply_parent_next (BtorNodeIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = btor_node_real_addr (BTOR_PREV_PARENT (result));
  assert (btor_node_is_regular (result));
  assert (btor_node_is_apply (result));
  return result;
}

/*------------------------------------------------------------------------*/

void
btor_iter_parent_init (BtorNodeIterator *it, const BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = btor_node_real_addr (exp)->first_parent;
}

bool
btor_iter_parent_has_next (const BtorNodeIterator *it)
{
  assert (it);
  return it->cur != 0;
}

BtorNode *
btor_iter_parent_next (BtorNodeIterator *it)
{
  assert (it);

  BtorNode *result;
  result = it->cur;
  assert (result);
  it->cur = BTOR_NEXT_PARENT (result);

  return btor_node_real_addr (result);
}

/*------------------------------------------------------------------------*/

void
btor_iter_args_init (BtorArgsIterator *it, const BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_args (exp));

  it->pos = 0;
  it->exp = exp;
  it->cur = exp->e[0];
}

bool
btor_iter_args_has_next (const BtorArgsIterator *it)
{
  assert (it);
  return it->cur != 0;
}

BtorNode *
btor_iter_args_next (BtorArgsIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;

  result = it->cur;

  /* end of this args node, continue with next */
  if (btor_node_is_args (result))
  {
    assert (it->pos == 2);
    assert (btor_node_is_regular (result));
    it->pos = 0;
    it->exp = result;
    it->cur = result->e[0];
    result  = it->cur;
  }

  /* prepare next argument */
  it->pos++;
  if (it->pos < it->exp->arity)
    it->cur = it->exp->e[it->pos];
  else
    it->cur = 0;

  assert (!btor_node_is_args (result));
  return result;
}

/*------------------------------------------------------------------------*/

void
btor_iter_binder_init (BtorNodeIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (btor_node_is_regular (exp));
  assert (btor_node_is_binder (exp));

  it->cur = exp;
}

BtorNode *
btor_iter_binder_next (BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;
  result  = it->cur;
  it->cur = result->e[1];
  return result;
}

bool
btor_iter_binder_has_next (const BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);
  return !btor_node_is_inverted (it->cur) && btor_node_is_binder (it->cur);
}

void
btor_iter_lambda_init (BtorNodeIterator *it, BtorNode *exp)
{
  btor_iter_binder_init (it, exp);
  assert (btor_node_is_lambda (exp));
}

BtorNode *
btor_iter_lambda_next (BtorNodeIterator *it)
{
  return btor_iter_binder_next (it);
}

bool
btor_iter_lambda_has_next (const BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);
  return btor_node_is_lambda (it->cur);
}

/*------------------------------------------------------------------------*/

#if 0
void
btor_iter_param_init (BtorNodeIterator * it, BtorNode * exp)
{
  btor_iter_binder_init (it, exp);
}

BtorNode *
btor_iter_param_next (BtorNodeIterator * it)
{
  BtorNode *result;
  result = btor_iter_binder_next (it);
  assert (btor_node_is_param (result->e[0]));
  return result->e[0];
}

bool
btor_has_next_param_iterator (BtorNodeIterator * it)
{
  return btor_has_next_binder_iterator (it);
}
#endif

/*------------------------------------------------------------------------*/

#if 0
static void
find_next_unique_node (BtorNodeIterator * it)
{
  while (!it->cur && it->pos < it->btor->nodes_unique_table.size)
    it->cur = it->btor->nodes_unique_table.chains[it->pos++];
  assert (it->cur
	  || it->num_elements == it->btor->nodes_unique_table.num_elements);
}

void
btor_iter_unique_table_init (BtorNodeIterator * it, const Btor * btor)
{
  assert (btor);
  assert (it);

  it->btor = btor;
  it->pos = 0;
#ifndef NDEBUG
  it->num_elements = 0;
#endif
  it->cur = 0;
  find_next_unique_node (it);
}

bool
btor_iter_unique_table_has_next (const BtorNodeIterator * it)
{
  assert (it);
  assert (it->cur || it->pos >= it->btor->nodes_unique_table.size);
  return it->cur != 0;
}

BtorNode *
btor_iter_unique_table_next (BtorNodeIterator * it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;

  result = it->cur;
#ifndef NDEBUG
  it->num_elements++;
  assert (it->num_elements <= it->btor->nodes_unique_table.num_elements);
  assert (result);
#endif
  it->cur = it->cur->next;
  if (!it->cur)
    find_next_unique_node (it);
  return result;
}
#endif
