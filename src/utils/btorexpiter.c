/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/btorexpiter.h"

/*------------------------------------------------------------------------*/
/* node iterators					                  */
/*------------------------------------------------------------------------*/

void
btor_init_apply_parent_iterator (BtorNodeIterator *it, const BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (BTOR_REAL_ADDR_NODE (exp)->last_parent);
}

bool
btor_has_next_apply_parent_iterator (const BtorNodeIterator *it)
{
  assert (it);
  assert (BTOR_IS_REGULAR_NODE (it->cur));
  /* function child of apply is at position 0, so cur is not tagged */
  return it->cur && btor_is_apply_node (it->cur);
}

BtorNode *
btor_next_apply_parent_iterator (BtorNodeIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_REAL_ADDR_NODE (BTOR_PREV_PARENT (result));
  assert (BTOR_IS_REGULAR_NODE (result));
  assert (btor_is_apply_node (result));
  return result;
}

/*------------------------------------------------------------------------*/

void
btor_init_parent_iterator (BtorNodeIterator *it, const BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->first_parent;
}

bool
btor_has_next_parent_iterator (const BtorNodeIterator *it)
{
  assert (it);
  return it->cur != 0;
}

BtorNode *
btor_next_parent_iterator (BtorNodeIterator *it)
{
  assert (it);

  BtorNode *result;
  result = it->cur;
  assert (result);
  it->cur = BTOR_NEXT_PARENT (result);

  return BTOR_REAL_ADDR_NODE (result);
}

/*------------------------------------------------------------------------*/

void
btor_init_args_iterator (BtorArgsIterator *it, const BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_args_node (exp));

  it->pos = 0;
  it->exp = exp;
  it->cur = exp->e[0];
}

bool
btor_has_next_args_iterator (const BtorArgsIterator *it)
{
  assert (it);
  return it->cur != 0;
}

BtorNode *
btor_next_args_iterator (BtorArgsIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;

  result = it->cur;

  /* end of this args node, continue with next */
  if (btor_is_args_node (result))
  {
    assert (it->pos == 2);
    assert (BTOR_IS_REGULAR_NODE (result));
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

  assert (!btor_is_args_node (result));
  return result;
}

/*------------------------------------------------------------------------*/

void
btor_init_lambda_iterator (BtorNodeIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));
  assert (btor_is_lambda_node (exp));

  it->cur = exp;
}

bool
btor_has_next_lambda_iterator (const BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);
  return btor_is_lambda_node (it->cur);
}

BtorNode *
btor_next_lambda_iterator (BtorNodeIterator *it)
{
  assert (it);
  assert (it->cur);

  BtorNode *result;
  result  = it->cur;
  it->cur = result->e[1];
  return result;
}

/*------------------------------------------------------------------------*/

#if 0
void
btor_init_param_iterator (BtorNodeIterator * it, BtorNode * exp)
{
  btor_init_lambda_iterator (it, exp);
}

bool
btor_has_next_param_iterator (const BtorNodeIterator * it)
{
  return btor_has_next_lambda_iterator (it);
}

BtorNode *
btor_next_param_iterator (BtorNodeIterator * it)
{
  BtorNode *result;
  result = btor_next_lambda_iterator (it);
  assert (btor_is_param_node (result->e[0]));
  return result->e[0];
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
btor_init_unique_table_iterator (BtorNodeIterator * it, const Btor * btor)
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
btor_has_next_unique_table_iterator (const BtorNodeIterator * it)
{
  assert (it);
  assert (it->cur || it->pos >= it->btor->nodes_unique_table.size);
  return it->cur != 0;
}

BtorNode *
btor_next_unique_table_iterator (BtorNodeIterator * it)
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
