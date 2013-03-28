/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btoriter.h"

void
init_read_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->first_parent;
}

void
init_write_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->last_parent;
}

void
init_aeq_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->first_aeq_acond_parent;
}

void
init_acond_parent_iterator (BtorPartialParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->cur = BTOR_REAL_ADDR_NODE (exp)->last_aeq_acond_parent;
}

void
init_full_parent_iterator (BtorFullParentIterator *it, BtorNode *exp)
{
  assert (it);
  assert (exp);
  it->exp = exp;
  if (BTOR_REAL_ADDR_NODE (exp)->first_parent)
  {
    it->regular_parents_done = 0;
    it->cur                  = BTOR_REAL_ADDR_NODE (exp)->first_parent;
  }
  else
  {
    it->regular_parents_done = 1;
    if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (exp)))
      it->cur = BTOR_REAL_ADDR_NODE (exp)->first_aeq_acond_parent;
    else
      it->cur = 0;
  }
}

BtorNode *
next_parent_read_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_NEXT_PARENT (result);
  /* array child of read is at position 0, so result is not tagged */
  assert (BTOR_IS_REGULAR_NODE (result));
  assert (BTOR_IS_READ_NODE (result));
  return result;
}

BtorNode *
next_parent_write_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_PREV_PARENT (result);
  /* array child of write is at position 0, so result is not tagged */
  assert (BTOR_IS_REGULAR_NODE (result));
  assert (BTOR_IS_WRITE_NODE (result));
  return result;
}

BtorNode *
next_parent_aeq_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_NEXT_AEQ_ACOND_PARENT (result);
  assert (BTOR_IS_ARRAY_EQ_NODE (BTOR_REAL_ADDR_NODE (result)));
  return BTOR_REAL_ADDR_NODE (result);
}

BtorNode *
next_parent_acond_parent_iterator (BtorPartialParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  it->cur = BTOR_PREV_AEQ_ACOND_PARENT (result);
  assert (BTOR_IS_ARRAY_COND_NODE (BTOR_REAL_ADDR_NODE (result)));
  return BTOR_REAL_ADDR_NODE (result);
}

BtorNode *
next_parent_full_parent_iterator (BtorFullParentIterator *it)
{
  BtorNode *result;
  assert (it);
  result = it->cur;
  assert (result);
  if (!it->regular_parents_done)
  {
    it->cur = BTOR_NEXT_PARENT (result);
    /* reached end of regular parent list ? */
    if (!it->cur)
    {
      it->regular_parents_done = 1;
      /* traverse aeq acond parent list */
      if (BTOR_IS_ARRAY_NODE (BTOR_REAL_ADDR_NODE (it->exp)))
        it->cur = BTOR_REAL_ADDR_NODE (it->exp)->first_aeq_acond_parent;
    }
  }
  else
    it->cur = BTOR_NEXT_AEQ_ACOND_PARENT (result);
  return BTOR_REAL_ADDR_NODE (result);
}

int
has_next_parent_read_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  /* array child of read is at position 0, so cur is not tagged */
  return it->cur && BTOR_IS_READ_NODE (it->cur);
}

int
has_next_parent_write_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  /* array child of write is at position 0, so cur is not tagged */
  return it->cur && BTOR_IS_WRITE_NODE (it->cur);
}

int
has_next_parent_aeq_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  return it->cur && BTOR_IS_ARRAY_EQ_NODE (BTOR_REAL_ADDR_NODE (it->cur));
}

int
has_next_parent_acond_parent_iterator (BtorPartialParentIterator *it)
{
  assert (it);
  return it->cur && BTOR_IS_ARRAY_COND_NODE (BTOR_REAL_ADDR_NODE (it->cur));
}

int
has_next_parent_full_parent_iterator (BtorFullParentIterator *it)
{
  assert (it);
  return it->cur != 0;
}
