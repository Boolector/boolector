/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "btorparamcache.h"
#include "btorbeta.h"
#include "btoriter.h"

BtorParamCacheTuple *
btor_new_param_cache_tuple (Btor *btor, BtorNode *exp)
{
  assert (btor);
  assert (exp);
  assert (BTOR_IS_REGULAR_NODE (exp));

  int i;
  unsigned int hash;
  BtorNode *param, *arg, *cur;
  BtorParamCacheTuple *t;
  BtorParameterizedIterator it;
  BtorNodeIterator pit;

  BTOR_NEW (btor->mm, t);
  BTOR_CLR (t);
  t->exp = btor_copy_exp (btor, exp);

  init_parameterized_iterator (btor, &it, exp);

  hash = BTOR_REAL_ADDR_NODE (exp)->id;
  if (has_next_parameterized_iterator (&it))
  {
    t->num_args = it.num_params;
    if (BTOR_IS_LAMBDA_NODE (exp))
      t->num_args += btor_get_fun_arity (btor, exp);

    BTOR_NEWN (btor->mm, t->args, t->num_args);

    i = 0;
    if (BTOR_IS_LAMBDA_NODE (exp))
    {
      init_lambda_iterator (&pit, exp);
      while (has_next_lambda_iterator (&pit))
      {
        cur = next_lambda_iterator (&pit);
        arg = btor_param_cur_assignment (
            (BtorNode *) BTOR_LAMBDA_GET_PARAM (cur));
        assert (arg);
        t->args[i++] = btor_copy_exp (btor, arg);
        hash += (unsigned int) BTOR_GET_ID_NODE (arg);
      }
    }

    do
    {
      param = next_parameterized_iterator (&it);
      assert (BTOR_IS_REGULAR_NODE (param));
      assert (BTOR_IS_PARAM_NODE (param));
      arg = btor_param_cur_assignment (param);
      assert (arg);
      t->args[i++] = btor_copy_exp (btor, arg);
      hash += (unsigned int) BTOR_GET_ID_NODE (arg);
    } while (has_next_parameterized_iterator (&it));
  }
  else if (BTOR_IS_LAMBDA_NODE (exp))
  {
    init_lambda_iterator (&pit, exp);
    t->num_args = btor_get_fun_arity (btor, exp);
    BTOR_NEWN (btor->mm, t->args, t->num_args);

    i = 0;
    while (has_next_lambda_iterator (&pit))
    {
      cur = next_lambda_iterator (&pit);
      arg =
          btor_param_cur_assignment ((BtorNode *) BTOR_LAMBDA_GET_PARAM (cur));
      assert (arg);
      t->args[i++] = btor_copy_exp (btor, arg);
      hash += (unsigned int) BTOR_GET_ID_NODE (arg);
    }
  }
  hash *= 7334147u;
  t->hash = hash;

  return t;
}

void
btor_delete_param_cache_tuple (Btor *btor, BtorParamCacheTuple *t)
{
  assert (btor);
  assert (t);

  int i;

  btor_release_exp (btor, t->exp);
  if (t->args)
  {
    for (i = 0; i < t->num_args; i++) btor_release_exp (btor, t->args[i]);
    BTOR_DELETEN (btor->mm, t->args, t->num_args);
  }
  BTOR_DELETE (btor->mm, t);
}

unsigned int
btor_hash_param_cache_tuple (BtorParamCacheTuple *t)
{
  assert (t);
  return t->hash;
}

int
btor_compare_param_cache_tuple (BtorParamCacheTuple *t0,
                                BtorParamCacheTuple *t1)
{
  assert (t0);
  assert (t1);

  int i, result;

  result = t0->num_args;
  result -= t1->num_args;
  if (result != 0) return result;

  result = t0->exp->id;
  result -= t1->exp->id;
  if (result != 0) return result;

  for (i = 0; i < t0->num_args; i++)
  {
    result = BTOR_GET_ID_NODE (t0->args[i]);
    result -= BTOR_GET_ID_NODE (t1->args[i]);
    if (result != 0) return result;
  }

  return result;
}

BtorParamCacheTuple *
btor_copy_param_cache_tuple (Btor *btor, BtorParamCacheTuple *t)
{
  assert (btor);
  assert (t);

  BtorParamCacheTuple *result;

  BTOR_NEW (btor->mm, result);
  BTOR_CLR (result);

  result->exp      = btor_copy_exp (btor, t->exp);
  result->hash     = t->hash;
  result->num_args = t->num_args;

  BTOR_NEWN (btor->mm, result->args, result->num_args);
  memcpy (result->args, t->args, t->num_args * sizeof (*result->args));

  return result;
}
