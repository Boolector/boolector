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

#ifndef BTOREXPITER_H_INCLUDED
#define BTOREXPITER_H_INCLUDED

#include "btorcore.h"

#include <stdbool.h>

/*------------------------------------------------------------------------*/

typedef struct BtorNodeIterator
{
  const Btor *btor; /* required for unique table iterator */
  int pos;          /* required for unique table iterator */
#ifndef NDEBUG
  int num_elements;
#endif
  BtorNode *cur;
} BtorNodeIterator;

#define BTOR_NEXT_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->next_parent[btor_exp_get_tag (exp)])

#define BTOR_PREV_PARENT(exp) \
  (BTOR_REAL_ADDR_NODE (exp)->prev_parent[btor_exp_get_tag (exp)])

void btor_init_apply_parent_iterator (BtorNodeIterator *it,
                                      const BtorNode *exp);
bool btor_has_next_apply_parent_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_apply_parent_iterator (BtorNodeIterator *it);

void btor_init_parent_iterator (BtorNodeIterator *it, const BtorNode *exp);
bool btor_has_next_parent_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_parent_iterator (BtorNodeIterator *it);

void btor_init_lambda_iterator (BtorNodeIterator *it, BtorNode *exp);
bool btor_has_next_lambda_iterator (const BtorNodeIterator *it);
BtorNode *btor_next_lambda_iterator (BtorNodeIterator *it);

#if 0
void btor_init_param_iterator (BtorNodeIterator * it, BtorNode * exp);
bool btor_has_next_param_iterator (const BtorNodeIterator * it);
BtorNode * btor_next_param_iterator (BtorNodeIterator * it);

void btor_init_unique_table_iterator (BtorNodeIterator * it, const Btor * exp);
bool btor_has_next_unique_table_iterator (const BtorNodeIterator * it);
BtorNode * btor_next_unique_table_iterator (BtorNodeIterator * it);
#endif

/*------------------------------------------------------------------------*/

typedef struct BtorArgsIterator
{
  int pos;
  BtorNode *cur;
  const BtorNode *exp;
} BtorArgsIterator;

void btor_init_args_iterator (BtorArgsIterator *it, const BtorNode *exp);
bool btor_has_next_args_iterator (const BtorArgsIterator *it);
BtorNode *btor_next_args_iterator (BtorArgsIterator *it);

/*------------------------------------------------------------------------*/

#endif
