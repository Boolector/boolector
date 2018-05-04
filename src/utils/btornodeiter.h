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

#ifndef BTOREXPITER_H_INCLUDED
#define BTOREXPITER_H_INCLUDED

#include "btorcore.h"

#include <stdbool.h>

/*------------------------------------------------------------------------*/

typedef struct BtorNodeIterator
{
  const Btor *btor; /* required for unique table iterator */
  uint32_t pos;     /* required for unique table iterator */
#ifndef NDEBUG
  uint32_t num_elements;
#endif
  BtorNode *cur;
} BtorNodeIterator;

#define BTOR_NEXT_PARENT(exp) \
  (btor_node_real_addr (exp)->next_parent[btor_node_get_tag (exp)])

#define BTOR_PREV_PARENT(exp) \
  (btor_node_real_addr (exp)->prev_parent[btor_node_get_tag (exp)])

void btor_iter_apply_parent_init (BtorNodeIterator *it, const BtorNode *exp);
bool btor_iter_apply_parent_has_next (const BtorNodeIterator *it);
BtorNode *btor_iter_apply_parent_next (BtorNodeIterator *it);

void btor_iter_parent_init (BtorNodeIterator *it, const BtorNode *exp);
bool btor_iter_parent_has_next (const BtorNodeIterator *it);
BtorNode *btor_iter_parent_next (BtorNodeIterator *it);

void btor_iter_lambda_init (BtorNodeIterator *it, BtorNode *exp);
bool btor_iter_lambda_has_next (const BtorNodeIterator *it);
BtorNode *btor_iter_lambda_next (BtorNodeIterator *it);

void btor_iter_binder_init (BtorNodeIterator *it, BtorNode *exp);
bool btor_iter_binder_has_next (const BtorNodeIterator *it);
BtorNode *btor_iter_binder_next (BtorNodeIterator *it);

#if 0
void btor_iter_param_init (BtorNodeIterator * it, BtorNode * exp);
bool btor_iter_param_has_next (const BtorNodeIterator * it);
BtorNode * btor_iter_param_next (BtorNodeIterator * it);

void btor_iter_unique_table_init (BtorNodeIterator * it, const Btor * exp);
bool btor_iter_unique_table_has_next (const BtorNodeIterator * it);
BtorNode * btor_iter_unique_table_next (BtorNodeIterator * it);
#endif

/*------------------------------------------------------------------------*/

typedef struct BtorArgsIterator
{
  uint32_t pos;
  BtorNode *cur;
  const BtorNode *exp;
} BtorArgsIterator;

void btor_iter_args_init (BtorArgsIterator *it, const BtorNode *exp);
bool btor_iter_args_has_next (const BtorArgsIterator *it);
BtorNode *btor_iter_args_next (BtorArgsIterator *it);

/*------------------------------------------------------------------------*/

#endif
