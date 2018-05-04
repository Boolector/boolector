/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORREWRITE_H_INCLUDED
#define BTORREWRITE_H_INCLUDED

#include "btornode.h"

/*------------------------------------------------------------------------*/

BtorNode *btor_rewrite_slice_exp (Btor *btor,
                                  BtorNode *exp,
                                  uint32_t upper,
                                  uint32_t lower);

BtorNode *btor_rewrite_binary_exp (Btor *btor,
                                   BtorNodeKind kind,
                                   BtorNode *e0,
                                   BtorNode *e1);

BtorNode *btor_rewrite_ternary_exp (
    Btor *btor, BtorNodeKind kind, BtorNode *e0, BtorNode *e1, BtorNode *e2);

bool btor_rewrite_linear_term (Btor *btor,
                               BtorNode *term,
                               BtorBitVector **fp,
                               BtorNode **lp,
                               BtorNode **rp);
#endif
