/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORREWRITE_H_INCLUDED
#define BTORREWRITE_H_INCLUDED

#include "btorexp.h"

/*------------------------------------------------------------------------*/

BtorNode *btor_rewrite_slice_exp (Btor *btor,
                                  BtorNode *exp,
                                  int upper,
                                  int lower);

BtorNode *btor_rewrite_binary_exp (Btor *,
                                   BtorNodeKind,
                                   BtorNode *,
                                   BtorNode *);

BtorNode *btor_rewrite_ternary_exp (
    Btor *, BtorNodeKind, BtorNode *, BtorNode *, BtorNode *);

int btor_rewrite_linear_term (
    Btor *btor, BtorNode *term, char **fp, BtorNode **lp, BtorNode **rp);
#endif
