/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
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

BtorNode *btor_rewrite_and_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_eq_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_add_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_mul_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_ult_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_sll_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_srl_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_udiv_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_urem_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

BtorNode *btor_rewrite_concat_exp (Btor *btor, BtorNode *e0, BtorNode *e1);

#if 0
BtorNode *btor_rewrite_read_exp (Btor * btor, BtorNode * e_array, 
				 BtorNode * e_index);

BtorNode *btor_rewrite_write_exp (Btor * btor, BtorNode * e_array, 
				  BtorNode * e_index, BtorNode *e_value);
#endif

BtorNode *btor_rewrite_cond_exp (Btor *btor,
                                 BtorNode *e_cond,
                                 BtorNode *e_if,
                                 BtorNode *e_else);

BtorNode *btor_rewrite_apply_exp (Btor *btor, BtorNode *fun, BtorNode *args);

int btor_rewrite_linear_term (
    Btor *btor, BtorNode *term, char **fp, BtorNode **lp, BtorNode **rp);
#endif
