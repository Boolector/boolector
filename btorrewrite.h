/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *  Copyright (C) 2010  Robert Daniel Brummayer, Armin Biere
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef BTORREWRITE_H_INCLUDED
#define BTORREWRITE_H_INCLUDED

#include "btorexp.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

BtorExp *btor_rewrite_slice_exp (Btor *btor,
                                 BtorExp *exp,
                                 int upper,
                                 int lower);

BtorExp *btor_rewrite_and_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_eq_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_add_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_mul_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_ult_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_sll_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_srl_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_udiv_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_urem_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_concat_exp (Btor *btor, BtorExp *e0, BtorExp *e1);

BtorExp *btor_rewrite_read_exp (Btor *btor, BtorExp *e_array, BtorExp *e_index);

BtorExp *btor_rewrite_write_exp (Btor *btor,
                                 BtorExp *e_array,
                                 BtorExp *e_index,
                                 BtorExp *e_value);

BtorExp *btor_rewrite_cond_exp (Btor *btor,
                                BtorExp *e_cond,
                                BtorExp *e_if,
                                BtorExp *e_else);

#endif
