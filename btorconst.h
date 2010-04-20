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

#ifndef BTORCONST_H_INCLUDED
#define BTORCONST_H_INCLUDED

#include "btormem.h"

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

enum BtorSpecialConst
{
  BTOR_SPECIAL_CONST_ZERO,
  BTOR_SPECIAL_CONST_ONE,
  BTOR_SPECIAL_CONST_ONES,
  BTOR_SPECIAL_CONST_ONE_ONES,
  BTOR_SPECIAL_CONST_NONE
};

typedef enum BtorSpecialConst BtorSpecialConst;

char *btor_zero_const (BtorMemMgr *mm, int len);

char *btor_one_const (BtorMemMgr *mm, int len);

char *btor_ones_const (BtorMemMgr *mm, int len);

char *btor_int_to_const (BtorMemMgr *mm, int x, int len);

char *btor_unsigned_to_const (BtorMemMgr *mm, unsigned x, int len);

char *btor_decimal_to_const (BtorMemMgr *mm, const char *str);

char *btor_decimal_to_const_n (BtorMemMgr *mm, const char *str, int len);

char *btor_hex_to_const (BtorMemMgr *mm, const char *str);

char *btor_hex_to_const_n (BtorMemMgr *mm, const char *str, int len);

int btor_is_zero_const (const char *str);

int btor_is_one_const (const char *str);

int btor_is_ones_const (const char *str);

BtorSpecialConst btor_is_special_const (const char *str);

/*------------------------------------------------------------------------*/
/* Unbounded bit width operators.
 */
char *btor_add_unbounded_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_mult_unbounded_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_sub_unbounded_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_udiv_unbounded_const (BtorMemMgr *mm,
                                 const char *a,
                                 const char *b,
                                 char **rest_ptr);

/*------------------------------------------------------------------------*/
/* Fixed width operators.  The arguments and the result have the same width.
 */

void btor_invert_const (BtorMemMgr *mm, char *a);

char *btor_not_const (BtorMemMgr *mm, const char *a);

char *btor_and_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_eq_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_ult_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_add_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_neg_const (BtorMemMgr *mm, const char *a);

char *btor_sub_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_mul_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_udiv_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_urem_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_sll_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_srl_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_uext_const (BtorMemMgr *mm, const char *c, int len);

char *btor_concat_const (BtorMemMgr *mm, const char *a, const char *b);

char *btor_inverse_const (BtorMemMgr *mm, const char *a);

/*------------------------------------------------------------------------*/
/* Three valued logic.
 */

char *btor_x_const_3vl (BtorMemMgr *mm, int len);

void btor_invert_const_3vl (BtorMemMgr *mm, char *a);

char *btor_not_const_3vl (BtorMemMgr *mm, const char *a);

char *btor_and_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_eq_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_ult_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_add_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_mul_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_sll_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_srl_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_udiv_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_urem_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_concat_const_3vl (BtorMemMgr *mm, const char *a, const char *b);

char *btor_slice_const_3vl (BtorMemMgr *mm,
                            const char *a,
                            int upper,
                            int lower);

char *btor_cond_const_3vl (BtorMemMgr *mm,
                           const char *a,
                           const char *b,
                           const char *c);

int btor_is_const_2vl (BtorMemMgr *mm, const char *c);

char *btor_ground_const_3vl (BtorMemMgr *mm, const char *c);

/*------------------------------------------------------------------------*/
/* Work for both fixed and unbounded bit width constants.
 */
char *btor_copy_const (BtorMemMgr *mm, const char *c);

void btor_delete_const (BtorMemMgr *mm, char *c);

int btor_get_num_leading_zeros_const (BtorMemMgr *mm, const char *c);

int btor_get_num_leading_ones_const (BtorMemMgr *mm, const char *c);

int btor_cmp_const (const char *a, const char *b);

char *btor_slice_const (BtorMemMgr *mm, const char *a, int upper, int lower);

/*------------------------------------------------------------------------*/
/* Output functions.
 */
char *btor_const_to_hex (BtorMemMgr *mm, const char *c);

char *btor_const_to_decimal (BtorMemMgr *mm, const char *c);

#endif
