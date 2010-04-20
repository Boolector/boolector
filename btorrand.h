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

#ifndef BTORRAND_H_INCLUDE
#define BTORRAND_H_INCLUDE

#include "btorexp.h"

typedef struct BtorRand BtorRand;
typedef struct BtorRandExpParams BtorRandExpParams;

struct BtorRandExpParams
{
  unsigned constants;
  unsigned variables;
  unsigned arrays;
  unsigned terms;
  unsigned predicates;
  unsigned formulas;
  struct
  {
    unsigned data;
    unsigned address;
  } width;
  unsigned linear : 1;
  unsigned equations : 1;
  unsigned write : 1;
};

BtorRand *btor_new_rand (BtorMemMgr *, unsigned seed);
void btor_delete_rand (BtorMemMgr *, BtorRand *);

BtorExp *btor_new_rand_exp (Btor *, BtorRand *, BtorRandExpParams *);

#endif
