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
