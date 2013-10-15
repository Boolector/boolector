#ifndef BTORPARAMCACHE_H_INCLUDED
#define BTORPARAMCACHE_H_INCLUDED

#include "btorexp.h"

struct BtorParamCacheTuple
{
  unsigned int hash;
  int num_args;
  BtorNode **args;
  BtorNode *exp;
};

typedef struct BtorParamCacheTuple BtorParamCacheTuple;

BtorParamCacheTuple *btor_new_param_cache_tuple (Btor *, BtorNode *);

void btor_delete_param_cache_tuple (Btor *, BtorParamCacheTuple *);

unsigned int btor_hash_param_cache_tuple (BtorParamCacheTuple *);

int btor_compare_param_cache_tuple (BtorParamCacheTuple *,
                                    BtorParamCacheTuple *);

BtorParamCacheTuple *btor_copy_param_cache_tuple (Btor *,
                                                  BtorParamCacheTuple *);

#endif
