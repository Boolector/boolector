/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTOR_HASH_H_INCLUDED
#define BTOR_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include "utils/btormem.h"

struct BtorHashTableData
{
  bool flag;
  union
  {
    int32_t as_int;
    double as_dbl;
    void* as_ptr;
    char* as_str;
  };
};

typedef struct BtorHashTableData BtorHashTableData;

typedef uint32_t (*BtorHashPtr) (const void* key);
typedef int32_t (*BtorCmpPtr) (const void* a, const void* b);

typedef void (*BtorCloneHashTableData) (BtorMemMgr* mm,
                                        const void* map,
                                        BtorHashTableData* data,
                                        BtorHashTableData* cloned_data);
#endif
