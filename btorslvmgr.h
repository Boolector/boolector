/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSAT_H_INCLUDED
#define BTORSAT_H_INCLUDED

#include "boolector.h"
#include "btormap.h"
#include "btormem.h"

struct BtorSlvMgr
{
  BtorMemMgr *mm;
  BtorMsg *msg;
  char *name;

  struct
  {
    void *(*new) (Btor *btor);
    void *(*clone) (Btor *clone, void *slv, BtorNodeMap *exp_map);
    void (*delete) (Btor *btor, void *slv);
    void (*print_stats) (Btor *btor, void *slv);
  } api;
};

typedef struct BtorSlvMgr BtorSlvMgr;

BtorSlvMgr *btor_new_slv_mgr (BtorMemMgr *mm, BtorMsg *msg);
BtorSlvMgr *btor_clone_slv_mgr (BtorMemMgr *mm, BtorSlvMgr *slvmgr);
void btor_delete_slv_mgr (BtorSlvMgr *slvmgr);

#endif
