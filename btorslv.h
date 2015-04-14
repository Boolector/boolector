/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLV_H_INCLUDED
#define BTORSLV_H_INCLUDED

#include "btortypes.h"
#include "utils/btormap.h"
#include "utils/btormem.h"

struct BtorSlvMgr
{
  char *name;
  void *slv;

  struct
  {
    void *(*clone_slv) (Btor *clone, Btor *btor, BtorNodeMap *exp_map);
    void (*delete_slv) (Btor *btor);
    int (*sat) (Btor *btor, int lod_limit, int sat_limit);
    void (*generate_model) (Btor *btor, int model_for_all_nodes, int reset);
    void (*print_stats) (Btor *btor);
    void (*print_time_stats) (Btor *btor);
  } api;
};

typedef struct BtorSlvMgr BtorSlvMgr;

void btor_delete_slv_mgr (Btor *btor);

BtorSlvMgr *btor_clone_slv_mgr (Btor *clone, Btor *btor, BtorNodeMap *exp_map);

#endif
