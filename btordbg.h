/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *  Copyright (C) 2012-2014 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORDBG_H_INCLUDED
#define BTORDBG_H_INCLUDED
#ifndef NDEBUG
#include "btorcore.h"

int check_unique_table_children_proxy_free_dbg (const Btor* btor);

int check_id_table_mark_unset_dbg (const Btor* btor);

int check_id_table_aux_mark_unset_dbg (const Btor* btor);

int check_unique_table_merge_unset_dbg (const Btor* btor);

int check_hash_table_proxy_free_dbg (BtorPtrHashTable* table);

int check_all_hash_tables_proxy_free_dbg (const Btor* btor);

int check_hash_table_simp_free_dbg (BtorPtrHashTable* table);

int check_all_hash_tables_simp_free_dbg (const Btor* btor);

int check_reachable_flag_dbg (const Btor* btor);

int check_constraints_not_const_dbg (Btor* btor);

#endif
#endif
