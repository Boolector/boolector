/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2016 Mathias Preiner.
 *  Copyright (C) 2012-2017 Aina Niemetz.
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

bool btor_dbg_check_lambdas_static_rho_proxy_free (const Btor* btor);

bool btor_dbg_check_unique_table_children_proxy_free (const Btor* btor);

bool btor_dbg_check_hash_table_proxy_free (BtorPtrHashTable* table);

bool btor_dbg_check_all_hash_tables_proxy_free (const Btor* btor);

bool btor_dbg_check_hash_table_simp_free (BtorPtrHashTable* table);

bool btor_dbg_check_all_hash_tables_simp_free (const Btor* btor);

bool btor_dbg_check_constraints_not_const (const Btor* btor);

bool btor_dbg_check_assumptions_simp_free (const Btor* btor);

#endif
#endif
