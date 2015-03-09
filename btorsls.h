/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLS_H_INCLUDED
#define BTORSLS_H_INCLUDED

void btor_generate_model_sls (Btor* btor, int model_for_all_nodes, int reset);
int btor_sat_aux_btor_sls (Btor* btor);

#endif
