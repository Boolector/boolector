/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORDC_H_INCLUDED
#define BTORDC_H_INCLUDED

void btor_compute_scores (Btor *);
void btor_compute_scores_dual_prop (Btor *);

int btor_compare_scores (Btor *, BtorNode *, BtorNode *);
int btor_compare_scores_qsort (const void *, const void *);
#endif
