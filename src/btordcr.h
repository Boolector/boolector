/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORDC_H_INCLUDED
#define BTORDC_H_INCLUDED

#include <stdint.h>
#include "btortypes.h"

void btor_dcr_compute_scores (Btor* btor);
void btor_dcr_compute_scores_dual_prop (Btor* btor);

int32_t btor_dcr_compare_scores (Btor* btor, BtorNode* a, BtorNode* b);
int32_t btor_dcr_compare_scores_qsort (const void* p1, const void* p2);
#endif
