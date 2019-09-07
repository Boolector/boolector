/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORPREPROCESS_H_INCLUDED
#define BTORPREPROCESS_H_INCLUDED

#include <stdint.h>

#include "btortypes.h"

int32_t btor_simplify (Btor* btor);

#endif
