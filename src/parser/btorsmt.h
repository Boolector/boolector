/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSMT_H_INCLUDED
#define BTORSMT_H_INCLUDED

#include "boolector.h"
#include "btorparse.h"

#include <stdio.h>

const BtorParserAPI* btor_parsesmt_parser_api ();

#endif
