/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2013 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORMISC_H_INCLUDED
#define BTORMISC_H_INCLUDED

#include "btorexp.h"

char *node2string (BtorNode *);
int btor_vis_exp (Btor *btor, BtorNode *exp);
void btor_print_bfs_path (Btor *btor, BtorNode *from, BtorNode *to);

#endif
