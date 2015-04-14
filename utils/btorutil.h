/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *
 *  All rights reserved.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORUTIL_H_INCLUDED
#define BTORUTIL_H_INCLUDED

#define BTOR_HAVE_GETRUSAGE  // TODO make this a configuration option

#define BTOR_MAX_UTIL(x, y) ((x) > (y) ? (x) : (y))

#define BTOR_MIN_UTIL(x, y) ((x) < (y) ? (x) : (y))

#define BTOR_AVERAGE_UTIL(a, b) ((b) ? ((double) (a)) / ((double) (b)) : 0.0)

int btor_is_power_of_2_util (int x);

int btor_log_2_util (int x);

int btor_pow_2_util (int x);

int btor_next_power_of_2_util (int x);

int btor_num_digits_util (int x);

#ifdef BTOR_HAVE_GETRUSAGE
double btor_time_stamp (void);
#endif

int btor_file_exists (const char *);

#endif
