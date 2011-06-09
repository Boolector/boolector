/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2010 Robert Daniel Brummayer, FMV, JKU.
 *  Copyright (C) 2010 Armin Biere, FMV, JKU.
 *
 *  This file is part of Boolector.
 *
 *  Boolector is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Boolector is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef BTORUTIL_H_INCLUDED
#define BTORUTIL_H_INCLUDED

#define BTOR_HAVE_GETRUSAGE  // TODO make this a configuration option

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

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

#endif
