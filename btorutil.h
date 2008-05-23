#ifndef BTORUTIL_H_INCLUDED
#define BTORUTIL_H_INCLUDED

/*------------------------------------------------------------------------*/
/* PRIVATE INTERFACE                                                      */
/*------------------------------------------------------------------------*/

#define BTOR_MAX_UTIL(x, y) ((x) > (y) ? (x) : (y))

#define BTOR_AVERAGE_UTIL(a, b) ((b) ? ((double) (a)) / ((double) (b)) : 0.0)

int btor_is_power_of_2_util (int x);

int btor_log_2_util (int x);

int btor_pow_2_util (int x);

int btor_next_power_of_2_util (int x);

int btor_num_digits_util (int x);

#endif
