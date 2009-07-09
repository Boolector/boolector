#ifndef BTORPRECO_H_INCLUDED
#define BTORPRECO_H_INCLUDED
#ifdef BTOR_USE_PRECOSAT

#include <stdio.h>

void btor_precosat_init (void);
void btor_precosat_init ();
int btor_precosat_add (int);
int btor_precosat_sat (int);
int btor_precosat_deref (int);
void btor_precosat_reset ();
void btor_precosat_set_output (FILE *);
void btor_precosat_set_prefix (const char *);
int btor_precosat_inc_max_var ();
int btor_precosat_variables ();
int btor_precosat_clauses ();
void btor_precosat_set_new (void *, void *(*) (void *, size_t));
void btor_precosat_set_delete (void *, void (*) (void *, void *, size_t));
void btor_precosat_set_resize (void *,
                               void *(*) (void *, void *, size_t, size_t));
void btor_precosat_stats (void);

const char *btor_precosat_version (void);

#endif
#endif
