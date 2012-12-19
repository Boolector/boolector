#ifndef NBTORLOG

#include "btorlog.h"
#include "btorexp.h"

#include <stdarg.h>

int
btor_log_start (Btor* btor, const char* fmt, ...)
{
  va_list ap;
  if (btor->loglevel <= 0) return 0;
  fputs ("[btorlog] ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  return 1;
}

void
btor_log_end (Btor* btor)
{
  assert (btor->loglevel > 0);
  fputc ('\n', stdout);
  fflush (stdout);
}

#endif
