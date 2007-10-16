
void*
memcpy (char* dst, char* src, unsigned n)
{
  unsigned i;
  char* q;
  char* eos;
  char* p;

#ifndef NDEBUG
  unsigned j, old, new;

  assume (j < n);
  assume (0 <= j);

  old = src[j];
#endif

  assume (src <= src + n);
  assume (dst <= dst + n);
  assume (dst + n <= src || src + n <= dst);

  for (p = src, q = dst, eos = src + n; p < eos; p++, q++) *q = *p;

#ifndef NDDEBUG
  new = dst[j];
  assert (old == new);
#endif

  return dst;
}
