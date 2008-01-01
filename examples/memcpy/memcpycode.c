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
  assume (0 <= j); /* only makes sense if size_t is signed */

  old = src[j];
#endif

  assume (src <= src + n);
  assume (dst <= dst + n);

  /* This assumption is dropped if we allow src and dst to overlap.
   */
  assume (dst + n <= src || src + n <= dst);

  for (p = src, q = dst, eos = src + n; p < eos; p++, q++) *q = *p;

#ifndef NDEBUG
  new = dst[j];
  assert (old == new);
#endif

  return dst;
}
