#include <assert.h>
#include <stdio.h>

static void
print (float f)
{
  unsigned w = *(unsigned *) &f;
  int i;
  for (i = 31; i >= 0; i--) putc ((w & (1u << i)) ? '1' : '0', stdout);
  printf (" %f\n", (double) f);
}

static float
gen (int sign, int e, unsigned m)
{
  unsigned w = 0;
  float res;
  assert (e > -(1 << 16));
  assert (e < (1 << 16));
  if (m)
  {
    while (m > (1u << 23)) m >>= 1, e++;
    while (m < (1u << 23)) m <<= 1, e--;
  }
  assert (!m || (m & (1u << 23)));
  if (e > 127) e = 127, w = 0;
  if (e < -127) e = -127, w = 0;
  w = m & ~(1u << 23);
  assert (w < (1u << 23));
  assert (e >= -127);
  w |= (e + 127) << 23;
  if (sign < 0) w |= (1u << 31);
  res = *(float *) &w;
  return res;
}

int
main ()
{
  print (gen (1, -2, 0x500000));
  print (.15625);
  return 0;
  return 0;
}
