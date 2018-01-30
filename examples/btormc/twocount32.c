#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
static bool
read_bool ()
{
  int ch = getc (stdin);
  if (ch == '0') return false;
  if (ch == '1') return true;
  exit (0);
}
int
main ()
{
  bool turn;              // input
  unsigned a = 0, b = 0;  // states
  for (;;)
  {
    turn = read_bool ();
    assert (!(a == 3 && b == 3));
    if (turn)
      a = a + 1;
    else
      b = b + 1;
  }
}
