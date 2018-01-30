#include <cassert>
#include <cstdlib>
#include <iostream>
using namespace std;
static bool
read_input_bit ()
{
  char ch;
  if (!(cin >> ch)) exit (0);
  if (ch == '0') return false;
  if (ch == '1') return true;
  exit (0);
}
int
main ()
{
  unsigned a = 0, b = 0;  // states
  bool turn;              // inputs
  cout << "sat" << endl;
  cout << "b0" << endl;
  cout << "#0" << endl;
  for (unsigned k = 0;; k++)
  {
    turn = read_input_bit ();
    cout << "#" << k << endl;
    cout << "0 " << a << " a#" << k << endl;
    cout << "1 " << b << " b#" << k << endl;
    cout << "@" << k << endl;
    cout << "0 " << turn << " turn@" << k << endl;
    cout << flush;
    if (a == 3 && b == 3)
    {
      cout << "*** twocount32.c: assertion failed at bound " << k << endl;
      exit (1);
    }
    if (turn)
      a = a + 1;
    else
      b = b + 1;
  }
}
