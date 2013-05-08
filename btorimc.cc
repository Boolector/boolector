#include "btoribv.h"

using namespace std;

#include <map>
#include <string>

static map<string, unsigned> symtab;
static BtorIBV* ibvm;

int
main (int argc, char** argv)
{
  ibvm = new BtorIBV ();
  ibvm->setVerbosity (10);
  ibvm->analyze ();
  ibvm->translate ();
  delete ibvm;
  return 0;
}
