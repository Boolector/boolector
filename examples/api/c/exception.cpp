extern "C" {
#include "boolector.h"
}

#include <cstdint>
#include <exception>
#include <iostream>

void abort_fun (void)
{
  throw std::exception();
}

int
main ()
{
  boolector_set_abort (&abort_fun);
  boolector_delete (0);

}
