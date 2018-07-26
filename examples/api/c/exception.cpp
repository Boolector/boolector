extern "C" {
#include "boolector.h"
}

#include <cstdint>
#include <exception>
#include <iostream>

class Exception : public std::exception
{
 public:
  Exception (const std::string& msg) : msg (msg) {}
  std::string getMsg () { return msg; }

 protected:
  std::string msg;
};

void
abort_fun (const char* msg)
{
  throw Exception (msg);
}

int
main ()
{
  boolector_set_abort (&abort_fun);
  try
  {
    boolector_delete (0);
  }
  catch (Exception& e)
  {
    std::cout << "Caught exception: " << e.getMsg () << std::endl;
  }
}
