/**
 * Boolector provides the option to plug in a callback function that is
 * called on abort conditions. This example demonstrates how to use this
 * functionality to extend Boolector's C API with exception handling.
 */

#include "boolector.h"

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

/**
 * The function to be called on abort conditions.
 */
void
abort_fun (const char* msg)
{
  throw Exception (msg);
}

int
main ()
{
  /* Set abort callback function. */
  boolector_set_abort (&abort_fun);

  /* Simple test. */
  try
  {
    boolector_delete (0);
  }
  catch (Exception& e)
  {
    std::cout << "Caught exception: " << e.getMsg () << std::endl;
  }
}
