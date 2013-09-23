#ifndef _GLOBAL_H_
#define _GLOBAL_H_

#include <string>
#include <iostream>



/** Global variables */
namespace avy
{
  struct AvyParams
  {
    std::string fName;
    
    /**Interpolantion sequence to use
       0 McMillan, 1 McMillan' */
    unsigned itp;

    /** verbosity level */
    unsigned verbosity;
  };
  
  std::ostream &operator<< (std::ostream& out, const AvyParams& p);
  
  extern AvyParams gParams;

  /** Output streams */

  
  /// std out
  inline std::ostream& outs() { return std::cout; }
  /// std err
  inline std::ostream& errs() { return std::cerr; }
  /// log stream. use in LOG() macro.
  inline std::ostream& logs() { return std::cerr; }
  /// verbose
  inline std::ostream& vout() { return std::cout; }
}

#define VERBOSE(LVL,CODE)                               \
  do { if (LVL <= ::avy::gParams.verbosity) { CODE; }   \
  } while (0)

#endif /* _GLOBAL_H_ */
