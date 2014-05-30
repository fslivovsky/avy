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

    /** Use new avy code */
    bool avy;
    
    /** verbosity level */
    unsigned verbosity;

    /** stutter instead of reseting to initial state*/
    bool stutter;

    /** shallow push at every iteration */
    bool shallow_push;
    
    /** reset global pdr cover before updating it */
    bool reset_cover;

    /** satminimize unsat core */
    bool min_core;

    /** interface abstraction */
    bool abstraction;

    /** Make Tr0 special */
    bool tr0;

    /** Frame at which to start PDR */
    int pdr;

    /** minimize suffix of interpolation sequence */
    bool min_suffix;

    /** always use sat_solver1 */
    bool sat1;

    /** use minisat */
    bool minisat;

    /** use glucose */
    bool glucose;
    
    /** use glucose for itp */
    bool glucose_itp;
    
    /** use minisat itp */
    bool minisat_itp;

    /** by how much to increase BMC in each iteration */
    unsigned kStep;

    /** stick error output */
    bool stick_error;
    
    bool itp_simplify;

    unsigned maxFrame;

    
    /// maximum number of conflict during cube generalization
    unsigned genConfLimit;
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
