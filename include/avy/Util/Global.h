#ifndef _GLOBAL_H_
#define _GLOBAL_H_

#include <string>
#include <ostream>
/** Global variables */

namespace avy
{
  struct AvyParams
  {
    std::string fName;
    
    /**Interpolantion sequence to use
       0 McMillan, 1 McMillan' */
    unsigned itp;
    
  };
  
  std::ostream &operator<< (std::ostream& out, const AvyParams& p);
  
  extern AvyParams gParams;
    
}


#endif /* _GLOBAL_H_ */
