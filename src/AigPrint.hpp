#ifndef _AIGPRINT_H_
#define _AIGPRINT_H_

/** C++ debug printing of AIG */

#include <iostream>

#include "aig/aig/aig.h"
namespace avy
{
  std::ostream &PrintAig (std::ostream &out, abc::Aig_Obj_t &obj);
  
  inline std::ostream &operator<< (std::ostream &out, abc::Aig_Obj_t &obj)
  {
    PrintAig (out, obj);
    return out;
  }
}


#endif /* _AIGPRINT_H_ */
