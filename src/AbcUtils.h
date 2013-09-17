#ifndef _ABCUTILS_H_
#define _ABCUTILS_H_
#include <iostream>

#include "aig/aig/aig.h"
#include "proof/pdr/pdrInt.h"

namespace avy
{
  void dummyName (abc::Aig_Man_t *pMan);
  void dumpAig (abc::Aig_Man_t *pMan, abc::Aig_Obj_t *pObj);
  std::ostream& dumpCube (std::ostream& out, abc::Pdr_Set_t *pCube);
  std::ostream& dumpCubes (std::ostream& out, abc::Vec_Ptr_t *pCubes);
}


#endif 
