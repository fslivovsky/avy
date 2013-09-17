#include <string.h>
#include <sstream>
#include <iostream>

#include "AbcUtils.h"
#include "aig/aig/aig.h"

namespace avy
{
  using namespace abc;
  using namespace std;

  void dummyName (Aig_Man_t *pMan)
  {
    int i;
    Aig_Obj_t *pObj;
  
    Aig_ManForEachCi (pMan, pObj, i)
      {
        std::ostringstream os;
        os << "v" << i;
        pObj->pData = strdup ((char*)os.str().c_str ());
      }
  }


  void dumpAig (Aig_Man_t *pMan, Aig_Obj_t *pObj)
  {
    assert (!Aig_ObjIsCo (pObj));

    Vec_Vec_t *v;
    v = Vec_VecAlloc (10);
    Aig_ObjPrintVerilog (stderr, pObj, v, 0);
    Vec_VecFree (v);
  }

  std::ostream &dumpCube (std::ostream &out, Pdr_Set_t *pCube)
  {
    for (int i = 0; i < pCube->nLits; ++i)
      {
        if (lit_sign (pCube->Lits[i]))
          out << "-";
        
        out << lit_var (pCube->Lits[i]) << " ";
      }    
    return out;
  }

  std::ostream &dumpCubes (std::ostream &out, Vec_Ptr_t *pCubes)
  {
    int j;
    Pdr_Set_t *pCube;
    out << "CUBES BEGIN\n";
    Vec_PtrForEachEntry (Pdr_Set_t*, pCubes, pCube, j)
      {
        out << j << ": ";
        dumpCube (out, pCube);
        out << "\n";
      }
    out << "CUBES END\n";
    return out;
  }
  
  
}
