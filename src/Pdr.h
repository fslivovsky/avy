#ifndef _PDR_H_
#define _PDR_H_

#include "proof/pdr/pdrInt.h"

namespace avy
{
  using namespace abc;
  
  class Pdr
  {
    Aig_Man_t *m_pAig;
    Pdr_Man_t *m_pPdr;
  
    void ensureFrames (unsigned level);
    Aig_Obj_t* cubeToAig (Pdr_Set_t *pCube, Aig_Man_t *pAig);
    
  public:
    Pdr (Aig_Man_t *pAig);

    void setLimit (unsigned v) { m_pPdr->pPars->nFrameMax = v; }
    void setVerbose (bool v) { m_pPdr->pPars->fVerbose = v; }
    bool isVerbose () { return m_pPdr->pPars->fVerbose; }
    
    void setSilent (bool v) { m_pPdr->pPars->fSilent = v; }
    
    
    
      
  
    void addCoverCubes (unsigned level, Vec_Ptr_t *pCubes);
    void getCoverDeltaCubes (unsigned level, Vec_Ptr_t *pCubes);
    void getCoverCubes (unsigned level, Vec_Ptr_t *pCubes);
  
    Aig_Obj_t *getCover (unsigned level, Aig_Man_t *pAig=0);
    Aig_Obj_t *getCoverDelta (unsigned level, Aig_Man_t *pAig=0);
  
  
  
    int solve ();
  
  
  
  };
}

  


#endif /* _PDR_H_ */
