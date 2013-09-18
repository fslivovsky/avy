#ifndef _PDR_H_
#define _PDR_H_

#include "proof/pdr/pdrInt.h"
#include <iostream>
namespace avy
{
  using namespace abc;
  
  class Pdr
  {
    Aig_Man_t *m_pAig;
    Pdr_Man_t *m_pPdr;
  
    void ensureFrames (unsigned level);
    Aig_Obj_t* cubeToAig (Pdr_Set_t *pCube, Aig_Man_t *pAig);

    int blockCube (Pdr_Set_t *pCube);
    
    Pdr_Set_t *reduceClause(int k, Pdr_Set_t * pCube );
    int generalize (int k, Pdr_Set_t * pCube, 
                    Pdr_Set_t ** ppPred, Pdr_Set_t ** ppCubeMin);
    void solverAddClause( int k, Pdr_Set_t * pCube );
    
  

  public:
    Pdr (Aig_Man_t *pAig);
    ~Pdr ();

    void setLimit (unsigned v) { m_pPdr->pPars->nFrameMax = v; }
    void setVerbose (bool v) { m_pPdr->pPars->fVerbose = v; }
    bool isVerbose () { return m_pPdr->pPars->fVerbose; }
    
    void setSilent (bool v) { m_pPdr->pPars->fSilent = v; }
    
    
    void addCoverCubes (unsigned level, Vec_Ptr_t *pCubes);
    void getCoverDeltaCubes (unsigned level, Vec_Ptr_t *pCubes);
    void getCoverCubes (unsigned level, Vec_Ptr_t *pCubes);
  
    Aig_Obj_t *getCover (unsigned level, Aig_Man_t *pAig=0);
    Aig_Obj_t *getCoverDelta (unsigned level, Aig_Man_t *pAig=0);

    /**
     * based on abc::Pdr_ManSolveInt
     * 
     * \return 1 if an invariant is found, 0 if not, -1 on internal error
     */
    int solve (bool safe = false);
    
    /** Special version of solve used internally 
     */
    int solveSafe () { return solve (true); }
    
        
    

    /**
     * based on abc::Pdr_ManPushClauses 
     * 
     * \return 1 if an invariant is found, 0 if not, -1 on internal error
     */
    int pushClauses ();


    Aig_Obj_t *getInit (Aig_Man_t *pAig = 0);
    
  
  };
}

  


#endif /* _PDR_H_ */
