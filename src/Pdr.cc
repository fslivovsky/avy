#include "Pdr.h"
#include "proof/pdr/pdrInt.h"
#include "AbcUtils.h"

namespace abc
{
  int Pdr_ManBlockCube( Pdr_Man_t * p, Pdr_Set_t * pCube );
  int Pdr_ManPushClauses( Pdr_Man_t * p );
}


using namespace abc;

namespace avy
{
  
  Pdr::Pdr (Aig_Man_t *pAig) : m_pAig (pAig)
  {
    Pdr_Par_t *p = ABC_ALLOC (Pdr_Par_t, 1);
    Pdr_ManSetDefaultParams (p);
    p->fMonoCnf = 1;
    m_pPdr = Pdr_ManStart (m_pAig, p, NULL);

    setVerbose (false);
    setSilent (true);
  }

  Pdr::~Pdr ()
  {
    std::cout.flush ();
    std::cerr.flush ();
    
    Pdr_Par_t *p = m_pPdr->pPars;
    Pdr_ManStop (m_pPdr);
    ABC_FREE (p);
  }

  void Pdr::ensureFrames (unsigned lvl)
  {
    for (unsigned i = Vec_PtrSize (m_pPdr->vSolvers); i <= lvl; ++i)
      Pdr_ManCreateSolver (m_pPdr, i);
  }
  

  void Pdr::addCoverCubes (unsigned level, Vec_Ptr_t *pCubes)
  {
    ensureFrames (level);
    
    int j;
    Pdr_Set_t *pCube;

    if (isVerbose ())
      std::cerr << "Adding cubes to level: " << level << "\n";

    Vec_PtrForEachEntry (Pdr_Set_t*, pCubes, pCube, j)
      {
        if (isVerbose ())
          {
            std::cerr << j << ": ";
            dumpCube (std::cerr, pCube);
            std::cerr << "\n";
          }
        
        
        Vec_VecPush (m_pPdr->vClauses, level, Pdr_SetDup (pCube));
        m_pPdr->nCubes++;
        
        for (int i = 1; i <= level; ++i)
          Pdr_ManSolverAddClause (m_pPdr, i, pCube);
      }
  }
  
  void Pdr::getCoverDeltaCubes (unsigned level, Vec_Ptr_t *pCubes)
  {
    Vec_Ptr_t *vVec = Vec_VecEntry (m_pPdr->vClauses, level);
    int j;
    Pdr_Set_t *pCube;
    
    Vec_PtrForEachEntry (Pdr_Set_t*, vVec, pCube, j)
      Vec_PtrPush (pCubes, pCube);
  }
  
  void Pdr::getCoverCubes (unsigned level, Vec_Ptr_t *pCubes)
  {
    int i;
    Vec_Ptr_t *vVec;
    Vec_VecForEachLevelStart (m_pPdr->vClauses, vVec, i, level)
      {
        int j;
        Pdr_Set_t *pCube;
        Vec_PtrForEachEntry (Pdr_Set_t*, vVec, pCube, j)
          Vec_PtrPush (pCubes, pCube);
      }
  }
  

  Aig_Obj_t* Pdr::cubeToAig (Pdr_Set_t *pCube, Aig_Man_t *pAig)
  {
    if (!pAig) pAig = m_pAig;
    Aig_Obj_t *pRes = Aig_ManConst1 (pAig);
    
    for (int i = 0; i < pCube->nLits; ++i)
      {
        if (pCube->Lits [i] == -1) continue;

        Aig_Obj_t *pObj;
        
        pObj = Aig_ManCi (pAig, lit_var (pCube->Lits [i]));
        pObj = Aig_NotCond (pObj, lit_sign (pCube->Lits [i]));
        pRes = Aig_And (pAig, pRes, pObj);
      }

    return pRes;
  }
  
  Aig_Obj_t *Pdr::getCover (unsigned level, Aig_Man_t *pAig)
  {
    assert (level > 0);
    if (!pAig) pAig = m_pAig;
    
    Vec_Ptr_t *pCubes = Vec_PtrAlloc (10);
    getCoverCubes (level, pCubes);
    
    int j;
    Pdr_Set_t *pCube;
    Aig_Obj_t *pRes = Aig_ManConst1 (pAig);
    
    Vec_PtrForEachEntry (Pdr_Set_t *, pCubes, pCube, j)
      {
        Aig_Obj_t *pAigCube = cubeToAig (pCube, pAig);
        pRes = Aig_And (pAig, pRes, Aig_Not (pAigCube));
      }
    
    return pRes;    
  }
  
  Aig_Obj_t *Pdr::getCoverDelta (unsigned level, Aig_Man_t *pAig)
  {
    assert (level > 0);
    if (!pAig) pAig = m_pAig;
  }
  



  int Pdr::solve ()
  {

    Pdr_Man_t *p = m_pPdr;
    
    int fPrintClauses = 0;
    Pdr_Set_t * pCube = NULL;
    Aig_Obj_t * pObj;
    int k, i, j, RetValue = -1;
    Vec_Ptr_t *vVec;
    int nOutDigits = Abc_Base10Log( Saig_ManPoNum(p->pAig) );
    abctime clkStart = Abc_Clock(), clkOne = 0;
    p->timeToStop = p->pPars->nTimeOut ? p->pPars->nTimeOut * CLOCKS_PER_SEC + Abc_Clock(): 0;
    //assert( Vec_PtrSize(p->vSolvers) == 0 );
    // create the first timeframe
    p->pPars->timeLastSolved = Abc_Clock();
    ensureFrames (k = 0);

    p->iOutCur = 0;

    while ( 1 )
      {
        std::cout << "At loop iteration " << k << "\n";
        std::cout.flush ();
        
        p->nFrames = k;
        //assert( k == Vec_PtrSize(p->vSolvers)-1 );
        p->iUseFrame = ABC_INFINITY;
        Saig_ManForEachPo( p->pAig, pObj, p->iOutCur )
          {
            // check if the output is trivially solved
            if ( Aig_ObjChild0(pObj) == Aig_ManConst0(p->pAig) )
              {
                assert (0);
                continue;
              }
            // check if the output is trivially solved
            if ( Aig_ObjChild0(pObj) == Aig_ManConst1(p->pAig) )
              {
                assert( 0 );
              }
            // try to solve this output
            if ( p->pTime4Outs )
              {
                assert( p->pTime4Outs[p->iOutCur] > 0 );
                clkOne = Abc_Clock();
                p->timeToStopOne = p->pTime4Outs[p->iOutCur] + Abc_Clock();
              }
            while ( 1 )
              {
                RetValue = Pdr_ManCheckCube( p, k, NULL, &pCube, p->pPars->nConfLimit );
                if ( RetValue == 1 )
                  break;
                if ( RetValue == -1 )
                  {
                    assert(0);
                    p->pPars->iFrame = k;
                    return -1;
                  }
                if ( RetValue == 0 )
                  {
                    RetValue = Pdr_ManBlockCube( p, pCube );
                    if ( RetValue == -1 )
                      {
                        assert(0);
                        p->pPars->iFrame = k;
                        return -1;
                      }
                    if ( RetValue == 0 )
                      {
                        assert (0);
                      }
                    if ( p->pPars->fVerbose )
                      Pdr_ManPrintProgress( p, 0, Abc_Clock() - clkStart );
                  }
              }
            if ( p->pTime4Outs )
              {
                abctime timeSince = Abc_Clock() - clkOne;
                assert( p->pTime4Outs[p->iOutCur] > 0 );
                p->pTime4Outs[p->iOutCur] = (p->pTime4Outs[p->iOutCur] > timeSince) ? p->pTime4Outs[p->iOutCur] - timeSince : 0;
                if ( p->pTime4Outs[p->iOutCur] == 0 && (p->vCexes == NULL || Vec_PtrEntry(p->vCexes, p->iOutCur) == NULL) )
                  {
                    p->pPars->nDropOuts++;
                    if ( p->pPars->vOutMap ) Vec_IntWriteEntry( p->pPars->vOutMap, p->iOutCur, -1 );
                    //                    printf( "Dropping output %d.\n", p->iOutCur );
                  }
                p->timeToStopOne = 0;
              }
          }

        if ( p->pPars->fVerbose )
          Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
        // open a new timeframe
        p->nQueLim = p->pPars->nRestLimit;
        assert( pCube == NULL );
        Pdr_ManSetPropertyOutput( p, k );
        ensureFrames (++k );
        if ( fPrintClauses )
          {
            Abc_Print( 1, "*** Clauses after frame %d:\n", k );
            Pdr_ManPrintClauses( p, 0 );
          }
        // push clauses into this timeframe
        RetValue = Pdr_ManPushClauses( p );
        if ( RetValue == -1 )
          {
            if ( p->pPars->fVerbose )
              Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
              {
                if ( p->timeToStop && Abc_Clock() > p->timeToStop )
                  Abc_Print( 1, "Reached timeout (%d seconds).\n",  p->pPars->nTimeOut );
                else
                  Abc_Print( 1, "Reached conflict limit (%d).\n",  p->pPars->nConfLimit );
              }
            p->pPars->iFrame = k;
            return -1;
          }
        if ( RetValue )
          {
            if ( p->pPars->fVerbose )
              Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
              Pdr_ManReportInvariant( p );
            if ( !p->pPars->fSilent )
              Pdr_ManVerifyInvariant( p );
            p->pPars->iFrame = k;
            // count the number of UNSAT outputs
            p->pPars->nProveOuts = Saig_ManPoNum(p->pAig) - p->pPars->nFailOuts - p->pPars->nDropOuts;
            // convert previously 'unknown' into 'unsat'
            if ( p->pPars->vOutMap )
              for ( k = 0; k < Saig_ManPoNum(p->pAig); k++ )
                if ( Vec_IntEntry(p->pPars->vOutMap, k) == -2 ) // unknown
                  Vec_IntWriteEntry( p->pPars->vOutMap, k, 1 ); // unsat
            return p->vCexes ? 0 : 1; // UNSAT
          }
        if ( p->pPars->fVerbose )
          Pdr_ManPrintProgress( p, 0, Abc_Clock() - clkStart );

        // check termination
        if ( p->pPars->nFrameMax && k >= p->pPars->nFrameMax )
          {
            if ( p->pPars->fVerbose )
              Pdr_ManPrintProgress( p, 1, Abc_Clock() - clkStart );
            if ( !p->pPars->fSilent )
              Abc_Print( 1, "Reached limit on the number of timeframes (%d).\n", p->pPars->nFrameMax );
            p->pPars->iFrame = k;

            return -1;
          }
      }
    assert (0);
    return -1;
  }    


  Aig_Obj_t *Pdr::getInit (Aig_Man_t *pAig)
  {
    if (!pAig) pAig = m_pAig;

    Aig_Obj_t *pRes;
    
    int nRegs = Aig_ManRegNum (m_pAig);
    assert (nRegs > 0);
    Aig_Obj_t **ppIntputs = ABC_ALLOC (Aig_Obj_t*, nRegs);
    for (int i = 0; i < nRegs; ++i)
      ppIntputs [i] = Aig_Not (Aig_ManCi (pAig, i));
    pRes = Aig_Multi (pAig, ppIntputs, nRegs, AIG_OBJ_AND);
    
    ABC_FREE (ppIntputs);
    return pRes;
  }
  
  
}
