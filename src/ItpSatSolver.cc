#include "ItpSatSolver.h"
#include "misc/vec/vec.h"
#include "sat/bsat/satStore.h"

#include "avy/Util/Global.h" 
#include "avy/Util/Stats.h" 
namespace avy
{
  /// Compute an interpolant. User provides the list of shared variables
  /// Variables can only be shared between adjacent partitions.
  /// fMcM == true for McMillan, and false for McMillan'
  // XXX Why is vSharedVars not Vec_Vec_t? It would make it easier to grow
  Aig_Man_t* ItpSatSolver::getInterpolant (std::vector<Vec_Int_t*> &vSharedVars, 
                                           bool fMcM)
  {
    Stats::resume ("sat1.itp");
    AVY_ASSERT (!isTrivial ());
    AVY_ASSERT (m_pSat != NULL);
    AVY_ASSERT (vSharedVars.size () == m_nParts - 1);
    
    AVY_VERIFY (!solve ());
    
    Sto_Man_t* pSatCnf = (Sto_Man_t*) sat_solver_store_release( m_pSat );
    sat_solver_delete( m_pSat );
    m_pSat = NULL;
      

    // Create the interpolating manager and extract the interpolation-seq
    // with m_nParts-1 interpolants
    Ints_Man_t* pManInter = Ints_ManAlloc(m_nParts-1);
    // XXX how to wire fMcM properly?
    Aig_Man_t* pMan = (Aig_Man_t *) Ints_ManInterpolate( pManInter,
                                                         pSatCnf, 
                                                         0, (void**)&vSharedVars[0],
                                                         0 );
    Ints_ManFree( pManInter );

    Aig_Man_t *tmp = Aig_ManSimplifyComb (pMan);
    Aig_ManStop (pMan);
    pMan = tmp; tmp = NULL;

    VERBOSE(1, Aig_ManPrintStats(pMan););

    // Release memory
    Sto_ManFree( pSatCnf );
    Stats::stop ("sat1.itp");
    return pMan;
  }
  
}
