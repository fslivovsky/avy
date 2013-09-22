#include "ItpSatSolver.h"
#include "misc/vec/vec.h"
#include "sat/bsat/satStore.h"

#include "avy/Util/Global.h" 
namespace avy
{
  /// Compute an interpolant. User provides the list of shared variables
  /// Variables can only be shared between adjacent partitions.
  /// fMcM == true for McMillan, and false for McMillan'
  // XXX Why is vSharedVars not Vec_Vec_t? It would make it easier to grow
  Aig_Man_t* ItpSatSolver::getInterpolant (Vec_Int_t** vSharedVars, bool fMcM)
  {
    AVY_ASSERT (!isTrivial ());
    AVY_ASSERT (m_pSat != NULL);
    //AVY_ASSERT (size of vSharedVars == m_nParts);
    
    AVY_VERIFY (!solve ());
    
    Sto_Man_t* pSatCnf = (Sto_Man_t*) sat_solver_store_release( m_pSat );
    sat_solver_delete( m_pSat );
    m_pSat = NULL;
      

    // Create the interpolating manager and extract the interpolation-seq
    // XXX is it m_nParts or m_nParts+1?
    // XXX Ints_ManAlloc (x), requires x to be the number of computed interpolants
    // XXX this is nParts - 1
    Ints_Man_t* pManInter = Ints_ManAlloc(m_nParts);
    // XXX how to wire fMcM properly?
    Aig_Man_t* pMan = (Aig_Man_t *) Ints_ManInterpolate( pManInter,
                                                         pSatCnf, 
                                                         0, (void**)vSharedVars,
                                                         0 );
    Ints_ManFree( pManInter );

    Aig_Man_t *tmp = Aig_ManSimplifyComb (pMan);
    Aig_ManStop (pMan);
    pMan = tmp; tmp = NULL;

    VERBOSE(1, Aig_ManPrintStats(pMan););

    // Release memory
    Sto_ManFree( pSatCnf );
    return pMan;
  }
  
}
