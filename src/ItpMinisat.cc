#include "ItpMinisat.h"
#include "misc/vec/vec.h"

#include "AigPrint.h"
#include "avy/Util/Global.h" 
#include "avy/Util/Stats.h"

#include "MinisatItpSeq.h"

namespace avy
{
  /// Compute an interpolant. User provides the list of shared variables
  /// Variables can only be shared between adjacent partitions.
  /// fMcM == true for McMillan, and false for McMillan'
  Aig_Man_t* ItpMinisat::getInterpolant (std::vector<int> &vVarToId, int nNumOfVars)
  {
    AVY_MEASURE_FN;
    AVY_ASSERT (!isTrivial ());
    AVY_ASSERT (m_pSat != NULL);
    AVY_ASSERT (vVarToId.size () >= m_nParts - 1);
    
    AVY_VERIFY (!solve ());
    
    MinisatItpSeq itpSeqVisitor(*m_pSat, nNumOfVars, vVarToId, m_nParts);
    m_pSat->replay(itpSeqVisitor);

    Aig_Man_t* pMan = Gia_ManToAigSimple(itpSeqVisitor.getInterpolantMan());

    VERBOSE(2, Aig_ManPrintStats(pMan););
    LOG("itp_verbose", logs () << *pMan << "\n";);


    // Release memory
    Sto_ManFree( pSatCnf );
    return pMan;
  }
  
}
