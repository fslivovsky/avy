#include "SafetyVC.h"

#include "aig/saig/saig.h"

using namespace std;
using namespace avy;
using namespace abc;

namespace avy
{

  void SafetyVC::init (Aig_Man_t *pCircuit)
  {
    AVY_ASSERT (Saig_ManPoNum(pCircuit) - Saig_ManConstrNum(pCircuit) == 1);
    AVY_ASSERT (Saig_ManConstrNum(pCircuit) == 0);

    // -- save circuit
    m_Circuit = aigPtr (Aig_ManDupSimple (pCircuit));
    
    // -- construct Tr 
    Aig_Man_t *pTr = Aig_ManDupNoPo (pCircuit);
    Aig_ManRebuild (&pTr);
    m_Tr = aigPtr (pTr);
    m_cnfTr = cnfPtr (Cnf_Derive (m_Tr.get (), Aig_ManRegNum (m_Tr.get ())));    

    // -- construct Bad
    Aig_Man_t *pBad = Aig_ManDupSinglePo (pCircuit, 0, false);
    Aig_ManRebuild (&pBad);
    m_Bad = aigPtr (pBad);
    m_cnfBad = cnfPtr (Cnf_Derive (&*m_Tr, Aig_ManCoNum (&*m_Bad)));
  }
}
