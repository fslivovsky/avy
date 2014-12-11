#include "SafetyAigVC.h"
#include "AigPrint.h"

#include "aig/saig/saig.h"

using namespace std;
using namespace avy;
using namespace avy::abc;

namespace avy
{

  void SafetyAigVC::init (Aig_Man_t *pCircuit)
  {
    AVY_ASSERT (Saig_ManPoNum(pCircuit) - Saig_ManConstrNum(pCircuit) == 1);
    AVY_ASSERT (Saig_ManConstrNum(pCircuit) == 0);

    // XXX HACK
    // XXX For combinatorial circuits, enable stick_error transformation that adds a latch
    // XXX This converts a combinatorial circuit into a trivial sequential one
    // XXX
    if (Saig_ManRegNum (pCircuit) == 0 && !gParams.stick_error) 
    {
      VERBOSE (2, vout () << "Combinatorial circuit. Enabling stick_error\n";);
      gParams.stick_error = 1;
    }
    
    // -- save circuit
    m_Circuit = aigPtr (Aig_ManDupSimple (pCircuit));


    AigManPtr aig;
    AigManPtr stuckErrorAig;
    if (gParams.stutter)
      aig = aigPtr (Aig_AddStutterPi (&*m_Circuit));
    else 
      {
        if (gParams.stick_error)
          {
            stuckErrorAig = aigPtr (Aig_AddStutterPo (&*m_Circuit));
            aig = stuckErrorAig;
            // XXX HACK XXX
            // Add one extra reg to the INPUT circuit
            Aig_ObjCreateCi (pCircuit);
            Aig_ObjCreateCo (pCircuit, Aig_ManConst0 (pCircuit));
            Aig_ManSetRegNum (pCircuit, pCircuit->nRegs + 1);
            m_Circuit = aigPtr (Aig_ManDupSimple (pCircuit));
          }
        else
          aig = m_Circuit;
        
        aig = aigPtr (Aig_AddResetPi (&*aig));
      }
        
    // -- construct Tr 
    Aig_Man_t *pTr0 = Aig_ManDupNoPo (&*aig);
    Aig_ManRebuild (&pTr0);
    Aig_Man_t* pNewTr0 = Aig_DupWithCiVals(pTr0, frameVals[0]);
    m_Tr0 = aigPtr (pNewTr0);

    if (gParams.tr0)
      {
        Aig_Man_t *pTr;
        if (gParams.stick_error)
          pTr = Aig_ManDupNoPo (&*stuckErrorAig);
        else
          pTr = Aig_ManDupNoPo (&*m_Circuit);
        
        Aig_ManRebuild (&pTr);
        m_MasterTr = aigPtr(pTr);
        Aig_TernarySimulate(pTr, 1, frameVals);
        Aig_Man_t* pNewTr = Aig_DupWithCiVals(pTr, frameVals[1]);
        m_Tr.push_back(aigPtr (pNewTr));
      }
    else
      {
        m_Tr.push_back(m_Tr0);
      }
    
    
    //AVY_ASSERT (Saig_ManRegNum (&*m_Tr0) == Saig_ManRegNum (&*m_Tr));

    // -- construct Bad
    Aig_Man_t *pBad = Aig_ManDupSinglePo (&*aig, 0, false);
    Aig_ManRebuild (&pBad);
    m_Bad = aigPtr (pBad);
    m_cnfBad = cnfPtr (Cnf_Derive (&*m_Bad, Aig_ManCoNum (&*m_Bad)));

    LOG ("tr", logs () 
         << "m_Circuit is: " << *m_Circuit << "\n"
         << "m_Tr is: \n " << *m_Tr[0] << "\n"
         << "m_Bad is: " << *m_Bad << "\n";);
  }
}
