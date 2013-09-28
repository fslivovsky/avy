#include "SafetyVC.h"
#include "AigPrint.h"

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

    AigManPtr aig;
    if (gParams.stutter)
      aig = aigPtr (Aig_AddStutterPi (&*m_Circuit));
    else 
      {
        aig = aigPtr (Aig_AddResetPi (&*m_Circuit));
        if (gParams.stick_error)
          aig = aigPtr (Aig_AddStutterPi (&*aig));
      }
    
    
    // -- construct Tr 
    Aig_Man_t *pTr0 = Aig_ManDupNoPo (&*aig);
    Aig_ManRebuild (&pTr0);
    m_Tr0 = aigPtr (pTr0);
    m_cnfTr0 = cnfPtr (Cnf_Derive (&*m_Tr0, Aig_ManRegNum (&*m_Tr0)));    

    if (gParams.tr0)
      {
        Aig_Man_t *pTr = Aig_ManDupNoPo (&*m_Circuit);
        Aig_ManRebuild (&pTr);
        m_Tr = aigPtr (pTr);
        m_cnfTr = cnfPtr (Cnf_Derive (&*m_Tr, Aig_ManRegNum (&*m_Tr)));
      }
    else
      {
        m_Tr = m_Tr0;
        m_cnfTr = m_cnfTr0;
      }
    
    
    AVY_ASSERT (Saig_ManRegNum (&*m_Tr0) == Saig_ManRegNum (&*m_Tr));

    // -- construct Bad
    Aig_Man_t *pBad = Aig_ManDupSinglePo (&*aig, 0, false);
    Aig_ManRebuild (&pBad);
    m_Bad = aigPtr (pBad);
    m_cnfBad = cnfPtr (Cnf_Derive (&*m_Bad, Aig_ManCoNum (&*m_Bad)));

    LOG ("tr", logs () 
         << "m_Circuit is: " << *m_Circuit << "\n"
         << "m_Tr is: \n " << *m_Tr << "\n"
         << "m_Bad is: " << *m_Bad << "\n";);
  }
}
