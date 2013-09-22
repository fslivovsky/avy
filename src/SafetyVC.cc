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
  
  unsigned SafetyVC::addGlueCnf (ItpSatSolver &solver, unsigned nFrame, 
                                 unsigned nOldOffset, unsigned nNewOffset)
  {
    int i;
    Aig_Obj_t *pLo, *pLi;
    lit Lits[2];
    
    Saig_ManForEachLo (&*m_Tr, pLo, i)
      {
        pLi = Saig_ManLi (&*m_Tr, i);
        int liVar = m_cnfTr->pVarNums [pLi->Id];
        int loVar = m_cnfTr->pVarNums [pLo->Id];

        liVar += nOldOffset;
        loVar += nNewOffset;
        
        // -- add equality constraints
        Lits [0] = toLitCond (liVar, 0);
        Lits [1] = toLitCond (loVar, 1);
        solver.addClause (Lits, Lits+2, 0);
        
        Lits [0] = lit_neg (Lits [0]);
        Lits [1] = lit_neg (Lits [1]);
        solver.addClause (Lits, Lits+2, 0);
        
      }

    return nNewOffset;
  }

  unsigned SafetyVC::addTrCnf (ItpSatSolver &solver, unsigned nFrame, unsigned nOffset)
  {
    // add clauses for initial state
    if (nFrame == 0)
      {
        Aig_Obj_t *pObj;
        int i;
        lit Lits[1];
        
        Saig_ManForEachLo (&*m_Tr, pObj, i)
          {
            Lits[0] = toLitCond (m_cnfTr->pVarNums [pObj->Id], 0);
            solver.addClause (Lits, Lits + 1, nOffset);
          }
      }

    // -- add clauses
    for (int i = 0; i < m_cnfTr->nClauses; ++i)
      {
        AVY_VERIFY (solver.addClause (m_cnfTr->pClauses [i], 
                                      m_cnfTr->pClauses[i+1], nOffset));
      }
    

    return addGlueCnf (solver, nFrame, nOffset, nOffset + cnfVarSize (nFrame));
  }
  
  unsigned SafetyVC::addBadCnf (ItpSatSolver &solver, unsigned nOffset)
  {
    // -- add clauses
    for (int i = 0; i < m_cnfBad->nClauses; ++i)
      AVY_VERIFY (solver.addClause (m_cnfBad->pClauses [i], 
                                    m_cnfBad->pClauses[i+1], nOffset));
    
    return nOffset + badVarSize ();
  }
}
