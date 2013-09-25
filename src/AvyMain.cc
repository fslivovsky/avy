#include "AvyMain.h"
#include "boost/lexical_cast.hpp"
#include "avy/Util/Global.h"
#include "SafetyVC.h"
#include "AigPrint.h"

#include "base/main/main.h"
#include "aig/ioa/ioa.h"

using namespace boost;
using namespace std;
using namespace abc;
using namespace avy;



namespace abc
{
  extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, 
                                   int fRegisters );
}

static Aig_Man_t *loadAig (std::string fname)
{
  Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame ();
    
  VERBOSE (2, vout () << "\tReading AIG from '" << fname << "'\n";);
  string cmd = "read " + fname;
  Cmd_CommandExecute (pFrame, cmd.c_str ());
    
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk (pFrame);
    
  return Abc_NtkToDar (pNtk, 0, 1);
}


namespace avy
{
  AvyMain::AvyMain (std::string fname) : 
    m_fName (fname), m_Vc (0), m_Solver(2, 2), m_vShared (0)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    
    Aig_Man_t *pAig1 = loadAig (fname);
    
    VERBOSE (2, vout () << "\tAdding reset signal\n");
    Aig_Man_t *pAig2 = Aig_AddResetPi (pAig1);
    Aig_ManStop (pAig1);
    pAig1 = NULL;
    
    string tmpName = "__tmp.aig";
    VERBOSE (2, vout () << "\tDumping to disk: " << tmpName << "\n");
    Ioa_WriteAiger (pAig2, const_cast<char*>(tmpName.c_str ()), 1, 0);

    VERBOSE(2, vout () << "Restarting ABC\n");
    Abc_Stop ();
    Abc_Start ();

    m_Aig = aigPtr (loadAig (tmpName));

    // -- keep abc running, just in case
    //Abc_Stop ()
    
    
  }  

  int AvyMain::run ()
  {
    SafetyVC vc (&*m_Aig);
    m_Vc = &vc;

    unsigned nMaxFrames = 100;
    for (unsigned nFrame = 0; nFrame < 100; ++nFrame)
      {
        tribool res = doBmc (nFrame);
        if (res)
          {
            VERBOSE (0, vout () << "SAT from BMC at frame: " << nFrame << "\n";);
            return 1;
          }
        else if (!res)
          {
            VERBOSE(0, vout () << "UNSAT from BMC at frame: " << nFrame << "\n";);
            if (m_Solver.isTrivial ()) 
              logs () << "Trivialy UNSAT\n";
            else
              {
                AigManPtr itp = aigPtr (m_Solver.getInterpolant (m_vShared));
                (logs () << "Interpolant is: \n").flush ();
                Aig_ManPrintStats (&*itp);

                AVY_ASSERT (validateItp (itp));
              }
          }
        else 
          {
            VERBOSE (0, vout () << "UNKNOWN from BMC at frame: " 
                     << nFrame << "\n";);
            return 2;
          }
      }
    return 0;
  }

  tribool AvyMain::doBmc (unsigned nFrame)
  {
    m_Solver.reset (nFrame + 2, m_Vc->varSize (0, nFrame, true));
    m_vShared.clear ();

    for (unsigned i = 0; i < nFrame+1; i++) 
      m_vShared.push_back (Vec_IntAlloc (0));
    
    
    unsigned nOffset = 0;
    unsigned nLastOffset = 0;
    
    for (unsigned i = 0; i <= nFrame; ++i)
      {
        nLastOffset = nOffset;
        nOffset = m_Vc->addTrCnf (m_Solver, i, nOffset);
        m_Solver.markPartition (i);

        if (i < nFrame) 
          nOffset = m_Vc->addTrGlue (m_Solver, i, nLastOffset, nOffset, m_vShared [i]);
        LOG("dump_cnf",
            m_Solver.dumpCnf ("frame" + lexical_cast<string>(nFrame) + ".cnf"););
      }

    nOffset = m_Vc->addBadGlue (m_Solver, nLastOffset, nOffset, m_vShared [nFrame]);
    nOffset = m_Vc->addBadCnf (m_Solver, nOffset);
    m_Solver.markPartition (nFrame + 1);
    LOG("dump_cnf", 
        m_Solver.dumpCnf ("frame" + lexical_cast<string>(nFrame+1) + ".cnf"););


    LOG("dump_shared",
        logs () << "Shared size: " << m_vShared.size () << "\n";
        for (unsigned i = 0; i < m_vShared.size (); ++i)
          {
            int j;
            Vec_Int_t *vVec = m_vShared [i];
            int nVar;
            logs () << i << ": ";
            Vec_IntForEachEntry (vVec, nVar, j)
              logs () << nVar << " ";
            logs () << "\n";
          });
    
    

    LitVector assumps;
    return m_Solver.solve (assumps);
  }
  
  
  bool AvyMain::validateItp (AigManPtr itp)
  {
    CnfPtr cnfItp = cnfPtr (Cnf_Derive (&*itp, Aig_ManCoNum (&*itp)));
   
    
    unsigned coNum = Aig_ManCoNum (&*itp);
    for (unsigned i = 0; i <= coNum; ++i)
      {
        unsigned nVars = cnfItp->nVars + m_Vc->trVarSize (i);
        if (0 < i && i < coNum ) nVars += cnfItp->nVars;
        else if (i  == coNum) nVars += m_Vc->badVarSize ();
        
                  
        ItpSatSolver satSolver (2, nVars);
        unsigned trOffset = 0;
        
        if (i > 0)
          {
            for (int j = 0; j < cnfItp->nClauses; ++j)
              satSolver.addClause (cnfItp->pClauses [j], cnfItp->pClauses [j+1]);
            trOffset += cnfItp->nVars;

            // glue 
            lit Lits[2];
            int j;
            Aig_Obj_t *pCi;
            Aig_ManForEachCi (&*itp, pCi, j)
              {
                Lits [0] = toLitCond (cnfItp->pVarNums [pCi->Id], 0);
                Lits [1] = toLitCond (m_Vc->getTrLoVar (j, i, trOffset), 1);
                satSolver.addClause (Lits, Lits + 2);
                Lits [0] = lit_neg (Lits [0]);
                Lits [1] = lit_neg (Lits [1]);
                satSolver.addClause (Lits, Lits + 2);
              }
            
          }

        
        unsigned nPostOffset = m_Vc->addTrCnf (satSolver, i, trOffset);
        
        if (i  < coNum)
          {
            ScoppedCnfLift scLift (cnfItp, nPostOffset);
            for (int j = 0; j < cnfItp->nClauses; ++j)
              satSolver.addClause (cnfItp->pClauses [j], cnfItp->pClauses [j+1]);

            // -- glue
            int j;
            Aig_Obj_t *pObj;
            Aig_ManForEachCi (&*itp, pObj, j)
              {
                lit Lits[2];
                Lits [0] = toLitCond (cnfItp->pVarNums [pObj->Id], 0);
                Lits [1] = toLitCond (m_Vc->getTrLiVar (j, i, trOffset), 1);
                satSolver.addClause (Lits, Lits + 2);
                Lits [0] = lit_neg (Lits [0]);
                Lits [1] = lit_neg (Lits [1]);
                satSolver.addClause (Lits, Lits + 2);
              }
          }
        else
          {
            nPostOffset = m_Vc->addBadGlue (satSolver, trOffset, nPostOffset);
            nPostOffset = m_Vc->addBadCnf (satSolver, nPostOffset);
          }
        if (satSolver.solve () != false) return false;
      }
    return true;
  }
}













