#include "AvyMain.h"
#include "boost/lexical_cast.hpp"
#include "avy/Util/Global.h"
#include "SafetyVC.h"
#include "AigPrint.h"

#include "base/main/main.h"
#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"

#include "Unroller.h"

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
    m_fName (fname), m_Vc (0), m_Solver(2, 2), m_Unroller (m_Solver)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    
    Aig_Man_t *pAig1 = loadAig (fname);
    
    Aig_Man_t *pAig2;

    if (gParams.stutter)
      {
        VERBOSE (2, vout () << "\tAdding stutering signal\n");
        pAig2 = Aig_AddStutterPi (pAig1);
      }
    else
      {
        VERBOSE (2, vout () << "\tAdding reset signal\n");
        pAig2 = Aig_AddResetPi (pAig1);
      }

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
        Stats::PrintBrunch (outs ());
        Stats::count("Frame");
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
                AigManPtr itp = 
                  aigPtr (m_Solver.getInterpolant (m_Unroller.getAllOutputs ()));
                (logs () << "Interpolant is: \n").flush ();
                LOG("itp_verbose", logs () << *itp << "\n";);
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
    m_Unroller.reset (&m_Solver);
    

    for (unsigned i = 0; i <= nFrame; ++i)
      {
        m_Vc->addTr (m_Unroller);
        m_Solver.markPartition (i);
        m_Unroller.newFrame ();
      }
    m_Vc->addBad (m_Unroller);
    m_Solver.markPartition (nFrame + 1);

    LOG("dump_cnf", 
        m_Solver.dumpCnf ("frame" + lexical_cast<string>(nFrame+1) + ".cnf"););

    LOG("dump_shared",
        std::vector<abc::Vec_Int_t *> &vShared = m_Unroller.getAllOutputs ();
        logs () << "Shared size: " << vShared.size () << "\n";
        for (unsigned i = 0; i < vShared.size (); ++i)
          {
            int j;
            Vec_Int_t *vVec = vShared [i];
            int nVar;
            logs () << i << ": ";
            Vec_IntForEachEntry (vVec, nVar, j)
              logs () << nVar << " ";
            logs () << "\n";
          });
    
    // -- do not expect assumptions yet
    AVY_ASSERT (m_Unroller.getAssumps ().empty ());
    return m_Solver.solve (m_Unroller.getAssumps ());
  }
  
  bool AvyMain::validateItp (AigManPtr itp)
  {
    outs () << "Validating ITP: ";
    CnfPtr cnfItp = cnfPtr (Cnf_Derive (&*itp, Aig_ManCoNum (&*itp)));

    unsigned coNum = Aig_ManCoNum (&*itp);
    for (unsigned i = 0; i <= coNum; ++i)
      {
        ItpSatSolver satSolver (2, 5000);
        Unroller<ItpSatSolver> unroller (satSolver);
        
        if (i > 0)
          {
            unroller.freshBlock (cnfItp->nVars);
            unroller.addCnf (&*cnfItp);
            
            // -- assert Itp_{i-1}
            lit Lit = toLit (cnfItp->pVarNums [Aig_ManCo (&*itp, i-1)->Id]);
            satSolver.addClause (&Lit, &Lit + 1);
            
            // -- register outputs
            Aig_Obj_t *pCi;
            int j;
            Aig_ManForEachCi (&*itp, pCi, j)
              unroller.addOutput (cnfItp->pVarNums [pCi->Id]);
            
            unroller.newFrame ();
          }

        if (i < coNum)
          {
            m_Vc->addTr (unroller);
            unroller.newFrame ();
            
            unsigned nOffset = unroller.freshBlock (cnfItp->nVars);
            ScoppedCnfLift scLift (cnfItp, nOffset);
            unroller.addCnf (&*cnfItp);
            Aig_Obj_t *pCi;
            int j;
            Aig_ManForEachCi (&*itp, pCi, j)
              unroller.addInput (cnfItp->pVarNums [pCi->Id]);
            unroller.glueOutIn ();
            
            // -- assert !Itp_i
            lit Lit = toLitCond (cnfItp->pVarNums [Aig_ManCo (&*itp, i)->Id], 1);
            unroller.addClause (&Lit, &Lit + 1);
          }
        else
          m_Vc->addBad (unroller);

        
        if (satSolver.solve () != false) 
          {
            errs () << "\nFailed validation at i: " << i << "\n";
            return false;
          }
        else
          outs () << "." << std::flush;
        
      }
    
    outs () << " Done\n" << std::flush;
    return true;    
  }
}













