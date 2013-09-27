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
    m_fName (fname), m_Vc (0), m_Solver(2, 2), 
    m_Unroller (m_Solver), m_pPdr(0)
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

    m_pPdr = new Pdr (&*m_Aig);
    
    
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

                // -- simplify
                itp = aigPtr (Aig_ManSimplifyComb (&*itp));
                
                if (doPdrTrace (itp)) 
                  {
                    VERBOSE (0, vout () << "SAFE\n");
                    return 0;
                  }

                doStrengthenVC ();
                
              }
          }
        else 
          {
            VERBOSE (0, vout () << "UNKNOWN from BMC at frame: " 
                     << nFrame << "\n";);
            return 2;
          }
      }
    return 3;
  }

  /// Strengthen VC using current PDR trace
  void AvyMain::doStrengthenVC ()
  {
    m_Vc->resetPreCond ();
    Vec_Ptr_t *pCubes = Vec_PtrAlloc (16);
    

    /**
                    I0      I1      I2
       Init & TR(0) & TR(1) & TR(2) & Bad
            F0      F1      F2      F3
       add F1 to pre of TR(1), F2 to pre of TR(2), etc.
     */

    for (unsigned i = 1; i < m_pPdr->maxFrames (); ++i)
      {
        Vec_PtrClear (pCubes);
        m_pPdr->getCoverCubes (i, pCubes);
        Pdr_Set_t *pCube;
        int j;
        Vec_PtrForEachEntry (Pdr_Set_t*, pCubes, pCube, j)
          m_Vc->addPreCondClause (pCube->Lits, (pCube->Lits) + pCube->nLits, i, true);
        
      }
    
    Vec_PtrFree (pCubes);
    
  }
  

  /// convert interpolant into PDR trace
  tribool AvyMain::doPdrTrace (AigManPtr itp)
  {
    VERBOSE (1, vout () << "Building PDR trace\n");
    unsigned itpSz = Aig_ManCoNum (&*itp);
    
    for (unsigned i = 0; i < itpSz; ++i)
      { 
        // -- skip if true
        if (Aig_ObjFanin0 (Aig_ManCo (&*itp, i)) == Aig_ManConst1 (&*itp)) continue;

        AigManPtr prevMan = aigPtr (Aig_ManStartFrom (&*itp));
        Aig_Obj_t *pPrev;
        pPrev = i == 0 ? Aig_ManConst0 (&*prevMan) : m_pPdr->getCover (i, &*prevMan);
        Aig_ObjCreateCo (&*prevMan, pPrev);
        pPrev = NULL;

        AigManPtr dupMan = aigPtr (Aig_ManDupSinglePo (&*itp, i, false));
        AigManPtr orMan = aigPtr (Aig_ManCreateMiter (&*dupMan, &*prevMan, 2));
        
        dupMan.reset ();
        prevMan.reset ();

        AigManPtr newTr = aigPtr (Aig_ManReplacePo (&*m_Aig, &*orMan, true));
        newTr = aigPtr (Aig_ManGiaDup (&*newTr));

        Pdr pdr (&*newTr);
        
        Vec_Ptr_t *pCubes = Vec_PtrAlloc(16);
        pdr.setLimit (i == 0 ? 2 : 3);
        if (i >= 1)
          {
            pCubes = Vec_PtrAlloc (16);
            m_pPdr->getCoverCubes (i, pCubes);
            pdr.addCoverCubes (1, pCubes);
            
            Vec_PtrClear (pCubes);
            m_pPdr->getCoverCubes (i+1, pCubes);
            pdr.addCoverCubes (2, pCubes);
            Vec_PtrClear (pCubes);
          }
        pdr.solveSafe ();
        
        Vec_PtrClear (pCubes);
        pdr.getCoverCubes (i == 0 ? 1 : 2, pCubes);
        m_pPdr->addCoverCubes (i+1, pCubes);
        Vec_PtrFree (pCubes);
        pCubes = NULL;
        
        if (m_pPdr->push ()) return true;
        
        VERBOSE(1, m_pPdr->statusLn (vout ()););
      }
    
    return boost::indeterminate;
  }

    
  tribool AvyMain::doBmc (unsigned nFrame)
  {
    m_Solver.reset (nFrame + 2, 5000);
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
    logs () << "Assumptions: " << m_Unroller.getAssumps ().size () << "\n";
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

        
        if (satSolver.solve (unroller.getAssumps ()) != false) 
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













