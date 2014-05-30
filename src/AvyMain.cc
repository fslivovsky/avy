#include "AvyMain.h"
#include "boost/lexical_cast.hpp"
#include "avy/Util/Global.h"
#include "SafetyVC.h"
#include "AigPrint.h"

#include "base/main/main.h"
#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"

#include "Unroller.h"
#include "boost/range/algorithm/copy.hpp"

#include "simp/SimpSolver.h"

#include <fstream>

using namespace boost;
using namespace std;
using namespace avy;
using namespace avy::abc;



namespace ABC_NAMESPACE
{
  extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
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
    m_Unroller (m_Solver, true), m_pPdr(0)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    m_Aig = aigPtr (loadAig (fname));
    m_pPdr = new Pdr (&*m_Aig);
  }
  
  AvyMain::AvyMain (AigManPtr pAig) :
    m_fName (std::string()), m_Aig(pAig), m_Vc (0), m_Solver(2, 2),
    m_Unroller (m_Solver, true), m_pPdr(0)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    m_pPdr = new Pdr (&*m_Aig);
  }

  AvyMain::~AvyMain() 
  { 
    if (m_pPdr) delete m_pPdr; 
    Abc_Stop ();
  }

  int AvyMain::run ()
  {
      if (gParams.minisat_itp)
        {
          ItpMinisat solver(2,2);
          Unroller<ItpMinisat> unroller(solver, true);
          return run(solver, unroller);
        }
      else if (gParams.glucose_itp)
        {
    	  ItpGlucose solver(2,2);
    	  Unroller<ItpGlucose> unroller(solver, true);
    	  return run(solver, unroller);
        }
      else
        {
          ItpSatSolver solver(2,2);
          Unroller<ItpSatSolver> unroller(solver, true);
          return run(solver, unroller);
        }
  }

  template<typename Sat>
  int AvyMain::run (Sat& solver, Unroller<Sat>& unroller)
  {

    if (gParams.kStep > 1 && !gParams.stutter)
      outs () << "Warning: using kStep>1 without stuttering is unsound\n";
    SafetyVC vc (&*m_Aig);
    m_Vc = &vc;

    unsigned nMaxFrames = gParams.maxFrame;
    for (unsigned nFrame = 0; nFrame < nMaxFrames; nFrame+=gParams.kStep)
      {
        ScoppedStats loopStats (string(__FUNCTION__) + ".loop");
        Stats::set ("Result", "UNKNOWN");
        Stats::PrintBrunch (outs ());
        Stats::count("Frame");
        Stats::uset("Depth", nFrame);

        if (nFrame >= ((unsigned int)gParams.pdr))
          {
            VERBOSE(2, m_pPdr->setVerbose (true));
            int res = m_pPdr->solve ();
            VERBOSE (1, m_pPdr->statusLn (vout ()));
            if (res == 1) 
              {
                outs () << "SAFE\n";
                Stats::set("Result", "UNSAT");
                return m_pPdr->validateInvariant () ? 0 : 3;
              }
            else if (res == 0)
              {
                outs () << "CEX\n";
                Stats::set ("Result", "SAT");
                return 1;
              }
            else
              {
                Stats::set ("Result", "UNKNOWN");
                outs () << "UNKNOWN\n";
                return 2;
              }
          }
        
        tribool res = doBmc (nFrame, solver, unroller);
        if (res)
          {
            VERBOSE (0, 
                     vout () << "SAT from BMC at frame: " << nFrame << "\n";);
            Stats::set ("Result", "SAT");
            //printCex(solver, unroller, nFrame);
            return 1;
          }
        else if (!res)
          {
            VERBOSE(0, 
                    vout () << "UNSAT from BMC at frame: " << nFrame << "\n";);
            if (solver.isTrivial () && typeid(solver) == typeid(ItpSatSolver))
              {
                Stats::count("Trivial");
                m_pPdr->setLimit (unroller.frame () + 1);
                int nPdrRes = m_pPdr->solve ();
                // -- Check if a CEX exists
                if (nPdrRes == 0)
                  {
                    // A CEX. Let BMC find it...
                    continue;
                  }
                if (nPdrRes == 1)
                  {
                    VERBOSE (1, m_pPdr->statusLn (vout ()););
                    Stats::set ("Result", "UNSAT");
                    return m_pPdr->validateInvariant () ? 0 : 3;
                  }
                m_pPdr->setLimit (100000);
                // logs () << *m_pPdr << "\n";
                // PrintAig (logs (), &*m_Aig, m_pPdr->getCover (1, &*m_Aig));
                // logs () << "\n";
                AVY_ASSERT (m_pPdr->validateTrace ());
              }
            else
              {
                vector<int> vVarToId;
                AigManPtr itp = 
                  aigPtr (solver.getInterpolant (unroller.getAllOutputs (),
                                                 Saig_ManRegNum(&*m_Aig)));

                // -- simplify
                if (gParams.itp_simplify)
                {
                    itp = aigPtr (Aig_ManSimplifyComb (&*itp));
                    Stats::uset("SimpItp", Aig_ManAndNum(&*itp));
                    VERBOSE(2, Aig_ManPrintStats (&*itp));
                }

                AVY_ASSERT (validateItp (itp));

                if (doPdrTrace (itp)) 
                  {
                    VERBOSE (0, vout () << "SAFE\n");
                    VERBOSE(1, m_pPdr->statusLn (vout ()););
                    Stats::set ("Result", "UNSAT");
                    return m_pPdr->validateInvariant () ? 0 : 3;
                  }
              }
            doStrengthenVC ();
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
    AVY_MEASURE_FN;
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
    AVY_MEASURE_FN;
    AVY_MEASURE_FN_LAST;
    
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
          }

        Vec_PtrClear (pCubes);
        m_pPdr->getCoverCubes (i+1, pCubes);
        pdr.addCoverCubes (i == 0 ? 1 : 2, pCubes);
        Vec_PtrClear (pCubes);

        pdr.solveSafe ();
        
        Vec_PtrClear (pCubes);
        pdr.getCoverCubes (i == 0 ? 1 : 2, pCubes);
        if (gParams.reset_cover && i >= 1) m_pPdr->resetCover (i+1);
        m_pPdr->addCoverCubes (i+1, pCubes);
        Vec_PtrFree (pCubes);
        pCubes = NULL;
        
        int kMin = gParams.shallow_push ? i+1 : 1;
        int kMax = 0;
        
        if (m_pPdr->push (kMin, kMax)) return true;
        
        VERBOSE(1, m_pPdr->statusLn (vout ()););
      }
    
    if (gParams.shallow_push && m_pPdr->push ()) return true;

    AVY_ASSERT (m_pPdr->validateTrace ());
    return boost::tribool (boost::indeterminate);
  }
    
  template<typename Sat>
  tribool AvyMain::doBmc (unsigned nFrame, Sat& solver, Unroller<Sat>& unroller)
  {
    AVY_MEASURE_FN;

    tribool res;
    m_Core.clear ();
    if ((res = solveWithCore (nFrame)) != false) return res;
    
    solver.reset (nFrame + 2, 5000);
    unroller.reset (&solver);
    unroller.setEnabledAssumps (m_Core);
    
    for (unsigned i = 0; i <= nFrame; ++i)
      {
    	if (gParams.minisat_itp || gParams.glucose_itp) {
    		solver.markPartition (i+1);
    		m_Vc->addTr (unroller);
    		unroller.newFrame ();
    	}
    	else {
    		m_Vc->addTr (unroller);
    		solver.markPartition (i);
			  unroller.newFrame ();
    	}

      }
    if (gParams.minisat_itp || gParams.glucose_itp) {
    	solver.markPartition (nFrame + 2);
    	m_Vc->addBad (unroller);
    	unroller.pushBadUnit ();
    }
    else {
    	m_Vc->addBad (unroller);
    	unroller.pushBadUnit ();
    	solver.markPartition (nFrame + 1);
    }


    LOG("dump_cnf", 
        solver.dumpCnf ("frame" + lexical_cast<string>(nFrame+1) + ".cnf"););

    LOG("dump_shared",
        std::vector<Vec_Int_t *> &vShared = unroller.getAllOutputs ();
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

    logs () << "Assumptions: " << unroller.getAssumps ().size () << "\n";
    BOOST_FOREACH (int a, unroller.getAssumps ())
      logs () << a << " ";
    logs () << "\n";
    
    // -- do not expect assumptions yet
    AVY_ASSERT (unroller.getAssumps ().empty ());

    LitVector bad;
    bad.push_back (unroller.getBadLit ());
    res = solver.solve ();
    // if (res == false)
    //   {
    //     AVY_ASSERT (unroller.pushBadUnit ());
    //     solver.markPartition (nFrame + 1);
    //     AVY_VERIFY (!solver.solve ());
    //   }
    return res;
  }

  boost::tribool AvyMain::solveWithCore (unsigned nFrame)
  {
    if (gParams.sat1)
      {
        ItpSatSolver sat (2, 2);
        return solveWithCore (sat, nFrame);
      }
    else if (gParams.minisat)
      {
        Minisat sat (5000);
        return solveWithCore (sat, nFrame);
      }
    else if (gParams.glucose)
      {
        Glucose sat (5000);
        return solveWithCore (sat, nFrame);
        //return incSolveWithCore(nFrame);
      }
    else
      {
        ItpSatSolver2 sat (2);
        return solveWithCore (sat, nFrame);
      }

  }
  
  template <typename Sat>
  boost::tribool AvyMain::solveWithCore (Sat &sat, unsigned nFrame)
  {
    Unroller<Sat> unroller (sat, true);

    for (unsigned i = 0; i <= nFrame; ++i)
      {
        m_Vc->addTr (unroller);
        unroller.newFrame ();
      }
    m_Vc->addBad (unroller);
    unroller.pushBadUnit ();
    
    // -- freeze
    BOOST_FOREACH (lit Lit, unroller.getAssumps ()) sat.setFrozen (lit_var (Lit), true);

    tribool res;
    if ((res = sat.solve (unroller.getAssumps ())) != false)
    {
      printCex(sat, unroller, nFrame);
      return res;
    }

    if (gParams.min_suffix)
      {
        // -- minimize suffix
        ScoppedStats _s_("min_suffix");
        LitVector assumps;
        
        assumps.reserve (unroller.getAssumps ().size ());
        for (int i = unroller.frame (); i >= 0; --i)
          {
            boost::copy (unroller.getFrameAssumps (i), std::back_inserter (assumps));
            res = sat.solve (assumps);
            if (!res)
              {
                VERBOSE(2, if (i > 0) vout () << "Killed " << i << " of prefix\n";);
                break;
              }
          }
      }
    
    int *pCore;
    int coreSz = sat.core (&pCore);
    
    VERBOSE(2, logs () << "Assumption size: " << unroller.getAssumps ().size ()  
            << " core size: " << coreSz << "\n";);

    LitVector core (pCore, pCore + coreSz);
    // -- negate
    BOOST_FOREACH (lit &p, core) p = lit_neg (p);
    std::reverse (core.begin (), core.end ());

    Stats::resume ("unsat_core");
    for (unsigned int i = 0; gParams.min_core && core.size () > 1 && i < core.size (); ++i)
      {
        lit tmp = core [i];
        core[i] = core.back ();
        if (!sat.solve (core, core.size () - 1))
          {
            core.pop_back ();
            --i;
          }
        else
          core[i] = tmp;
      }
    Stats::stop ("unsat_core");

    VERBOSE(2, if (gParams.min_core)
                 logs () << "Core size: original: " << coreSz 
                         << " mincore: " << core.size () << "\n");
    

    m_Core.reset ();
    for (unsigned i = 0; i < core.size (); ++i)
      {
        unsigned int a = core [i];
        if (m_Core.size () <= a) m_Core.resize (a + 1);
        m_Core.set (a);
      }
    return false;
  }
  
  bool AvyMain::validateItp (AigManPtr itp)
  {
    outs () << "Validating ITP: ";
    CnfPtr cnfItp = cnfPtr (Cnf_Derive (&*itp, Aig_ManCoNum (&*itp)));

    unsigned coNum = Aig_ManCoNum (&*itp);
    outs() << "CoNum: " << coNum << "\n";
    for (unsigned int i = 0; i <= coNum; ++i)
      {
        ItpSatSolver satSolver (2, 5000);
        Unroller<ItpSatSolver> unroller (satSolver);

        // -- fast forward the unroller to the right frame
        while (i >= 2 && unroller.frame () < i-1) unroller.newFrame  ();

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
          {
            m_Vc->addBad (unroller);
            unroller.pushBadUnit ();
          }
        

        
        if (satSolver.solve (unroller.getAssumps ()) != false) 
          {
            outs () << "\nFailed validation at i: " << i << "\n";
            return false;
          }
        else
          outs () << "." << std::flush;
      }
    
    outs () << " Done\n" << std::flush;
    return true;    
  }
}

template<typename Sat>
void AvyMain::printCex(Sat& s, Unroller<Sat>& unroller, unsigned nFrame)
{
  outs() << "Printing CEX\n";
  ofstream o("witness.cex", ofstream::out);
  o << "1\n" << "b0\n";
  int nRegs = Aig_ManRegNum(&*m_Aig);
  for (int i=0; i < nRegs; i++)
    o << "0";
  o << "\n";
  for (int i=0; i <= nFrame; i++) {
    abc::Vec_Int_t* PIs = unroller.getPrimaryInputs(i);
    int j, input;
    Vec_IntForEachEntry(PIs, input, j) {
      o << (s.getVarVal(input) ? "1" : "0");
    }
    o <<  "\n";
  }

  // For some reason, aigsim needs another transition?
  abc::Vec_Int_t* PIs = unroller.getPrimaryInputs(nFrame);
  int j, input;
  Vec_IntForEachEntry(PIs, input, j) {
    o << "x";
  }
  o <<  "\n";
  o << ".\n";
  o.close();
}













