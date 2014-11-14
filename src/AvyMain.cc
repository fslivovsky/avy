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
#include "boost/scoped_ptr.hpp"
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
    m_fName (fname), m_Vc (0), m_pPdr(0)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    m_Aig = aigPtr (loadAig (fname));
    //m_pPdr = new Pdr (&*m_Aig);
  }
  
  AvyMain::AvyMain (AigManPtr pAig) :
    m_fName (std::string()), m_Aig(pAig), m_Vc (0), m_pPdr(0)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    //m_pPdr = new Pdr (&*m_Aig);
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
          ItpMinisat solver(2,2, gParams.itp_simp);
          Unroller<ItpMinisat> unroller(solver, true);
          return run(solver, unroller);
        }
      else if (gParams.glucose_itp)
        {
    	  ItpGlucose solver(2,2, gParams.itp_simp);
    	  Unroller<ItpGlucose> unroller(solver, true);
    	  return run(solver, unroller);
        }
      else
        {
          assert(false);
        }
  }

  template<typename Sat>
  int AvyMain::run (Sat& solver, Unroller<Sat>& unroller)
  {

    VERBOSE (1, 
             if (gParams.kStep > 1 && 
                 !gParams.stutter && !gParams.stick_error)
               vout () << "Warning: using kStep>1 without stuttering " 
                       << "or stick-error is unsound\n";);
    
    SafetyVC vc (&*m_Aig);
    m_Vc = &vc;
    m_pPdr = new Pdr (&*m_Aig);
 
    unsigned nMaxFrames = gParams.maxFrame;
    for (unsigned nFrame = 0; nFrame < nMaxFrames; nFrame+=gParams.kStep)
      {
        ScoppedStats loopStats (string(__FUNCTION__) + ".loop");
        Stats::set ("Result", "UNKNOWN");
        VERBOSE (2, Stats::PrintBrunch (vout ()););
        Stats::count("Frame");
        Stats::uset("Depth", nFrame);

        if (nFrame >= ((unsigned int)gParams.pdr))
          {
            VERBOSE(2, m_pPdr->setVerbose (true));
            int res = m_pPdr->solve ();
            VERBOSE (1, m_pPdr->statusLn (vout ()));
            if (res == 1) 
              {
                //vout () << "SAFE\n";
                outs () << "0\n\b0\n.\n";
                Stats::set("Result", "UNSAT");
                return m_pPdr->validateInvariant () ? 0 : 3;
              }
            else if (res == 0)
              {
                outs () << "1\n\b0\n.\n";
                Stats::set ("Result", "SAT");
                return 1;
              }
            else
              {
                Stats::set ("Result", "UNKNOWN");
                vout () << "UNKNOWN\n";
                return 2;
              }
          }
        
        tribool res = doBmc (nFrame, solver, unroller);
        if (res)
          {
            VERBOSE (1, 
                     vout () << "SAT from BMC at frame: " << nFrame << "\n";);
            Stats::set ("Result", "SAT");
            //printCex(solver, unroller, nFrame);
            return 1;
          }
        else if (!res)
          {
            VERBOSE(1, 
                    vout () << "UNSAT from BMC at frame: " << nFrame << "\n";);

            vector<int> vVarToId;
            AigManPtr itp =
              aigPtr (solver.getInterpolant (unroller.getAllOutputs (),
                                             Saig_ManRegNum(&*m_Aig)));

            Stats::uset ("OrigItp", Aig_ManAndNum (&*itp));
            // -- simplify
            if (gParams.itp_simplify)
            {
                itp = aigPtr (Aig_ManSimplifyComb (&*itp));
                Stats::uset("SimpItp", Aig_ManAndNum(&*itp));
                VERBOSE(2, Aig_ManPrintStats (&*itp));
            }
            VERBOSE (3, Stats::PrintBrunch (vout ()););

            AVY_ASSERT (validateItp (itp));

            if (doPdrTrace (itp))
              {
                outs () << "0\nb0\n.\n";
                VERBOSE(1, m_pPdr->statusLn (vout ()););
                Stats::set ("Result", "UNSAT");
                return m_pPdr->validateInvariant () ? 0 : 3;
              }

            doStrengthenVC ();
          }
        else 
          {
            VERBOSE (1, vout () << "UNKNOWN from BMC at frame: " 
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
        m_pPdr->ensureFrames (i+1);
        // -- skip if true
        if (Aig_ObjFanin0 (Aig_ManCo (&*itp, i)) == Aig_ManConst1 (&*itp)) continue;

        AigManPtr prevMan = aigPtr (Aig_ManStartFrom (&*itp));
        Aig_Obj_t *pPrev;
        pPrev = i == 0 ? Aig_ManConst0 (&*prevMan) : m_pPdr->getCover (i, &*prevMan);
        Aig_ObjCreateCo (&*prevMan, pPrev);
        pPrev = NULL;

        Stats::resume ("doPdrTrace_part1");
        AigManPtr dupMan = aigPtr (Aig_ManDupSinglePo (&*itp, i, false));
        AigManPtr orMan = aigPtr (Aig_ManCreateMiter (&*dupMan, &*prevMan, 2));
        
        dupMan.reset ();
        prevMan.reset ();

        AigManPtr newTr = aigPtr (Aig_ManReplacePo (&*m_Aig, &*orMan, true));
        newTr = aigPtr (Aig_ManGiaDup (&*newTr));
        Stats::stop ("doPdrTrace_part1");
        Stats::resume ("doPdrTrace_part2");

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
        Stats::stop ("doPdrTrace_part2");
        
        pdr.setVerbose (false);
        pdr.setGenConfLimit (gParams.genConfLimit);
        pdr.solveSafe ();
        
        Vec_PtrClear (pCubes);
        pdr.getCoverCubes (i == 0 ? 1 : 2, pCubes);
        if (gParams.reset_cover && i >= 1) m_pPdr->resetCover (i+1);
        m_pPdr->addCoverCubes (i+1, pCubes);
        Vec_PtrFree (pCubes);
        pCubes = NULL;
        
        int kMin = gParams.shallow_push ? i+1 : 1;
        int kMax = 0;
        
        // create place for pushing
        m_pPdr->ensureFrames (i+2);
        if (m_pPdr->push (kMin, kMax)) return true;
        
        VERBOSE(1, m_pPdr->statusLn (vout ()););
      }

    if ((gParams.shallow_push ||
        Aig_ObjFanin0 (Aig_ManCo (&*itp, itpSz - 1)) == Aig_ManConst1 (&*itp))
        && m_pPdr->push ()) return true;

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
    if (gParams.glucose)
      {
        Glucose sat (5000, gParams.sat_simp, gParams.glucose_inc_mode);
        return solveWithCore (sat, nFrame);
        //return incSolveWithCore(nFrame);
      }
    else
      {
        Minisat sat (5000);
        return solveWithCore (sat, nFrame);
      }
  }
  
  template <typename Sat>
  boost::tribool AvyMain::solveWithCore (Sat &sat, unsigned nFrame)
  {
    AVY_MEASURE_FN;
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
      printCex(sat, unroller);
      return res;
    }

    if (gParams.min_suffix)
      {
        // -- minimize suffix
        ScoppedStats _s_("solveWithCore_minSuffix");
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
    
    VERBOSE(2, vout () << "Assumption size: " << unroller.getAssumps ().size ()  
            << " core size: " << coreSz << "\n";);

    LitVector core (pCore, pCore + coreSz);
    // -- negate
    BOOST_FOREACH (lit &p, core) p = lit_neg (p);
    std::reverse (core.begin (), core.end ());

    if (gParams.min_core)
    {
      ScoppedStats __stats__("solveWithCore_minCore");
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

      VERBOSE(2, vout () << "Core size: original: " << coreSz 
              << " mincore: " << core.size () << "\n");
    }
    

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
    VERBOSE (1, vout () << "Validating ITP: ";);
    CnfPtr cnfItp = cnfPtr (Cnf_Derive (&*itp, Aig_ManCoNum (&*itp)));

    unsigned coNum = Aig_ManCoNum (&*itp);
    VERBOSE (1, vout() << "CoNum: " << coNum << "\n";);
    for (unsigned int i = 0; i <= coNum; ++i)
      {
        Glucose satSolver (2, 5000);
        Unroller<Glucose> unroller (satSolver);

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
            VERBOSE (1, vout () << "\nFailed validation at i: " << i << "\n";);
            return false;
          }
        else
          VERBOSE (1, vout () << "." << std::flush;);
      }
    
    VERBOSE (1, vout () << " Done\n" << std::flush;);
    return true;    
  }

  template<typename Sat>
  void AvyMain::printCex(Sat& s, Unroller<Sat>& unroller)
  {
    // -- skip cex if no output file is given
    if (gParams.cexFileName.empty ()) return;
    
    AVY_ASSERT (!gParams.stutter);
    AVY_ASSERT (gParams.tr0);
    
    VERBOSE(2, vout () << "Generating CEX: " << gParams.cexFileName << "\n";);
    boost::scoped_ptr<std::ofstream> pFout;
    std::ostream *pOut;
    
    if (gParams.cexFileName == "-")
      pOut = &outs ();
    else
    {
      pFout.reset (new std::ofstream (gParams.cexFileName.c_str (), 
                                      ofstream::out));
      pOut = pFout.get ();
    }

    std::ostream &out = *pOut;
    out << "1\n" << "b0\n";
    int nRegs = Aig_ManRegNum(&*m_Aig);
    // HACK: stick_error adds an extra latch
    if (gParams.stick_error) nRegs--;
    
    for (int i=0; i < nRegs; i++) out << "0";
    out << "\n";
    
    for (int i=0; i < unroller.frames (); i++) 
    {
      abc::Vec_Int_t* PIs = unroller.getPrimaryInputs (i);
      
      int j, input;
      
      // -- in the first frame, first PI is the reset signal
      if (i == 0)
      {
        input = Vec_IntEntry (PIs, 0);
        // reset PI is on, current frame does not count
        if (s.getVarVal(input)) continue;
      }
      
      Vec_IntForEachEntry(PIs, input, j)
      {
        // -- skipping the first input of the first and last
        // -- frames. It is used for reset and is not part of the
        // -- original circuit.
        if (j == 0 && (i == 0 || i + 1 == unroller.frames ())) continue;
        out << (s.getVarVal(input) ? "1" : "0");
      }
      out <<  "\n";
      if (gParams.stick_error && i + 1 < unroller.frames ())
      {
        abc::Vec_Int_t *vOuts = unroller.getOutputs (i);
        int output = Vec_IntEntry (vOuts, Vec_IntSize (vOuts) - 1);
        if (s.getVarVal (output))
        {
          VERBOSE(2, vout () << "Early CEX termination is untested!!!\n");
          // -- reached an early end of the counter-example
          break;
        }
      }
    }

    out << ".\n";
    out << std::flush;
    
  }

}
