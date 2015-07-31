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
    m_fName (fname), m_Vc (0), m_OptVc(0), m_pPdr(0)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    m_Aig = aigPtr (loadAig (fname));
    //m_pPdr = new Pdr (&*m_Aig);
  }
  
  AvyMain::AvyMain (AigManPtr pAig) :
    m_fName (std::string()), m_Aig(pAig), m_Vc (0), m_OptVc(0), m_pPdr(0)
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
    
    SafetyAigVC optVc (&*m_Aig);
    m_OptVc = &optVc;
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
              aigPtr (solver.getInterpolant (unroller.getBadLit(), unroller.getAllOutputs (),
                                             Saig_ManRegNum(&*m_Aig)));

            //lit good = lit_neg(unroller.getBadLit());
            //solver.addClause(&good, &good+1);
            Stats::uset ("OrigItp", Aig_ManAndNum (&*itp));
            // -- simplify
            if (gParams.itp_simplify)
            {
                itp = aigPtr (Aig_ManSimplifyComb (&*itp));
                Stats::uset("SimpItp", Aig_ManAndNum(&*itp));
                VERBOSE(2, Aig_ManPrintStats (&*itp));
            }
            VERBOSE (3, Stats::PrintBrunch (vout ()););

            findItpConstraints(itp, m_OptVc->getFrameEquivs());

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
    m_OptVc->resetPreCond ();
    Vec_Ptr_t *pCubes = Vec_PtrAlloc (16);
    

    /**
                    I0      I1      I2
       Init & TR(0) & TR(1) & TR(2) & Bad
            F0      F1      F2      F3
       add F1 to pre of TR(1), F2 to pre of TR(2), etc.
     */

    /*Aig_Man_t* pAig = Aig_ManStart( 5000 );
    for (int i=0; i < m_Aig->nRegs; i++)
    	Aig_ObjCreateCi(pAig);
    Aig_Obj_t* pCo = Aig_ObjCreateCo(pAig, Aig_ManConst1(pAig));*/

    for (unsigned i = 1; i < m_pPdr->maxFrames (); ++i)
      {
        Vec_PtrClear (pCubes);
        m_pPdr->getCoverCubes (i, pCubes);
        Pdr_Set_t *pCube;
        int j;
        Vec_PtrForEachEntry (Pdr_Set_t*, pCubes, pCube, j)
        {
          m_Vc->addPreCondClause (pCube->Lits, (pCube->Lits) + pCube->nLits, i, true);
          m_OptVc->addPreCondClause (pCube->Lits, (pCube->Lits) + pCube->nLits, i, true);
        }
        //Aig_Obj_t* p = m_pPdr->getCover(i, pAig);
        //Aig_ObjDisconnect(pAig, pCo);
        //Aig_ObjConnect(pAig, pCo, p, NULL);
        //m_OptVc->resimplifyFrame(pAig, i-1);
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

    m_Core.clear ();
    tribool res = solveWithCore (solver, unroller, nFrame);
    return res;
  }

  template <typename Sat>
  boost::tribool AvyMain::solveWithCore (Sat &sat, Unroller<Sat>& unroller, unsigned nFrame)
  {
    AVY_MEASURE_FN;

    unroller.resetLastFrame();
    if (nFrame > 1) unroller.setFrozenOutputs(nFrame-1, false);
    for (unsigned i = unroller.frame(); i <= nFrame; ++i)
      {
        sat.markPartition (i+1);
        m_OptVc->addTr (unroller);
        unroller.newFrame ();
      }
    unroller.setFrozenOutputs(nFrame, true);
    sat.markPartition (nFrame + 2);
    m_OptVc->addBad (unroller);
    //unroller.pushBadUnit ();
    lit badLit = unroller.getBadLit();
    unroller.addAssump(badLit);
    
    // -- freeze
    BOOST_FOREACH (lit Lit, unroller.getAssumps ()) sat.setFrozen (lit_var (Lit), true);

    tribool res;
    if ((res = sat.solve (unroller.getAssumps ())) != false)
    {
      printCex(sat, unroller);
      return res;
    }

    unroller.getAssumps().pop_back();

    if (gParams.min_suffix)
      {
        // -- minimize suffix
        ScoppedStats _s_("solveWithCore_minSuffix");
        LitVector assumps;
        assumps.push_back(badLit);
        
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
        if (core[i] == badLit)
        	continue;
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

  bool AvyMain::findItpConstraints (AigManPtr& itp, vector<vector<int> >& equivFrames)
  {
      AVY_MEASURE_FN;
    VERBOSE (1, vout () << "FINDING NEEDED CONSTRAINTS: ";);

    //Aig_Man_t* itp = *pItpMan;
    unsigned coNum = Aig_ManCoNum (&*itp);
    VERBOSE (1, vout() << "CoNum: " << coNum << " EquivNum: " << equivFrames.size() << "\n";);

    bool bChanged = false;
    CnfPtr cnfItp = cnfPtr (Cnf_Derive (&*itp, Aig_ManCoNum (&*itp)));

    for (unsigned int i = coNum; i > 0; --i)
      {
    	// -- skip if true
		//if (Aig_ObjFanin0 (Aig_ManCo (&*itp, i-1)) == Aig_ManConst1 (&*itp)) continue;

		// Need to rederive the CNF in case it was changed
    	if (bChanged) {
    		//itp = *pItpMan;
    		cnfItp = cnfPtr (Cnf_Derive (&*itp, Aig_ManCoNum (&*itp)));
    		bChanged = false;
    	}

        Glucose satSolver (2, false, true);
        Unroller<Glucose> unroller (satSolver);

        // -- fast forward the unroller to the right frame
        while (i >= 2 && unroller.frame () < i-1) unroller.newFrame  ();

        // For now store a semi-map from the index of an equivalence
		// to the generated literal that represents it.
		// This should be thought of, maybe a full map is a better choice
		// as the memory is going to be taken only during the execution of
		// this function, and not through out the execution of AVY
		// map<lit, int> litToEquiv
		vector<lit> equivToLit;
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

            // Take care of equivalence constraints
            const vector<int>& equiv_i = equivFrames[i-1];
            bool bNoConstraints = true;
            for (int x = 0; x < equiv_i.size() && bNoConstraints; x++)
                if (equiv_i[x] != -1)
                    bNoConstraints = false;
            if (bNoConstraints &&
                Aig_ObjFanin0 (Aig_ManCo (&*itp, i-1)) == Aig_ManConst1 (&*itp)) break;
            if (bNoConstraints) {
                VERBOSE (1, vout () << "." << std::flush;);
                continue;
            }

            equivToLit.resize(equiv_i.size(), -1);
            for (unsigned j = 0; j < equiv_i.size(); j++)
            {
            	int val = equiv_i[j];
            	if (val == 0 || val == 1)
            	{
            		// Negative value means a constant: -2 is Const0 and -3 is Const1
            		int a = unroller.freshVar ();
                    lit aLit = toLit (a);
                    lit Lit[2];
                    Lit[0] = lit_neg(aLit);
            		Lit[1] = toLitCond (cnfItp->pVarNums [Aig_ManCi (&*itp, j)->Id], 1);
            		if (val == 0)
            			unroller.addClause(Lit, Lit + 2);
            		else
            		{
            			Lit[1] = lit_neg(Lit[1]);
            			unroller.addClause(Lit, Lit + 2);
            		}
            		unroller.addAssump(aLit);
            		equivToLit[j] = aLit;
            	}
            	else if (val != -1)
            	{
            		// This CI equals to the CI at '|(val/2)-1|' location
            	    bool neg = (val < 0);
            	    if (val < 0) val *= -1;
            	    int loc = (val / 2) - 1;
            		int a = unroller.freshVar ();
					lit aLit = toLit (a);
            		lit Lit[3];
            		Lit[0] = lit_neg(aLit);
            		Lit[1] = toLit(cnfItp->pVarNums [Aig_ManCi (&*itp, j)->Id]);
            		Lit[2] = toLitCond(cnfItp->pVarNums [Aig_ManCi (&*itp, loc)->Id], !neg);
            		unroller.addClause(Lit, Lit + 3);
            		Lit[1] = lit_neg (Lit[1]);
  	     	        Lit[2] = lit_neg (Lit[2]);
	                unroller.addClause (Lit, Lit+3);

	                unroller.addAssump(aLit);
	                equivToLit[j] = aLit;
            	}
            }

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
            // Assuming that it already contains the needed equivalence
            // constraints
            lit Lit = toLitCond (cnfItp->pVarNums [Aig_ManCo (&*itp, i)->Id], 1);
            unroller.addClause (&Lit, &Lit + 1);
          }
        else
          {
            m_Vc->addBad (unroller);
            unroller.pushBadUnit ();
          }


        //boost::tribool res = satSolver.solve ();
        boost::tribool res = satSolver.solve (unroller.getAssumps ());
        if (res == true)
          {
            VERBOSE (1, vout () << "\nFailed implication at i: " << i << "\n";);
            return false;
          }
        else if (res == false)
        {
          VERBOSE (1, vout () << "." << std::flush;);
          if (i > 0)
          {
            int *pCore;
            int coreSz = satSolver.core(&pCore);
            LitVector core (pCore, pCore + coreSz);
            // -- negate
            BOOST_FOREACH (lit &p, core) p = lit_neg (p);
            /*std::reverse (core.begin (), core.end ());
            for (unsigned int x = 0; core.size () > 1 && x < core.size (); ++x)
              {
                lit tmp = core [x];
                core[x] = core.back ();
                if (!satSolver.solve (core, core.size () - 1))
                {
                  core.pop_back ();
                  --x;
                }
                else
                  core[x] = tmp;
              }*/
            if (core.size() > 0) printf("YESS\n");
            else continue;
            vector<int>& equivs = equivFrames[i-1];
            Aig_Obj_t* pEq = Aig_ManConst1(&*itp);
            for (int j=0; j < equivs.size(); j++)
            {
            	bool found = false;
            	for (int c=0; c < core.size() && !found; c++)
            		if (core[c] == equivToLit[j])
            			found = true;

            	// If the quivalence was not used, remove it from the vector
            	// Need to check that this does not add extra complexity in
            	// subsequent calls to the SAT-sweeper. Maybe this is not
            	// needed, or maybe it should be done on a copy of the
            	// original vector.
            	//if (!found)
            	//	equivs[j] = -1;
            	if (found)
            	{
            		// Track the constraints
            		int val = equivs[j];
            		if (val == 0 || val == 1)
            			if (val == 0)
            				pEq = Aig_And(&*itp, pEq, Aig_Not(Aig_ManCi(&*itp, j)));
            			else
            				pEq = Aig_And(&*itp, pEq, Aig_ManCi(&*itp, j));
            		else if (val != -1)
            		{
            		    bool neg = (val < 0);
                        if (val < 0) val *= -1;
                        int loc = (val / 2) - 1;
            			// Create an AIG expression representing
            			// the equivalence
            		    Aig_Obj_t* p1 = Aig_ManCi(&*itp, j);
            		    Aig_Obj_t* p2 = Aig_ManCi(&*itp, loc);
            		    if (neg)
            		        p2 = Aig_Not(p2);
            		    Aig_Obj_t* t =
            		      Aig_And(&*itp,
            		    		  Aig_Or(&*itp, p1, Aig_Not(p2)),
								  Aig_Or(&*itp, Aig_Not(p1), p2));

            		    pEq = Aig_And(&*itp, pEq, t);
            		}

            		//if (i < coNum-1) equivs[j] = -1;
            	}
            }

            // If there were equivalences used, pEq is going to be different
            // than TRUE
            if (Aig_ObjIsConst1(Aig_Regular(pEq)) == false)
            {
            	// In this case, add the constraints to the interpolant
            	Aig_Obj_t* pItp = Aig_ObjChild0(Aig_ManCo(&*itp, i-1));
            	pItp = Aig_And(&*itp, pItp, pEq);
            	//Aig_ObjPatchFanin0(&*itp, Aig_ManCo(&*itp, i-1), pItp);
            	Aig_ObjDisconnect(&*itp, Aig_ManCo(&*itp, i-1));
            	Aig_ObjConnect(&*itp, Aig_ManCo(&*itp, i-1), pItp, NULL);
            	Aig_Man_t* p = &*itp;
            	//Aig_ManRebuild(&*itp, itp);
            	bChanged = true;
            }
          }
        }
      }

    //pItp = &itp;
    VERBOSE (1, vout () << " Done\n" << std::flush;);
    return true;
  }

}
