#include <vector>
#include <string>

#include "boost/logic/tribool.hpp"
#include "boost/logic/tribool_io.hpp"
#include "boost/noncopyable.hpp"
#include "boost/program_options.hpp"
namespace po = boost::program_options;

#include "AigUtils.h"
#include "Minisat.h"
#include "Glucose.h"


#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "SafetyVC.h"
#include "SafetyAigVC.h"
#include "AigPrint.h"

#include "base/main/main.h"
#include "aig/ioa/ioa.h"
#include "avy/Util/Stats.h"

#include "Unroller.h"
#include "simp/SimpSolver.h"



using namespace boost;
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
  std::string cmd = "read " + fname;
  Cmd_CommandExecute (pFrame, cmd.c_str ());
    
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk (pFrame);
    
  return Abc_NtkToDar (pNtk, 0, 1);
}

static std::string gCnfFile;
static bool gDoBmc;


namespace avy
{
  class AvyBmc : boost::noncopyable
  {
  private:
    std::string m_FName;
    bool m_doBmc;
    AigManPtr m_Aig;

    std::string m_CnfFile;
    
  public:
    AvyBmc (std::string fname, bool doBmc);
    ~AvyBmc ();
    
    boost::tribool run (unsigned uDepth);
    
    template <typename Sat> 
    boost::tribool bmc (SafetyAigVC& vc, Sat &solver, Unroller<Sat>& unroller, unsigned uDepth);
    
    void setCnfFile (std::string &cnf) { m_CnfFile = cnf; }
    
    
  };

  AvyBmc::AvyBmc (std::string fname, bool doBmc = true) : 
    m_FName (fname), m_doBmc (doBmc)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    m_Aig = aigPtr (loadAig (fname));
  }

  AvyBmc::~AvyBmc () { Abc_Stop (); }
  
  tribool AvyBmc::run (unsigned uDepth)
  {
    Stats::set ("Result", "UNKNOWN");
    VERBOSE (1, Stats::PrintBrunch (outs ()););
    tribool res;

    SafetyAigVC vc (&*m_Aig);

    if (gParams.glucose)
      {
    	Glucose sat (5000, gParams.sat_simp);
    	Unroller<Glucose> unroller (sat, false);
        for (unsigned f = 0; f <= uDepth; f++)
        {
            res = bmc (vc, sat, unroller, f);
            if (res) break;
        }
      }
    else
      {
    	Minisat sat (5000, gParams.sat_simp);
    	Unroller<Minisat> unroller (sat, false);
        for (unsigned f = 0; f <= uDepth; f++)
		{
		    res = bmc (vc, sat, unroller, f);
		    if (res) break;
		}
      }
    
    VERBOSE (1, Stats::PrintBrunch (outs ()););
    return res;
    
  }
  
  template <typename Sat>
  tribool AvyBmc::bmc (SafetyAigVC& vc, Sat &solver, Unroller<Sat>& unroller, unsigned uDepth)
  {
    AVY_MEASURE_FN;

    unroller.resetLastFrame();
    if (uDepth > 1) unroller.setFrozenOutputs(uDepth-1, false);
    for (unsigned i = unroller.frame(); i <= uDepth; ++i)
    {
      vc.addTr (unroller);
      unroller.newFrame ();
    }
    unroller.setFrozenOutputs(uDepth, true);
    vc.addBad (unroller);
   // unroller.pushBadUnit ();

    if (m_CnfFile != "") solver.dumpCnf (m_CnfFile);
    
    tribool res = false;
    if (m_doBmc)
    {
      std::vector<int> assumptions;
      assumptions.push_back(unroller.getBadLit());
      ScoppedStats _s_ ("solve");
      VERBOSE (1, vout () << "Solving " << uDepth << " ...\n" << std::flush;);
      res = solver.solve (assumptions);
      lit p = lit_neg(assumptions[0]);
      solver.addClause(&p, &p+1);
      VERBOSE(1, vout () << "Result: " << std::boolalpha << res << "\n");
      if (res) Stats::set ("Result", "SAT");
      else if (!res) Stats::set ("Result", "UNSAT");
    }
    
    return res;
  } 
}

static std::string parseCmdLine (int argc, char**argv)
{
  po::options_description generic("Options");
  generic.add_options()
    ("help", "print help message")
    ("print-params", "print current parameters")
    ("log,L", po::value< std::vector<std::string> >(), "log levels to enable")
    ("verbose,v", po::value<unsigned> (&gParams.verbosity)->default_value(0),
     "Verbosity level: 0 means silent")
    ("stutter,s", 
     po::value<bool> (&gParams.stutter)->default_value (false)->implicit_value(true),
     "Stutter circuit instead of reseting to the initial state")
    ("tr0",
     po::value<bool> (&gParams.tr0)->default_value (false)->implicit_value(true),
     "Make only Tr0 be special (stutter or reset init)")
    ("sat1",
     po::value<bool> (&gParams.sat1)->default_value (false)->implicit_value (true),
     "Always use satSolver (do not use satSolver2)")
    ("minisat",
     po::value<bool> (&gParams.minisat)->default_value(false)->implicit_value (true),
     "Use Minisat 2.2.0 for abstraction")
    ("glucose",
     po::value<bool> (&gParams.glucose)->default_value(false)->implicit_value (true),
     "Use Glucose for abstraction")
    ("stick-error",
     po::value<bool> (&gParams.stick_error)->default_value (false)->implicit_value (true),
     "Stick error output")
     ("itp-simplify",
      po::value<bool> (&gParams.itp_simplify)->default_value (true),
      "Simplify the interpolant using synthesis")
    ("depth",
     po::value<unsigned> (&gParams.maxFrame)->default_value (1),
     "BMC depth")
    ("dump-cnf",
     po::value<std::string> (&gCnfFile),
     "File to dump CNF of the unrolling")
    ("bmc",
     po::value<bool> (&gDoBmc)->default_value(true)->implicit_value (true),
     "Do BMC")
      ("sat-simp", 
     po::value<bool> (&gParams.sat_simp)->default_value (true)->implicit_value(true),
     "Enable pre-processing for the non-interpolating SAT solver (if available)")
    ("glucose-inc-mode", 
     po::value<bool> (&gParams.glucose_inc_mode)->default_value(false)->implicit_value(true),
     "Enable Glucose incremental mode")
	("opt-bmc",
	 po::value<bool> (&gParams.opt_bmc)->default_value(true)->implicit_value(true),
	 "Enable optimized BMC");

  
  po::options_description hidden("Hidden options");
  hidden.add_options()
    ("input-file", po::value< std::string >(), "input file");        

  po::options_description cmdline;
  cmdline.add (generic).add (hidden);  

  po::positional_options_description p;
  p.add("input-file", -1);

  try
    {
      po::variables_map vm;
      po::store(po::command_line_parser(argc, argv).
                options(cmdline).positional(p).run(), vm);
      po::notify(vm);

      if (vm.count("help")) {
        outs () << generic << "\n";
        std::exit (1);
      }
  
      if (vm.count ("print-params"))
        {
          outs () << gParams << "\n";
          std::exit (1);
        }

      if (!vm.count("input-file"))
        {
          outs () << "Error: No AIG file specified\n";
          std::exit (1);
        }

      if (vm.count("log"))
        {
          using namespace std;
          vector<string> logs = vm["log"].as< vector<string> > ();
          for (vector<string>::iterator it = logs.begin (), end = logs.end (); 
               it != end; ++it)
            AvyEnableLog (it->c_str ());
        }

      gParams.fName = vm["input-file"].as< std::string > ();

      VERBOSE(2, vout () << gParams << "\n";);
  
      return gParams.fName;
    }
  catch (std::exception &e)
    {
      outs () << "Error: " << e.what () << "\n";
      std::exit (1);
    }
}


int main (int argc, char**argv)
{
  std::string fileName = parseCmdLine (argc, argv);
  AvyBmc bmc (fileName, gDoBmc);
  bmc.setCnfFile (gCnfFile);

  tribool res = bmc.run (gParams.maxFrame);
  if (res) return 1;
  else if (!res) return 0;
  else return 2;
}

