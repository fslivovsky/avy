/*
 * main.cc
 *
 *  Created on: Jul 29, 2013
 *      Author: yakir
 */

#include <iostream>
#include <cstdlib>
#include <vector>

#include "boost/dynamic_bitset.hpp"
#include "boost/program_options.hpp"
namespace po = boost::program_options;

#include "AvyMain.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"

using namespace std;
using namespace avy;

std::string parseCmdLine (int argc, char** argv)
{
  po::options_description generic("Options");
  generic.add_options()
    ("help", "produce help message")
    ("print-params", "print current parameters")
    ("log,L", po::value< vector<string> >(), "log levels to enable")
    ("itp", po::value<unsigned> (&gParams.itp)->default_value(0), 
     "Interpolation system: 0 - McM, 1 - Mcm-prime")
    ("verbose,v", po::value<unsigned> (&gParams.verbosity)->default_value(0),
     "Verbosity level: 0 means silent")
    ("avy", po::value<bool> (&gParams.avy)->implicit_value(true)->default_value (true))
    ("stutter,s", 
     po::value<bool> (&gParams.stutter)->default_value (false)->implicit_value(true),
     "Stutter circuit instead of reseting to the initial state")
    ("reset-cover", 
     po::value<bool> (&gParams.reset_cover)->default_value (false)->implicit_value(true),
     "Reset cover of global PDR before updating it")
    ("shallow-push", 
     po::value<bool> (&gParams.shallow_push)->default_value (false)->implicit_value (true),
     "Push only updated covers")
    ("min-core", 
     po::value<bool> (&gParams.min_core)->default_value (false)->implicit_value(true),
     "Minimize unsat core")
    ("abstraction,a",
     po::value<bool> (&gParams.abstraction)->default_value(false)->implicit_value(true),
     "Enable interface abstraction (one-assumption-per-wire)")
    ("tr0",
     po::value<bool> (&gParams.tr0)->default_value (false)->implicit_value(true),
     "Make only Tr0 be special (stutter or reset init)")
    ("pdr",
     po::value<int> (&gParams.pdr)->default_value (100000),
     "Frame at which to drop to PDR")
    ("min-suffix",
     po::value<bool> (&gParams.min_suffix)->default_value (false)->implicit_value(true),
     "Minimize the suffix of the interpolation sequence")
    ("sat1",
     po::value<bool> (&gParams.sat1)->default_value (false)->implicit_value (true),
     "Always use satSolver (do not use satSolver2)")
    ("minisat",
     po::value<bool> (&gParams.minisat)->default_value(false)->implicit_value (true),
     "Use Minisat 2.2.0 for abstraction")
    ("glucose",
     po::value<bool> (&gParams.glucose)->default_value(false)->implicit_value (true),
     "Use Glucose for abstraction")
     ("minisat_itp",
      po::value<bool> (&gParams.minisat_itp)->default_value(false)->implicit_value (true),
      "Use Minisat 2.2.0 for interpolation")
      ("glucose_itp",
	   po::value<bool> (&gParams.glucose_itp)->default_value(false)->implicit_value (true),
	   "Use Glucose for interpolation")
    ("kstep,k",
     po::value<unsigned> (&gParams.kStep)->default_value (1),
     "Step size for BMC problems")
    ("stick-error",
     po::value<bool> (&gParams.stick_error)->default_value (false)->implicit_value (true),
     "Stick error output")
     ("itp-simplify",
      po::value<bool> (&gParams.itp_simplify)->default_value (true),
      "Simplify the interpolant using synthesis")
    ("max-frame",
     po::value<unsigned> (&gParams.maxFrame)->default_value (100000),
     "Max BMC depth")
    ("gen-conf-limit",
     po::value<unsigned> (&gParams.genConfLimit)->default_value (0))
    ("sat-simp", 
     po::value<bool> (&gParams.sat_simp)->default_value (true)->implicit_value(true),
     "Enable pre-processing for the non-interpolating SAT solver (if available)")
    ("itp-simp", 
     po::value<bool> (&gParams.itp_simp)->default_value (true)->implicit_value(true),
     "Enable pre-processing during interpolation (if available)")
    ("proof-reorder",
     po::value<bool> (&gParams.proof_reorder)->default_value (false)->implicit_value(true),
     "Enable proof reordering for the interpolating SAT solver (if available)")
    ("glucose-inc-mode",
     po::value<bool> (&gParams.glucose_inc_mode)->default_value(false)->implicit_value(true),
     "Enable Glucose incremental mode")
    ("cex",
     po::value<std::string> (&gParams.cexFileName)->default_value (""),
     "Location to output counter-example")
	 ("opt-bmc",
	  po::value<bool> (&gParams.opt_bmc)->default_value(true)->implicit_value(true),
	  "Enable optimized BMC");
  
  
  po::options_description hidden("Hidden options");
  hidden.add_options()
    ("input-file", po::value< string >(), "input file");        

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
        cout << generic << "\n";
        std::exit (1);
      }
  
      if (vm.count ("print-params"))
        {
          cout << gParams << "\n";
          std::exit (1);
        }

      if (!vm.count("input-file"))
        {
          cout << "Error: No AIG file specified\n";
          std::exit (1);
        }

      if (vm.count("log"))
        {
          vector<string> logs = vm["log"].as< vector<string> > ();
          for (vector<string>::iterator it = logs.begin (), end = logs.end (); it != end; ++it)
            AvyEnableLog (it->c_str ());
        }

      gParams.fName = vm["input-file"].as< string > ();

      VERBOSE(2, vout () << gParams << "\n";);
  
      return gParams.fName;
    }
  catch (std::exception &e)
    {
      cout << "Error: " << e.what () << "\n";
      std::exit (1);
    }
  
}


int main(int argc, char* argv[])
{
  std::string fileName = parseCmdLine (argc, argv);
  int ret = 0;
  
  if (gParams.avy)
    {
      AvyMain avy (fileName);
      ret = avy.run ();
    }
  else
    {
      assert(false);
    }

  VERBOSE (1, Stats::PrintBrunch (outs ()););
  return ret;
}


