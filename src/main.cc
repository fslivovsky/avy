/*
 * main.cc
 *
 *  Created on: Jul 29, 2013
 *      Author: yakir
 */

#include "ClsItpSeqMc.h"
#include <iostream>
#include <cstdlib>
#include <vector>

#include "boost/program_options.hpp"
namespace po = boost::program_options;

#include "AvyMain.h"
#include "avy/Util/Global.h"

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
    ("avy", po::value<bool> (&gParams.avy)->default_value(false));
  

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

  if (gParams.avy)
    {
      AvyMain avy (fileName);
      return avy.run ();
    }
  else
    {
      ClsItpSeqMc cism(fileName);
      cism.prove();
    }
}


