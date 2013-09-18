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

using namespace std;

std::string parseCmdLine (int argc, char** argv)
{
  po::options_description generic("Options");
  generic.add_options()
    ("help", "produce help message")
    ("log,L", po::value< vector<string> >(), "log levels to enable");

  po::options_description hidden("Hidden options");
  hidden.add_options()
    ("input-file", po::value< string >(), "input file");        

  po::options_description cmdline;
  cmdline.add (generic).add (hidden);  

  po::positional_options_description p;
  p.add("input-file", -1);

  po::variables_map vm;
  po::store(po::command_line_parser(argc, argv).
            options(cmdline).positional(p).run(), vm);
  po::notify(vm);

  if (vm.count("help")) {
    cout << generic << "\n";
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
        avy::AvyEnableLog (it->c_str ());
    }

  return vm["input-file"].as< string > ();
}


int main(int argc, char* argv[])
{
  std::string fileName = parseCmdLine (argc, argv);

  ClsItpSeqMc cism(fileName);
  cism.prove();
}


