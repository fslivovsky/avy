#include "avy/Util/AvyDebug.hpp"
#include "avy/Util/AvyAssert.hpp"

#include <string>
#include <set>

#ifndef NAVYLOG
using namespace avy;

bool avy::AvyLogFlag = false;
std::set<std::string> avy::AvyLog;

void avy::AvyEnableLog (std::string x) 
{
  if (x.empty ()) return;
  AvyLogFlag = true;
  AvyLog.insert (x); 
}



#else
#endif

