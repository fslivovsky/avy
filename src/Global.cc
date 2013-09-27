#include "avy/Util/Global.h"

namespace avy
{
  AvyParams gParams;

  std::ostream &operator<< (std::ostream& out, const AvyParams& p)
  {
    out << "AVY PARAMETERS\n"
        << "\tfName = " << p.fName << "\n"
        << "\tipt = " << p.itp << "\n"
        << "\tavy = " << p.avy << "\n"
        << "\tstutter = " << p.stutter << "\n"
        << "\treset_cover = " << p.reset_cover << "\n"
        << "\tshallow_push = " << p.shallow_push << "\n"
        << "END";
    return out;
  }
  

}

