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
        << "END";
    return out;
  }
  

}

