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
        << "\treset-cover = " << p.reset_cover << "\n"
        << "\tshallow_push = " << p.shallow_push << "\n"
        << "\tmin-core = " << p.min_core << "\n"
        << "\tabstraction = " << p.abstraction << "\n"
        << "\ttr0 = " << p.tr0 << "\n"
        << "\tpdr = " << p.pdr << "\n"
        << "\tmin-suffix = " << p.min_suffix << "\n"
        << "\tsat1 = " << p.sat1 << "\n"
        << "\tminisat = " << p.minisat << "\n"
        << "\tglucose = " << p.glucose << "\n"
        << "\tkstep = " << p.kStep << "\n"
        << "\tstick-error = " << p.stick_error << "\n"
        << "\titp-simplify = " << p.itp_simplify << "\n"
        << "\tmax-frame = " << p.maxFrame << "\n"
        << "END";
    return out;
  }
  

}

