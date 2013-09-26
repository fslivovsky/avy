#ifndef _AVYMAIN_H_
#define _AVYMAIN_H_

#include "AigUtils.h"
#include "SafetyVC.h"
#include "ItpSatSolver.h"
#include "Unroller.h"
#include <string>
#include "boost/logic/tribool.hpp"
#include "boost/foreach.hpp"

namespace avy
{
  class AvyMain
  {
    std::string m_fName;
    
    AigManPtr m_Aig;

    /** reference to the current VC */
    SafetyVC *m_Vc;
    
    /** refernece to the current Sat solver */
    ItpSatSolver m_Solver;
    Unroller<ItpSatSolver> m_Unroller;

  public:
    AvyMain(std::string fname);
    
    virtual ~AvyMain() {}

    int run ();

    boost::tribool doBmc (unsigned nFrame);
    bool validateItp (AigManPtr itp);
  };
}


#endif /* _AVYMAIN_H_ */






