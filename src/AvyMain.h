#ifndef _AVYMAIN_H_
#define _AVYMAIN_H_

#include "AigUtils.h"
#include "SafetyVC.h"
#include "ItpSatSolver.h"
#include <string>
#include "boost/logic/tribool.hpp"

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
    
  public:
    AvyMain(std::string fname);
    
    virtual ~AvyMain()
    {
      
    }
    

    int run ();

    boost::tribool doBmc (unsigned nFrame);
    
  
  };
}


#endif /* _AVYMAIN_H_ */
