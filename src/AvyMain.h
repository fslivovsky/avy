#ifndef _AVYMAIN_H_
#define _AVYMAIN_H_

#include "AigUtils.h"
#include "SafetyVC.h"
#include "ItpSatSolver.h"
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

    std::vector<Vec_Int_t *> m_vShared;
    
  public:
    AvyMain(std::string fname);
    
    virtual ~AvyMain()
    {
      BOOST_FOREACH (Vec_Int_t *p, m_vShared) Vec_IntFree (p);
    }
    

    int run ();

    boost::tribool doBmc (unsigned nFrame);
    bool validateItp (AigManPtr itp);
    
  
  };
}


#endif /* _AVYMAIN_H_ */
