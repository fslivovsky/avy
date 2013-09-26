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

    std::vector<Vec_Int_t *> m_vShared;
    
  public:
    AvyMain(std::string fname);
    
    virtual ~AvyMain()
    { BOOST_FOREACH (Vec_Int_t *p, m_vShared) Vec_IntFree (p); }
    

    int run ();

    boost::tribool doBmc (unsigned nFrame);
    bool validateItp (AigManPtr itp);

    boost::tribool doBmcOld (unsigned nFrame);
    
  
  };
}


#endif /* _AVYMAIN_H_ */






