#ifndef _AVYMAIN_H_
#define _AVYMAIN_H_

#include "AigUtils.h"
#include "SafetyVC.h"
#include "SafetyAigVC.h"
#include "Minisat.h"
#include "Glucose.h"
#include "Pdr.h"
#include "Unroller.h"
#include <string>
#include "boost/logic/tribool.hpp"
#include "boost/foreach.hpp"
#include "boost/dynamic_bitset.hpp"

#include "boost/noncopyable.hpp"

#include "ItpMinisat.h"
#include "ItpGlucose.h"

namespace avy
{
  class AvyMain : boost::noncopyable
  {
    std::string m_fName;
    
    AigManPtr m_Aig;

    /** reference to the current VC */
    SafetyVC *m_Vc;
    SafetyAigVC *m_OptVc;
    
    Pdr *m_pPdr;
    
    dynamic_bitset<> m_Core;

    template <typename Sat>
    boost::tribool solveWithCore (Sat &sat, Unroller<Sat>& unroller, unsigned nFrame);
    

  public:
    AvyMain(std::string fname);
    AvyMain (AigManPtr pAig);
    
    virtual ~AvyMain() ;

    int run ();
    template <typename Sat>
    int run (Sat& solver, Unroller<Sat>& unroller);

    /// do BMC check up to depth nFrame
    template <typename Sat>
    boost::tribool doBmc (unsigned nFrame, Sat& solver, Unroller<Sat>& unroller);
    /// convert interpolant into PDR trace
    boost::tribool doPdrTrace (AigManPtr itp);
    /// strengthen VC with current Pdr trace
    void doStrengthenVC ();
    
    bool validateItp (AigManPtr itp);

    template<typename Sat>
    void printCex(Sat& s, Unroller<Sat>& unroller);

    bool findItpConstraints (AigManPtr &itp, std::vector<std::vector<int> >& equivFrames);
  };
}


#endif /* _AVYMAIN_H_ */






