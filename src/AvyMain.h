#ifndef _AVYMAIN_H_
#define _AVYMAIN_H_

#include "AigUtils.h"
#include <string>

namespace avy
{
  class AvyMain
  {
    std::string m_fName;
    
    AigManPtr m_Aig;
    
  public:
    AvyMain(std::string fname);
    
    virtual ~AvyMain()
    {
    }
    

    int run ();
  
  };
}


#endif /* _AVYMAIN_H_ */
