#include "AvyMain.h"
#include "boost/lexical_cast.hpp"
#include "avy/Util/Global.h"

#include "base/main/main.h"
#include "aig/ioa/ioa.h"

using namespace boost;
using namespace std;
using namespace abc;
using namespace avy;

namespace abc
{
  extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, 
                                   int fRegisters );
}

static Aig_Man_t *loadAig (std::string fname)
{
  Abc_Frame_t *pFrame = Abc_FrameGetGlobalFrame ();
    
  VERBOSE (2, vout () << "\tReading AIG from '" << fname << "'\n";);
  string cmd = "read " + fname;
  Cmd_CommandExecute (pFrame, cmd.c_str ());
    
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk (pFrame);
    
  return Abc_NtkToDar (pNtk, 0, 1);
}


namespace avy
{
  AvyMain::AvyMain (std::string fname) : m_fName (fname)
  {
    VERBOSE (2, vout () << "Starting ABC\n");
    Abc_Start ();
    
    Aig_Man_t *pAig1 = loadAig (fname);
    
    VERBOSE (2, vout () << "\tAdding reset signal\n");
    Aig_Man_t *pAig2 = Aig_AddResetPi (pAig1);
    Aig_ManStop (pAig1);
    pAig1 = NULL;
    
    string tmpName = "__tmp.aig";
    VERBOSE (2, vout () << "\tDumping to disk: " << tmpName << "\n");
    Ioa_WriteAiger (pAig2, const_cast<char*>(tmpName.c_str ()), 1, 0);

    VERBOSE(2, vout () << "Restarting ABC\n");
    Abc_Stop ();
    Abc_Start ();

    m_Aig = aigPtr (loadAig (tmpName));

    // -- keep abc running, just in case
    //Abc_Stop ()
    
    
  }  

  int AvyMain::run ()
  {
    return 0;
  }
  

}
