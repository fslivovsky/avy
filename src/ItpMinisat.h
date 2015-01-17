#ifndef _ITP_MINISAT_H_
#define _ITP_MINISAT_H_

#include "boost/noncopyable.hpp"
#include "boost/logic/tribool.hpp"

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "avy/Util/Stats.h"
#include "AigUtils.h"

#include "simp/SimpSolver.h"

#include <vector>

namespace avy
{
  using namespace abc;

  //typedef std::vector< ::Minisat::Lit> LitVector;
  
  
  /// Thin wrapper around interpolating sat solver
  class ItpMinisat : boost::noncopyable
  {
  private:
    std::unique_ptr<::Minisat::SimpSolver> m_pSat;

    /// true if last result was trivial
    bool m_Trivial;
    bool m_Simplifier;
    
    /// number of partitions
    unsigned m_nParts;

    /// current state
    boost::tribool m_State;

    
  public:
    /// create a solver with nParts partitions and nVars variables
    ItpMinisat (unsigned nParts, unsigned nVars, bool simp = true) : 
      m_pSat (nullptr), m_Simplifier(simp)
    { reset (nParts, nVars); }
    
    ~ItpMinisat () {}
    
    

    /// reset and allocate nParts partitions and nVars variables
    void reset (unsigned nParts, unsigned nVars)
    {
      AVY_ASSERT (nParts >= 2 && "require at least 2 partitions");
      m_nParts = nParts;
      m_Trivial = false;
      m_State = boost::tribool (boost::indeterminate);
      m_pSat.reset (new ::Minisat::SimpSolver());
      m_pSat->ccmin_mode = 2;
      m_pSat->reorderProof(gParams.proof_reorder);
      m_pSat->setCurrentPart(1);
    }

    /// Mark currently unmarked clauses as belonging to partition nPart
    void markPartition (unsigned nPart)
    { 
      AVY_ASSERT (nPart > 0);
      if (nPart > m_nParts) m_nParts = nPart;
      m_pSat->setCurrentPart(nPart);
      LOG ("minisat_dump", logs () << "c partition\n";);
    }
    
    void reserve (int nVars)
    { while (m_pSat->nVars () < nVars) m_pSat->newVar (); }

    
    bool addUnit (int unit)
    {
      ::Minisat::Lit p = ::Minisat::toLit (unit);
      LOG ("sat", logs () << "UNT: "
           << (::Minisat::sign (p) ? "-" : "")
           << (::Minisat::var (p)) << " ";);
      m_Trivial = !m_pSat->addClause (p);
      LOG ("minisat_dump", 
           logs () << (::Minisat::sign (p) ? "-" : "")
           << (::Minisat::var (p) + 1) << " 0\n";);
      return m_Trivial;
    }

    bool addClause (int* bgn, int* end)
    {
      LOG("sat", logs () << "NEW CLS: ";);
      ::Minisat::vec< ::Minisat::Lit> cls;
      cls.capacity (end-bgn);
      for (int* it = bgn; it != end; ++it)
        {
          ::Minisat::Lit p = ::Minisat::toLit (*it);
          cls.push (p);


          LOG("sat", logs () << (::Minisat::sign (p) ? "-" : "")
              << (::Minisat::var (p)) << " ";);
          LOG("minisat_dump", logs () << (::Minisat::sign (p) ? "-" : "")
              << (::Minisat::var (p) + 1) << " ";);

        }
      LOG("sat", logs () << "\n" << std::flush;);
      LOG("minisat_dump", logs () << " 0\n" << std::flush;);
      

      m_Trivial = !m_pSat->addClause (cls);
      return !m_Trivial;
    }
    
    void dumpCnf (std::string fname)
    { 
      ::Minisat::vec< ::Minisat::Lit> assumps;
      m_pSat->toDimacs(const_cast<char*>(fname.c_str ()), assumps);
    }


    /// raw access to the sat solver
    ::Minisat::Solver* get () { return m_pSat.get (); }
    
    /// true if the context is decided 
    bool isSolved () { return m_Trivial || m_State || !m_State; }

    /// decide context with assumptions
    //boost::tribool solve (LitVector &assumptions, int maxSize = -1)
    boost::tribool solve (std::vector<int> &assumptions, int maxSize = -1)
	{
	  if (m_Trivial) return false;

	  if (!m_pSat->okay ()) return false;

	  ::Minisat::vec< ::Minisat::Lit> massmp;
	  massmp.capacity (assumptions.size ());
	  int max = assumptions.size ();
	  if (maxSize >= 0 && maxSize < max) max = maxSize;

	  for (unsigned i = 0; i < max; ++i)
		{
		  ::Minisat::Lit p = ::Minisat::toLit (assumptions [i]);
		  massmp.push (p);
		  LOG ("sat", logs () << "ASM: " << (::Minisat::sign (p) ? "-" : "")
			   << (::Minisat::var (p)) << " " << "\n";);
		}
	  return m_pSat->solve (massmp, m_Simplifier, !m_Simplifier);
	}
    /// a pointer to the unsat core
    //int core (int **out) { return sat_solver_final (m_pSat, out); }
    
    /// decide current context
    boost::tribool solve () 
    { 
      ScoppedStats __stats__("ItpMinisat_solve");
      return m_pSat->solve (m_Simplifier, !m_Simplifier); 
    }

    bool isTrivial () { return m_Trivial; }
    
    void setFrozen (int v, bool p) { }//m_pSat->setFrozen (v, p); }

    /// Compute an interpolant. User provides the list of shared variables
    /// Variables can only be shared between adjacent partitions.
    /// fMcM == true for McMillan, and false for McMillan'
    Aig_Man_t* getInterpolant (lit bad, std::vector<Vec_Int_t*> &vSharedVars, int nNumOfVars, bool fMcM = true);
    
    bool getVarVal(int v)
    {
      return false;
      /*::Minisat::Var x = v;
      ::Minisat::lbool val = m_pSat->modelValue(x);
      return (val == ::Minisat::l_True) ? true : false;*/
    }
  };
  
}

#undef l_True
#undef l_False
#undef l_Undef

#endif /* _ITP_MINISAT_H_ */
