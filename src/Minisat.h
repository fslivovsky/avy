#ifndef _MINISAT_H_
#define _MINISAT_H_

#include "avy/Util/AvyDebug.h"
#include "avy/Util/Global.h"
#include "simp/SimpSolver.h"
#include "avy/AvyAbc.h"

namespace avy
{
  class Minisat
  {
    std::unique_ptr<::Minisat::SimpSolver> m_sat;
    bool m_Trivial;
    bool m_Simplifier;

    std::vector<int> m_core;
    
  public:
    Minisat (unsigned nVars, bool simp=true) : m_sat(nullptr), m_Trivial(false), m_Simplifier(simp)
    { reset (nVars); }

    virtual ~Minisat () {}

    void reset (int nVars)
    {
      m_core.clear ();
      m_sat.reset (new ::Minisat::SimpSolver ());
      m_sat->ccmin_mode = 2;
      m_sat->proofLogging (false);
      reserve (nVars);
    }

    void reserve (int nVars)
    { while (m_sat->nVars () < nVars) m_sat->newVar (); }
    
    
    bool addUnit (int unit) 
    { 
      ::Minisat::Lit p = ::Minisat::toLit (unit);
      LOG ("sat", logs () << "UNT: "
           << (::Minisat::sign (p) ? "-" : "") 
           << (::Minisat::var (p)) << " ";);
      m_Trivial = !m_sat->addClause (p); 
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
        }
      LOG("sat", logs () << "\n" << std::flush;);
      
      m_Trivial = !m_sat->addClause (cls);
      return !m_Trivial;
    }
    
    void dumpCnf (std::string fname)
    { 
      ::Minisat::vec< ::Minisat::Lit> assumps;
      m_sat->toDimacs(const_cast<char*>(fname.c_str ()), assumps);
    }
    

    boost::tribool solve (std::vector<int> &assumptions, int maxSize = -1)
    {
      if (m_Trivial) return false;

      if (!m_sat->okay ()) return false;
      
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
      return m_sat->solve (massmp, m_Simplifier, !m_Simplifier);
    }
    
    int core (int **out)
    {
      m_core.clear ();
      m_core.resize (m_sat->conflict.size ());
      for (unsigned i = 0 ; i < m_sat->conflict.size (); i++)
        m_core[i] = m_sat->conflict[i].x;

      *out = &m_core[0];
      return m_core.size ();
    }
    
    boost::tribool solve () { return m_sat->solve (m_Simplifier, !m_Simplifier); }
    
    bool isTrivial () { return m_Trivial; }
    
    void setFrozen (int v, bool p) { m_sat->setFrozen (v, p); }
    
    bool getVarVal(int v)
    {
      return false;
      /*::Minisat::Var x = v;
      ::Minisat::lbool val = m_pSat->modelValue(x);
      return (val == ::Minisat::l_True) ? true : false;*/
    }
    
    void markPartition(int nPart) {}

    
  };
  
}

#undef l_True
#undef l_False
#undef l_Undef

#endif /* _MINISAT_H_ */
