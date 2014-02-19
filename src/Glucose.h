#ifndef _GLUCOSE_H_
#define _GLUCOSE_H_

#include "glucose/simp/SimpSolver.h"

namespace avy
{
  class Glucose
  {
    ::Glucose::SimpSolver *m_sat;
    bool m_Trivial;

    std::vector<int> m_core;
    
  public:
    Glucose (unsigned nVars) : m_sat(NULL), m_Trivial(false)
    { reset (nVars); }

    virtual ~Glucose () { if (m_sat) delete m_sat; }

    void reset (int nVars)
    {
      m_core.clear ();
      if (m_sat) delete m_sat;
      m_sat = new ::Glucose::SimpSolver ();
      m_sat->proofLogging(false);
      reserve (nVars);
    }

    void reserve (int nVars)
    { while (m_sat->nVars () < nVars) m_sat->newVar (); }
    
    
    bool addUnit (int unit) 
    { 
      ::Glucose::Lit p = ::Glucose::toLit (unit);
      LOG ("sat", logs () << "UNT: "
           << (::Glucose::sign (p) ? "-" : "") 
           << (::Glucose::var (p)) << " ";);
      m_Trivial = !m_sat->addClause (p); 
      return m_Trivial;
    }

    bool addClause (int* bgn, int* end)
    {
      LOG("sat", logs () << "NEW CLS: ";);
      ::Glucose::vec< ::Glucose::Lit> cls;
      cls.capacity (end-bgn);
      for (int* it = bgn; it != end; ++it)
        {
          ::Glucose::Lit p = ::Glucose::toLit (*it);
          cls.push (p);

          
          LOG("sat", logs () << (::Glucose::sign (p) ? "-" : "") 
              << (::Glucose::var (p)) << " ";);
        }
      LOG("sat", logs () << "\n" << std::flush;);
      
      m_Trivial = !m_sat->addClause (cls);
      return !m_Trivial;
    }
    
    boost::tribool solve (std::vector<int> &assumptions, int maxSize = -1)
    {
      if (m_Trivial) return false;

      if (!m_sat->okay ()) return false;
      
      ::Glucose::vec< ::Glucose::Lit> massmp;
      massmp.capacity (assumptions.size ());
      int max = assumptions.size ();
      if (maxSize >= 0 && maxSize < max) max = maxSize;
      
      for (unsigned i = 0; i < max; ++i) 
        { 
          ::Glucose::Lit p = ::Glucose::toLit (assumptions [i]);
          massmp.push (p);
          LOG ("sat", logs () << "ASM: " << (::Glucose::sign (p) ? "-" : "") 
               << (::Glucose::var (p)) << " " << "\n";);
        }
      return m_sat->solve (massmp);
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
    
    boost::tribool solve () { return m_sat->solve (); }
    
    bool isTrivial () { return m_Trivial; }
    
    void setFrozen (int v, bool p) { m_sat->setFrozen (v, p); }
    
    
    

  };
    
}

#undef l_True
#undef l_False
#undef l_Undef

#endif /* _GLUCOSE_H_ */
