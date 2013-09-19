#ifndef _AIGUTILS_H_
#define _AIGUTILS_H_

#include "aig/aig/aig.h"

namespace avy
{
  abc::Aig_Man_t *Aig_ManReplacePo (abc::Aig_Man_t *pMan, abc::Aig_Man_t *pMiter, bool fComp);
  abc::Aig_Man_t *Aig_ManDupSinglePo (abc::Aig_Man_t *pCombMan, int nPo);
}



#endif /* _AIGUTILS_H_ */
