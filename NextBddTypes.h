#ifndef NEXT_BDD_TYPES_H
#define NEXT_BDD_TYPES_H

#include <limits>

namespace NextBdd {
  
  typedef unsigned short var;
  typedef int bvar;
  typedef unsigned lit;
  typedef unsigned short ref;
  typedef unsigned long long size;
  typedef unsigned edge;

  typedef unsigned uniq;
  typedef unsigned cac;

  static inline var VarMax() {
    return std::numeric_limits<var>::max();
  }
  static inline bvar BvarMax() {
    return std::numeric_limits<bvar>::max();
  }
  static inline lit LitMax() {
    return std::numeric_limits<lit>::max();
  }
  static inline ref RefMax() {
    return std::numeric_limits<ref>::max();
  }
  static inline size SizeMax() {
    return std::numeric_limits<size>::max();
  }

  static inline uniq UniqHash(lit Arg0, lit Arg1) {
    return Arg0 + 4256249 * Arg1;
  }
  static inline uniq CacHash(lit Arg0, lit Arg1) {
    return Arg0 + 4256249 * Arg1;
  }

}

#endif
