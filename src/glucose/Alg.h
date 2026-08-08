#pragma once

#include "Vec.h"

namespace Simp21 {

//=================================================================================================
// Useful functions on vector-like types:

//=================================================================================================
// Removing and searching for elements:
//

template <class V, class T> static inline void remove(V &ts, const T &t) {
  int j = 0;

  for (; j < ts.size() && ts[j] != t; j++)
    ;

  assert(j < ts.size());

  for (; j < ts.size() - 1; j++) {
    ts[j] = ts[j + 1];
  }

  ts.pop();
}

template <class V, class T> static inline bool find(V &ts, const T &t) {
  int j = 0;

  for (; j < ts.size() && ts[j] != t; j++)
    ;

  return j < ts.size();
}

//=================================================================================================
// Copying vectors with support for nested vector types:
//

// Base case:
template <class T> static inline void copy(const T &from, T &to) { to = from; }

// Recursive case:
template <class T> static inline void copy(const vec<T> &from, vec<T> &to, bool append = false) {
  if (!append) {
    to.clear();
  }

  for (int i = 0; i < from.size(); i++) {
    to.push();
    copy(from[i], to.last());
  }
}

template <class T> static inline void append(const vec<T> &from, vec<T> &to) { copy(from, to, true); }

//=================================================================================================
} // namespace Simp21
