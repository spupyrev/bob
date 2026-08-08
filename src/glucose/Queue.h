#pragma once

#include "Vec.h"

namespace Simp21 {

template <class T> class Queue {
  vec<T> buf;
  int first;
  int end;

public:
  typedef T Key;

  Queue() : buf(1), first(0), end(0) {}

  void clear(bool dealloc = false) {
    buf.clear(dealloc);
    buf.growTo(1);
    first = end = 0;
  }
  int size() const { return (end >= first) ? end - first : end - first + buf.size(); }

  const T &operator[](int index) const {
    assert(index >= 0);
    assert(index < size());
    return buf[(first + index) % buf.size()];
  }
  T &operator[](int index) {
    assert(index >= 0);
    assert(index < size());
    return buf[(first + index) % buf.size()];
  }

  T peek() const {
    assert(first != end);
    return buf[first];
  }
  void pop() {
    assert(first != end);
    first++;
    if (first == buf.size())
      first = 0;
  }
  void insert(T elem) { // INVARIANT: buf[end] is always unused
    buf[end++] = elem;

    if (end == buf.size()) {
      end = 0;
    }

    if (first == end) { // Resize:
      vec<T> tmp((buf.size() * 3 + 1) >> 1);
      int i = 0;

      for (int j = first; j < buf.size(); j++) {
        tmp[i++] = buf[j];
      }

      for (int j = 0; j < end; j++) {
        tmp[i++] = buf[j];
      }

      first = 0;
      end = buf.size();
      tmp.moveTo(buf);
    }
  }
};

//=================================================================================================
} // namespace Simp21
