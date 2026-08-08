#pragma once

#include "Vec.h"

namespace Simp21 {

// Some sorting algorithms for vec's

template <class T> struct LessThan_default {
  bool operator()(T x, T y) { return x < y; }
};

template <class T>
inline void swap(T& a, T& b) {
  T tmp = a;
  a = b;
  b = tmp;
}

template <class T, class LessThan> void selectionSort(T *array, int size, LessThan less_than) {
  for (int i = 0; i < size - 1; i++) {
    int best_i = i;

    for (int j = i + 1; j < size; j++) {
      if (less_than(array[j], array[best_i])) {
        best_i = j;
      }
    }

    swap(array[i], array[best_i]);
  }
}

template <class T> static inline void selectionSort(T *array, int size) {
  selectionSort(array, size, LessThan_default<T>());
}

template <class T, class LessThan> void sort(T *array, int size, LessThan less_than) {
  if (size <= 16) {
    selectionSort(array, size, less_than);
  } else {
    T pivot = array[size / 2];
    int i = -1;
    int j = size;

    for (;;) {
      do {
        i++;
      } while (less_than(array[i], pivot));

      do {
        j--;
      } while (less_than(pivot, array[j]));

      if (i >= j) {
        break;
      }

      swap(array[i], array[j]);
    }

    sort(array, i, less_than);
    sort(&array[i], size - i, less_than);
  }
}

template <class T> 
static inline void sort(T *array, int size) { 
  sort(array, size, LessThan_default<T>()); 
}

//=================================================================================================
// For 'vec's:

template <class T, class LessThan> 
void sort(vec<T> &v, LessThan lt) { 
  sort((T *)v, v.size(), lt); 
}

template <class T> 
void sort(vec<T> &v) {
  if (v.size() <= 1) return;
  if (v.size() == 2) {
    if (v[1] < v[0]) 
      swap(v[0], v[1]);
    return;
  }
  if (v.size() == 3) {
    if (v[1] < v[0])
      swap(v[0], v[1]);
    if (v[2] < v[1])
      swap(v[1], v[2]);
    if (v[1] < v[0])
      swap(v[0], v[1]);
    return;
  }

  sort((T *)v, v.size(), LessThan_default<T>()); 
}

//=================================================================================================
} // namespace Simp21
