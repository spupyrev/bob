#pragma once

#include <errno.h>
#include <stdlib.h>

namespace Simp21 {

//=================================================================================================
// Simple layer on top of malloc/realloc to catch out-of-memory situations and provide some typing:

class OutOfMemoryException {};
static inline void *xrealloc(void *ptr, size_t size) {
  void *mem = realloc(ptr, size);

  if (mem == nullptr && errno == ENOMEM) {
    throw OutOfMemoryException();
  } else {
    return mem;
  }
}

//=================================================================================================
} // namespace Simp21
