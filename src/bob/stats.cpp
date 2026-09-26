#include "stats.h"

#include "graph_algorithms.h"
#include "logging.h"

void printStats(int n, const std::vector<EdgeTy>& edges) {
  LOG("degree           = [%d, %d]", minDegree(n, edges), maxDegree(n, edges));
  LOG("girth            = %d", computeGirth(n, edges));
  LOG("connected        = %d", isConnected(n, edges));
  LOG("diameter         = %d", computeDiameter(n, edges));
  LOG("radius           = %d", computeRadius(n, edges));
}
