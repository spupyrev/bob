#pragma once

#include "logging.h"

#include <algorithm>
#include <vector>

using EdgeTy = std::pair<int, int>;
using AdjListTy = std::vector<std::vector<int>>;

inline std::vector<EdgeTy> adj_to_edges(const AdjListTy& adjList) {
  std::vector<EdgeTy> edges;
  for (size_t i = 0; i < adjList.size(); i++) {
    for (size_t j = 0; j < adjList[i].size(); j++) {
      if ((int)i < adjList[i][j])
        edges.push_back({i, adjList[i][j]});
    }
  }
  return edges;
}

inline AdjListTy edges_to_adj(const int n, const std::vector<EdgeTy>& edges) {
  CHECK(!edges.empty());

  for (const auto& [u, v] : edges) {
    CHECK(u < v);
    CHECK(0 <= u && u < n);
    CHECK(0 <= v && v < n);
  }
  AdjListTy adjList(n, std::vector<int>());
  for (const auto& [u, v] : edges) {
    adjList[u].push_back(v);
    adjList[v].push_back(u);
  }
  return adjList;
}

inline AdjListTy edges_to_adj(const std::vector<EdgeTy>& edges) {
  CHECK(!edges.empty());

  int minN = -1;
  int maxN = -1;
  for (auto& e : edges) {
    CHECK(e.first < e.second);
    if (minN == -1 || minN > std::min(e.first, e.second))
      minN = std::min(e.first, e.second);
    if (maxN == -1 || maxN < std::max(e.first, e.second))
      maxN = std::max(e.first, e.second);
  }
  CHECK(maxN >= minN);
  int N = maxN - minN + 1;
  AdjListTy adjList(N, std::vector<int>());
  for (auto& e : edges) {
    int src = e.first - minN;
    int dst = e.second - minN;
    adjList[src].push_back(dst);
    adjList[dst].push_back(src);
  }
  return adjList;
}

class Adjacency {
  Adjacency(const Adjacency&);
  Adjacency& operator = (const Adjacency&);

 public:
  explicit Adjacency(int n) {
    adjList = std::vector<std::vector<int>>(n);
  }

  explicit Adjacency(int n, const std::vector<EdgeTy>& edges) {
    adjList = std::vector<std::vector<int>>(n);
    from_edges(edges);
  }

  void init(int n) {
    adjList = std::vector<std::vector<int>>(n);
  }

  template <typename F> 
  void forEach(int index, F func) const {
    for (size_t j = 0; j < adjList[index].size(); j++) {
      func(adjList[index][j]);
    }
  }  

  template <typename F> 
  void forEachSliced(int index, F func) const {
    CHECK(slice.size() == adjList.size());
    for (size_t j = 0; j < adjList[index].size(); j++) {
      if (slice[adjList[index][j]]) {
        func(adjList[index][j]);
      }
    }
    // not using explicit slice
    // CHECK(std::is_sorted(vertices.begin(), vertices.end()));
    // CHECK(std::is_sorted(adjList[index].begin(), adjList[index].end()));

    // // find intersections of the vectors
    // size_t idxV = 0;
    // size_t idxA = 0; 
    // while (idxV < vertices.size() && idxA < adjList[index].size()) { 
    //   if (vertices[idxV] < adjList[index][idxA]) {
    //      idxV++;
    //   } else if (vertices[idxV] > adjList[index][idxA]) {
    //      idxA++;
    //   } else {
    //      func(vertices[idxV]);
    //      idxV++;
    //      idxA++;
    //   } 
    // }
  }  

  void reserve(int index, size_t size) {
    adjList[index].reserve(size);
  }

  void set(int first, int second) {
    adjList[first].push_back(second);
  }

  bool test(int first, int second) const {
    auto& list = adjList[first];
    return std::find(list.begin(), list.end(), second) != list.end();
  }

  size_t size() const {
    return adjList.size();
  }

  size_t num_edges() const {
    size_t m = 0;
    for (size_t i = 0; i < adjList.size(); i++) {
      for (size_t j = 0; j < adjList[i].size(); j++) {
        if ((int)i < adjList[i][j])
          m++;
      }
    }
    return m;
  }

  size_t degree(int index) const {
    return adjList[index].size();
  }

  int get(int index, int pos) const {
    return adjList[index][pos];
  }

  std::vector<int> getAdjacent(int index) const {
    return adjList[index];
  }

  void shrink_to_fit() {
    for (size_t i = 0; i < adjList.size(); i++) {
      auto& list = adjList[i];
      std::sort(list.begin(), list.end());
      list.erase( std::unique( list.begin(), list.end() ), list.end() );
    }
  }

  std::vector<EdgeTy> to_edges() const {
    std::vector<EdgeTy> edges;
    for (size_t i = 0; i < adjList.size(); i++) {
      for (size_t j = 0; j < adjList[i].size(); j++) {
        if ((int)i < adjList[i][j]) {
          edges.push_back({i, adjList[i][j]});
        }
      }
    }
    return edges;
  }

  void from_edges(const std::vector<EdgeTy>& edges) {
    for (auto& edge : edges) {
      set(edge.first, edge.second);
      set(edge.second, edge.first);
    }
    shrink_to_fit();
  }

  void init_slice(Adjacency& slice, const std::vector<int>& vertices) const {
    auto is_vertex = std::vector<bool>(adjList.size(), false);
    for (int v : vertices) {
      is_vertex[v] = true;
    }
    for (size_t i = 0; i < adjList.size(); i++) {
      if (!is_vertex[i]) continue;
      for (size_t j = 0; j < adjList[i].size(); j++) {
        if (!is_vertex[adjList[i][j]]) continue;
        slice.set(i, adjList[i][j]);
      }
    }
  }

  void init_slice(const std::vector<int>& vertices) const {
    CHECK(slice.empty());
    slice = std::vector<bool>(adjList.size(), false);
    for (int v : vertices) {
      slice[v] = true;
    }
  }

  void clear_slice() const {
    slice.clear();
  }

private:
  std::vector<std::vector<int>> adjList;
  mutable std::vector<bool> slice;
};

// class Adjacency {
//   Adjacency(const Adjacency&);
//   Adjacency& operator = (const Adjacency&);

//  public:
//   explicit Adjacency(int n_) {
//     n = n_;
//     bits = std::vector<std::vector<bool>>(n, std::vector<bool>(n, false));
//     degrees = std::vector<int>(n, 0);
//   }

//   explicit Adjacency(int n_, const std::vector<EdgeTy>& edges) {
//     n = n_;
//     bits = std::vector<std::vector<bool>>(n, std::vector<bool>(n, false));
//     degrees = std::vector<int>(n, 0);
//     from_edges(edges);
//   }

//   template <typename F> 
//   void forEach(int index, F func) const {
//     for (int j = 0; j < n; j++) {
//       if (bits[index][j]) {
//         func(j);
//       }
//     }
//   }  

//   void reserve(int index, size_t size) {
//   }

//   void set(int first, int second) {
//     if (bits[first][second]) return;
//     bits[first][second] = true;
//     degrees[first]++;
//   }

//   bool test(int first, int second) const {
//     return bits[first][second];
//   }

//   size_t size() const {
//     return n;
//   }

//   size_t degree(int index) const {
//     return degrees[index];
//   }

//   int get(int index, int pos) const {
//     int r = 0;
//     for (int j = 0; j < n; j++) {
//       if (bits[index][j]) {
//         if (r >= pos) return j;
//         r++;
//       }
//     }
//     throw 1;
//   }

//   void shrink_to_fit() {
//   }

//   std::vector<EdgeTy> to_edges() const {
//     std::vector<EdgeTy> edges;
//     for (int i = 0; i < n; i++) {
//       for (int j = i + 1; j < n; j++) {
//         if (bits[i][j]) {
//           edges.push_back(std::make_pair(i, j));
//         }
//       }
//     }
//     return edges;
//   }

//   void from_edges(const std::vector<EdgeTy>& edges) {
//     for (auto& edge : edges) {
//       set(edge.first, edge.second);
//       set(edge.second, edge.first);
//     }
//   }

//   void init_slice(Adjacency& slice, const std::vector<int>& vertices) const {
//     auto is_vertex = std::vector<bool>(n, false);
//     for (int v : vertices) {
//       is_vertex[v] = true;
//     }
//     for (int i = 0; i < n; i++) {
//       if (!is_vertex[i]) continue;
//       for (int j = 0; j < n; j++) {
//         if (!is_vertex[j]) continue;
//         if (!bits[i][j]) continue;
//         slice.set(i, j);
//       }
//     }
//   }

// private:
//   int n;  
//   std::vector<int> degrees;
//   std::vector<std::vector<bool>> bits;
// };
