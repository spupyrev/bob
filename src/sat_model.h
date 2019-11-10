#pragma once

#include "logging.h"

#include <sstream>
#include <fstream>
#include <string>
#include <vector>
#include <map>

using namespace std;

struct MVar {
  int id;
  bool positive;

  MVar(int id, bool positive): id(id), positive(positive) {}
};

struct MClause {
  vector<MVar> vars;

  MClause() {
  }

  MClause(const MVar& v1) {
    vars.push_back(v1);
  }

  MClause(const MVar& v1, const MVar& v2) {
    vars.push_back(v1);
    vars.push_back(v2);
  }

  MClause(const MVar& v1, const MVar& v2, const MVar& v3) {
    vars.push_back(v1);
    vars.push_back(v2);
    vars.push_back(v3);
  }

  MClause(const MVar& v1, const MVar& v2, const MVar& v3, const MVar& v4) {
    vars.push_back(v1);
    vars.push_back(v2);
    vars.push_back(v3);
    vars.push_back(v4);
  }

  MClause(const MVar& v1, const MVar& v2, const MVar& v3, const MVar& v4, const MVar& v5) {
    vars.push_back(v1);
    vars.push_back(v2);
    vars.push_back(v3);
    vars.push_back(v4);
    vars.push_back(v5);
  }

  MClause(const MClause& clause, const MVar& v1) {
    vars.insert(vars.end(), clause.vars.begin(), clause.vars.end());
    vars.push_back(v1);
  }

  MClause(const MClause& clause, const MVar& v1, const MVar& v2) {
    vars.insert(vars.end(), clause.vars.begin(), clause.vars.end());
    vars.push_back(v1);
    vars.push_back(v2);
  }

  void addVar(const MVar& v1) {
    vars.push_back(v1);
  }
};

class SATModel {
  vector<MClause> clauses;
  int curId;

  // relative order variables
  map<pair<int, int>, int> relVars;
  // page variables [edge_index][page]
  map<pair<int, int>, int> pageVars;
  // same-page variables
  map<pair<int, int>, int> spVars;
  // track variables [node_index][page]
  map<pair<int, int>, int> trackVars;
  // same track variables
  map<pair<int, int>, int> stVars;

  // solution (provided by an external solver)
  std::string externalResult = ""; // not provided
  map<int, bool> externalVars;

 public:
  SATModel() {
    clauses.clear();
    curId = 0;
  }

  int addVar() {
    curId++;
    return curId - 1;
  }

  void addClause(MClause c) {
    clauses.push_back(c);
  }

  MVar getRelVar(int i, int j, bool positive) const {
    CHECK(i != j);
    pair<int, int> pair;
    if (i < j) {
      pair = make_pair(i, j);
    } else {
      pair = make_pair(j, i);
    }

    CHECK(relVars.count(pair));
    int index = (*relVars.find(pair)).second;
    return MVar(index, i < j ? positive : !positive);
  }

  void addRelVar(int i, int j) {
    if (i >= j) return;

    int var = addVar();
    CHECK(relVars.count(make_pair(i, j)) == 0);
    relVars[make_pair(i, j)] = var;
  }

  MVar getPageVar(int edge, int page, bool positive) const {
    auto pair = make_pair(edge, page);
    CHECK(pageVars.count(pair));
    int index = (*pageVars.find(pair)).second;
    return MVar(index, positive);
  }

  void addPageVar(int edge, int page) {
    int var = addVar();
    auto pair = make_pair(edge, page);
    CHECK(pageVars.count(pair) == 0);
    pageVars[pair] = var;
  }

  MVar getTrackVar(int node, int page, bool positive) const {
    auto pair = make_pair(node, page);
    CHECK(trackVars.count(pair));
    int index = (*trackVars.find(pair)).second;
    return MVar(index, positive);
  }

  void addTrackVar(int node, int page) {
    int var = addVar();
    auto pair = make_pair(node, page);
    CHECK(trackVars.count(pair) == 0);
    trackVars[pair] = var;
  }

  MVar getSamePageVar(int edge1, int edge2, bool positive) const {
    auto pair = edge1 < edge2 ? make_pair(edge1, edge2) : make_pair(edge2, edge1);
    CHECK(spVars.count(pair));
    int index = (*spVars.find(pair)).second;
    return MVar(index, positive);
  }

  void addSamePageVar(int edge1, int edge2) {
    int var = addVar();
    auto pair = edge1 < edge2 ? make_pair(edge1, edge2) : make_pair(edge2, edge1);
    CHECK(spVars.count(pair) == 0);
    spVars[pair] = var;
  }

  MVar getSameTrackVar(int node1, int node2, bool positive) const {
    auto pair = node1 < node2 ? make_pair(node1, node2) : make_pair(node2, node1);
    CHECK(stVars.count(pair));
    int index = (*stVars.find(pair)).second;
    return MVar(index, positive);
  }

  void addSameTrackVar(int node1, int node2) {
    CHECK(node1 < node2);
    int var = addVar();
    auto pair = make_pair(node1, node2);
    CHECK(stVars.count(pair) == 0);
    stVars[pair] = var;
  }

  void toDimacs(const string& filename) {
  	if (filename == "") {
  		toDimacs(cout);
  	} else {
	    std::ofstream out;
  	  out.open(filename);
  	  toDimacs(out);
  	  out.close();
  	}
  }

  void toDimacs(ostream& out) {
    int nvars = varCount();
    out << "p cnf " << nvars << " " << clauseCount() << "\n";
    for (auto& c : clauses) {
      for (auto& l : c.vars) {
        int var = l.id + 1;
        CHECK(1 <= var && var <= nvars);
        if (l.positive) {
          out << var << " ";
        } else {
          out << "-" << var << " ";
        }
      }
      out << "0\n";
    }
  }

  std::string fromDimacs(const string& filename) {
    std::ifstream in;
    in.open(filename);
    std::string line;
    std::string externalResult = "";
    while (std::getline(in, line)) {
      std::istringstream iss(line);
      char mode;
      if (!(iss >> mode)) {break;} // hmm
      if (mode == 's') {
        // result
        iss >> externalResult;
      } else if (mode == 'v') {
        // var
        int vv;
        while (iss >> vv) {
          if (vv > 0) {
            int id = vv - 1;
            CHECK(externalVars.find(id) == externalVars.end());
            externalVars[id] = true;
          } else if (vv < 0) {
            int id = -vv - 1;
            CHECK(externalVars.find(id) == externalVars.end());
            externalVars[id] = false;
          }  
        }
      }
    }    
    in.close();
    CHECK(externalResult != "");
    if (externalResult == "SATISFIABLE" && externalVars.size() != varCount()) {
      ERROR("incorrect number of variables in '" + filename + "': " + std::to_string(varCount()) + " != " + std::to_string(externalVars.size()));
    }
    return externalResult;
  }

  bool value(int id) {
    CHECK(externalVars.count(id));
    return externalVars[id];
  }

  bool value(MVar v) {
    CHECK(externalVars.count(v.id));
    return externalVars[v.id] ? v.positive : !v.positive;
  }

  size_t varCount() {
    return curId;
  }

  size_t clauseCount() {
    return clauses.size();
  }
};
