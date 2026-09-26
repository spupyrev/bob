#pragma once

#include "logging.h"
#include "glucose/SolverSimp21.h"
#include "satsuma/sat_symmetry.h"

#include <sstream>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <zlib.h>

using namespace std;

struct MVar {
  int id;
  bool positive;

  MVar(int id, bool positive): id(id), positive(positive) {}

  bool operator < (const MVar& other) const {
    if (id != other.id)
      return id < other.id;
    return positive < other.positive;
  }
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

  MClause(const MClause& clause, const MVar& v1, const MVar& v2, const MVar& v3) {
    vars.insert(vars.end(), clause.vars.begin(), clause.vars.end());
    vars.push_back(v1);
    vars.push_back(v2);
    vars.push_back(v3);
  }

  void addVar(const MVar& v1) {
    vars.push_back(v1);
  }

  void addAllVars(const MClause& clause) {
    vars.insert(vars.end(), clause.vars.begin(), clause.vars.end());
  }

  bool operator == (const MClause& other) const {
    if (vars.size() != other.vars.size())
      return false;
    for (size_t i = 0; i < vars.size(); i++) {
      if (vars[i].id != other.vars[i].id || vars[i].positive != other.vars[i].positive) {
        return false;
      }
    }
    return true;
  }
};

class SATModel {
  struct pair_hash {
    inline std::size_t operator()(const std::pair<int, int>& v) const {
      return v.first * 31 + v.second;
    }
  };

  std::unordered_map<int, Simp21::Var> vars;
  vector<MClause> clauses;
  int curId = 0;
  int trueVarId;

  // relative order variables
  std::unordered_map<pair<int, int>, int, pair_hash> relVars;
  // page variables [edge_index][page]
  std::unordered_map<pair<int, int>, int, pair_hash> pageVars;
  // same-page variables
  std::unordered_map<pair<int, int>, int, pair_hash> spVars;
  // adjacent-vertices variables
  std::unordered_map<pair<int, int>, int, pair_hash> adjVars;
  // track variables [node_index][page]
  std::unordered_map<pair<int, int>, int, pair_hash> trackVars;
  // same track variables
  std::unordered_map<pair<int, int>, int, pair_hash> stVars;
  // page type variables: true=stack, false=queue
  std::unordered_map<int, int> pageTypeVars;

  // solution (provided by an external solver)
  std::unordered_map<int, bool> externalVars;

 public:
  SATModel() {
    vars.clear();
    clauses.clear();
    curId = 0;

    trueVarId = addVar();
    addClause(MClause(MVar(trueVarId, true)));
  }

  MVar trueVar() const {
    return MVar(trueVarId, true);
  }

  int addVar() {
    curId++;
    return curId - 1;
  }

  void addClause(MClause c) {
    // skip the clause if it contains the true variable
    for (MVar& var : c.vars) {
      if (var.id == trueVarId && var.positive)
        return;
    }
    clauses.push_back(c);
  }

  MVar getRelVar(int i, int j, bool positive) const {
    CHECK(i != j);
    auto pair = i < j ? make_pair(i, j) : make_pair(j, i);
    auto it = relVars.find(pair);
    CHECK(it != relVars.end(), "cannot find relVar for pair (%d, %d)", pair.first, pair.second);
    int index = (*it).second;
    return MVar(index, i < j ? positive : !positive);
  }

  void addRelVar(int i, int j) {
    if (i >= j) {
      return;
    }

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

  void addPageTypeVar(int page) {
    int var = addVar();
    CHECK(pageTypeVars.count(page) == 0);
    pageTypeVars[page] = var;
  }

  MVar getPageTypeVar(int page, bool positive) const {
    CHECK(pageTypeVars.count(page));
    int index = (*pageTypeVars.find(page)).second;
    return MVar(index, positive);
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

  bool hasSamePageVar(int edge1, int edge2) const {
    auto pair = edge1 < edge2 ? make_pair(edge1, edge2) : make_pair(edge2, edge1);
    return spVars.count(pair);
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

  MVar getAdjVar(int i, int j, bool positive) const {
    CHECK(i != j);
    pair<int, int> pair;
    pair = make_pair(i, j);
    CHECK(adjVars.count(pair));
    int index = (*adjVars.find(pair)).second;
    return MVar(index, positive);
  }

  void addAdjVar(int i, int j) {
    int var = addVar();
    CHECK(adjVars.count(make_pair(i, j)) == 0);
    adjVars[make_pair(i, j)] = var;
  }

  template<class T>
  void initVars(T& solver) {
    // variables
    for (int i = 0; i < curId; i++) {
      auto var = solver.newVar();
      vars[i] = var;
      CHECK(0 <= vars[i] && vars[i] < curId);
    }
  }

  template<class T>
  void initClauses(T& solver) {
    // clauses
    for (auto& c : clauses) {
      Simp21::vec<Simp21::Lit> clause;

      for (auto& l : c.vars) {
        CHECK(vars.count(l.id));
        auto var = vars[l.id];

        if (l.positive) {
          clause.push(Simp21::mkLit(var));
        } else {
          clause.push(~Simp21::mkLit(var));
        }
      }

      solver.addClause_(clause);
    }
  }

  template<class T>
  void init(T& solver) {
    initVars(solver);
    initClauses(solver);
  }

  void toDimacs(const string& filename) {
    std::string ext = filename.substr(filename.find_last_of(".") + 1);
    
    if (ext == "gz") {
      // zlib
      std::ostringstream oss;
      // need this?
      ios_base::sync_with_stdio(false);
      oss.tie(nullptr);

      toDimacs(oss);
      const auto& content = oss.str(); // make it "const auto content = " if there are issues
      const char* content_str = content.c_str();
      const size_t content_len = content.length();
      gzFile out = gzopen(filename.c_str(), "wb9");
      std::cerr << "started gzwrite...\n";
      gzwrite(out, content_str, content_len);
      std::cerr << "completed gzwrite...\n";
      gzclose(out);
    } else {
      // usual route
      std::ofstream out;
      out.open(filename);
      toDimacs(out);
      out.close();
    }
  }

  void toDimacs(std::ostream& out) {
    int nvars = varCount();
    out << "p cnf " << nvars << " " << clauseCount() << "\n";

    for (auto& c : clauses) {
      for (auto& l : c.vars) {
        CHECK(vars.count(l.id));
        auto var = vars[l.id] + 1;
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

      if (!(iss >> mode)) {
        break; // hmm
      }

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

    if (externalResult == "SATISFIABLE" && externalVars.size() != vars.size()) {
      ERROR("incorrect number of variables in '" + filename + "': " + std::to_string(vars.size()) + " != " + std::to_string(externalVars.size()));
    }

    return externalResult;
  }

  template<class T>
  void applySatsuma(int verbose, T& solver) {
    // variables are in [1..nvars]; negations are negative
    const int nvars = varCount();
    vector<vector<int>> cl;
    cl.reserve(clauses.size());

    vector<int> clause;
    for (auto& c : clauses) {
      clause.clear();
      for (auto& l : c.vars) {
        CHECK(vars.count(l.id));
        auto var = vars[l.id] + 1;
        CHECK(1 <= var && var <= nvars);

        if (l.positive) {
          clause.push_back(var);
        } else {
          clause.push_back(-var);
        }
      }
      cl.push_back(clause);
    }

    auto result = applySatsumaSymmetry(verbose, nvars, cl);
    LOG_IF(verbose, "introduced %'d new variables and %'d symmetry-breaking clauses",
           result.first - nvars, (int)result.second.size() - (int)clauses.size());

    // nothing to add
    if (result.first == nvars && result.second.size() == clauses.size())
      return;

    // adding vars
    for (int i = nvars; i < result.first; i++) {
      curId++;
      auto var = solver.newVar();
      vars[i] = var;
      CHECK(0 <= vars[i] && vars[i] < curId);
    }

    // Satsuma returns the complete transformed formula
    clauses.clear();
    for (const auto& c : result.second) {
      MClause clause;
      for (int l : c) {
        CHECK(l != 0);
        if (l > 0) {
          clause.addVar(MVar(l - 1, true));
        } else {
          clause.addVar(MVar(-l - 1, false));
        }
      }
      clauses.push_back(clause);
    }
  }

  template<class T>
  bool value(T& solver, int id) {
    CHECK(vars.count(id));
    auto var = vars[id];

    if (!externalVars.empty()) {
      return externalVars[id];
    }

    return (solver.model[var] == l_True ? true : false);
  }

  template<class T>
  bool value(T& solver, MVar v) {
    CHECK(vars.count(v.id));
    auto var = vars[v.id];
    bool positive = v.positive;

    if (!externalVars.empty()) {
      return externalVars[v.id] ? positive : !positive;
    }

    return (solver.model[var] == l_True ? positive : !positive);
  }

  size_t varCount() {
    return vars.size();
  }

  size_t clauseCount() {
    return clauses.size();
  }
};
