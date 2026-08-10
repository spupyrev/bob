#pragma once

#include "cnf2wl.h"
#include "utility.h"
#include "tsl.hpp"

#include <string>
#include <unordered_map>

class cnf {
private:
  tsl::robin_set<std::vector<int>, any_hash>          clause_db_arbitrary;
  tsl::robin_set<std::pair<int, int>, pair_hash>          clause_db_size2;
  tsl::robin_set<std::tuple<int, int, int>, triple_hash>      clause_db_size3;
  std::vector<std::pair<int, int>> clauses_pt;
  std::vector<int> clauses;
  std::vector<std::pair<int, int>> variable_to_nclauses;
  std::vector<std::vector<int>>  variable_used_list;

  dejavu::markset test_used;
  int number_of_variables = 0;

  dejavu::markset support_test;
  std::vector<int> need_to_test_clauses;
  std::vector<int> test_clause;
  std::vector<std::pair<int, int>> add_pairs;

public:
  void read_from_cnf2wl(cnf2wl& other_formula) {
    reserve(other_formula.n_variables(), other_formula.n_clauses() - other_formula.satisfied_clauses());
    std::vector<int> next_clause;
    for(int i = 0; i < other_formula.n_clauses(); ++i) {
      if(other_formula.is_satisfied(i)) continue;
      next_clause.clear();
      bool satisfied = false;
      for(int j = 0; j < other_formula.clause_size(i); ++j) {
        const int lit = other_formula.literal_at_clause_pos(i, j);
        const int assigned = other_formula.assigned(lit);
        satisfied = satisfied || (assigned == 1);
        if(assigned == 0) next_clause.push_back(lit);
      }
      if(!satisfied) add_clause(next_clause);
    }
  }

  void reserve(int n, int m) {
    number_of_variables = n;
    clauses_pt.reserve(m);
    clauses.reserve(4*m);
    variable_used_list.resize(n);
    variable_to_nclauses.reserve(n);
    clause_db_arbitrary.reserve(m);
    clause_db_size2.reserve(m);
    //clause_db_size3.reserve(2*m);
    for(int i = 0; i < n; ++i) {
      variable_to_nclauses.emplace_back(0, 0);
    }
  }

  bool write_db(std::vector<int>& clause) {
    // we're adding the clause, we are gonna update the hash tables in any case
    if (clause.size() == 2) {
      return !clause_db_size2.insert({clause[0], clause[1]}).second;
    } else if (clause.size() == 3) {
      return !clause_db_size3.insert({clause[0], clause[1], clause[2]}).second;
    } else {
      return !clause_db_arbitrary.insert(clause).second;
    }
  }

  bool read_db(std::vector<int>& clause) const {
    // if we're not adding the clause, try to use sequential search
    int min_v = -1;
    int min_v_size = INT32_MAX;
    for (const auto l: clause) {
      const int v = abs(l) - 1;
      const int sz = variable_used_list[v].size();
      if (sz < min_v_size) {
        min_v = v;
        min_v_size = sz;
      }
    }
    if (min_v != -1 && min_v_size < 128) {
      for(auto const c : variable_used_list[min_v]) {
        auto const [pt_start, pt_end] = clauses_pt[c];
        if(pt_end - pt_start != static_cast<int>(clause.size())) continue;
        int j = 0;
        for(int i = pt_start; i < pt_end; ++i) {
          if(clauses[i] != clause[j]) break;
          ++j;
        }
        if(j == static_cast<int>(clause.size())) return true;
      }
      return false;
    } else {
      if(clause.size() == 2) {
        const std::pair<int, int> check_pair = {clause[0], clause[1]};
        return clause_db_size2.find(check_pair) != clause_db_size2.end();
      } else if(clause.size() == 3) {
        const std::tuple<int, int, int> check_triple = {clause[0], clause[1], clause[2]};
        return clause_db_size3.find(check_triple) != clause_db_size3.end();
      } else {
        return clause_db_arbitrary.find(clause) != clause_db_arbitrary.end();
      }
    }
  }

  void add_clause(std::vector<int>& clause) {
    std::sort(clause.begin(), clause.end());
    clause.erase( unique( clause.begin(), clause.end() ), clause.end() );

    if(write_db(clause)) [[unlikely]] return;

    const int clause_number = clauses_pt.size();
    clauses_pt.emplace_back(clauses.size(), clauses.size() + clause.size());
    clauses.insert(clauses.end(), clause.begin(), clause.end());
    for(auto& l : clause) {
      assert(l != 0);
      const int v = abs(l) - 1;
      assert(v >= 0);
      assert(v < number_of_variables);
      if(l > 0) {
        variable_to_nclauses[v].first += 1;
      } else {
        variable_to_nclauses[v].second += 1;
      }
      variable_used_list[v].push_back(clause_number);
    }
  }

  bool complete_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
    support_test.initialize(domain_size);

    assert(automorphism.nsupp() < domain_size);
    for(int i = 0; i < automorphism.nsupp(); ++i) {
      assert(i >= 0);
      assert(i <= automorphism.nsupp());
      assert(automorphism.supp()[i] >= 0);
      assert(automorphism.supp()[i] < domain_size);
      support_test.set(automorphism.supp()[i]);
    }

    add_pairs.clear();
    for(int j = 0; j < automorphism.nsupp(); ++j) {
      const int i = automorphism.supp()[j];
      const int nv = sat_to_graph(-graph_to_sat(i));
      if(support_test.get(i) && !support_test.get(nv)) {
        const int npv = sat_to_graph(-graph_to_sat(automorphism.p()[i]));
        if(support_test.get(npv)) return false;
        //automorphism.write_single_map(nv, npv);
        add_pairs.emplace_back(nv, npv);
      }
    }

    for(auto p : add_pairs) {
      assert(p.first < domain_size);
      assert(p.second < domain_size);
      automorphism.write_single_map(p.first, p.second);
    }

    return true;
  }

  static bool cycle_check(dejavu::ds::markset& scratch_set, const int *p, int supp, const int *supp_arr) {
    scratch_set.reset();
    bool comp = true;
    for(int i = 0; i < supp && comp; ++i) {
      const int v = supp_arr[i];
      if(scratch_set.get(v)) continue;
      int v_next = p[v];
      while(v_next != v && comp) {
        comp = !scratch_set.get(v_next);
        scratch_set.set(v_next);
        v_next = p[v_next];
      }
    }
    return comp;
  }

  int vertex_variable_occurence(int v) {
    return variable_used_list[abs(graph_to_sat(v)) - 1].size();
  }

  bool is_automorphism(int domain_size, dejavu::groups::automorphism_workspace& automorphism) {
    test_used.initialize(n_clauses());
    support_test.initialize(domain_size);
    need_to_test_clauses.clear();

    cycle_check(support_test, automorphism.p(), automorphism.nsupp(), automorphism.supp());
    support_test.reset();

    assert(automorphism.nsupp() <= domain_size);
    for(int i = 0; i < automorphism.nsupp(); ++i) {
      assert(i >= 0);
      assert(i <= automorphism.nsupp());
      assert(automorphism.supp()[i] >= 0);
      assert(automorphism.supp()[i] < domain_size);

      support_test.set(automorphism.supp()[i]);
      const int v = abs(graph_to_sat(automorphism.supp()[i])) - 1;
      for(auto c : variable_used_list[v]) {
        if(!test_used.get(c)) {
          need_to_test_clauses.push_back(c);
          test_used.set(c);
        }
      }
    }

    test_used.reset();

    for(int j = 0; j < automorphism.nsupp(); ++j) {
      const int i = automorphism.supp()[j];
      const int nv = sat_to_graph(-graph_to_sat(i));
      const int nvp = automorphism.p()[nv];
      const int p  = automorphism.p()[i];
      const int pn = sat_to_graph(-graph_to_sat(p));
      if(nvp != pn) return false;
      if(!support_test.get(nv)) return false;
    }

    for(auto c : need_to_test_clauses) {
      test_clause.clear();
      bool all_identity = true;

      for (int j = 0; j < clause_size(c); ++j) {
        int l = literal_at_clause_pos(c, j);
        const int graph_literal = sat_to_graph(l);

        if(support_test.get(graph_literal)) {
          all_identity = false;
          int image_vert = automorphism.p()[graph_literal];
          int image_literal = graph_to_sat(image_vert);
          test_clause.push_back(image_literal);
        } else {
          test_clause.push_back(l);
        }
      }

      if(all_identity) continue;
      std::sort(test_clause.begin(), test_clause.end());

      int j = 0;
      for (; j < clause_size(c); ++j) if(test_clause[j] != literal_at_clause_pos(c, j)) break;
      if(j == clause_size(c)) continue;

      if(!read_db(test_clause)) return false;
    }

    return true;
  }

  int literal_to_number_of_clauses(int l) {
    const int v = abs(l) - 1;
    if(l > 0) {
      return variable_to_nclauses[v].first;
    } else {
      return variable_to_nclauses[v].second;
    }
  }

  int clause_size(int c) {
    return clauses_pt[c].second - clauses_pt[c].first;
  }

  int literal_at_clause_pos(int c, int i) {
    return clauses[clauses_pt[c].first + i];
  }

  int n_total_clause_size() {
    return clauses.size();
  }

  int n_len() {
    return clauses.size();
  }

  int n_clauses() {
    return clauses_pt.size();
  }

  int n_variables() {
    return number_of_variables;
  }

  void dimacs_output_clauses_to(std::vector<std::vector<int>>& clauses) {
    std::vector<int> cl;
    for(int i = 0; i < n_clauses(); ++i) {
      cl.clear();
      for (int j = 0; j < clause_size(i); ++j) {
        const int l = literal_at_clause_pos(i, j);
        cl.push_back(l);
      }
      clauses.push_back(cl);
    }
  }

  void dimacs_output_clauses(std::ostream& out) {
    for(int i = 0; i < n_clauses(); ++i) {
      for (int j = 0; j < clause_size(i); ++j) {
        const int l = literal_at_clause_pos(i, j);
        out << l << " ";
      }
      out << "0" << "\n";
    }
  }

  void dimacs_output_clauses_unlocked(FILE* out) {
    constexpr int buffer_size = 16;
    char      buffer[buffer_size];

    for(int i = 0; i < n_clauses(); ++i) {
      for (int j = 0; j < clause_size(i); ++j) {
        const int l = literal_at_clause_pos(i, j);
        auto const [end_ptr, err] = std::to_chars(buffer, buffer + buffer_size, l);
        for(char* ptr = buffer; ptr < end_ptr; ++ptr) putc_unlocked(*ptr, out);
        putc_unlocked(' ', out);
      }
      putc_unlocked('0', out);
      putc_unlocked('\n', out);
    }
  }
};
