#pragma once

#include "ds.h"
#include "utility.h"
#include "tsl.hpp"

#include <charconv>
#include <string>
#include <unordered_map>

class cnf2wl {
private:
  std::vector<std::pair<int, int>> clauses_pt;
  std::vector<std::pair<int, int>> clauses_watches;
  std::vector<int> clauses;
  std::vector<std::vector<int>>  literal_used_list;
  std::vector<std::vector<int>>  variable_watches_clause;

  std::vector<int> assignment;

  int number_of_variables = 0;
  dejavu::ds::markset in_units;
  std::vector<int>  units;

  dejavu::ds::markset clause_satisfied;
  dejavu::ds::markset found_literal;

public:
  void reserve(int n, int m) {
    number_of_variables = n;
    clauses_pt.reserve(m);
    clauses.reserve(4*m);
    clauses_watches.resize(m);
    literal_used_list.resize(2*n);
    variable_watches_clause.resize(2*n);
    assignment.resize(2*n);
    found_literal.initialize(2*n);

    clause_satisfied.initialize(m);
    in_units.initialize(2*n);
  }

  void mark_literal_uses() {
    for(int i = 0; i < n_clauses(); ++i) {
      if(clause_satisfied.get(i)) continue;
      for(int j = 0; j < clause_size(i); ++j) {
        const int lit = literal_at_clause_pos(i, j);
        if(assigned(lit) == 0) found_literal.set(sat_to_graph(lit));
      }
    }
  }

  bool is_literal_marked_used(int lit) {
    return found_literal.get(sat_to_graph(lit));
  }

  int satisfied_clauses() {
    int satisfied = 0;
    for(int i = 0; i < n_clauses(); ++i) {
      satisfied += clause_satisfied.get(i);
    }
    return satisfied;
  }

  bool is_satisfied(int clause) {
    return clause_satisfied.get(clause);
  }

  void add_clause(std::vector<int>& clause) {
    std::sort(clause.begin(), clause.end());
    clause.erase( unique( clause.begin(), clause.end() ), clause.end() );

    const int clause_number = clauses_pt.size();
    clauses_pt.emplace_back(clauses.size(), clauses.size() + clause.size());
    clauses.insert(clauses.end(), clause.begin(), clause.end());
    for(auto& l : clause) {
      assert(l != 0);
      [[maybe_unused]] const int v = abs(l) - 1;
      assert(v >= 0);
      assert(v < number_of_variables);
      literal_used_list[sat_to_graph(l)].push_back(clause_number);
    }

    initialize_watches(clause_number);
  }

  int propagate () {
    int propagations = 0;
    while(true) {
      const int next_unit_literal = dequeue_next_unit();
      if(next_unit_literal == 0) break;
      //std::clog << "unit " << next_unit_literal << std::endl;
      assign_literal(next_unit_literal);
      ++propagations;
    }
    return propagations;
  }

  void queue_units(int literal, int reason_clause) {
    if(!in_units.get(sat_to_graph(literal))) {
      in_units.set(sat_to_graph(literal));
      units.push_back(literal);
    }
  }

  int dequeue_next_unit() {
    if(units.empty()) return 0;
    const int c = units.back();
    units.resize(units.size()-1);
    in_units.unset(sat_to_graph(c));
    return c;
  }


  void assign_literal(int literal) {
    assert(assignment[sat_to_graph(literal)] == 0);
    assert(assignment[sat_to_graph(-literal)] == 0);
    assignment[sat_to_graph(literal)]  = 1;
    assignment[sat_to_graph(-literal)] = -1;

    for(auto c : literal_used_list[sat_to_graph(literal)]) update_satisfied(c);
    while(!variable_watches_clause[abs(literal)].empty()) {
      int next_watched_clause = variable_watches_clause[abs(literal)].back();
      int pos = variable_watches_clause[abs(literal)].size() - 1;
      update_watches(next_watched_clause, abs(literal), pos);
    }
  }

  int assigned(int literal) {
    return assignment[sat_to_graph(literal)];
  }


  void update_satisfied(int clause_number) {
    clause_satisfied.set(clause_number);
  }

  void add_watch(int variable, int watch_clause) {
    variable_watches_clause[abs(variable)].push_back(watch_clause);
  }

  void remove_watch(int variable, int watch_pos) {
    //std::clog << "remove_watch: " << variable << "<-" << watch_pos << std::endl;
    int back_watch = variable_watches_clause[variable].back();
    variable_watches_clause[variable][watch_pos] = back_watch;
    variable_watches_clause[variable].resize(variable_watches_clause[variable].size()-1);
  }

  void initialize_watches(int clause_number) {
    if(clause_size(clause_number) == 1) {
      queue_units(literal_at_clause_pos(clause_number, 0), clause_number);
    } else {
      add_watch(literal_at_clause_pos(clause_number, 0), clause_number);
      add_watch(literal_at_clause_pos(clause_number, 1), clause_number);
      clauses_watches[clause_number] = {clauses_pt[clause_number].first, clauses_pt[clause_number].first+1};
      assert(clauses[clauses_watches[clause_number].first]  == literal_at_clause_pos(clause_number, 0));
      assert(clauses[clauses_watches[clause_number].second] == literal_at_clause_pos(clause_number, 1));
    }
  }

  void update_watches(int clause_number, int from_variable, int from_pos) {
    if(clause_satisfied.get(clause_number)) {
      remove_watch(from_variable, from_pos);
      return;
    }
    auto [watch1, watch2] = clauses_watches[clause_number];
    //std::clog << clause_number << ":" << abs(clauses[watch1]) << ", " <<  abs(clauses[watch2]) << ", " << from_variable << std::endl;
    assert(abs(clauses[watch1]) == from_variable || abs(clauses[watch2]) == from_variable);
    int new_watch = -1;
    for(int i = clauses_pt[clause_number].first; i < clauses_pt[clause_number].second; ++i) {
      if(i != watch1 && i != watch2 && assigned(clauses[i]) == 0) {
        new_watch = i;
        break;
      }
    }
    if(new_watch == -1) {
      remove_watch(from_variable, from_pos);
      if (abs(clauses[watch1]) == from_variable) {
        queue_units(clauses[watch2], clause_number);
      } else {
        assert(abs(clauses[watch2]) == from_variable);
        queue_units(clauses[watch1], clause_number);
      }
    } else {
      remove_watch(from_variable, from_pos);
      add_watch(clauses[new_watch], clause_number);
      if (abs(clauses[watch1]) == from_variable) {
        clauses_watches[clause_number].first = new_watch;
      } else {
        assert(abs(clauses[watch2]) == from_variable);
        clauses_watches[clause_number].second = new_watch;
      }
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

  void dimacs_output_clauses(std::ostream& out) {
    for(int i = 0; i < n_clauses(); ++i) {
      for (int j = 0; j < clause_size(i); ++j) {
        int l = literal_at_clause_pos(i, j);
        out << l << " ";
      }
      out << "0" << "\n";
    }
  }

  void dimacs_output_clauses(FILE* out) {
    constexpr int buffer_size = 16;
    char      buffer[buffer_size];

    for(int i = 0; i < n_clauses(); ++i) {
      for (int j = 0; j < clause_size(i); ++j) {
        const int l = literal_at_clause_pos(i, j);
        std::to_chars(buffer, buffer + buffer_size, l);
        for(int j = 0; buffer[j] != 0; ++j) putc_unlocked(buffer[j], out);
        putc_unlocked(' ', out);
      }
      putc_unlocked('0', out);
      putc_unlocked('\n', out);
    }
  }
};
