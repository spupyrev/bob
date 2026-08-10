#pragma once

#include "cnf.h"

namespace satsuma {
  class hypergraph_wrapper {
  private:
    std::vector<int> literal_to_binary_clauses;
    std::vector<int> literal_to_ternary_clauses;
    std::vector<int> literal_to_hyperedges;
    std::vector<int> literal_to_removed;
    std::vector<int> literal_iso_inv;
    std::vector<bool> clause_tombstone;

  public:
    cnf& wrapped_formula;
    std::vector<std::vector<int>> hyperedge_list;
    std::vector<int>        hyperedge_color;
    int binary_clauses   = 0;
    int ternary_clauses  = 0;

    int removed_clauses = 0;
    int removed_clause_support = 0;
    int hyperedge_support = 0;

    hypergraph_wrapper(cnf &formula) : wrapped_formula(formula) {
      // initialize trivial hypergraph wrapper (which does not change the underlying formula)
      literal_to_binary_clauses.resize(wrapped_formula.n_variables()*2);
      literal_to_ternary_clauses.resize(wrapped_formula.n_variables()*2);
      literal_to_hyperedges.resize(wrapped_formula.n_variables()*2);
      literal_to_removed.resize(wrapped_formula.n_variables()*2);
      for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
        if(wrapped_formula.clause_size(i) == 2) {
          literal_to_binary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0))] += 1;
          literal_to_binary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1))] += 1;
          ++binary_clauses;
        }

        if(wrapped_formula.clause_size(i) == 3) {
          ++ternary_clauses;
          literal_to_ternary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0))] += 1;
          literal_to_ternary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1))] += 1;
          literal_to_ternary_clauses[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 2))] += 1;
        }
      }
      clause_tombstone.resize(wrapped_formula.n_clauses());
    }

    int literal_to_number_of_binary_clauses(int literal) {
      return literal_to_binary_clauses[sat_to_graph(literal)];
    }

    int literal_to_number_of_hyperedges(int literal) {
      return literal_to_hyperedges[sat_to_graph(literal)];
    }

    int literal_to_number_of_removed_uses(int literal) {
      return literal_to_removed[sat_to_graph(literal)];
    }

    int literal_to_number_of_ternary_clauses(int literal) {
      return literal_to_ternary_clauses[sat_to_graph(literal)];
    }


    void add_hyperedge(std::vector<int> hyperedge, int color) {
      for(auto& l : hyperedge) {
        ++literal_to_hyperedges[sat_to_graph(l)];
      }
      hyperedge_support += hyperedge.size();
      hyperedge_list.push_back(hyperedge);
      hyperedge_color.push_back(color);
    }

    void remove_clause(int i) {
      clause_tombstone[i] = true;
      for(int j = 0; j < wrapped_formula.clause_size(i); ++j) {
        ++literal_to_removed[sat_to_graph(wrapped_formula.literal_at_clause_pos(i, j))];
      }
      removed_clause_support += wrapped_formula.clause_size(i);
      ++removed_clauses;
      if(wrapped_formula.clause_size(i) == 2) --binary_clauses;
    }

    bool is_clause_removed(int i) {
      return clause_tombstone[i];
    }

    int n_hyperedges() {
      return hyperedge_list.size();
    }

    unsigned long iso_inv(int literal) {
      unsigned long hash = hash32shift(wrapped_formula.literal_to_number_of_clauses(literal));
      hash = add_to_hash(hash, hash32shift(literal_to_number_of_binary_clauses(literal)));
      hash = add_to_hash(hash, hash32shift(literal_to_number_of_ternary_clauses(literal)));
      hash = add_to_hash(hash, hash32shift(literal_iso_inv[sat_to_graph(literal)]));
      return hash;
    }

    void hypergraph_reduction() {
      dejavu::groups::orbit orbits2(wrapped_formula.n_variables()*2);
      literal_iso_inv.resize(wrapped_formula.n_variables()*2);
      tsl::robin_set<std::pair<int, int>, pair_hash> clause_tombstone2;

      for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
        if(wrapped_formula.clause_size(i) == 2) {
          orbits2.combine_orbits(sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 0)),
                      sat_to_graph(wrapped_formula.literal_at_clause_pos(i, 1)));
        }
      }
      std::clog << " (binary=" << binary_clauses << ", ternary=" << ternary_clauses << ")" << std::endl;

      for(int i = 0; i < 2*wrapped_formula.n_variables(); ++i) {
        literal_iso_inv[i] = orbits2.orbit_size(i);
      }

      //std::vector<std::vector<int>> vertex_to_orbit2;
      //vertex_to_orbit2.resize(2*wrapped_formula.n_variables());

      // orbit_collect
      /*for(int i = 0; i < 2*wrapped_formula.n_variables(); ++i) {
        //if (!orbits.represents_orbit(i)) continue;
        if (orbits2.orbit_size(i) < 3) continue;
        vertex_to_orbit2[orbits2.find_orbit(i)].push_back(i);
      }*/

      // orbit_replace
      /*clause_tombstone2.reserve(binary_clauses);
      for(int i = 0; i < 2*wrapped_formula.n_variables(); ++i) {
        if (vertex_to_orbit2[i].size() < 3) continue;

        //std::clog << vertex_to_orbit[i].size() << std::endl;

        bool can_replace = true;
        for (int j = 0; j < vertex_to_orbit2[i].size(); ++j) {
          int l1 = graph_to_sat(vertex_to_orbit2[i][j]);
          for (int k = j + 1; k < vertex_to_orbit2[i].size(); ++k) {
            int l2 = graph_to_sat(vertex_to_orbit2[i][k]);
            std::vector<int> clause = {l1, l2};
            std::sort(clause.begin(), clause.end());
            can_replace = wrapped_formula.access_clause_db(clause, false);
            if (!can_replace) break;
          }
          if (!can_replace) break;
        }

        if (can_replace) {
          ++orbit_replace;
          for (int j = 0; j < vertex_to_orbit2[i].size(); ++j) {
            int l1 = graph_to_sat(vertex_to_orbit2[i][j]);
            for (int k = j + 1; k < vertex_to_orbit2[i].size(); ++k) {
              int l2 = graph_to_sat(vertex_to_orbit2[i][k]);
              std::vector<int> clause = {l1, l2};
              std::sort(clause.begin(), clause.end());
              clause_tombstone2.insert({clause[0],clause[1]});
            }
          }
          std::vector<int> hyperedge;
          for (int j = 0; j < vertex_to_orbit2[i].size(); ++j) {
            int l1 = graph_to_sat(vertex_to_orbit2[i][j]);
            hyperedge.push_back(l1);
          }
          add_hyperedge(hyperedge, 3);
          continue;
        }
      }
      for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
        if (wrapped_formula.clause_size(i) != 2) continue;
        const int l1 = wrapped_formula.literal_at_clause_pos(i, 0);
        const int l2 = wrapped_formula.literal_at_clause_pos(i, 1);
        if(clause_tombstone2.find({l1, l2}) != clause_tombstone2.end()) remove_clause(i);
      }*/

      // ternary negation macro
      for(int i = 0; i < wrapped_formula.n_clauses(); ++i) {
        if (wrapped_formula.clause_size(i) != 3) continue;
        const int l1 = wrapped_formula.literal_at_clause_pos(i, 0);
        const int l2 = wrapped_formula.literal_at_clause_pos(i, 1);
        const int l3 = wrapped_formula.literal_at_clause_pos(i, 2);

        bool canonical = true;

        std::vector<int> orig_clause = {l1, l2, l3};
        std::vector<int> flips = {};
        int flips_exist = 0;
        std::vector<int> test_clause;
        for(int f1 = 0; f1 <= 1; ++f1) {
          for(int f2 = 0; f2 <= 1; ++f2) {
            for(int f3 = 0; f3 <= 1; ++f3) {
              test_clause = orig_clause;
              if(f1 == 1) test_clause[0] = -test_clause[0];
              if(f2 == 1) test_clause[1] = -test_clause[1];
              if(f3 == 1) test_clause[2] = -test_clause[2];
              std::sort(test_clause.begin(), test_clause.end());
              if(wrapped_formula.read_db(test_clause)) {
                if(test_clause < orig_clause) {
                  canonical = false;
                }

                flips_exist += 1;
                flips.push_back(f1 + f2 + f3);
              }
            }
          }
        }


        int excluded_negation_symmetry = (iso_inv(l1) != iso_inv(-l1)) +
                       (iso_inv(l2) != iso_inv(-l2)) +
                       (iso_inv(l3) != iso_inv(-l3));


        if(flips_exist == 4 && flips[0] == 0 && flips[1] == 2 && flips[2] == 2 && flips[3] == 2 &&
           excluded_negation_symmetry >= 2) {
          // CFI gate with fixed flips
          remove_clause(i);
          if(canonical) {
            std::vector<int> hyperedge;
            for(int k = 0; k < 3; ++k) {
              if (iso_inv(orig_clause[k]) <
                iso_inv(-orig_clause[k])) {
                hyperedge.push_back(orig_clause[k]);
              } else if (iso_inv(-orig_clause[k]) <
                  iso_inv(orig_clause[k])) {
                hyperedge.push_back(-orig_clause[k]);
              } else {
                hyperedge.push_back(orig_clause[k]);
              }
            }
            add_hyperedge(hyperedge, 0);
          }
        } else if(flips_exist == 2 && flips[0] == 0 && flips[1] == 3 && excluded_negation_symmetry > 0) {
          // full negation flip
          remove_clause(i);
          if(canonical) {
            std::vector<int> canonical_literals;
            for(int k = 0; k < 3; ++k) {
              if (iso_inv(orig_clause[k]) <
                  iso_inv(-orig_clause[k])) {
                canonical_literals.push_back(orig_clause[k]);
              } else if (iso_inv(-orig_clause[k]) <
                  iso_inv(orig_clause[k])) {
                canonical_literals.push_back(-orig_clause[k]);
              }
            }
            if ( std::find(orig_clause.begin(), orig_clause.end(), canonical_literals[0]) != orig_clause.end()) {
              add_hyperedge(orig_clause, 1);
            } else {
              add_hyperedge({-orig_clause[0], -orig_clause[1], -orig_clause[2]}, 1);
            }
          }
        } else if(flips_exist == 4 && flips[0] == 0 && flips[1] == 2 && flips[2] == 2 && flips[3] == 2 &&
              excluded_negation_symmetry == 1) {
          /*remove_clause(i);
          //std::clog << "CFI_gadget flips exist: " << flips_exist << " excluded_negation_symmetry: "
          //      << excluded_negation_symmetry << std::endl;
          if(canonical) {
            std::vector<int> hyperedge;
            for(int k = 0; k < 3; ++k) {
              if (iso_inv(orig_clause[k]) <
                iso_inv(-orig_clause[k])) {
                hyperedge.push_back(orig_clause[k]);
              } else if (iso_inv(-orig_clause[k]) <
                     iso_inv(orig_clause[k])) {
                hyperedge.push_back(-orig_clause[k]);
              } else {
                hyperedge.push_back(orig_clause[k]);
              }
            }
            add_hyperedge(hyperedge, 0);
            ++ternary_negations;
          }*/
        }
        /*
        std::clog << "orig: " << std::endl;
        std::clog << l1 << " " << l2 << " " << l3 << " " << std::endl;

        for(int k = 0; k < 3; ++k) {
          std::vector<int> clause1 = {l1, l2, l3};
          std::vector<int> clause2 = {l1, l2, l3};

          const int kf1 = (k+1) % 3;
          const int kf2 = (k+2) % 3;

          clause1[k] = -clause1[k];
          clause2[k] = -clause2[k];
          clause1[kf1] = -clause1[kf1];
          clause2[kf2] = -clause2[kf2];

          std::clog << clause1[0] << " " << clause1[1] << " " << clause1[2] << " " << std::endl;
          std::clog << clause2[0] << " " << clause2[1] << " " << clause2[2] << " " << std::endl;

          std::sort(clause1.begin(), clause1.end());
          std::sort(clause2.begin(), clause2.end());

          const bool test1 = wrapped_formula.access_clause_db(clause2, false);
          const bool test2 = wrapped_formula.access_clause_db(clause1, false);

          const bool can_replace = test1 && test2;
          if(can_replace) can_replace_count += 1;
          replace_k = can_replace? k : replace_k;
        }
        */
      }
      std::clog << "c\t +hyedge=" << n_hyperedges() << ", +hyedge_sup=" << hyperedge_support << ", -cl=" << removed_clauses
            << ", -cl_sup=" << removed_clause_support << std::endl;
      //std::clog << "c\t found " << replacement_possible.size() << " [clauses: " << potential_removed_clauses << "] potential hypergraph reductions" << std::endl;
    }
  };
}
