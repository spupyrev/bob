#pragma once

#include "cnf.h"
#include "dejavu.h"
#include "predicate.h"
#include "hypergraph.h"

/**
 * Constructs and analysis a group from a CNF representation of a SAT instance.
 */
class group_analyzer {
  dejavu::solver d;
  dejavu::ir::refinement ref;

  dejavu::static_graph graph;
  dejavu::sgraph   save_graph;
  dejavu::coloring save_col;
  dejavu::coloring remainder_col;

  dejavu::coloring row_test_col;
  std::vector<int> row_touched_size;

  std::vector<int> orbit_list;
  dejavu::markset orbit_handled;
  dejavu::groups::orbit orbits;
  dejavu::groups::orbit orbits_graph;
  std::vector<std::vector<int>> orbit_vertices;

  dejavu::groups::automorphism_workspace aw;
  dejavu::markset store_helper;
  std::vector<dejavu::groups::stored_automorphism*> generators;

  int domain_size = 0;
  int domain_size_graph = 0;

  void my_hook(int n, const int* p, int nsupp, const int *supp) {
    orbits_graph.add_automorphism_to_orbit(p, nsupp, supp);

    aw.reset();
    for(int j = 0; j < nsupp; ++j) {
      if(supp[j] < domain_size) {
        assert(p[supp[j]] < domain_size); // ensured by vertex coloring, can't interchange literals and clauses
        aw.write_single_map(supp[j], p[supp[j]]);
      }
    }
    if(aw.nsupp() > 0) {
      orbits.add_automorphism_to_orbit(aw);
      generators.push_back(new dejavu::groups::stored_automorphism());
      generators.back()->store(domain_size, aw, store_helper);
    }
    aw.reset();
  }

  std::function<type_dejavu_hook> self_hook() {
    return [this](auto && PH1, auto && PH2, auto && PH3, auto && PH4) { return
        my_hook(std::forward<decltype(PH1)>(PH1), std::forward<decltype(PH2)>(PH2),
               std::forward<decltype(PH3)>(PH3), std::forward<decltype(PH4)>(PH4));
    };
  }

public:

  /**
   * Computes the automorphism group of the given CNF \p formula. Constructs a graph from the formula, followed by
   * a call to dejavu, collecting the necessary data for the group analysis.
   *
   * @param formula The CNF formula for which symmetries shall be computed.
   */
  void compute_from_cnf(cnf& formula, bool out_graph = false, std::string filename = "") {
    domain_size = 2*formula.n_variables();
    domain_size_graph = 2*formula.n_variables() + formula.n_clauses();
    aw.resize(domain_size);
    orbits.initialize(domain_size);
    orbits_graph.initialize(domain_size_graph);
    store_helper.initialize(domain_size);

    // construct graph
    graph.initialize_graph(domain_size_graph, formula.n_total_clause_size() + formula.n_variables());
    int unused_color = 2;

    // vertices for literals
    for(int i = 1; i < formula.n_variables() + 1; ++i) {
      const int lp = i;
      const int ln = -i;

      const int lp_uses = formula.literal_to_number_of_clauses(lp);
      const int ln_uses = formula.literal_to_number_of_clauses(ln);

      if(lp_uses == 0 && ln_uses == 0) {
        graph.add_vertex(unused_color++, lp_uses + 1);
        graph.add_vertex(unused_color++, ln_uses + 1);
      } else {
        graph.add_vertex(0, lp_uses + 1);
        graph.add_vertex(0, ln_uses + 1);
      }
    }

    // vertices for clauses
    int clause_vertex_st = 2*formula.n_variables();
    for(int i = 0; i < formula.n_clauses(); ++i) {
      graph.add_vertex(1, formula.clause_size(i));
    }

    // connect literals belonging to the same variable
    for(int i = 0; i < formula.n_variables(); ++i) {
      int vert_lp = 2*i;
      int vert_ln = 2*i+1;
      graph.add_edge(vert_lp, vert_ln);
    }

    // connect clauses to contained literals
    for(int i = 0; i < formula.n_clauses(); ++i) {
      for(int j = 0; j < formula.clause_size(i); ++j) {
        int l = formula.literal_at_clause_pos(i, j);
        int v = abs(l) - 1;
        int is_neg = l < 0;
        int l_to_vertex = 2*v + is_neg;
        graph.add_edge(l_to_vertex, clause_vertex_st+i);
      }
    }
    if(out_graph) graph.dump_dimacs(filename);

    // save graph for heuristics later
    save_graph.copy_graph(graph.get_sgraph());
    save_graph.initialize_coloring(&save_col, graph.get_coloring());
    ref.refine_coloring(graph.get_sgraph(), &save_col);

    remainder_col.copy_any(&save_col);

    // make orbits from color refinement
    for(int j = 0; j < domain_size_graph;) {
      const int col_sz = save_col.ptn[j] + 1;
      const int vref = save_col.lab[j];
      for(int k = j; k < j + col_sz; ++k) {
        const int v = save_col.lab[k];
        if(v < domain_size) orbits.combine_orbits(v, vref);
        orbits_graph.combine_orbits(v, vref);
      }

      j += col_sz;
    }

    // call dejavu
    //detect_symmetries_generic();

    // make list of orbits
    orbit_handled.initialize(domain_size);
    orbit_vertices.resize(domain_size);
    for(int i = 0; i < domain_size; ++i) {
      if (orbits.represents_orbit(i) && orbits.orbit_size(i) > 1) orbit_list.push_back(i);
      orbit_vertices[orbits.find_orbit(i)].push_back(i);
    }

    // make a vertex coloring from the orbit partition
    dejavu::ds::worklist vertex_to_orbit(domain_size_graph);
    for(int i = 0; i < domain_size_graph; ++i) vertex_to_orbit[i] = orbits_graph.find_orbit(i);
    save_graph.initialize_coloring(&save_col, vertex_to_orbit.get_array());
  }

  void compute_from_hypergraph(satsuma::hypergraph_wrapper& hypergraph, bool out_graph = false,
                 std::string filename = "") {

    cnf& formula = hypergraph.wrapped_formula;
    const bool use_binary_graph  = (hypergraph.binary_clauses > formula.n_variables());
    const bool use_variable_vertex = use_binary_graph;
    //const bool use_binary_graph = false;
    std::clog << " (binary_graph=" << use_binary_graph << ")";

    domain_size = 2*formula.n_variables();
    domain_size_graph = 2*formula.n_variables() + formula.n_clauses()
              - use_binary_graph*hypergraph.binary_clauses + use_variable_vertex*formula.n_variables()
              - hypergraph.removed_clauses + hypergraph.n_hyperedges();

    aw.resize(domain_size);
    orbits.initialize(domain_size);
    orbits_graph.initialize(domain_size_graph);
    store_helper.initialize(domain_size);

    const int total_edges = formula.n_total_clause_size() + formula.n_variables()
                - use_binary_graph*hypergraph.binary_clauses
                + use_variable_vertex*formula.n_variables()
                - hypergraph.removed_clause_support
                + hypergraph.hyperedge_support;
    // construct graph
    graph.initialize_graph(domain_size_graph, total_edges);
    int unused_color = 2 + use_variable_vertex;

    // vertices for literals
    for(int i = 1; i < formula.n_variables() + 1; ++i) {
      const int lp = i;
      const int ln = -i;

      const int lp_uses = formula.literal_to_number_of_clauses(lp)
                - hypergraph.literal_to_number_of_removed_uses(lp)
                + hypergraph.literal_to_number_of_hyperedges(lp);
      const int ln_uses = formula.literal_to_number_of_clauses(ln)
                - hypergraph.literal_to_number_of_removed_uses(ln)
                + hypergraph.literal_to_number_of_hyperedges(ln);

      if(lp_uses == 0 && ln_uses == 0) {
        graph.add_vertex(unused_color++, lp_uses + 1);
        graph.add_vertex(unused_color++, ln_uses + 1);
      } else {
        graph.add_vertex(0, lp_uses + 1);
        graph.add_vertex(0, ln_uses + 1);
      }
    }

    // vertices for clauses
    int clause_vertex_st = 2*formula.n_variables();
    for(int i = 0; i < formula.n_clauses(); ++i) {
      if(use_binary_graph && formula.clause_size(i) == 2) continue;
      if(hypergraph.is_clause_removed(i)) continue;
      graph.add_vertex(1, formula.clause_size(i));
    }

    // vertices for hyperedges
    const int hyperedge_start = 2*formula.n_variables() + formula.n_clauses() - hypergraph.removed_clauses
                  - use_binary_graph*hypergraph.binary_clauses;
    int hyperedge_added_support = 0;
    for(int i = 0; i < hypergraph.n_hyperedges(); ++i) {
      //assert(hypergraph.hyperedge_list[i].size() == 3);
      graph.add_vertex(3+hypergraph.hyperedge_color[i], hypergraph.hyperedge_list[i].size());
      hyperedge_added_support += hypergraph.hyperedge_list[i].size();
    }
    assert(hyperedge_added_support == hypergraph.hyperedge_support);

    const int variable_vertex_start = 2 * formula.n_variables() + formula.n_clauses() - hypergraph.removed_clauses
                      - use_binary_graph*hypergraph.binary_clauses + hypergraph.n_hyperedges();
    // vertices for binary graph
    if(use_variable_vertex) {
      for (int i = 1; i < formula.n_variables() + 1; ++i) {
        graph.add_vertex(2, 2);
      }
    }

    for(int i = 0; i < static_cast<int>(hypergraph.hyperedge_list.size()); ++i) {
      assert((int)hypergraph.hyperedge_list[i].size() < formula.n_variables()*2);
    }

    // connect literals belonging to the same variable
    for(int i = 0; i < formula.n_variables(); ++i) {
      const int vert_lp = 2*i;
      const int vert_ln = 2*i+1;
      if(use_variable_vertex) {
        const int bin_vert = variable_vertex_start + i;
        graph.add_edge(vert_lp, bin_vert);
        graph.add_edge(vert_ln, bin_vert);
      } else {
        graph.add_edge(vert_lp, vert_ln);
      }
    }

    // connect clauses to contained literals
    int actual_i = 0;
    for(int i = 0; i < formula.n_clauses(); ++i) {
      if(hypergraph.is_clause_removed(i)) continue;
      if(use_binary_graph && formula.clause_size(i) == 2) {
        const int l1 = formula.literal_at_clause_pos(i, 0);
        const int l2 = formula.literal_at_clause_pos(i, 1);

        const int v1 = abs(l1) - 1;
        const int is_neg1 = l1 < 0;
        const int l_to_vertex1 = 2*v1 + is_neg1;

        const int v2 = abs(l2) - 1;
        const int is_neg2 = l2 < 0;
        const int l_to_vertex2 = 2*v2 + is_neg2;

        assert(l_to_vertex1 != l_to_vertex2);
        if(l_to_vertex1 < l_to_vertex2) graph.add_edge(l_to_vertex1, l_to_vertex2);
        else graph.add_edge(l_to_vertex2, l_to_vertex1);
        continue;
      }
      for(int j = 0; j < formula.clause_size(i); ++j) {
        const int l = formula.literal_at_clause_pos(i, j);
        const int v = abs(l) - 1;
        const int is_neg = l < 0;
        const int l_to_vertex = 2*v + is_neg;
        graph.add_edge(l_to_vertex, clause_vertex_st+actual_i);
      }
      ++actual_i;
    }

    assert(actual_i == formula.n_clauses() - hypergraph.removed_clauses - use_binary_graph*hypergraph.binary_clauses);

    assert(hypergraph.n_hyperedges() == (int)hypergraph.hyperedge_list.size());
    for(int i = 0; i < static_cast<int>(hypergraph.hyperedge_list.size()); ++i) {
      assert(i < (int)hypergraph.hyperedge_list.size());
      assert((int)hypergraph.hyperedge_list[i].size() < formula.n_variables()*2);
      int support_added = 0;
      for(int j = 0; j < static_cast<int>(hypergraph.hyperedge_list[i].size()); ++j) {
        const int l = hypergraph.hyperedge_list[i][j];
        assert(l <= formula.n_variables());
        const int v = abs(l) - 1;
        const int is_neg = l < 0;
        const int l_to_vertex = 2*v + is_neg;
        ++support_added;
        assert(support_added < hypergraph.hyperedge_support);
        graph.add_edge(l_to_vertex, hyperedge_start+i);
      }
    }

    if(out_graph) graph.dump_dimacs(filename);

    // save graph for heuristics later
    save_graph.copy_graph(graph.get_sgraph());
    save_graph.initialize_coloring(&save_col, graph.get_coloring());
    ref.refine_coloring(graph.get_sgraph(), &save_col);

    remainder_col.copy_any(&save_col);

    // make orbits from color refinement
    for(int j = 0; j < domain_size_graph;) {
      const int col_sz = save_col.ptn[j] + 1;
      const int vref = save_col.lab[j];
      for(int k = j; k < j + col_sz; ++k) {
        const int v = save_col.lab[k];
        if(v < domain_size) orbits.combine_orbits(v, vref);
        orbits_graph.combine_orbits(v, vref);
      }

      j += col_sz;
    }

    // make list of orbits
    orbit_handled.initialize(domain_size);
    orbit_vertices.resize(domain_size);
    for(int i = 0; i < domain_size; ++i) {
      if (orbits.represents_orbit(i) && orbits.orbit_size(i) > 1) orbit_list.push_back(i);
      orbit_vertices[orbits.find_orbit(i)].push_back(i);
    }

    // make a vertex coloring from the orbit partition
    dejavu::ds::worklist vertex_to_orbit(domain_size_graph);
    for(int i = 0; i < domain_size_graph; ++i) vertex_to_orbit[i] = orbits_graph.find_orbit(i);
    save_graph.initialize_coloring(&save_col, vertex_to_orbit.get_array());
  }

  int n_orbits() {
    return orbit_list.size();
  }

  int n_generators() {
    return generators.size();
  }

  void detect_symmetries_generic(bool dejavu_print=false, bool dejavu_prefer_dfs=false) {
    orbits.reset();
    orbits_graph.reset();
    orbits_graph.reset();

    // call dejavu
    std::clog << "c\t [graph: #vertices " << graph.get_sgraph()->v_size << " #edges " << graph.get_sgraph()->e_size << "]";
    //auto test_hook = dejavu::hooks::ostream_hook(std::clog);
    auto hook_func = dejavu_hook(self_hook());
    dejavu::hooks::strong_certification_hook cert_hook(graph, &hook_func);
    //graph.dump_dimacs("graph_binary.dimacs");
    d.set_prefer_dfs(dejavu_prefer_dfs);
    d.set_print(dejavu_print);
    orbits_graph.reset();
    orbits.reset();
    d.automorphisms(graph.get_sgraph(), remainder_col.vertex_to_col, cert_hook.get_hook());
    //d.automorphisms(graph.get_sgraph(), graph.get_coloring(), test_hook.get_hook());
  }

  /**
   *   Checks whether the group contains orbits exhibiting a natural symmetric action, and adds appropriate breaking
   *   constraints to the predicate \p sbp.
   *   @param formula The formula, used to test candidate symmetries.
   *   @param sbp The symmetry breaking predicate, to which potential breaking constraints are added.
   */
  void detect_symmetric_action(cnf& formula, predicate& sbp) {
    std::clog << "c\t probe for symmetric actions..." << std::endl;

    // proceed orbit-by-orbit
    for (int i = 0; i < static_cast<int>(orbit_list.size()); ++i) {
      if(orbit_handled.get(orbit_list[i])) continue;
      const int anchor_vertex = orbit_list[i];
      std::vector<int> orbit = orbit_vertices[anchor_vertex];

      bool potential_symmetric_action = true;

      // check that transposition between vertex 0 and vertex j is a symmetry of formula
      for(int j = 1; j < static_cast<int>(orbit.size()); ++j) {
        aw.reset();
        aw.write_single_map(orbit[0], orbit[j]);
        aw.write_single_map(orbit[j], orbit[0]);
        potential_symmetric_action = potential_symmetric_action &&
            formula.complete_automorphism(domain_size, aw);
        if(!potential_symmetric_action || !formula.is_automorphism(domain_size, aw)) {
          potential_symmetric_action = false;
          break;
        }
      }

      if(!potential_symmetric_action) continue;

      // if all the above transpositions are allowed, the orbit admits a natural symmetric action
      std::clog << "c\t symmetric action orbit " << anchor_vertex << std::endl;
      for(int j = 1; j < static_cast<int>(orbit.size()); ++j) {
        aw.reset();
        aw.write_single_map(orbit[0], orbit[j]);
        aw.write_single_map(orbit[j], orbit[0]);

        if(!formula.complete_automorphism(domain_size, aw)) break;
        assert(formula.is_automorphism(domain_size, aw));
        sbp.add_lex_leader_predicate(formula, aw, orbit);
      }

      // mark the orbit, and negation orbit, as handled (will not be touched again)
      orbit_handled.set(orbits.find_orbit(anchor_vertex));
      orbit_handled.set(orbits.find_orbit(sat_to_graph(-graph_to_sat(anchor_vertex))));
    }

  }

  /**
   * Part of the detection algorithm for Johnson actions.
   * @param ir_controller
   * @param orbit
   * @param anchor_vertex
   * @param second_anchor
   * @return
   */
  std::vector<int> detect_intersection(dejavu::ir::controller& ir_controller, std::vector<int>& orbit,
                     int anchor_vertex, int second_anchor = -1) {
    assert(ir_controller.get_base_pos() == 0);
    assert(ir_controller.c->ptn[ir_controller.c->vertex_to_col[anchor_vertex]] + 1 ==
         static_cast<int>(orbit.size()));

    ir_controller.move_to_child(&save_graph, anchor_vertex);
    dejavu::markset intersected_vertices(domain_size);

    // which variables belong to these vertices
    dejavu::markset colors(domain_size);
    std::vector<int> remainders_sz;
    std::vector<int> remainders_col;
    for(auto v : orbit) {
      const int col  = ir_controller.c->vertex_to_col[v];
      const int col_sz = ir_controller.c->ptn[col] + 1;
      if(!colors.get(col)) {
        colors.set(col);
        remainders_col.push_back(col);
        remainders_sz.push_back(col_sz);
      }
    }

    if(remainders_sz.size() != 3) return {};

    std::sort(remainders_sz.begin(), remainders_sz.end());

    int candidate_col = 0;
    for(auto r : remainders_col) {
      if(ir_controller.c->ptn[r] + 1 == remainders_sz[1]) {
        candidate_col = r;
        break;
      }
    }

    for(int j = candidate_col; j < candidate_col + ir_controller.c->ptn[candidate_col] + 1; ++j) {
      intersected_vertices.set(ir_controller.c->lab[j]);
    }

    std::vector<int> second_remainders_col;
    std::vector<int> second_remainders_sz;
    const int second_anchor_vertex = second_anchor==-1?ir_controller.c->lab[candidate_col]:second_anchor;

    ir_controller.move_to_parent();
    ir_controller.move_to_child(&save_graph, second_anchor_vertex);

    colors.reset();
    for(auto v : orbit) {
      const int col  = ir_controller.c->vertex_to_col[v];
      const int col_sz = ir_controller.c->ptn[col] + 1;
      if(!colors.get(col)) {
        colors.set(col);
        second_remainders_sz.push_back(col_sz);
        second_remainders_col.push_back(col);
      }
    }

    if(second_remainders_sz.size() != 3) return {};
    std::sort(second_remainders_sz.begin(), second_remainders_sz.end());
    int second_candidate_col = 0;
    for(auto r : second_remainders_col) {
      if(ir_controller.c->ptn[r] + 1 == second_remainders_sz[1]) {
        second_candidate_col = r;
        break;
      }
    }

    std::vector<int> intersected_vertices_list;
    intersected_vertices_list.push_back(anchor_vertex);
    intersected_vertices_list.push_back(second_anchor_vertex);
    for(int j = second_candidate_col; j < second_candidate_col + ir_controller.c->ptn[second_candidate_col] + 1; ++j) {
      if(intersected_vertices.get(ir_controller.c->lab[j])) {
        intersected_vertices_list.push_back(ir_controller.c->lab[j]);
      }
    }

    ir_controller.move_to_parent();

    ir_controller.move_to_child(&save_graph, anchor_vertex);
    ir_controller.move_to_child(&save_graph, second_anchor_vertex);
    for(auto sing : ir_controller.singletons) {
      if(sing >= domain_size) continue;
      if(intersected_vertices.get(sing) && sing != anchor_vertex && sing != second_anchor_vertex) {
        intersected_vertices_list.erase(std::remove(intersected_vertices_list.begin(),
                              intersected_vertices_list.end(), sing),
                              intersected_vertices_list.end());
      }
    }
    ir_controller.move_to_parent();
    ir_controller.move_to_parent();

    return intersected_vertices_list;
  }

  // A hash function used to hash a pair of any kind
  struct hash_pair {
    template <class T1, class T2>
    size_t operator()(const std::pair<T1, T2>& p) const
    {
      auto hash1 = std::hash<T1>{}(p.first);
      auto hash2 = std::hash<T2>{}(p.second) + 1002583;

      if (hash1 != hash2) {
        return hash1 ^ hash2;
      }

      // If hash1 == hash2, their XOR is zero.
      return hash1;
    }
  };

  /**
   * Checks whether the group contains orbits exhibiting a Johnson action, and adds appropriate breaking
   * constraints to the predicate \p sbp. On further orbits, the Johnson action is accepted on blocks of the orbits.
   * Finally, it is recursively checked whether these blocks admit a further row symmetry action.
   *
   * @param formula The given CNF formula.
   * @param sbp The predicate to which the double-lex constraint is added.
   */
  void detect_johnson_arity2(cnf& formula, predicate& sbp, int limit = -1) {
    std::clog << "c\t probe for Johnson action (limit=" << limit << ")" << std::endl;

    for(int i = 0; i < static_cast<int>(orbit_list.size()); ++i) {
      if(limit >= 0 && i >= limit) return;
      if(orbit_handled.get(orbit_list[i] )) continue;
      int anchor_vertex = orbit_list[i];
      if(orbit_vertices[anchor_vertex].size() < 28) continue;
      std::vector<int> orbit = orbit_vertices[anchor_vertex];


      bool potential_johnson = true;
      dejavu::coloring test_col;
      test_col.copy_any(&save_col);

       int johnson_color = save_col.vertex_to_col[anchor_vertex];
       int johnson_color_sz = save_col.ptn[johnson_color] + 1;

      int imaginary_domain_cnt = 0;
      std::vector<std::vector<int>> models_subset;
      models_subset.resize(domain_size);

      dejavu::ir::controller ir_controller(&ref, &test_col);

      for(auto vertex : orbit) {
        if(models_subset[vertex].size() != 0) continue;
        std::vector<int> intersected_vertices_list = detect_intersection(ir_controller, orbit, vertex);

        if(intersected_vertices_list.size() == 0) {
          potential_johnson = false;
          break;
        }

        for (auto iv: intersected_vertices_list) {
          models_subset[iv].push_back(imaginary_domain_cnt);
          if(models_subset[iv].size() > 2) {
            potential_johnson = false;
            break;
          }
        }
        if(!potential_johnson) break;
        ++imaginary_domain_cnt;
      }

      if(!potential_johnson) continue;

      int first_anchor  = -1;
      int second_anchor = -1;

      for(auto vertex : orbit) {
        if (models_subset[vertex].size() == 1 && first_anchor == -1) {
          first_anchor = vertex;
        } else if (models_subset[vertex].size() == 1 && second_anchor == -1) {
          second_anchor = vertex;
        }
      }

      if(first_anchor >= 0 && second_anchor >= 0) {
        std::vector<int> intersected_vertices_list = detect_intersection(ir_controller, orbit,
                                         first_anchor, second_anchor);
        if(intersected_vertices_list.size() == 0) {
          potential_johnson = false;
          continue;
        }

        for (auto iv: intersected_vertices_list) {
          models_subset[iv].push_back(imaginary_domain_cnt);
          if(models_subset[iv].size() > 2) {
            potential_johnson = false;
            break;
          }
        }
      }

      for(auto vertex : orbit) {
        if (models_subset[vertex].size() != 2) {
          potential_johnson = false;
          break;
        }
      }

      if(!potential_johnson) continue;

      std::clog << "c\t candidate Johnson " << imaginary_domain_cnt+1 << ", ar 2" << std::endl;

      std::unordered_map<std::pair<int,int>, int, hash_pair> lookup_subset;
      for(auto vertex : orbit) {
        lookup_subset[std::pair<int, int>(models_subset[vertex][0], models_subset[vertex][1])] = vertex;
        lookup_subset[std::pair<int, int>(models_subset[vertex][1], models_subset[vertex][0])] = vertex;
      }

      // Johnson might act on blocks of other orbits, so let's find them
      std::vector<std::vector<int>> johnson_block_action;
      johnson_block_action.resize(imaginary_domain_cnt+1);
      dejavu::markset block_tester(domain_size);
      dejavu::workspace singleton_pos(domain_size);

      for(int k = 0; k < static_cast<int>(orbit_list.size()); ++k) {
        if(k == i) continue;
        const int v_test = orbit_list[k];
        if(orbits.find_orbit(sat_to_graph(-graph_to_sat(v_test))) == i) continue;
        const int check_col = save_col.vertex_to_col[v_test];
        const int check_col_sz = save_col.ptn[check_col] + 1;

        for(int x = check_col; x < check_col + check_col_sz; ++x) {
          const int v = save_col.lab[x];
          ir_controller.move_to_child(&save_graph, v);

          for (int l = johnson_color; l < johnson_color + johnson_color_sz;) {
            const int col_sz = ir_controller.c->ptn[l] + 1;
            if (col_sz == imaginary_domain_cnt) {
              block_tester.reset();
              // find out if this fragment determines a imaginary domain vertex
              int domain_vertex = -1;
              for(int y = l; y < l + col_sz; ++y) {
                const int fragment_vertex = ir_controller.c->lab[y];
                if(fragment_vertex >= domain_size) break;
                if(y == l) {
                  block_tester.set(models_subset[fragment_vertex][0]);
                  block_tester.set(models_subset[fragment_vertex][1]);
                } else {
                  if(block_tester.get(models_subset[fragment_vertex][0])) {
                    domain_vertex = models_subset[fragment_vertex][0];
                    break;
                  } else if(block_tester.get(models_subset[fragment_vertex][1])) {
                    domain_vertex = models_subset[fragment_vertex][1];
                    break;
                  }
                }
              }
              if(domain_vertex == -1) break;
              johnson_block_action[domain_vertex].push_back(v);
              break;
            }
            l += col_sz;
          }
          ir_controller.move_to_parent();
        }
      }

      block_tester.reset();
      for(int j = 1; j < imaginary_domain_cnt+1; ++j) {
        for(int k = 0; k < static_cast<int>(johnson_block_action[j].size()); ++k) {
          assert(save_col.vertex_to_col[johnson_block_action[j][k]] == save_col.vertex_to_col[johnson_block_action[j-1][k]]);
        }
      }
      for(int j = 0; j < imaginary_domain_cnt+1 && potential_johnson; ++j) {
        for(auto v : johnson_block_action[j]) {
          if(block_tester.get(v)) {
            potential_johnson = false;
            break;
          }
          block_tester.set(v);
        }
      }

      if(!potential_johnson) continue;

      // check if blocks of johnson_block_action admit row symmetry
      block_tester.reset();
      std::vector<int> in_row;
      std::vector<int> row_pos;
      in_row.resize(domain_size);
      row_pos.resize(domain_size);
      for(int j = 0; j < static_cast<int>(johnson_block_action[0].size()); ++j) {
        const int test_block = save_col.vertex_to_col[johnson_block_action[0][j]];
        const int test_block_neg = save_col.vertex_to_col[sat_to_graph(-graph_to_sat(johnson_block_action[0][j]))];
        if(block_tester.get(test_block) || block_tester.get(test_block_neg)) continue;
        block_tester.set(test_block);
        std::vector<int> extracted_block;
        for (int k = 0; k < static_cast<int>(johnson_block_action[0].size()); ++k) {
          const int vs = johnson_block_action[0][k];
          if(save_col.vertex_to_col[vs] == test_block) extracted_block.push_back(vs);
        }
        detect_row_symmetry_orbit(formula, sbp, extracted_block, ir_controller, nullptr, &orbit,
                      &in_row, &row_pos);
      }

      // order block action according to which row vertices belong to
      for(int j = 0; j < imaginary_domain_cnt+1; ++j) {
        std::sort(johnson_block_action[j].begin(), johnson_block_action[j].end(),[&](int A, int B) -> bool
        {return (save_col.vertex_to_col[A] < save_col.vertex_to_col[B]) ||
            ((save_col.vertex_to_col[A] == save_col.vertex_to_col[B]) && in_row[A] < in_row[B]);});
      }

      // now try to confirm the Johnson action
      for(int j = 1; j < imaginary_domain_cnt+1; ++j) {
        aw.reset();

        for(int k = 0; k < imaginary_domain_cnt+1; ++k) {
          if(k == j || k == j - 1) continue;
          const std::pair<int, int> p_from = {k, j};
          const std::pair<int, int> p_to   = {k, j-1};

          const int subset_from = lookup_subset[p_from];
          const int subset_to = lookup_subset[p_to];

          //models_subset
          aw.write_single_map(subset_from, subset_to);
          aw.write_single_map(subset_to, subset_from);
        }

        for(int k = 0; k < static_cast<int>(johnson_block_action[j].size()); ++k) {
          aw.write_single_map(johnson_block_action[j-1][k], johnson_block_action[j][k]);
          aw.write_single_map(johnson_block_action[j][k], johnson_block_action[j-1][k]);
        }

        potential_johnson = potential_johnson && formula.complete_automorphism(domain_size, aw);
        if(!potential_johnson || !formula.is_automorphism(domain_size, aw)) {
          potential_johnson = false;
          std::clog << "c\t not a Johnson action(" << j-1 << ", " << j << ") " << johnson_block_action[0].size() << std::endl;
          break;
        }
      }

      if(potential_johnson) {
        std::clog << "c\t  found Johnson " << imaginary_domain_cnt+1 << ", ar 2, block_sz " << johnson_block_action[0].size() << std::endl;

        // suggest order according to Johnson
        std::vector<int> order;
        for(int j = 0; j < imaginary_domain_cnt+1; ++j) {
          for (int k = j+1; k < imaginary_domain_cnt + 1; ++k) {
            const std::pair<int, int> p = {k, j};
            order.push_back(lookup_subset[p]);
          }
        }

        for(int j = 0; j < imaginary_domain_cnt+1; ++j) {
          for (int k = 0; k < static_cast<int>(johnson_block_action[j].size()); ++k) {
            order.push_back(johnson_block_action[j][k]);
          }
        }

        for(int j = 1; j < imaginary_domain_cnt+1; ++j) {
          aw.reset();

          for(int k = 0; k < imaginary_domain_cnt+1; ++k) {
            if(k == j || k == j - 1) continue;
            const std::pair<int, int> p_from = {k, j};
            const std::pair<int, int> p_to   = {k, j-1};

            const int subset_from = lookup_subset[p_from];
            const int subset_to = lookup_subset[p_to];

            //models_subset
            aw.write_single_map(subset_from, subset_to);
            aw.write_single_map(subset_to, subset_from);
          }

          for(int k = 0; k < static_cast<int>(johnson_block_action[j].size()); ++k) {
            aw.write_single_map(johnson_block_action[j-1][k], johnson_block_action[j][k]);
            aw.write_single_map(johnson_block_action[j][k], johnson_block_action[j-1][k]);
          }

          potential_johnson = potential_johnson && formula.complete_automorphism(domain_size, aw);
          if(!potential_johnson) break;
          assert(formula.is_automorphism(domain_size, aw));

          sbp.add_lex_leader_predicate(formula, aw, order);
        }

        for(auto v : orbit) {
          const int col = remainder_col.vertex_to_col[v];
          const int col_sz = remainder_col.ptn[col] + 1;
          if(col_sz > 1) dejavu::ir::refinement::individualize_vertex(&remainder_col, v);
        }

        orbit_handled.set(orbits.find_orbit(anchor_vertex));
        orbit_handled.set(orbits.find_orbit(sat_to_graph(-graph_to_sat(anchor_vertex))));

        for(int k = 0; k < static_cast<int>(johnson_block_action[0].size()); ++k) {
          orbit_handled.set(orbits.find_orbit(johnson_block_action[0][k]));
          orbit_handled.set(orbits.find_orbit(sat_to_graph(-graph_to_sat(johnson_block_action[0][k]))));
        }
      }
    }
  }

  /**
   * Produce a double-lex predicate for the given matrix model.
   *
   * @param matrix_model The matrix model.
   */
  void double_lex(cnf& formula, predicate& sbp, std::vector<std::vector<int>>& matrix_model) {
    std::vector<int> order;

    std::vector<int> reorder_rows_row;
    std::vector<int> reorder_rows_orbit;
    for (int k = 0; k < static_cast<int>(matrix_model[0].size()); ++k) {
      reorder_rows_row.push_back(k);
      reorder_rows_orbit.push_back(matrix_model[0][k]);
    }

    std::sort(reorder_rows_row.begin(), reorder_rows_row.end(),[&](int A, int B) -> bool
          {return reorder_rows_orbit[A] < reorder_rows_orbit[B];});

    std::vector<int> reorder_columns_column;
    std::vector<int> reorder_columns_orbit;
    for (int k = 0; k < static_cast<int>(matrix_model.size()); ++k) {
      reorder_columns_column.push_back(k);
      reorder_columns_orbit.push_back(matrix_model[k][reorder_rows_row[0]]);
    }

    std::sort(reorder_columns_column.begin(), reorder_columns_column.end(),[&](int A, int B) -> bool
          {return reorder_columns_orbit[A] < reorder_columns_orbit[B];});


    for(int j = 0; j < static_cast<int>(matrix_model.size()); ++j) {
      for (int k = 0; k < static_cast<int>(matrix_model[0].size()); ++k) {
      assert(matrix_model[j].size() == matrix_model[0].size());
        order.push_back(matrix_model[j][k]);
      }
    }

    for(int j = 1; j < static_cast<int>(matrix_model[0].size()); ++j) {
      aw.reset();
      for(int k = 0; k < static_cast<int>(matrix_model.size()); ++k) {
        aw.write_single_map(matrix_model[k][j-1], matrix_model[k][j]);
        aw.write_single_map(matrix_model[k][j], matrix_model[k][j-1]);
      }
      if(!formula.complete_automorphism(domain_size, aw)) break;
      assert(formula.is_automorphism(domain_size, aw));
      sbp.add_lex_leader_predicate(formula, aw, order, INT32_MAX);
    }

    for(int j = 1; j < static_cast<int>(matrix_model.size()); ++j) {
      aw.reset();
      for(int k = 0; k < static_cast<int>(matrix_model[0].size()); ++k) {
        aw.write_single_map(matrix_model[j-1][k], matrix_model[j][k]);
        aw.write_single_map(matrix_model[j][k], matrix_model[j-1][k]);
      }

      if(!formula.complete_automorphism(domain_size, aw)) break;
      assert(formula.is_automorphism(domain_size, aw));
      sbp.add_lex_leader_predicate(formula, aw, order, INT32_MAX);
    }

    // diagonal maps
    /*const int diag_min = std::min(matrix_model.size(), matrix_model[0].size());
    for(int j = 1; j < diag_min; ++j) {
      aw.reset();

      for(int k = 0; k < matrix_model[0].size(); ++k) {
        if(k == j || k == j-1) continue;
        aw.write_single_map(matrix_model[j-1][k], matrix_model[j][k]);
        aw.write_single_map(matrix_model[j][k], matrix_model[j-1][k]);
      }
      for(int k = 0; k < matrix_model.size(); ++k) {
        if(k == j || k == j-1) continue;
        aw.write_single_map(matrix_model[k][j-1], matrix_model[k][j]);
        aw.write_single_map(matrix_model[k][j], matrix_model[k][j-1]);
      }

      aw.write_single_map(matrix_model[j-1][j-1], matrix_model[j][j]);
      aw.write_single_map(matrix_model[j][j], matrix_model[j-1][j-1]);
      aw.write_single_map(matrix_model[j-1][j], matrix_model[j][j-1]);
      aw.write_single_map(matrix_model[j][j-1], matrix_model[j-1][j]);

      if(!formula.complete_automorphism(domain_size, aw)) {
        std::cout << "fail" << std::endl;
        break;
      }
      assert(formula.is_automorphism(domain_size, aw));
      sbp.add_lex_leader_predicate(aw, order);
    }*/
  }

  /**
   * Checks whether the group contains orbits exhibiting a row-column symmetry action, and adds appropriate breaking
   * constraints to the predicate \p sbp. If the row-column symmetry action is not a natural action on the orbit,
   * the check is also performed on pointwise stabilizers of the orbit. Lastly, a double-lex constraint is produced.
   *
   * @param formula The given CNF formula.
   * @param sbp The predicate to which the double-lex constraint is added.
   */
  void detect_row_column_symmetry(cnf& formula, predicate& sbp, int limit = -1) {
    std::clog << "c\t probe for row-column symmetry (limit=" << limit << ")" << std::endl;

    std::vector<int> in_row; // maps vertices to representative in column of anchor_vertex
    std::vector<int> in_column; // maps vertices to representative in row of anchor_vertex
    in_row.resize(domain_size, -1);
    in_column.resize(domain_size, -1);

    dejavu::markset test_remainders(domain_size);
    dejavu::markset tested(domain_size);

    dejavu::coloring test_col;
    test_col.copy_any(&save_col);
    dejavu::ir::controller ir_controller(&ref, &test_col);

    std::vector<int> row; // row of the anchor vertex
    std::vector<int> column; // column of the anchor vertex
    std::vector<int> orbit;

    for(int i = 0; i < static_cast<int>(orbit_list.size()); ++i) {
      if(limit >= 0 && i >= limit) return;
      if(orbit_handled.get(orbit_list[i] )) continue;
      const int anchor_vertex = orbit_list[i];
      if(tested.get(sat_to_graph(-graph_to_sat(anchor_vertex)))) continue; // skip if we've tested negation
      tested.set(anchor_vertex);
      if(orbit_vertices[anchor_vertex].size() < 6) continue;
      orbit = orbit_vertices[anchor_vertex];

      // anchor vertex is represented by itself
      in_row[anchor_vertex] = anchor_vertex;
      in_column[anchor_vertex] = anchor_vertex;

      // individualize the anchor vertex
      while(ir_controller.get_base_pos() > 0) ir_controller.move_to_parent();
      ir_controller.move_to_child(&save_graph, anchor_vertex);
      //const int init_color = dejavu::ir::refinement::individualize_vertex(&test_col, anchor_vertex);
      //ref.refine_coloring(&save_graph, &test_col, init_color);

      // graph discrete after one individualization, no need to look further
      if(test_col.cells == save_graph.v_size) return;

      // check that there is the correct number of remainders, with plausible size
      int largest_remainder_sz = -1;
      int largest_remainder = -1;
      test_remainders.reset();
      int num_remainders = 0;
      for(auto v : orbit) {
        const int col  = test_col.vertex_to_col[v];
        const int col_sz = test_col.ptn[col] + 1;
        if(!test_remainders.get(col)) {
          ++num_remainders;
          test_remainders.set(col);
        }
        if(col_sz > largest_remainder_sz) {
          largest_remainder_sz = col_sz;
          largest_remainder = col;
        }
      }

      int test_color = -1;
      for(auto v : orbit) {
        const int col  = test_col.vertex_to_col[v];
        const int col_sz = test_col.ptn[col] + 1;
        if(col_sz > 1 && col_sz < largest_remainder_sz) {
          test_color = col;
          break;
        }
      }

      // orbit discrete
      if(test_color == -1) {
        orbit_handled.set(orbit_list[i]);
        continue;
      }

      row.clear();
      column.clear();

      // attempt to find the row and column of the anchor vertex
      row.push_back(anchor_vertex);

      // put vertices in specific remainders into the row and column of the anchor vertex
      for(int j = 0; j < static_cast<int>(orbit.size()); ++j) {
        const int v     = orbit[j];
        const int v_color = test_col.vertex_to_col[v];
        const int v_color_sz = test_col.ptn[v_color] + 1;
        if(v_color == test_color) {
          row.push_back(v);
          in_column[v] = v;
          in_row[v] = anchor_vertex;
        } else if (v_color_sz < largest_remainder_sz) {
          column.push_back(v);
          in_row[v] = v;
          in_column[v] = anchor_vertex;
        }
      }

      // Are the sizes of the row and column plausible compared to the orbit size?
      if(row.size() == 1 || column.size() == 1) {
        continue;
      }
      if(row.size() * column.size() != orbit.size() ||
         largest_remainder_sz != static_cast<int>((row.size()-1)*(column.size()-1)) || num_remainders != 4) {
        // If not, we repeat the check in the pointwise stabilizer of the anchor vertex...
        while(true) {
          // construct a block of vertices in the remainder of the pointwise stabilizer
          std::vector<int> new_orbit;
          for (int j = 0; j < static_cast<int>(orbit.size()); ++j) {
            const int v = orbit[j];
            const int v_color = test_col.vertex_to_col[v];
            // const int v_color_sz = test_col.ptn[v_color] + 1;
            if (v_color == largest_remainder) {
              new_orbit.push_back(v);
            }
          }

          // individualize the new anchor vertex
          int new_anchor_vertex = new_orbit[0];
          //const int init_color2 = dejavu::ir::refinement::individualize_vertex(&test_col, new_anchor_vertex);
          //ref.refine_coloring(&save_graph, &test_col, init_color2);
          ir_controller.move_to_child(&save_graph, new_anchor_vertex);

          // again, check which vertices are in the row and column of the new anchor vertex
          row.clear();
          column.clear();

          row.push_back(new_anchor_vertex);
          largest_remainder_sz = -1;
          largest_remainder = -1;
          for (auto v: new_orbit) {
            const int col = test_col.vertex_to_col[v];
            const int col_sz = test_col.ptn[col] + 1;
            if (col_sz > largest_remainder_sz) {
              largest_remainder_sz = col_sz;
              largest_remainder = col;
            }
          }

          test_color = -1;
          for (auto v: new_orbit) {
            const int col = test_col.vertex_to_col[v];
            const int col_sz = test_col.ptn[col] + 1;
            if (col_sz > 1 && col_sz < largest_remainder_sz) {
              test_color = col;
              break;
            }
          }

          if (test_color == -1) break;

          for (int j = 0; j < static_cast<int>(new_orbit.size()); ++j) {
            const int v = new_orbit[j];
            const int v_color = test_col.vertex_to_col[v];
            const int v_color_sz = test_col.ptn[v_color] + 1;
            if (v_color == test_color) {
              row.push_back(v);
              in_column[v] = v;
              in_row[v] = new_anchor_vertex;
            } else if (v_color_sz < largest_remainder_sz) {
              column.push_back(v);
              in_row[v] = v;
              in_column[v] = new_anchor_vertex;
            }
          }

          // again, check if sizes are plausible
          if(row.size() == 1 || column.size() == 1) break;
          if(row.size() * column.size() != new_orbit.size()) continue;

          // If sizes are plausible, we have a candidate, which we check in the row-routine below.
          check_row_column_candidate(formula, sbp, new_orbit, row, column, in_row, in_column,
                         new_anchor_vertex,
                         largest_remainder_sz);
          break;
        }
        continue;
      }

      //std::clog << "c\t candidate " << row.size() << "x" << column.size() << " matrix model" << std::endl;
      //std::clog << "c\t attempting to order..." << std::endl;

      // If sizes are plausible, we have a candidate, which we check in the routine below.
      const bool confirmed = check_row_column_candidate(formula, sbp, orbit, row, column, in_row, in_column,
                                anchor_vertex, largest_remainder_sz);

      if(confirmed) {
        for(auto v : orbit) {
          const int col = remainder_col.vertex_to_col[v];
          const int col_sz = remainder_col.ptn[col] + 1;
          if(col_sz > 1) dejavu::ir::refinement::individualize_vertex(&remainder_col, v);
        }
      }
    }
  }

  /**
   * Part of the row-column symmetry test. Verifies a candidate matrix, and produces a double-lex constraint if
   * verification is successful.
   *
   * @param formula The given CNF formula.
   * @param sbp The predicate to which the double-lex constraint is added.
   * @param orbit The orbit on which the candidate exists
   * @param row Row of the anchor_vertex
   * @param column Column of the anchor_vertex
   * @param in_row Maps vertices to representative in column of anchor_vertex
   * @param in_column Maps vertices to representative in row of anchor_vertex
   * @param anchor_vertex The anchor vertex
   * @param largest_remainder_sz Size of the largest remainder.
   */
  bool check_row_column_candidate(cnf& formula, predicate& sbp,
                  std::vector<int>& orbit, std::vector<int>& row, std::vector<int>& column,
                  std::vector<int>& in_row, std::vector<int>& in_column,
                  int anchor_vertex, int largest_remainder_sz) {
    bool potential_row_column_symmetry = true;
    row_test_col.copy_any(&save_col);

    // Now we compute the column representatives for all vertices in the given orbit.
    for(auto v : row) {
      if(v == anchor_vertex) continue;
      const int next_anchor = v;
      assert(in_row[v] == anchor_vertex);
      assert(in_column[v] == v);
      //in_column[v] = next_anchor;
      const int next_init_color = dejavu::ir::refinement::individualize_vertex(&row_test_col, next_anchor);
      ref.refine_coloring(&save_graph, &row_test_col, next_init_color);

      largest_remainder_sz = -1;
      for(auto test_v : orbit) {
        const int col  = row_test_col.vertex_to_col[test_v];
        const int col_sz = row_test_col.ptn[col] + 1;
        if(col_sz > largest_remainder_sz) {
          largest_remainder_sz = col_sz;
        }
      }

      int found_candidates = 0;
      for(auto test_v : orbit) {
        const int col  = row_test_col.vertex_to_col[test_v];
        const int col_sz = row_test_col.ptn[col] + 1;
        if(in_column[test_v] == -1 &&
           (col_sz < largest_remainder_sz || largest_remainder_sz == static_cast<int>(column.size() - 1))) {
          ++found_candidates;
          in_column[test_v] = next_anchor;
        }
      }

      if(found_candidates == 0) potential_row_column_symmetry = false;
    }

    if(!potential_row_column_symmetry) return false;

    // Next, we compute the row representatives for all vertices in the given orbit.
    dejavu::coloring column_test_col;
    column_test_col.copy_any(&save_col);
    for(auto v : column) {
      if(v == anchor_vertex) continue;
      const int next_anchor = v;
      assert(in_column[v] == anchor_vertex);
      assert(in_row[v] == v);
      const int next_init_color = dejavu::ir::refinement::individualize_vertex(&column_test_col, next_anchor);
      ref.refine_coloring(&save_graph, &column_test_col, next_init_color);

      largest_remainder_sz = -1;
      for(auto test_v : orbit) {
        const int col  = column_test_col.vertex_to_col[test_v];
        const int col_sz = column_test_col.ptn[col] + 1;
        if(col_sz > largest_remainder_sz) {
          largest_remainder_sz = col_sz;
        }
      }

      int found_candidates = 0;
      for(auto test_v : orbit) {
        const int col  = column_test_col.vertex_to_col[test_v];
        const int col_sz = column_test_col.ptn[col] + 1;
        if(in_row[test_v] == -1 && (col_sz < largest_remainder_sz ||
           largest_remainder_sz == static_cast<int>(row.size() - 1))) {
          ++found_candidates;
          in_row[test_v] = next_anchor;
        }
      }

      if(found_candidates == 0) potential_row_column_symmetry = false;
    }

    if(!potential_row_column_symmetry) return false;

    // verify that this is indeed a row-column symmetry matrix model
    //std::clog << "c\t testing row-column symmetry..." << std::endl;

    // we have found all the representatives, so let's construct the actual matrix
    std::vector<int> row_to_index;
    row_to_index.resize(domain_size);
    std::vector<int> column_to_index;
    column_to_index.resize(domain_size);
    int j = 0;
    for(auto c : column) {
      row_to_index[c] = j;
      ++j;
    }
    j = 0;
    for(auto r : row) {
      column_to_index[r] = j;
      ++j;
    }

    // Plausability test: check that rows and columns are mutually exclusive and have same size
    std::vector<int> row_size;
    row_size.resize(column.size());
    std::vector<int> column_size;
    column_size.resize(row.size());
    for(auto v : orbit) {
      //std::cout << v << " in row  " << in_row[v] << " ind: " << row_to_index[in_row[v]] << std::endl;
      //std::cout << v << " in column  " << in_column[v] << " ind: " << column_to_index[in_column[v]] << std::endl;
      ++row_size[row_to_index[in_row[v]]];
      ++column_size[column_to_index[in_column[v]]];
    }
    for(j = 1; j < static_cast<int>(column.size()); ++j) {
      if(row_size[0] != row_size[j]) {
        // std::clog << "c\t row " << j << "(different size " << row_size[0] << "-" << row_size[j] << std::endl;
        potential_row_column_symmetry = false;
      }
    }
    for(j = 1; j < static_cast<int>(row.size()); ++j) {
      if(column_size[0] != column_size[j]) {
        // std::clog << "c\t column " << j << " different size" << column_size[0] << "-" << column_size[j] << std::endl;
        potential_row_column_symmetry = false;
      }
    }

    if(!potential_row_column_symmetry) return false;

    // let's put everything into a datastrcutre that looks like a matrix
    std::vector<std::vector<int>> matrix_model;
    matrix_model.resize(column.size());
    for(int i = 0; i < static_cast<int>(matrix_model.size()); ++i)
      matrix_model[i].resize(row.size());
    for(auto v : orbit) matrix_model[row_to_index[in_row[v]]][column_to_index[in_column[v]]] = v;

    //for(auto v : orbit) assert(matrix_model[row_to_index[in_row[v]]][column_to_index[in_column[v]]] == v);
    //for(int i = 0; i < static_cast<int>(matrix_model.size()); ++i) {
    //  for(int j = 0; j < static_cast<int>(matrix_model[i].size()); ++j) {
    //    const int test_v = matrix_model[i][j];
    //    assert(row_to_index[in_row[test_v]] == i);
    //    assert(column_to_index[in_column[test_v]] == j);
    //  }
    //}

    dejavu::ds::markset touched_orig_color(domain_size);
    touched_orig_color.reset();



    /*
    std::vector<std::vector<int>> orbit_row;
    for(int j = 0; j < domain_size; ++j) {
      orbit_row.emplace_back();
    }
    std::vector<std::vector<int>> potential_blocks;
    dejavu::ir::controller ir_controller(&ref, &save_col);

    for(auto v : orbit) {
      ir_controller.move_to_child(&save_graph, v);
      touched_orig_color.reset();
      for(int single_pos = 0; single_pos < ir_controller.singletons.size(); ++single_pos) {
        orbit_row[v].push_back(ir_controller.singletons[single_pos]);
      }
      ir_controller.move_to_parent();
    }*/

    // check that transposition between row 1 and row j is a symmetry
    for(j = 1; j < static_cast<int>(column.size()); ++j) {
      aw.reset();
      for(int k = 0; k < static_cast<int>(row.size()); ++k) {
        aw.write_single_map(matrix_model[0][k], matrix_model[j][k]);
        aw.write_single_map(matrix_model[j][k], matrix_model[0][k]);

        /*
         for(int l = 0; l < orbit_row[matrix_model[0][k]].size(); ++l) {
          const int from = orbit_row[matrix_model[0][k]][l];
          const int to = orbit_row[matrix_model[j][k]][l];
          aw.write_single_map(from, to);
          aw.write_single_map(to, from);
        }*/
      }

      potential_row_column_symmetry = potential_row_column_symmetry &&
                      formula.complete_automorphism(domain_size, aw);
      if(!potential_row_column_symmetry || !formula.is_automorphism(domain_size, aw)) {
        //std::clog << "c\t not a row transposition (" << 0 << ", " << j << ")" << std::endl;
        potential_row_column_symmetry = false;
        break;
      }
    }

    if(!potential_row_column_symmetry) return false;

    // check that transposition between column 1 and column j is a symmetry
    for(j = 1; j < static_cast<int>(row.size()); ++j) {
      aw.reset();
      for(int k = 0; k < static_cast<int>(column.size()); ++k) {
        aw.write_single_map(matrix_model[k][0], matrix_model[k][j]);
        aw.write_single_map(matrix_model[k][j], matrix_model[k][0]);

        /*for(int l = 0; l < orbit_row[matrix_model[k][0]].size(); ++l) {
          const int from = orbit_row[matrix_model[k][0]][l];
          const int to = orbit_row[matrix_model[k][j]][l];
          aw.write_single_map(from, to);
          aw.write_single_map(to, from);
        }*/
      }

      potential_row_column_symmetry = potential_row_column_symmetry &&
                      formula.complete_automorphism(domain_size, aw);
      if(!potential_row_column_symmetry || !formula.is_automorphism(domain_size, aw)) {
        //std::clog << "c\t not a column transposition (" << 0 << ", " << j << ")" << std::endl;
        potential_row_column_symmetry = false;
        break;
      }
    }

    if(!potential_row_column_symmetry) return false;

    // matrix is confirmed to be row-column symmetry, now we write a double-lex predicate
    std::clog << "c\t  found row-column " << row.size() << "x" << column.size() << std::endl;

    double_lex(formula, sbp, matrix_model);
    orbit_handled.set(orbits.find_orbit(anchor_vertex));
    orbit_handled.set(orbits.find_orbit(sat_to_graph(-graph_to_sat(anchor_vertex))));

    return true;
  }

  void put_in_own_color(dejavu::coloring& col, int* arr, int arr_sz) {
    const int vtest = arr[0];
    const int old_col = col.vertex_to_col[vtest];
    const int old_col_sz = (col.ptn[old_col] + 1);
    const int new_col_sz = arr_sz;

    const int new_col = old_col + old_col_sz - new_col_sz;
    col.ptn[old_col] -= new_col_sz;
    col.ptn[new_col]  = new_col_sz - 1;

    for(int i = 0; i < arr_sz; ++i) {
      const int v1 = arr[i];

      const int v1_lab_pos = col.vertex_to_lab[v1];
      const int v1_new_lab_pos = new_col;
      const int v1_vertex_at_lab = col.lab[v1_new_lab_pos];

      col.lab[v1_lab_pos] = v1_vertex_at_lab;
      col.vertex_to_lab[v1_vertex_at_lab] = v1_lab_pos;
      col.lab[v1_new_lab_pos] = v1;
      col.vertex_to_lab[v1] = v1_new_lab_pos;

      col.vertex_to_col[v1] = new_col;
    }
  }

  void detect_row_symmetry_orbit(cnf& formula, predicate& sbp, std::vector<int>& entire_orbit,
                   dejavu::ir::controller& ir_controller, std::vector<int>* recurse_order = nullptr,
                       std::vector<int>* individualize = nullptr,
                      std::vector<int>* in_row = nullptr,
                       std::vector<int>* row_pos = nullptr) {
    bool potential_row_symmetry = true;

    if(entire_orbit.size() <= 1) return;

    int singleton_start = 0;
    int touch_start = 0;
    if(individualize) {
      for(auto v : *individualize) {
        if(ir_controller.c->ptn[ir_controller.c->vertex_to_col[v]] > 0)
          ir_controller.move_to_child(&save_graph, v);
      }
      singleton_start = ir_controller.singletons.size();
      touch_start = ir_controller.touched_color_list.size();
    }

    // orbit reduction test
    const int anchor_vertex = entire_orbit[0];
    ir_controller.move_to_child(&save_graph, anchor_vertex);
    bool reduce_orbit = false;
    int  reduce_orbit_to_color = -1;
    int  reduce_orbit_to_color_sz = -1;
    for (int k = 1; k < static_cast<int>(entire_orbit.size()); ++k) {
      const int remainder_orbit = ir_controller.c->ptn[ir_controller.c->vertex_to_col[entire_orbit[k]]] + 1;
      if (remainder_orbit < static_cast<int>(entire_orbit.size() - 1)) {
        reduce_orbit = true;
        if(remainder_orbit > reduce_orbit_to_color_sz) {
          reduce_orbit_to_color = ir_controller.c->vertex_to_col[entire_orbit[k]];
          reduce_orbit_to_color_sz = remainder_orbit;
        }
      } else {
        break;
      }
    }

    // skip if anchor_vertex was already considered with reduced orbit size
    //if(reduce_orbit && reduce_orbit_to_color_sz + 1 == row_touched_size[anchor_vertex]) {
      //return;
    //}

    // skip if orbit too small
    if(reduce_orbit && reduce_orbit_to_color_sz + 1 == 2) return;

    std::vector<int> orbit;
    if(reduce_orbit) {
      orbit.push_back(entire_orbit[0]);
      for(int k = reduce_orbit_to_color; k < reduce_orbit_to_color +
                           ir_controller.c->ptn[reduce_orbit_to_color] + 1; ++k) {
        orbit.push_back(ir_controller.c->lab[k]);
      }
      ir_controller.move_to_parent();
    } else {
      ir_controller.move_to_parent();
      orbit = entire_orbit;
    }

    std::vector<std::vector<int>> orbit_row;
    for (int j = 0; j < static_cast<int>(orbit.size()); ++j) {
      orbit_row.emplace_back();
    }

    dejavu::ds::markset orbit_test(domain_size);
    dejavu::ds::markset touched_orig_color(domain_size);
    std::vector<std::vector<int>> potential_blocks;

    dejavu::ds::markset rows_are_unique(domain_size);

    for(int j = 0; j < static_cast<int>(orbit.size()) && potential_row_symmetry; ++j) {
      ir_controller.move_to_child(&save_graph, orbit[j]);
      // this can fire :(
      // assert(ir_controller.c->vertex_to_col[orbit[j]] != save_col.vertex_to_col[orbit[j]]);

      if (j == 0) {
        const int remainder_orbit = ir_controller.c->ptn[ir_controller.c->vertex_to_col[orbit[1]]] + 1;
        if (remainder_orbit < static_cast<int>(orbit.size()) - 1) {
          std::clog << "c remainder orbit too small " << remainder_orbit << std::endl;
          ir_controller.move_to_parent();
          potential_row_symmetry = false;
          break;
        }
      }

      orbit_test.reset();
      for (int singleton_pos = singleton_start;
         singleton_pos < static_cast<int>(ir_controller.singletons.size()); ++singleton_pos) {
        const int sing = ir_controller.singletons[singleton_pos];
        if(sing < domain_size) {
          if(rows_are_unique.get(sing)) {
            potential_row_symmetry = false;
            break;
          }
          orbit_row[j].push_back(sing);
          rows_are_unique.set(sing);
          orbit_test.set(orbits.find_orbit(ir_controller.singletons[singleton_pos]));
          if(recurse_order == nullptr && individualize == nullptr) {
            row_touched_size[orbits.find_orbit(ir_controller.singletons[singleton_pos])] =
                static_cast<int>(orbit.size());
          }
        }
      }

      touched_orig_color.reset();
      for(int touch_pos = touch_start; touch_pos < ir_controller.touched_color_list.size(); ++touch_pos) {
        if(ir_controller.c->ptn[ir_controller.touched_color_list[touch_pos]] >= 1 &&
           ir_controller.c->lab[ir_controller.touched_color_list[touch_pos]] < domain_size) {
          const int col = ir_controller.touched_color_list[touch_pos];
          const int test_vertex = ir_controller.c->lab[col];
          const int orig_color = save_col.vertex_to_col[test_vertex];
          if(!touched_orig_color.get(orig_color)) {
            touched_orig_color.set(orig_color);
            const int orig_color_sz = save_col.ptn[orig_color] + 1;
            for (int k = orig_color; k < orig_color + save_col.ptn[orig_color] + 1;) {
              const int col_sz_now = ir_controller.c->ptn[k] + 1;
              if(col_sz_now > 1 && col_sz_now * static_cast<int>(orbit.size()) == orig_color_sz) {
                potential_blocks.emplace_back();
                for(int l = k; l < k + col_sz_now; ++l) {
                  if(rows_are_unique.get(ir_controller.c->lab[l])) {
                    potential_row_symmetry = false;
                    break;
                  }
                  orbit_row[j].push_back(ir_controller.c->lab[l]);
                  rows_are_unique.set(ir_controller.c->lab[l]);
                  potential_blocks.back().push_back(ir_controller.c->lab[l]);
                }
                break;
              }
              k += col_sz_now;
            }
          }
        }
      }

      ir_controller.move_to_parent();

      // special code for symmetric action
      if(j == 0 && orbit_row[j].size() == 2 && orbit_row[j][0] == orbit[j] &&
         graph_to_sat(orbit_row[j][1]) == -graph_to_sat(orbit[j]) && potential_blocks.empty()) {
        for(int j = 1; j < static_cast<int>(orbit.size()) && potential_row_symmetry; ++j) {
          orbit_row[j] = {orbit[j], sat_to_graph(-graph_to_sat(orbit[j]))};
        }

        break;
      }
    }

    rows_are_unique.reset();
    for(int j = 0; j < static_cast<int>(orbit.size()) && potential_row_symmetry; ++j) {
      for (int k = 0; k < static_cast<int>(orbit_row[j].size()); ++k) {
        if(rows_are_unique.get(orbit_row[j][k])) {
          potential_row_symmetry = false;
          break;
        }
        rows_are_unique.set(orbit_row[j][k]);
      }
    }

    if(!potential_row_symmetry) return;

    for(int j = 0; j < static_cast<int>(orbit.size()); ++j) assert(orbit_row[j][0] == orbit[j]);

    // recursively test & order blocks for row symmetry, in order to determine order
    if(potential_blocks.size() > 0){
      std::clog << "c\t recursing " << potential_blocks.size() << " blocks of candidate " << orbit.size() << "x"
            << orbit_row[0].size() << "r" << std::endl;
      std::vector<int> in_row;
      in_row.resize(domain_size);
      dejavu::markset unique_block_size(domain_size);

      for (auto potential_block: potential_blocks) {
        if (!unique_block_size.get(potential_block.size())) {
          unique_block_size.set(potential_block.size());
          detect_row_symmetry_orbit(formula, sbp, potential_block, ir_controller, nullptr, &orbit, &in_row);
          if (ir_controller.get_base_pos() > 0) ir_controller.move_to_parent();
        }
      }

      for(int j = 0; j < static_cast<int>(orbit.size()); ++j) {
        std::sort(orbit_row[j].begin(), orbit_row[j].end(),[&](int A, int B) -> bool
        {return (save_col.vertex_to_col[A] < save_col.vertex_to_col[B]) ||
            ((save_col.vertex_to_col[A] == save_col.vertex_to_col[B]) && in_row[A] < in_row[B]);});
      }

    }

    // check that transposition between row 1 and row j is a symmetry
    for(int j = 1; j < static_cast<int>(orbit.size()); ++j) {
      aw.reset();
      for(int k = 0; k < static_cast<int>(orbit_row[j].size()); ++k) {
        assert(orbits.are_in_same_orbit(orbit_row[0][k], orbit_row[j][k]));
        aw.write_single_map(orbit_row[0][k], orbit_row[j][k]);
        aw.write_single_map(orbit_row[j][k], orbit_row[0][k]);
      }
      potential_row_symmetry = potential_row_symmetry && formula.complete_automorphism(domain_size, aw);
      if(!potential_row_symmetry || !formula.is_automorphism(domain_size, aw)) {
        potential_row_symmetry = false;
        break;
      }
    }

    if(!potential_row_symmetry) return;

    // matrix is confirmed to be row-column symmetry, now we write a double-lex predicate
    std::clog << "c\t  found row " << orbit.size() << "x" << orbit_row[0].size() << (reduce_orbit?" (red. orbit)":"") << ", generating row predicate" << std::endl;

    if(recurse_order == nullptr && individualize == nullptr && !reduce_orbit) {
      for(auto v : orbit) {
        const int col = remainder_col.vertex_to_col[v];
        const int col_sz = remainder_col.ptn[col] + 1;
        if(col_sz > 1) dejavu::ir::refinement::individualize_vertex(&remainder_col, v);
      }
    } else if(recurse_order == nullptr) {
      dejavu::ds::workspace scratch(domain_size);
      dejavu::ds::work_set_int color_counter(domain_size);
      dejavu::ds::worklist color_list(domain_size);

      for (int j = 0; j < static_cast<int>(orbit.size()); ++j) {
        color_counter.reset();
        color_list.reset();

        for (int k = 0; k < static_cast<int>(orbit_row[j].size()); ++k) {
          const int col = remainder_col.vertex_to_col[orbit_row[j][k]];
          if(color_counter.get(col) == -1) {
            color_list.push_back(col);
          }
          color_counter.inc(col);
          scratch[col + color_counter.get(col)] = orbit_row[j][k];
        }

        for(int k = 0; k < static_cast<int>(color_list.size()); ++k) {
          const int col = color_list[k];
          put_in_own_color(remainder_col, scratch.get_array() + col, color_counter.get(col) + 1);
        }
      }
    }

    std::vector<int> order;
    if(recurse_order == nullptr) {
      std::vector<int> reorder_rows_row;
      std::vector<int> reorder_rows_orbit;
      for (int k = 0; k < static_cast<int>(orbit_row[0].size()); ++k) {
        reorder_rows_row.push_back(k);
        reorder_rows_orbit.push_back(orbit_row[0][k]);
      }

      std::vector<int> reorder_orbit;
      std::vector<int> reorder_orbit_j;
      for (int k = 0; k < static_cast<int>(orbit.size()); ++k) {
        reorder_orbit.push_back(k);
        reorder_orbit_j.push_back(orbit_row[k][reorder_rows_row[0]]);
      }

      std::sort(reorder_rows_row.begin(), reorder_rows_row.end(),[&](int A, int B) -> bool {return reorder_rows_orbit[A] < reorder_rows_orbit[B];});
      std::sort(reorder_orbit.begin(), reorder_orbit.end(),[&](int A, int B) -> bool {return reorder_orbit_j[A] < reorder_orbit_j[B];});
      for (int j = 0; j < static_cast<int>(orbit.size()); ++j) {
        for (int k = 0; k < static_cast<int>(orbit_row[0].size()); ++k) {
          order.push_back(orbit_row[reorder_orbit[j]][reorder_rows_row[k]]);
        }
      }
    } else {
      order = *recurse_order;
    }

    for(int j = 1; j < static_cast<int>(orbit.size()); ++j) {
        aw.reset();
        for (int k = 0; k < static_cast<int>(orbit_row[j].size()); ++k) {
          assert(orbits.are_in_same_orbit(orbit_row[j-1][k], orbit_row[j][k]));
          aw.write_single_map(orbit_row[j-1][k], orbit_row[j][k]);
          aw.write_single_map(orbit_row[j][k], orbit_row[j-1][k]);
        }
        if(!formula.complete_automorphism(domain_size, aw)) break;
        assert(formula.is_automorphism(domain_size, aw));
        sbp.add_lex_leader_predicate(formula, aw, order, INT32_MAX);
      //}
    }

    /*// test if "blocks" can be handled recursively, too
    if(potential_blocks.size() > 0) {
      std::clog << "c\t recursing " << potential_blocks.size() << " blocks of " << orbit.size() << "x" <<
            orbit_row[0].size() << "r" << std::endl;

      dejavu::markset unique_block_size(domain_size);
    
      for (auto potential_block: potential_blocks) {
        if (!unique_block_size.get(potential_block.size())) {
          unique_block_size.set(potential_block.size());
          detect_row_symmetry_orbit(formula, sbp, potential_block, ir_controller, &order, &orbit);
          if (ir_controller.get_base_pos() > 0) ir_controller.move_to_parent();
        }
      }
    }*/

    for (int j = 0; j < static_cast<int>(orbit.size()); ++j) {
      for (int k = 0; k < static_cast<int>(orbit_row[j].size()); ++k) {
        if(row_pos != nullptr) (*row_pos)[orbit_row[j][k]] = k;
        if(in_row != nullptr) (*in_row)[orbit_row[j][k]]  = j;
      }
    }

    orbit_handled.set(anchor_vertex);
    orbit_handled.set(orbits.find_orbit(sat_to_graph(-graph_to_sat(anchor_vertex))));

    for(int j = 0; j < static_cast<int>(orbit_row[0].size()); ++j) {
      const int repr = orbits.find_orbit(orbit_row[0][j]);
      orbit_handled.set(repr);
      orbit_handled.set(orbits.find_orbit(sat_to_graph(-graph_to_sat(repr))));
    }
  }

  /**
   * Checks whether the group contains orbits exhibiting a row symmetry action, and adds appropriate breaking
   * constraints to the predicate \p sbp. If the row symmetry action is not a natural action on the orbit,
   * the check is also performed on pointwise stabilizers of the orbit. On further orbits, the row symmetry action
   * is also accepted on blocks of the orbit. Finally, it is recursively checked whether these blocks admit a further
   * row symmetry action.
   *
   * @param formula The given CNF formula.
   * @param sbp The predicate to which the double-lex constraint is added.
   */
  void detect_row_symmetry(cnf& formula, predicate& sbp, int limit = -1, std::vector<int>* order_prev = nullptr) {
    std::clog << "c\t probe for row symmetry (limit=" << limit << ")" << std::endl;

    dejavu::coloring test_col;
    test_col.copy_any(&save_col);
    dejavu::ir::controller ir_controller(&ref, &test_col);

    row_touched_size.resize(domain_size);

    int i = 0;
    for(int anchor_vertex : orbit_list) {
      if(limit >= 0 && i >= limit) return;
      ++i;
      if(orbit_handled.get(anchor_vertex)) continue;
      if(row_touched_size[anchor_vertex] == static_cast<int>(orbit_vertices[anchor_vertex].size())) continue;
      std::vector<int> entire_orbit = orbit_vertices[anchor_vertex];
      detect_row_symmetry_orbit(formula, sbp, entire_orbit, ir_controller);
    }
  }

  std::vector<std::vector<int>> vertex_to_generators;

  void create_generator_used_list(predicate& sbp) {
    vertex_to_generators.resize(domain_size);
    for(int j = 0; j < static_cast<int>(generators.size()); ++j) {
      aw.reset();
      generators[j]->load(aw);

      for(int k = 0; k < aw.nsupp(); ++k) {
        vertex_to_generators[aw.supp()[k]].push_back(j);
      }
    }
  }

  void create_generator_used_list_marked_gens(predicate& sbp, dejavu::ds::markset& marked_gens) {
    vertex_to_generators.clear();
    vertex_to_generators.resize(domain_size);
    for(int j = 0; j < static_cast<int>(generators.size()); ++j) {
      if(marked_gens.get(j)) continue;
      aw.reset();
      generators[j]->load(aw);

      for(int k = 0; k < aw.nsupp(); ++k) {
        vertex_to_generators[aw.supp()[k]].push_back(j);
      }
    }
  }

  bool add_unmarked_generators_to_orbit(dejavu::ds::markset& marked_gens, dejavu::groups::orbit& ps_orbits) {
    int added_gens = 0;
    for(int j = 0; j < static_cast<int>(generators.size()); ++j) {
      if(!marked_gens.get(j)) {
        generators[j]->load(aw);
        ps_orbits.add_automorphism_to_orbit(aw);
        aw.reset();
        added_gens += 1;
      }
    }
    return added_gens > 0;
  }

  int find_non_trivial_orbit(dejavu::groups::orbit& ps_orbits, std::vector<int>& unordered_variables) {
    int i;
    for(i = unordered_variables.size()-1; i >= 0; --i) {
      const int v = unordered_variables[i];
      if(ps_orbits.orbit_size(v) > 1) {
        unordered_variables.resize(i);
        return v;
      }
    }
    unordered_variables.clear();
    return -1;
  }

  void update_score_with_used_list(std::vector<int>& vertex_score, int remove_gen) {
    aw.reset();
    generators[remove_gen]->load(aw);

    for(int k = 0; k < aw.nsupp(); ++k) vertex_score[aw.supp()[k]] -= 1;
  }

  int add_binary_clauses_no_schreier(cnf& formula, predicate& sbp, int depth_limit = 128) {
    create_generator_used_list(sbp);
    dejavu::ds::markset fixed_generator(generators.size());
    dejavu::groups::orbit ps_orbits(domain_size);

    std::vector<int> vertex_score;
    vertex_score.resize(domain_size);
    std::vector<int> unordered_variables;
    for(int i = 0; i < domain_size; i += 2) {
      vertex_score[i] = vertex_to_generators[i].size();
      if(!sbp.is_ordered(i)) unordered_variables.push_back(i);
    }

    int binary_clauses = 0;
    int depth = 0;

    while(add_unmarked_generators_to_orbit(fixed_generator, ps_orbits)) {
      if(depth_limit >= 0 && depth > depth_limit) break;
      ++depth;
      std::sort(unordered_variables.begin(), unordered_variables.end(),[&](int A, int B) -> bool
        {
        return (ps_orbits.orbit_size(A) < ps_orbits.orbit_size(B)) || (
            (ps_orbits.orbit_size(A) ==  ps_orbits.orbit_size(B)) &&
            (vertex_score[A] > vertex_score[B])
            );
        });

      // find any non-trivial orbit with unfixed literal
      const int v = find_non_trivial_orbit(ps_orbits, unordered_variables);
      if(v == -1) break;

      // create binary clauses for orbit
      assert(!sbp.is_ordered(v));
      // we add v to the prefix of our global order
      sbp.add_to_global_order(v, true);
      for(int i = 0; i < domain_size; i += 1) {
        if (ps_orbits.are_in_same_orbit(v, i) && v != i) {
          ++binary_clauses;
          sbp.add_binary_clause(graph_to_sat(v), graph_to_sat(i));
        }
      }

      // mark all generators containing v (or the negation of v)
      for(auto gen : vertex_to_generators[v]) {
        if(!fixed_generator.get(gen)) update_score_with_used_list(vertex_score, gen);
        fixed_generator.set(gen);
      }
      for(auto gen : vertex_to_generators[sat_to_graph(-graph_to_sat(v))]) {
        if(!fixed_generator.get(gen)) update_score_with_used_list(vertex_score, gen);
        fixed_generator.set(gen);
      }
      ps_orbits.reset();
    }

    return binary_clauses;
  }

  bool generators_intersect(dejavu::groups::automorphism_workspace& aw1,
                dejavu::groups::automorphism_workspace& aw2) {
    store_helper.reset();
    for(int i = 0; i < aw1.nsupp(); ++i) {
      store_helper.set(aw1.supp()[i]);
    }
    for(int i = 0; i < aw2.nsupp(); ++i) {
      if(store_helper.get(aw2.supp()[i])) {
        return true;
      }
    }
    return false;
  }

  int generator_intersection(dejavu::groups::automorphism_workspace& aw1,
                             dejavu::groups::automorphism_workspace& aw2) {
    int intersection = 0;
    store_helper.reset();
    for(int i = 0; i < aw1.nsupp(); ++i) {
      store_helper.set(aw1.supp()[i]);
    }
    for(int i = 0; i < aw2.nsupp(); ++i) {
      intersection += store_helper.get(aw2.supp()[i]);
    }
    return intersection;
  }

  void inverse_of(dejavu::groups::automorphism_workspace& aw_from,
          dejavu::groups::automorphism_workspace& aw_to) {
    aw_to.reset();
    for(int i = 0; i < aw_from.nsupp(); ++i) {
      const int j  = aw_from.supp()[i];
      const int to_j = aw_from[j];
      aw_to.write_single_map(to_j, j);
    }
  }

  std::pair<int, int> generator_cycle_analysis(dejavu::groups::automorphism_workspace& automorphism,
                                dejavu::ds::markset& helper) {
    int max_cycle_size = INT32_MIN;
    int min_cycle_size = INT32_MAX;

    helper.reset();
    for (int i = 0; i < automorphism.nsupp(); ++i) {
      const int j = automorphism.supp()[i];
      if (automorphism.p()[j] == j) continue; // no need to consider trivially mapped vertices
      if (helper.get(j)) continue; // we have already considered cycle of this vertex

      int cycle_length = 1;
      helper.set(j); // mark that we have already considered the vertex

      // move along the cycle of j, until we come back to j
      int map_j = automorphism.p()[j];
      dej_assert(map_j != j);
      while (!helper.get(map_j)) {
        ++cycle_length;
        helper.set(map_j); // mark that we have already considered the vertex
        map_j = automorphism.p()[map_j];
      }

      if(cycle_length > max_cycle_size) max_cycle_size = cycle_length;
      if(cycle_length < min_cycle_size) min_cycle_size = cycle_length;
      // finally we reach j, the vertex we started with
      dej_assert(map_j == j);
    }

    return {min_cycle_size, max_cycle_size};
  }

  struct comp_pair_second {
    constexpr bool operator()(std::pair<int, int> const& a, std::pair<int, int> const& b)
    const noexcept
    {
      return a.second < b.second;
    }
  };

  std::pair<int, double> optimize_support(dejavu::groups::automorphism_workspace& aw2,
              dejavu::random_source& rng,
              int optimize_passes, int power_limit, int generator_limit) {
    int shrinks = 0;
    double last_avg_support  = INT32_MAX;
    int  last_best_support = INT32_MAX;
    int  best_support_stable_rounds = 0;
    int  it_score  = 8;
    int  loads1  = 0;
    int  loads2  = 0;
    int  mults   = 0;

    constexpr int support_opt_hard_limit = 4;

    std::vector<int> generator_to_support;
    std::vector<int> generator_to_score;
    generator_to_support.resize(generators.size());
    generator_to_score.resize(generators.size());

    std::vector<int> support_to_number_of_generators;

    for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
      aw.reset();
      generators[j]->load(aw);
      generator_to_support[j] = aw.nsupp();
      generator_to_score[j]   = 0;
    }

    int best_support = INT32_MAX;

    for(int k = 0; k < optimize_passes; ++k) {
      double total_support = 0;
      //int best_j     = -1;

      int worst_j     = -1;
      int worst_support = INT32_MIN;


      for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
        const int support = generator_to_support[j];

        if (support > 0 && support < best_support) {
          best_support = support;
          //best_j     = j;
        }

        if (support > 0 && support > worst_support && j > generator_limit) {
          worst_support = support;
          worst_j = j;
        }

        total_support += support;
        if (support <= last_best_support + 4 && best_support_stable_rounds > 12) continue;
        if (support <= support_opt_hard_limit) continue;

        aw.reset();
        generators[j]->load(aw);
        ++loads1;

        bool continue_opt = true;

        while(continue_opt) {
          continue_opt = false;
          int j2 = rng() % generators.size();
          while(j == j2 && generators.size() > 20) {
            j2 = rng() % generators.size();
            break;
          }
          if(j == j2) continue;

          aw2.reset();
          generators[j2]->load(aw2);
          ++loads2;

          const int intersection = generator_intersection(aw, aw2);
          if(intersection == 0) break;
          if(aw.nsupp() + aw2.nsupp() - 2*intersection > aw.nsupp()) break;

          //if (!generators_intersect(aw, aw2)) break;

          bool smaller = true;
          while (smaller && aw.nsupp() > 0) {
            int pwr2 = 1;

            const auto [min_cycle, max_cycle] = generator_cycle_analysis(aw2, store_helper);

            if(min_cycle == max_cycle && min_cycle >= 2) {
              pwr2 = 1 + (rng() % (min_cycle-1));
            } else {
              pwr2 = 1 + (rng() % (std::min(power_limit, max_cycle)));
            }
            int pre_support = aw.nsupp();

            aw.apply(aw2, pwr2);

            ++mults;
            smaller = (aw.nsupp() < pre_support);
            continue_opt = continue_opt || (smaller && aw.nsupp() > 0);
            if (smaller && aw.nsupp() > 0) {
              shrinks += 1;
              generators[j]->store(domain_size, aw, store_helper);
              generator_to_support[j] = aw.nsupp();
            }
          }
        }
      }

      if(last_best_support == best_support) {
        best_support_stable_rounds += 1;
      } else {
        best_support_stable_rounds = 0;
        last_best_support = best_support;
      }

      double avg_support = total_support / generators.size();
      it_score -= 1;

      bool rem_gen = false;
      if(avg_support < last_avg_support - 0.01 || avg_support > last_avg_support + 0.01 ) {
        it_score = 8;
      } else if(worst_j > generator_limit && worst_support > avg_support*2) { // best_support*1.125
          generators[worst_j]       = generators.back();
          generator_to_support[worst_j] = generator_to_support[generators.size()-1];
          generators.resize(generators.size()-1);
          generator_to_support.resize(generator_to_support.size()-1);
          rem_gen = true;
      }

      if(k % 16 == 15) {
        std::clog << "c\t " << "opt it=" << k << ", l=" << loads1+loads2 << ", m=" << mults << ", opt=" << shrinks << ", avg=" << ((int)round(avg_support)) << ", b=" << best_support << ", gens=" << generators.size() <<
              std::endl;
      }

      // reached best support on average up to a constant -- let's stop
      if(avg_support-2 > last_avg_support && rem_gen) break;
      if(avg_support <= best_support) break;
      if(it_score < 0) break;
      last_avg_support = avg_support;
    }

    return {best_support, last_avg_support};
  }

  void optimize_generators(int optimize_passes, int addition_limit, int conjugate_limit, bool reopt,
               int power_limit = 5) {

    if(static_cast<int>(generators.size()) < 3) return;

    const int original_generators = static_cast<int>(generators.size());
    dejavu::groups::automorphism_workspace aw2(domain_size);
    dejavu::groups::automorphism_workspace aw3(domain_size);
    int additions = 0;

    constexpr int min_group_exp = 3;

    const dejavu::big_number grp_size = group_size();
    if(grp_size.exponent < min_group_exp) return;

    dejavu::random_source rng(false, 0);

    // randomize generators
    /*for(int k = 0; k < 3; ++k) {
      for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
        int other_j = rng() % generators.size();

        aw.reset();
        generators[j]->load(aw);

        aw2.reset();
        generators[other_j]->load(aw2);

        if(j == other_j) continue;
        if(!generators_intersect(aw, aw2)) continue;

        const int pwr = 1 + (rng() % power_limit);
        aw.apply(aw2, pwr);
        if (aw.nsupp() > 0) {
          replacements += 1;
          generators[j]->store(domain_size, aw, store_helper);
        }
      }
    }*/

    // optimize generators
    optimize_support(aw2, rng, optimize_passes, power_limit, original_generators);


    // add generators by conjugation

    // find generator with best support
    std::vector<int> good_support_gens;
    int best_support   = INT32_MAX;
    for (int j = 0; j < static_cast<int>(generators.size()); ++j) {
      aw.reset();
      generators[j]->load(aw);
      if(aw.nsupp() < best_support) {
        good_support_gens.clear();
        best_support = aw.nsupp();
        good_support_gens.push_back(j);
      } else if (aw.nsupp() == best_support){
        good_support_gens.push_back(j);
      }
    }

    // add generators random
    for(int k = 0; k < 1 && additions < addition_limit; ++k) {
      int limit = static_cast<int>(generators.size());
      for (int l = 0; l < limit; ++l) {
        const int j = rng() % generators.size();
        aw.reset();
        generators[j]->load(aw);

        const int other_j = rng() % generators.size();
        aw2.reset();
        generators[other_j]->load(aw2);
        if (!generators_intersect(aw, aw2)) continue;
        const int pwr = 1 + (rng() % power_limit);
        aw.apply(aw2, pwr);

        if (aw.nsupp() > 0 && additions < addition_limit) {
          additions += 1;
          generators.push_back(new dejavu::groups::stored_automorphism());
          generators.back()->store(domain_size, aw, store_helper);
        }
      }
      std::clog << "c\t ran it=" << k << ", +gens=" << additions << " " << std::endl;
    }

    // add generators by conjugation
    additions = 0;
    int limit = static_cast<int>(generators.size());
    for (int l = 0; l < conjugate_limit; ++l) {
      // give up early if not successful
      if(l == 32 && additions == 0) break;

      const int conj_j = good_support_gens[rng() % good_support_gens.size()];

      aw.reset();
      generators[conj_j]->load(aw);
      //std::clog << "from:" << std::endl;
      //print_automorphism(domain_size, aw.p(), aw.nsupp(), aw.supp());

      const int j = rng() % limit;
      if(j == conj_j) continue;

      aw2.reset();
      generators[j]->load(aw2);
      if(!generators_intersect(aw2, aw)) continue;

      // make a random element
      constexpr int word_length = 9;
      for(int k = 0; k < word_length; ++k) {
        aw3.reset();
        const int h = rng() % limit;
        const int pwr = 1 + (rng() % power_limit);
        if(h == conj_j) continue;
        generators[h]->load(aw3);
        aw2.apply(aw3, pwr);
      }

      // conjugation
      aw3.reset();
      inverse_of(aw2, aw3);
      aw3.apply(aw);
      aw3.apply(aw2);

      // check if generator actually changed
      bool equal = true;
      for(int i = 0; i < aw.nsupp() && equal; ++i) {
        const int v = aw.supp()[i];
        equal = aw.p()[v] == aw3.p()[v];
      }

      if(equal) continue;

      additions += 1;
      generators.push_back(new dejavu::groups::stored_automorphism());
      generators.back()->store(domain_size, aw3, store_helper);
      //std::clog << "c\t con " << j << "^-1 " << conj_j << " " << j << " support " << aw.nsupp() << std::endl;
    }


    std::clog << "c\t con " << "best_support=" << best_support << ", best_gens=" << good_support_gens.size() << ", +gens="
           << additions << std::endl;

    // re-optimize generators
    if(reopt) optimize_support(aw2, rng, optimize_passes, power_limit, original_generators);
  }

  int add_lex_leader_for_generators(cnf& formula, predicate& sbp, int depth = 50) {
    int constraints_added = 0;
    //for(int j = 0; j < static_cast<int>(generators.size()); ++j) {

    // we specify a literal order
    std::vector<std::pair<int, int>> literal_occurence;
    for(int i = 0; i < 2*formula.n_variables(); ++i) literal_occurence.emplace_back(i, 0);
    for(int j = 0; j < static_cast<int>(generators.size()); ++j) {
      aw.reset();
      generators[j]->load(aw);

      for(int k = 0; k < aw.nsupp(); ++k) {
        const int lit = aw.supp()[k];
        ++literal_occurence[lit].second;
      }
    }

    // heuristic: least-used literals first
    std::sort(literal_occurence.begin(), literal_occurence.end(), [](auto &left, auto &right) {
      return left.second < right.second;
    });

    for (const auto& [lit, occ] : literal_occurence) {
      if(occ >= 1) // if literal does not occur at all, no need to add it
        sbp.add_to_global_order(lit);
    }


    // now output breaking constraints for generators
    for(int j = 0; j < static_cast<int>(generators.size()); ++j) {
      aw.reset();
      generators[j]->load(aw);
      sbp.add_lex_leader_predicate(formula, aw, sbp.get_global_order(), depth);
      ++constraints_added;
    }
    return constraints_added;
  }

  dejavu::big_number group_size() {
    return d.get_automorphism_group_size();
  }

  ~group_analyzer() {
    for(int j = 0; j < static_cast<int>(generators.size()); ++j) {
      delete generators[j];
    }
  }
};
