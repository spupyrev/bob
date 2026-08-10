#pragma once

#define SATSUMA_VERSION_MAJOR 1
#define SATSUMA_VERSION_MINOR 1

#include "dejavu.h"
#include "cnf.h"
#include "cnf2wl.h"
#include "utility.h"
#include "group_analyzer.h"
#include "hypergraph.h"

#include <utility>

namespace satsuma {
  /**
   * \brief The satsuma preprocessor.
   */
  class preprocessor {
  private:
    int verbose = 0;

    // limits for special detection
    int row_orbit_limit    = 64;
    int row_column_orbit_limit = 64;
    int johnson_orbit_limit  = 64;

    // routines
    bool optimize_generators = true;
    bool preprocess_cnf    = false;
    bool hypergraph_macros   = false;
    bool binary_clauses    = false;

    // limits for generator optimization
    int  opt_optimize_passes = 64;
    int  opt_addition_limit  = 196;
    int  opt_conjugate_limit = 256;
    bool opt_reopt = false;

    // options for breaking constraints
    int break_depth      = 512;

    // dejavu settings
    bool dejavu_print    = false;
    bool dejavu_prefer_dfs   = false;

    std::ostream* log = &std::clog;
    /**
      Compute a symmetry breaking predicate for the given formula.
    */
    void generate_symmetry_predicate(cnf& formula, int &newNumVars, std::vector<std::vector<int>>& newClauses) {
      hypergraph_wrapper hypergraph(formula);
      if (hypergraph_macros) {
        if (verbose >= 2) {
          (*log) << "c\n";
          (*log) << "c apply hypergraph macros";
        }
        hypergraph.hypergraph_reduction();
      }

      // transform the formula into a graph and apply color refinement to approximate orbits
      if (verbose >= 2) {
        (*log) << "c\n";
        (*log) << "c make graph and approximate orbits";
      }
      group_analyzer symmetries;
      //symmetries.compute_from_cnf(formula);
      symmetries.compute_from_hypergraph(hypergraph);
      if (verbose >= 2) {
        (*log) << "\n" << "c\t [group: #orbits ~= " << symmetries.n_orbits() << "]";
      }

      // now try to detect and break specific group actions
      if (verbose >= 2) {
        (*log) << "c\n";
        (*log) << "c detect special group actions" << "\n";
      }
      predicate sbp(formula.n_variables());

      // symmetries.detect_symmetric_action(formula, sbp);
      symmetries.detect_johnson_arity2(formula, sbp, johnson_orbit_limit);
      symmetries.detect_row_column_symmetry(formula, sbp, row_column_orbit_limit);
      symmetries.detect_row_symmetry(formula, sbp, row_orbit_limit);

      // next, apply dejavu on remainder, and break generators with generic strategy
      if (verbose >= 2) {
        (*log) << "c\n";
        (*log) << "c detect symmetries on remainder" << "\n";
      }
      symmetries.detect_symmetries_generic(dejavu_print, dejavu_prefer_dfs);
      if (verbose >= 2) {
        (*log) << "\n" << "c\t [group: #symmetries " << symmetries.group_size() << " #generators " << symmetries.n_generators()
               << "]";
      }

      if (symmetries.n_generators() > 0) {
        if (binary_clauses) {
          if (verbose >= 2) {
            (*log) << "c\n";
            (*log) << "c add binary clauses" << "\n";
          }
          symmetries.add_binary_clauses_no_schreier(formula, sbp);
        }

        if (optimize_generators) {
          if (verbose >= 2) {
            (*log) << "c\n";
            (*log) << "c optimize generators (opt_passes="
                 << opt_optimize_passes << ", conjugate_limit=" << opt_addition_limit << ")" << "\n";
          }
          symmetries.optimize_generators(opt_optimize_passes, opt_addition_limit, opt_conjugate_limit, opt_reopt);
        }

        if (verbose >= 2) {
          (*log) << "c\n";
          (*log) << "c add generic predicates (break_depth=" << break_depth << ")" << "\n";
        }
        symmetries.add_lex_leader_for_generators(formula, sbp, break_depth);
      }

      if (verbose >= 2) {
        (*log) << "c\n";
        (*log) << "c generation finished" << "\n";
        (*log) << "c\t [org: #vars " << formula.n_variables() << " #clauses " << formula.n_clauses() << "]" << "\n";
        (*log) << "c\t [sbp: #extra_vars " << sbp.n_extra_variables() << " #clauses " << sbp.n_clauses() << "]" << "\n";
      }

      // output result
      newNumVars = formula.n_variables() + sbp.n_extra_variables();
      newClauses.reserve(formula.n_clauses() + sbp.n_clauses());

      formula.dimacs_output_clauses_to(newClauses);
      sbp.dimacs_output_clauses_to(newClauses);
    }

  public:
    void set_verbose(int verbose) {
      this->verbose = verbose;
      if (verbose < 2)
        (*log).setstate(std::ios_base::badbit);
    }

    void set_optimize_generators(bool use_optimize_generators) {
      optimize_generators = use_optimize_generators;
    }

    int get_row_orbit_limit() const {
      return row_orbit_limit;
    }

    void set_row_orbit_limit(int rowOrbitLimit) {
      row_orbit_limit = rowOrbitLimit;
    }

    int get_row_column_orbit_limit() const {
      return row_column_orbit_limit;
    }

    void set_row_column_orbit_limit(int rowColumnOrbitLimit) {
      row_column_orbit_limit = rowColumnOrbitLimit;
    }

    int get_johnson_orbit_limit() const {
      return johnson_orbit_limit;
    }

    void set_johnson_orbit_limit(int johnsonOrbitLimit) {
      johnson_orbit_limit = johnsonOrbitLimit;
    }

    int get_break_depth() const {
      return break_depth;
    }

    void set_break_depth(int breakDepth) {
      break_depth = breakDepth;
    }

    void set_opt_passes(int passes) {
      opt_optimize_passes = passes;
    }

    void set_opt_conjugations(int conjugations) {
      opt_conjugate_limit = conjugations;
    }

    void set_opt_random(int random) {
      opt_addition_limit = random;
    }

    void set_opt_reopt(bool reopt) {
      opt_reopt = reopt;
    }

    void set_dejavu_print(bool print) {
      dejavu_print = print;
    }

    void set_dejavu_prefer_dfs(bool prefer_dfs) {
      dejavu_prefer_dfs = prefer_dfs;
    }

    void set_preprocess_cnf(bool preprocessCNF) {
      preprocess_cnf = preprocessCNF;
    }

    void set_hypergraph_macros(bool hypergraphMacros) {
      hypergraph_macros = hypergraphMacros;
    }

    void set_binary_clauses(bool binaryClauses) {
      binary_clauses = binaryClauses;
    }

    void set_log_output(std::ostream* new_logout) {
      if (new_logout == nullptr) terminate_with_error("log output can not be nullptr");
      log = new_logout;
    }

    void preprocess(cnf2wl& formula, int &newNumVars, std::vector<std::vector<int>>& newClauses) {
      if (preprocess_cnf) {
        (*log) << "c\n";
        (*log) << "c preprocess cnf" << "\n";

        // propagate unit literals
        formula.propagate();

        // collect pure literals
        std::vector<int> pure_literals;
        formula.mark_literal_uses();
        for(int i = 0; i < formula.n_variables(); ++i) {
          const int pos_lit = 1 + i;
          const int neg_lit = -pos_lit;
          if (formula.assigned(pos_lit) == 0) {
            if (formula.is_literal_marked_used(pos_lit) && !formula.is_literal_marked_used(neg_lit)) {
              pure_literals.push_back(pos_lit);
            }
            if (formula.is_literal_marked_used(neg_lit) && !formula.is_literal_marked_used(pos_lit)) {
              pure_literals.push_back(neg_lit);
            }
          }
        }

        // propagate one round of pure literals
        for(const auto lit : pure_literals) {
          formula.assign_literal(lit);
        }

        // propagate unit again
        formula.propagate();
      }
      if (verbose >= 2) {
        (*log) << "c\n";
        (*log) << "c make clause database";
      }
      cnf formula_db;
      formula_db.read_from_cnf2wl(formula);
      if (verbose >= 2) {
        (*log) << "\n";
      }
      generate_symmetry_predicate(formula_db, newNumVars, newClauses);
    }
  };
}
