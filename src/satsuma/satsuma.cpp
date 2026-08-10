#include "satsuma.h"
#include "cnf.h"
#include "cnf2wl.h"

#include <string>

// satsuma::preprocessor satsuma_preprocessor;
// if (arg == "__HELP" || arg == "_H") {
//     std::clog << "Usage: satsuma [file] [options]" << std::endl;
//     std::clog << "Computes symmetry breaking predicates for a CNF SAT formula." << std::endl;
//     std::clog << "FILE is expected to be in DIMACS format (may also be piped)." << std::endl;
//     std::clog << "\n";
//     std::clog << "Options:" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                     "--file [FILE]" << std::setw(16) <<
//                     "Input file in CNF format" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                     "--out-file [FILE]" << std::setw(16) <<
//                     "Output file in CNF format" << std::endl;
//     std::clog << "   -----------------------------------------------------------------------\n";
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--dejavu-print" << std::setw(16) <<
//                 "Print progress of dejavu" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--dejavu-prefer-dfs" << std::setw(16) <<
//                 "Makes dejavu prefer depth-first search" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--graph-only" << std::setw(16) <<
//                 "Outputs the model graph in DIMACS" << std::endl;
//     std::clog << "   -----------------------------------------------------------------------\n";
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--break-depth [N]" << std::setw(16) <<
//                 "Limits generic breaking constraints to depth n" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--preprocess-cnf" << std::setw(16) <<
//                 "Preprocess before symmetry breaking" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--binary-clauses" << std::setw(16) <<
//                 "Use the binary clause heuristic" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--no-opt" << std::setw(16) <<
//                 "Don't optimize generators" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--opt-passes [N]" << std::setw(16) <<
//                 "Passes used in support optimization " << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--opt-conjugations [N]" << std::setw(16) <<
//                 "Limit for conjugates added from generators" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--opt-random [N]" << std::setw(16) <<
//                 "Maximum number of random generators added" << std::endl;
//     std::clog << "   "  << std::left << std::setw(23) <<
//                 "--opt-reopt" << std::setw(16) <<
//                 "Optimizes generators twice" << std::endl;
//     return 0;
// } else if (arg == "__BREAK_DEPTH") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_break_depth(atoi(argv[i]));
//     } else {
//         std::cerr << "--break-depth option requires one argument." << std::endl;
//         return 1;
//     }
// } else if (arg == "__ROW_ORBIT_LIMIT") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_row_orbit_limit(atoi(argv[i]));
//     } else {
//         std::cerr << "--row-orbit-limit option requires one argument." << std::endl;
//         return 1;
//     }
// }  else if (arg == "__ROW_COLUMN_ORBIT_LIMIT") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_row_column_orbit_limit(atoi(argv[i]));
//     } else {
//         std::cerr << "--row-orbit-limit option requires one argument." << std::endl;
//         return 1;
//     }
// } else if (arg == "__JOHNSON_ORBIT_LIMIT") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_johnson_orbit_limit(atoi(argv[i]));
//     } else {
//         std::cerr << "--johnson-orbit-limit option requires one argument." << std::endl;
//         return 1;
//     }
// } else if (arg == "__OPT_PASSES") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_opt_passes(atoi(argv[i]));
//     } else {
//         std::cerr << "--opt-passes option requires one argument." << std::endl;
//         return 1;
//     }
// } else if (arg == "__OPT_CONJUGATIONS") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_opt_conjugations(atoi(argv[i]));
//     } else {
//         std::cerr << "--opt-conjugations option requires one argument." << std::endl;
//         return 1;
//     }
// } else if (arg == "__OPT_RANDOM") {
//     if (i + 1 < argc) {
//         i++;
//         satsuma_preprocessor.set_opt_random(atoi(argv[i]));
//     } else {
//         std::cerr << "--opt-random option requires one argument." << std::endl;
//         return 1;
//     }
// } else if (arg == "__OPT_REOPT") {
//     satsuma_preprocessor.set_opt_reopt(true);
// } else if (arg == "__DEJAVU_PRINT") {
//     satsuma_preprocessor.set_dejavu_print(true);
// } else if (arg == "__DEJAVU_PREFER_DFS") {
//     satsuma_preprocessor.set_dejavu_prefer_dfs(true);
// } else if (arg == "__NO_OPT") {
//     satsuma_preprocessor.set_optimize_generators(false);
// } else if(arg == "__PREPROCESS_CNF") {
//     satsuma_preprocessor.set_preprocess_cnf(true);
// } else if(arg == "__HYPERGRAPH_MACROS") {
//     satsuma_preprocessor.set_hypergraph_macros(true);
// } else if(arg == "__BINARY_CLAUSES") {
//     satsuma_preprocessor.set_binary_clauses(true);
// } else if (arg == "__STRUCT_ONLY") {
//     satsuma_preprocessor.set_struct_only(true);
// } else if (arg == "__GRAPH_ONLY") {
//     satsuma_preprocessor.set_graph_only(true);
// } else  {
//     std::cerr << "Invalid commandline option '" << argv[i] << "'." << std::endl;
//     return 1;
// }

void create_cnf2wl(cnf2wl& formula, int numVars, const std::vector<std::vector<int>> &clauses) {
  formula.reserve(numVars, clauses.size());
  std::vector<int> construct_clause;
  for (const auto& clause : clauses) {
    construct_clause.clear();
    construct_clause.insert(construct_clause.end(), clause.begin(), clause.end());
    formula.add_clause(construct_clause);
  }
}

std::pair<int, std::vector<std::vector<int>>>
applySatsumaSymmetry(int verbose, int numVars, std::vector<std::vector<int>> &clauses) {
  cnf2wl formula;
  create_cnf2wl(formula, numVars, clauses);
  clauses.clear();

  if (verbose >= 2) {
    std::clog << "c input cnf: #variables " << formula.n_variables() << " #clauses " << formula.n_clauses() 
              << " #arr " << formula.n_len() << "\n";
  }

  // call main algorithm
  satsuma::preprocessor satsuma_preprocessor;
  satsuma_preprocessor.set_verbose(verbose);
  int newNumVars;
  std::vector<std::vector<int>> newClauses;
  satsuma_preprocessor.preprocess(formula, newNumVars, newClauses);

  return std::make_pair(newNumVars, newClauses);
}
