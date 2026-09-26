#pragma once

#include "SolverTypes.h"
#include "Alg.h"
#include "Heap.h"
#include "Vec.h"

#include <algorithm>
#include <chrono>
#include <map>
#ifdef SIMP21_ENABLE_USER_PROPAGATOR
#include <memory>
#include <set>
#endif
#include <unordered_map>
#include <vector>

enum clause_Type { LONG = 0, REMOVED, MIDSZ, SMALL };

namespace Simp21 {

#ifdef SIMP21_ENABLE_USER_PROPAGATOR
class UserPropagator {
public:
  virtual ~UserPropagator() = default;

  virtual void onAssignment(Lit p, int decisionLevel) {
    (void)p;
    (void)decisionLevel;
  }

  virtual void onBacktrack(int decisionLevel) {
    (void)decisionLevel;
  }

  virtual bool findConflict(std::vector<Lit>& conflict_clause) = 0;
};
#endif

class Solver {
private:
  template <typename T> class MyQueue {
    int max_sz, q_sz;
    int ptr;
    int64_t sum;
    vec<T> q;

  public:
    MyQueue(int sz) : max_sz(sz), q_sz(0), ptr(0), sum(0) {
      assert(sz > 0);
      q.growTo(sz);
    }
    inline bool full() const { return q_sz == max_sz; }
    inline T avg() const {
      assert(full());
      return sum / max_sz;
    }
    inline void clear() {
      sum = 0;
      q_sz = 0;
      ptr = 0;
    }
    void push(T e) {
      if (q_sz < max_sz) {
        q_sz++;
      } else {
        sum -= q[ptr];
      }

      sum += e;
      q[ptr++] = e;

      if (ptr == max_sz) {
        ptr = 0;
      }
    }
  };

public:
  // Constructor/Destructor:
  //
  Solver();
  virtual ~Solver();

  // Problem specification:
  //
  Var newVar(bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

  bool addClause(const vec<Lit> &ps);  // Add a clause to the solver.
  bool addEmptyClause();               // Add the empty clause, making the solver contradictory.
  bool addClause(Lit p);               // Add a unit clause to the solver.
  bool addClause(Lit p, Lit q);        // Add a binary clause to the solver.
  bool addClause(Lit p, Lit q, Lit r); // Add a ternary clause to the solver.
  bool addClause_(vec<Lit> &ps);       // Add a clause to the solver without making superflous internal copy. Will
                                       // change the passed vector 'ps'.

  // Solving:
  //
  bool simplify();                             // Removes already satisfied clauses.
  bool solve(const vec<Lit> &assumps);         // Search for a model that respects a given set of assumptions.
  lbool solveLimited(const vec<Lit> &assumps); // Search for a model that respects a given set of assumptions (With
                                               // resource constraints).
  lbool solve();                                // Search without assumptions.
  bool solve(Lit p);                           // Search for a model that respects a single assumption.
  bool solve(Lit p, Lit q);                    // Search for a model that respects two assumptions.
  bool solve(Lit p, Lit q, Lit r);             // Search for a model that respects three assumptions.
  bool okay() const;                           // FALSE means solver is in a conflicting state

#ifdef SIMP21_ENABLE_USER_PROPAGATOR
  // Optional problem-specific propagation. Compile with
  // SIMP21_ENABLE_USER_PROPAGATOR to enable this API and its callbacks.
  void setUserPropagator(std::unique_ptr<UserPropagator> propagator);
#endif

  // Variable mode:
  //
  void setPolarity(Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires
                                   // mode 'polarity_user'.
  void setDecisionVar(Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

  // Read state:
  //
  lbool value(Var x) const; // The current value of a variable.
  lbool value(Lit p) const; // The current value of a literal.
  lbool modelValue(Var x) const; // The value of a variable in the last model. The last call to solve must have been satisfiable.
  lbool modelValue(Lit p) const; // The value of a literal in the last model. The last call to solve must have been satisfiable.
  int nAssigns() const; // The current number of assigned literals.
  int nClauses() const; // The current number of original clauses.
  int nLearnts() const; // The current number of learnt clauses.
  int nVars() const;    // The current number of variables.
  int nFreeVars() const;

  // Resource contraints:
  //
  void setConfBudget(int64_t x);
  void setPropBudget(int64_t x);
  void budgetOff();
  void interrupt();      // Trigger a (potentially asynchronous) interruption of the solver.
  void clearInterrupt(); // Clear interrupt indicator flag.

  // Memory managment:
  //
  virtual void garbageCollect();
  void checkGarbage(double gf);
  void checkGarbage();

  // Extra results: (read-only member variable)
  //
  vec<lbool> model;  // If problem is satisfiable, this vector contains the model (if any).
  vec<Lit> conflict; // If problem is unsatisfiable (possibly under assumptions),
  // this vector represent the final conflict clause expressed in the assumptions.

  // Mode of operation:
  //
  int verbosity;
  double step_size;
  double step_size_dec;
  double min_step_size;
  int timer;
  double var_decay;
  double clause_decay;
  bool VSIDS;
  int ccmin_mode;      // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
  int phase_saving;    // Controls the level of phase saving (0=none, 1=limited, 2=full).
  double garbage_frac; // The fraction of wasted memory allowed before a garbage collection is triggered.

  int restart_first;        // The initial restart limit. (default 100)
  double restart_inc;       // The factor with which the restart limit is multiplied in each restart. (default 1.5)
  double learntsize_factor; // The intitial limit for learnt clauses is a factor of the original clauses. (default 1 / 3)
  double learntsize_inc;    // The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)

  int learntsize_adjust_start_confl;
  double learntsize_adjust_inc;

  // duplicate learnts version
  uint64_t VSIDS_props_limit;
  uint32_t min_number_of_learnts_copies;
  uint32_t dupl_db_init_size;
  uint32_t max_lbd_dup;
  // duplicate learnts version

  // Statistics: (read-only member variable)
  //
  uint64_t solves, starts, decisions, propagations, conflicts, conflicts_VSIDS;
  uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;
  uint64_t chrono_backtrack, non_chrono_backtrack;

  // duplicate learnts version
  uint64_t duplicates_added_conflicts;
  uint64_t duplicates_added_tier2;
  uint64_t duplicates_added_minimization;
  uint64_t dupl_db_size;

  // duplicate learnts version
  vec<uint32_t> picked;
  vec<uint32_t> conflicted;
  vec<uint32_t> almost_conflicted;
  vec<uint32_t> canceled;

  // timeouts
  int timeout_ms = -1;
  std::chrono::system_clock::time_point start_time;

protected:
  // Helper structures:
  //
  struct VarData {
    CRef reason;
    int level;
  };
  static inline VarData mkVarData(CRef cr, int l) {
    VarData d = {cr, l};
    return d;
  }

  struct Watcher {
    CRef cref;
    Lit blocker;
    Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
    bool operator==(const Watcher &w) const { return cref == w.cref; }
    bool operator!=(const Watcher &w) const { return cref != w.cref; }
  };

  struct WatcherDeleted {
    const ClauseAllocator &ca;
    WatcherDeleted(const ClauseAllocator &_ca) : ca(_ca) {}
    bool operator()(const Watcher &w) const { return ca[w.cref].mark() == 1; }
  };

  struct VarOrderLt {
    const vec<double> &activity;
    bool operator()(Var x, Var y) const { return activity[x] > activity[y]; }
    VarOrderLt(const vec<double> &act) : activity(act) {}
  };

  struct ConflictData {
    ConflictData() : nHighestLevel(-1), bOnlyOneLitFromHighest(false) {}

    int nHighestLevel;
    bool bOnlyOneLitFromHighest;
  };

  // Solver state:
  bool ok;           // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
  vec<CRef> clauses; // List of problem clauses.
  vec<CRef> learnts; // List of learnt clauses.

  double cla_inc;           // Amount to bump next clause with.
  // A heuristic measurement of the activity of a variable.
  vec<double> activity_CHB, activity_VSIDS, activity_distance;
  // Amount to bump next variable with.
  double var_inc;
  OccLists<Lit, vec<Watcher>, WatcherDeleted> watches_bin, // Watches for binary clauses only.
      watches;        // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
  vec<lbool> assigns; // The current assignments.
  vec<char> polarity; // The preferred polarity of each variable.
  vec<char> decision; // Declares if a variable is eligible for selection in the decision heuristic.
  vec<Lit> trail;     // Assignment stack; stores all assigments made in the order they were made.
  vec<int> trail_lim; // Separator indices for different decision levels in 'trail'.
  vec<VarData> vardata; // Stores reason and level for each variable.
  int qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
  int simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
  int64_t simpDB_props; // Remaining number of propagations that must be made before next execution of 'simplify()'.
  vec<Lit> assumptions; // Current set of assumptions provided to solve by the user.
  // A priority queue of variables ordered with respect to the variable activity.
  Heap<VarOrderLt> order_heap_CHB, order_heap_VSIDS, order_heap_distance;
  bool remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed
                         // in 'simplify'.

  int core_lbd_cut;
  float global_lbd_sum;
  uint64_t lbd_sum;
  MyQueue<int> lbd_queue; // For computing moving averages of recent LBD values.

  uint64_t next_T2_reduce, next_L_reduce;

  ClauseAllocator ca;

  // duplicate learnts version
  std::map<int32_t, std::map<uint32_t, std::unordered_map<uint64_t, uint32_t>>> ht;
  uint32_t reduceduplicates(); // Reduce the duplicates DB
  // duplicate learnts version

  int confl_to_chrono;
  int chrono;

  // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
  // used, exept 'seen' wich is used in several places.
  //
  vec<char> seen;
  vec<Lit> analyze_stack;
  vec<Lit> analyze_toclear;
  vec<Lit> add_tmp;
  vec<Lit> add_oc;

#ifdef SIMP21_ENABLE_USER_PROPAGATOR
  std::unique_ptr<UserPropagator> user_propagator;
  std::set<CRef> user_conflict_clause_refs;
#endif

  vec<uint64_t> seen2; // Mostly for efficient LBD computation. 'seen2[i]' will indicate if decision level or variable
                       // 'i' has been seen.
  uint64_t counter;    // Simple counter for marking purpose with 'seen2'.

  double max_learnts;
  double learntsize_adjust_confl;
  int learntsize_adjust_cnt;

  // Resource contraints:
  //
  int64_t conflict_budget;    // -1 means no budget.
  int64_t propagation_budget; // -1 means no budget.
  bool asynch_interrupt;

  // Progress reporting:
  //
  std::chrono::steady_clock::time_point progress_start_time;
  std::chrono::steady_clock::time_point last_progress_time;
  uint64_t last_progress_conflicts = 0;
  uint64_t next_progress_check_conflicts = 0;
  int progress_num_vars = 0;
  int progress_num_clauses = 0;

  // Main internal methods:
  //
  void insertVarOrder(Var x); // Insert a variable in the decision order priority queue.
  Lit pickBranchLit();        // Return the next decision variable.
  void newDecisionLevel();    // Begins a new decision level.
  void uncheckedEnqueue(Lit p, int level = 0,
                        CRef from = CRef_Undef); // Enqueue a literal. Assumes value of literal is undefined.
  bool enqueue(Lit p, CRef from = CRef_Undef);   // Test if fact 'p' contradicts current state, enqueue otherwise.
  CRef propagate();                              // Perform unit propagation. Returns possibly conflicting clause.
#ifdef SIMP21_ENABLE_USER_PROPAGATOR
  CRef propagateUserConflict();                  // Ask the registered user propagator for a conflict.
  CRef addUserConflictClause(const std::vector<Lit>& literals);
#endif
  void cancelUntil(int level);                   // Backtrack until a certain level.
  void analyze(CRef confl, vec<Lit> &out_learnt, int &out_btlevel, int &out_lbd); // (bt = backtrack)
  void analyzeFinal(Lit p, vec<Lit> &out_conflict);   // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME
                                                      // REASONABLE GENERALIZATION?
  bool litRedundant(Lit p, uint32_t abstract_levels); // (helper method for 'analyze()')
  lbool search(int &nof_conflicts);                   // Search for a given number of conflicts.
  lbool solve_();                                     // Main solve method (assumptions given in 'assumptions').
  void reduceDB();                                    // Reduce the set of learnt clauses.
  void reduceDB_Tier2();
  void removeSatisfied(vec<CRef> &cs); // Shrink 'cs' to contain only non-satisfied clauses.
  void rebuildOrderHeap();
  bool binResMinimize(vec<Lit> &out_learnt); // Further learnt clause minimization by binary resolution.

  // Maintaining Variable/Clause activity:
  //
  void varDecayActivity(); // Decay all variables with the specified factor. Implemented by increasing the 'bump' value
                           // instead.
  void varBumpActivity(Var v, double mult); // Increase a variable with the current 'bump' value.
  void claDecayActivity(); // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value
                           // instead.
  void claBumpActivity(Clause &c); // Increase a clause with the current 'bump' value.

  // Operations on clauses:
  void attachClause(CRef cr);                      // Attach a clause to watcher lists.
  void detachClause(CRef cr, bool strict = false); // Detach a clause to watcher lists.
  void removeClause(CRef cr);                      // Detach and free a clause.
  bool locked(const Clause &c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
  bool satisfied(const Clause &c) const; // Returns TRUE if a clause is satisfied in the current state.

  void relocAll(ClauseAllocator &to);

  // duplicate learnts version
  int is_duplicate(std::vector<uint32_t> &c); // returns TRUE if a clause is duplicate
  // duplicate learnts version

  // Misc:
  int decisionLevel() const;           // Gives the current decisionlevel.
  uint32_t abstractLevel(Var x) const; // Used to represent an abstraction of sets of decision levels.
  CRef reason(Var x) const;

  ConflictData FindConflictLevel(CRef cind);

  // Timeout:
  bool isTimeout() const;
  void resetProgress();
  void maybePrintProgress();

public:
  int level(Var x) const;
  // Public wrapper exposing varBumpActivity for callers that want to
  // prioritise domain-specific decision variables.
  void publicBumpActivity(Var v, double mult) { varBumpActivity(v, mult); }

protected:
  template <class V> int computeLBD(const V &c) {
    int lbd = 0;
    counter++;

    for (int i = 0; i < c.size(); i++) {
      int l = level(var(c[i]));

      if (l != 0 && seen2[l] != counter) {
        seen2[l] = counter;
        lbd++;
      }
    }

    return lbd;
  }

  // simplify
public:
  bool simplifyAll();
  void simplifyLearnt(Clause &c);
  bool simplifyLearnt_core();
  int trailRecord;
  void cancelUntilTrailRecord();
  void simpleUncheckEnqueue(Lit p, CRef from = CRef_Undef);
  CRef simplePropagate();
  uint64_t nbSimplifyAll;
  uint64_t simplified_length_record, original_length_record;
  uint64_t s_propagations;

  vec<Lit> simp_learnt_clause;
  vec<CRef> simp_reason_clause;
  void simpleAnalyze(CRef confl, vec<Lit> &out_learnt, vec<CRef> &reason_clause, bool True_confl);

  // adjust simplifyAll occasion
  long curSimplify;
  int nbconfbeforesimplify;
  int incSimplify;

  bool DISTANCE;

private:
  bool cur_solustion_used;
  int freeze_restart_num;
  int best_unsat_num;
  int max_trail;

  std::vector<char> cur_solution;
  std::vector<char> best_solution;
  std::vector<char> top_trail_soln;

  void propagate_solution();
  void rand_rephase();
};

//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline int Solver::level(Var x) const { return vardata[x].level; }

inline void Solver::insertVarOrder(Var x) {
  //    Heap<VarOrderLt>& order_heap = VSIDS ? order_heap_VSIDS : order_heap_CHB;
  Heap<VarOrderLt> &order_heap = DISTANCE ? order_heap_distance : ((!VSIDS) ? order_heap_CHB : order_heap_VSIDS);

  if (!order_heap.inHeap(x) && decision[x]) {
    order_heap.insert(x);
  }
}

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }

inline void Solver::varBumpActivity(Var v, double mult) {
  if ((activity_VSIDS[v] += var_inc * mult) > 1e100) {
    // Rescale:
    for (int i = 0; i < nVars(); i++) {
      activity_VSIDS[i] *= 1e-100;
    }

    var_inc *= 1e-100;
  }

  // Update order_heap with respect to new activity:
  if (order_heap_VSIDS.inHeap(v)) {
    order_heap_VSIDS.decrease(v);
  }
}

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity(Clause &c) {
  if ((c.activity() += cla_inc) > 1e20) {
    // Rescale:
    for (int i = 0; i < learnts.size(); i++) {
      ca[learnts[i]].activity() *= 1e-20;
    }

    cla_inc *= 1e-20;
  }
}

inline void Solver::checkGarbage(void) { return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf) {
  if (ca.wasted() > ca.size() * gf) {
    garbageCollect();
  }
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool Solver::enqueue(Lit p, CRef from) {
  return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, decisionLevel(), from), true);
}
inline bool Solver::addClause(const vec<Lit> &ps) {
  ps.copyTo(add_tmp);
  return addClause_(add_tmp);
}
inline bool Solver::addEmptyClause() {
  add_tmp.clear();
  return addClause_(add_tmp);
}
inline bool Solver::addClause(Lit p) {
  add_tmp.clear();
  add_tmp.push(p);
  return addClause_(add_tmp);
}
inline bool Solver::addClause(Lit p, Lit q) {
  add_tmp.clear();
  add_tmp.push(p);
  add_tmp.push(q);
  return addClause_(add_tmp);
}
inline bool Solver::addClause(Lit p, Lit q, Lit r) {
  add_tmp.clear();
  add_tmp.push(p);
  add_tmp.push(q);
  add_tmp.push(r);
  return addClause_(add_tmp);
}
inline bool Solver::locked(const Clause &c) const {
  int i = c.size() != 2 ? 0 : (value(c[0]) == l_True ? 0 : 1);
  return value(c[i]) == l_True && reason(var(c[i])) != CRef_Undef && ca.lea(reason(var(c[i]))) == &c;
}
inline void Solver::newDecisionLevel() { trail_lim.push(trail.size()); }

inline int Solver::decisionLevel() const { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel(Var x) const { return 1 << (level(x) & 31); }
inline lbool Solver::value(Var x) const { return assigns[x]; }
inline lbool Solver::value(Lit p) const { return assigns[var(p)] ^ sign(p); }
inline lbool Solver::modelValue(Var x) const { return model[x]; }
inline lbool Solver::modelValue(Lit p) const { return model[var(p)] ^ sign(p); }
inline int Solver::nAssigns() const { return trail.size(); }
inline int Solver::nClauses() const { return clauses.size(); }
inline int Solver::nLearnts() const { return learnts.size(); }
inline int Solver::nVars() const { return vardata.size(); }
inline int Solver::nFreeVars() const { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void Solver::setPolarity(Var v, bool b) { polarity[v] = b; }
inline void Solver::setDecisionVar(Var v, bool b) {
  if (b && !decision[v]) {
    dec_vars++;
  } else if (!b && decision[v]) {
    dec_vars--;
  }

  decision[v] = b;

  if (b && !order_heap_CHB.inHeap(v)) {
    order_heap_CHB.insert(v);
    order_heap_VSIDS.insert(v);
    order_heap_distance.insert(v);
  }
}
inline void Solver::setConfBudget(int64_t x) { conflict_budget = conflicts + x; }
inline void Solver::setPropBudget(int64_t x) { propagation_budget = propagations + x; }
inline void Solver::interrupt() { asynch_interrupt = true; }
inline void Solver::clearInterrupt() { asynch_interrupt = false; }
inline void Solver::budgetOff() { conflict_budget = propagation_budget = -1; }

// TODO: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'.
inline lbool Solver::solve() {
  budgetOff();
  assumptions.clear();
  return solve_();
}
inline bool Solver::solve(Lit p) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  return solve_() == l_True;
}
inline bool Solver::solve(Lit p, Lit q) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  assumptions.push(q);
  return solve_() == l_True;
}
inline bool Solver::solve(Lit p, Lit q, Lit r) {
  budgetOff();
  assumptions.clear();
  assumptions.push(p);
  assumptions.push(q);
  assumptions.push(r);
  return solve_() == l_True;
}
inline bool Solver::solve(const vec<Lit> &assumps) {
  budgetOff();
  assumps.copyTo(assumptions);
  return solve_() == l_True;
}
inline lbool Solver::solveLimited(const vec<Lit> &assumps) {
  assumps.copyTo(assumptions);
  return solve_();
}
inline bool Solver::okay() const { return ok; }

inline bool Solver::isTimeout() const { 
  if (timeout_ms == -1) 
    return false;
  const auto end_time = std::chrono::system_clock::now();
  const auto durationMs = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
  return durationMs > timeout_ms; 
}

} // namespace Simp21
