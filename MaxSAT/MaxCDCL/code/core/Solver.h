/****************************************************************************************[Solver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh

Maple_LCM, Based on MapleCOMSPS_DRUP --Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause minimisation approach
 Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L. , “An effective learnt clause minimization approach for cdcl sat solvers,” in IJCAI-2017, 2017, pp.703-711.
 
Maple_CM, Based on Maple_LCM --Copyright (c) 2018, Chu-Min LI, Mao Luo, Fan Xiao: implementing a clause minimisation approach.

Copyright (c) 2021,Chu-Min Li (chu-min.li@u-picardie.fr)

A MaxSAT solver combining branch-and-bound and clause learning, implemented by Chu-Min Li with the help of Jordi Coll
Based on Maple_LCM

Reference: Chu-Min Li, Zhenxing Xu, Jordi Coll, Felip Manyà, Djamal Habet, Kun He, Combining Clause Learning and Branch and Bound for MaxSAT, in CP-2021, to appear
 
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#define ANTI_EXPLORATION
#define BIN_DRUP

#define GLUCOSE23
//#define INT_QUEUE_AVG
//#define LOOSE_PROP_STAT

#ifdef GLUCOSE23
  #define INT_QUEUE_AVG
  #define LOOSE_PROP_STAT
#endif

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/SolverTypes.h"


// Don't change the actual numbers.
#define LOCAL 0
#define TIER2 2
#define CORE  3

#define NON -7

namespace Minisat {

template<class Idx, class Vec>
class vec2
{
    vec<Vec>  occs;
    
 public:
    void  init      (const Idx& idx){ occs.growTo(toInt(idx)+1);}
    Vec&  operator[](const Idx& idx){ return occs[toInt(idx)]; }
    int size() {return occs.size();}
    void     shrink_  (int nelems) {occs.shrink_(nelems);}

    void  clear(bool free = false){
        occs   .clear(free);
    }
};

//=================================================================================================
// Solver -- the main class:

class Solver {
private:
    template<typename T>
    class MyQueue {
        int max_sz, q_sz;
        int ptr;
        int64_t sum;
        vec<T> q;
    public:
        MyQueue(int sz) : max_sz(sz), q_sz(0), ptr(0), sum(0) { assert(sz > 0); q.growTo(sz); }
        inline bool   full () const { return q_sz == max_sz; }
#ifdef INT_QUEUE_AVG
        inline T      avg  () const { assert(full()); return sum / max_sz; }
#else
        inline double avg  () const { assert(full()); return sum / (double) max_sz; }
#endif
        inline void   clear()       { sum = 0; q_sz = 0; ptr = 0; }
        void push(T e) {
            if (q_sz < max_sz) q_sz++;
            else sum -= q[ptr];
            sum += e;
            q[ptr++] = e;
            if (ptr == max_sz) ptr = 0;
        }
    };

public:

    // Constructor/Destructor:
    //
    Solver();
    virtual ~Solver();

    // Problem specification:
    //
    Var     newVar    (bool polarity = false, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver. 
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Lit p);                                  // Add a unit clause to the solver. 
    bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver. 
    bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver. 
    bool    addClause_(      vec<Lit>& ps, unsigned weight = 1);                     // Add a clause to the solver without making superflous internal copy. Will
                                                                // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     (bool simplifyOriginal=false);                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);
    
    // Variable mode:
    // 
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    FILE*     drup_file;
    int       verbosity;
    double    step_size;
    double    step_size_dec;
    double    min_step_size;
    int       timer;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      VSIDS;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts, conflicts_VSIDS;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

    vec<uint32_t> picked;
    vec<uint32_t> conflicted;
    vec<uint32_t> almost_conflicted;
#ifdef ANTI_EXPLORATION
    vec<uint32_t> canceled;
#endif

protected:

    // Helper structures:
    //
    struct VarData { CRef reason; int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts_core,     // List of learnt clauses.
                        learnts_tier2,
                        learnts_local;
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity_CHB,     // A heuristic measurement of the activity of a variable.
                        activity_VSIDS,activity_distance;
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
                        watches_bin,      // Watches for binary clauses only.
                        watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap_CHB,   // A priority queue of variables ordered with respect to the variable activity.
      order_heap_VSIDS; //order_heap_distance;
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    int                 core_lbd_cut;
    float               global_lbd_sum;
    MyQueue<int>        lbd_queue;  // For computing moving averages of recent LBD values.

    uint64_t            next_T2_reduce,
                        next_L_reduce;

    ClauseAllocator     ca;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;
    vec<Lit>            add_oc;

    vec<uint64_t>       seen2;    // Mostly for efficient LBD computation. 'seen2[i]' will indicate if decision level or variable 'i' has been seen.
    uint64_t            counter;  // Simple counter for marking purpose with 'seen2'.

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int& nof_conflicts);                                    // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     reduceDB_Tier2   ();
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     safeRemoveSatisfied(vec<CRef>& cs, unsigned valid_mark);
    void     rebuildOrderHeap ();
    bool     binResMinimize   (vec<Lit>& out_learnt);                                  // Further learnt clause minimization by binary resolution.

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double mult);    // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;

    template<class V> int computeLBD(const V& c) {
        int lbd = 0;

        counter++;
        for (int i = 0; i < c.size(); i++){
            int l = level(var(c[i]));
            if (l != 0 && seen2[l] != counter){
                seen2[l] = counter;
                lbd++; } }

        return lbd;
    }


    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }

    // simplify
    //
public:
    
#ifdef BIN_DRUP
    static int buf_len;
    static unsigned char drup_buf[];
    static unsigned char* buf_ptr;
    
    static inline void byteDRUP(Lit l){
        unsigned int u = 2 * (var(l) + 1) + sign(l);
        do{
            *buf_ptr++ = u & 0x7f | 0x80; buf_len++;
            u = u >> 7;
        }while (u);
        *(buf_ptr - 1) &= 0x7f; // End marker of this unsigned number.
    }
    
    template<class V>
    static inline void binDRUP(unsigned char op, const V& c, FILE* drup_file){
        assert(op == 'a' || op == 'd');
        *buf_ptr++ = op; buf_len++;
        for (int i = 0; i < c.size(); i++) byteDRUP(c[i]);
        *buf_ptr++ = 0; buf_len++;
        if (buf_len > 1048576) binDRUP_flush(drup_file);
    }
    
    static inline void binDRUP_strengthen(const Clause& c, Lit l, FILE* drup_file){
        *buf_ptr++ = 'a'; buf_len++;
        for (int i = 0; i < c.size(); i++)
            if (c[i] != l) byteDRUP(c[i]);
        *buf_ptr++ = 0; buf_len++;
        if (buf_len > 1048576) binDRUP_flush(drup_file);
    }
    
    static inline void binDRUP_flush(FILE* drup_file){
      fwrite(drup_buf, sizeof(unsigned char), buf_len, drup_file);
      //   fwrite_unlocked(drup_buf, sizeof(unsigned char), buf_len, drup_file);
        buf_ptr = drup_buf; buf_len = 0;
    }
#endif
    
    bool	simplifyAll();
    bool	simplifyLearnt(Clause& c, CRef cr, vec<Lit>& lits);
    // bool	simplifyLearnt_x(vec<CRef>& learnts_x);
    bool	simplifyLearnt_core();
    bool	simplifyLearnt_tier2();
    bool        simplifyOriginalClauses();
    int		trailRecord;
    void	litsEnqueue(int cutP, Clause& c);
    void	cancelUntilTrailRecord();
    void	simpleUncheckEnqueue(Lit p, CRef from = CRef_Undef);
    CRef    simplePropagate();
    uint64_t nbSimplifyAll;
    uint64_t simplified_length_record, original_length_record;
    uint64_t s_propagations;

    vec<Lit> simp_learnt_clause;
    // vec<CRef> simp_reason_clause;
    void	simpleAnalyze(CRef confl, vec<Lit>& out_learnt, bool True_confl, bool flysbsmrslv=true);

    // in redundant
    bool removed(CRef cr);
    // adjust simplifyAll occasion
    long curSimplify;
    uint64_t nbconfbeforesimplify;
    int incSimplify;

   bool collectFirstUIP(CRef confl);
    vec<double> var_iLevel,var_iLevel_tmp;
    uint64_t nbcollectfirstuip, nblearntclause, nbDoubleConflicts, nbTripleConflicts;
    int uip1, uip2;
    vec<int> pathCs;
    CRef propagateLits(vec<Lit>& lits);
    uint64_t previousStarts;
    double var_iLevel_inc;
    vec<Lit> involved_lits;
    double    my_var_decay;
    bool   DISTANCE;

    vec<CRef> usedClauses;

    //  bool simplifyUsedOriginalClauses();

    void simplifyConflictClause(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);
    void attachSoftClause(CRef cr);
    void detachSoftClause(CRef cr, bool strict=false);
    void removeSoftClause(CRef cr);
    void removeSoftSatisfied(vec<CRef>& cs);
    void analyzeSoftConflict(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);
    bool shortenSoftClauses(Lit p);
    vec<CRef> falseSoftClauses, softClauses;
    vec<int> falseSoftClauses_lim;
    uint64_t softConflicts, softLiterals;
    bool softConflictFlag;
    struct softWatcher {
        CRef cref;
        softWatcher(CRef cr) : cref(cr) {}
        bool operator==(const softWatcher& w) const { return cref == w.cref; }
        bool operator!=(const softWatcher& w) const { return cref != w.cref; }
    };

    /* struct softWatcherDeleted */
    /* { */
    /*     const ClauseAllocator& ca; */
    /*     softWatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {} */
    /*     bool operator()(const softWatcher& w) const { return ca[w.cref].mark() == 1; } */
    /* }; */
    
    /* OccLists<Lit, vec<softWatcher>, softWatcherDeleted> softWatches; */
    uint64_t hardWeight, solutionCost, totalWeight, UB;
    unsigned int weight;
    int instanceType, nbOriVars;
    int nbClauseReduce;
    void simpleAnalyzeSoftConflict(vec<Lit>& out_learnt);
    int falseSoftClausesRecord;
    bool WithNewUB;
    bool simplifyLearnt_local();

    int nbOrignalVars;
    void addHardClausesForSoftClauses();
    bool auxiVar(Var v);
    vec<Lit> falseLits;
    vec<int> falseLits_lim;
    int falseLitsRecord;
    int next_C_reduce;
    void reduceDB_core();

    bool UBconflictFlag;
    uint64_t LOOKAHEAD, lk_propagations, nbLKsuccess, totalPrunedLB, totalPrunedLB2;
    Var falseVar;
    vec<CRef> hardSoftClauses;
    bool lookahead();
    void lookbackResetTrail(CRef confl, Var falseVar, int nbIsets, vec<Lit>& out_learnt, bool last=false);
    CRef propagateForLK();
    bool uncheckedEnqueueForLK(Lit p, CRef from=CRef_Undef);
    //   vec<uint64_t> lookaheadCNT;
    vec<Lit> imply;
    bool redundantLit(Lit p);
    vec<Lit> lastConflLits, conflLits, initConflLits;
    //  Heap<VarOrderLt>    orderHeapAuxi;
    void insertAuxiVarOrder(Var x);
    vec<double> activityLB;
    double stepSizeLB;
    Var pickAuxiVar();
    void bumpConflVars();
    //  vec<uint64_t> lastTested;
    vec<Lit> softLits, unitSoftLits, nonUnitSoftLits, allSoftLits;
    void removeLearntClauses();
    uint64_t subconflicts; // to control iterative calls of search()
    uint64_t objForSearch, fixedCostBySearch, derivedCost;
    void cancelUntilBeginning(int begnning);
    void checkSolution();
    bool feasible;
    uint64_t infeasibleUB;
    bool findConflictSoftLits();
    vec2<Lit, vec<Lit> > conflictLits;
    void partition();
    void addConflictLit(Lit p, Lit q);
    Lit createHardClausesFromLits(vec<Lit>& lits);
    int simplelookahead();
    
    vec<int> softVarLocked;
    vec<int> inConflict;
    vec<int> unLockedVars;
    vec<int> unLockedVars_lim;
    int unLockedVarsRecord;
    //  uint64_t relaxedCost;

    void harden();
    vec<CRef> hardens;
    int hardenLevel;
    CRef lPropagate();
    unsigned int nbHardens;
    uint64_t fixedByHardens;
    vec<Var> unlockReason;
    bool constraintRelaxed;

    Var newAuxiVar(bool sign=false);
    void reduceHardens();
    int staticNbVars;
    bool dynVar(Var v);
    bool detectInitConflicts();
    vec<Var> dynVars;
    void collectDynVars();
    void cleanClausesForNewVars(vec<CRef>& cs);
    uint64_t initUB, initLB;
    int setCounter(CRef cr);
    int countCommunLiterals(CRef cr);
    void splitClauses(vec<CRef>& cs);
    void identifyClausesToSplit(vec<CRef>& cs);
    bool softLearnt;
    vec<CRef> softLearnts, hardLearnts;
    uint64_t nbSavedLits;

    uint64_t savedLOOKAHEAD, savednbLKsuccess;

    vec<int> inConflicts;
    vec2< Var, vec<int> > isets;
    vec2< int, vec<Lit> > isetsLits;
    void setConflict(int& nbIsets);
    void resetConflicts(int nbIsets);
    void copyInitConflicts(int& nbIsets);
    void simpleuncheckedEnqueueForLK(Lit p, CRef from=CRef_Undef);
    CRef simplepropagateForLK();
    void simplelookbackResetTrail(CRef confl, bool fromFalseVar);
    // vec<Var> unlockReasonForLK;
    int seeUnlockLits(int iset, int falseVar);
    int                 tier2_lbd_cut;
    
    int coreLimit, coreInactiveLimit, tier2Limit, tier2InactiveLimit;

    vec<int> finalIset, isetLock;
    bool isetLocked(int iset);

    inline int getIsetLock(int iset) { return  isetLock[finalIset[iset]];}
    inline void decrmentIsetLock(int iset) {isetLock[finalIset[iset]]--;}
    inline void incrementIsetLock(int iset) {isetLock[finalIset[iset]]++;}
    inline void setIsetLock(int iset, int lock) {isetLock[finalIset[iset]] = lock;}
    inline bool unLockedSoftVarForLK(Var v) {
      return (inConflicts[v] == NON || getIsetLock(inConflicts[v])==0);
    }
    inline int getLockedVarIsetForLK(Var v) {
      return finalIset[inConflicts[v]];
    }

    void getAllUIP(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);

    bool hardenEnable;

    Var simplePickAuxiVar();
    void moreHarden();

    uint64_t quasiSoftConflicts;
    
    void hardenFromQuasiSoftConflict(int trailRecord, int nbIsets);
    uint64_t fixedByQuasiConfl;
    void analyzeQuasiSoftConflict(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);

    void simplifyQuasiConflictClause(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);

    void addCardinalityConstraints();
    void addCardinalityConstraints(vec<Lit>& activeSoftLits, int k);
    
    vec<CRef> cardinalityC;
    vec<Var> dynVarsForCardinality;
    inline Var newAuxiVarForCardinality();

    int pureSoftConfl;

    vec<CRef> isetClauses;
    int lookaheadForRestart();
    int rootNbIsets;

    void hardenForRestart(int nbIsets, int trailRecord);
    void updateIsetLock(int savedFalseLits);

    double avgAct(vec<CRef>& cs, int& nb0);

    void resetConflicts_(int nbIsets);

    vec<Lit> allSoftLitsForCardC;

    void reduceClause(CRef cr, int pathC);
    void simplereduceClause(CRef cr, int pathC);
    int nbFlyReduced;

    void addCardinalityConstraintsMTO(vec<Lit>& activeSoftLits, int k);
    void nLevelsMTO(vec<Lit> & x, int lIndex, int m, vec<Lit> & result);

    inline bool bitIsSet(int x, int pos){
      return 1 & (x>>pos);
    }

    void fixByLookahead(vec<Lit>& out_learnt);
    uint64_t nbFixedByLH;
    CRef LHconfl;

    void simplelookback(CRef confl, Var falseVar, vec<Lit>& lits, vec<Lit>& out_learnt);

    struct VarOrderGt {
      const vec<double>&  activity;
      bool operator () (Var x, Var y) const { return activity[x] < activity[y]; }
    VarOrderGt(const vec<double>&  act) : activity(act) { }
    };

    Heap<VarOrderGt>    orderHeapAuxi;

    Lit binConfl[2];

    void  updateClauseUse(CRef confl);
    bool failedLiteralDetection();
    vec<Var> testedVars;

    vec<Lit> involvedLits;
    vec<char> involved;

    void cancelUntilTrailRecord1();
    /* void cancelUntilTrailRecord2(); */

    void cancelUntilTrailRecord2(Lit p, int& nbeq, int& nbSoftEq);
    vec<Lit> rpr;
    Lit getRpr(Lit p);
    int feasibleNbEq, nbEqUse, nbSoftEq;
    // void eliminateEqLit(vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);
    bool eliminateEqLit(CRef cr, Var v, Var targetV);
    bool eliminateEqLits_(int& debut);
    bool eliminateEqLits();
    bool moreEliminateEqLits();
    bool cleanClause(CRef cr);
    vec<Lit> equivLits;
    vec<Lit> tmpLits;
    vec<CRef> savedOriC;
    vec<CRef> shortens;
    bool eliminateEqLitFromOriC(CRef cr);
    void assignEquivLit(Lit q, lbool val);
    int prevEquivLitsNb, prevNbSoftEq;
    //  int64_t myDerivedCost;
    bool extendEquivLitValue(int debut, bool all);

    vec<Lit>   impliedLits;

    vec<CRef>         subsumptionQueue;
    // Temporaries:
    //
    CRef                bwdsub_tmpunit;

    struct ClauseDeleted {
      const ClauseAllocator& ca;
      explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
      bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; } };
    
    OccLists<Var, vec<CRef>, ClauseDeleted>
      occurIn;

    void removeClauseFromOccur(CRef dr, bool strict=false);
    void collectClauses(vec<CRef>& clauseSet, int learntType=CORE);
    bool simpleStrengthenClause(CRef cr, Lit l);
    bool subsumeClauses(CRef cr, int& subsumed, int& deleted_literals);
    bool backwardSubsume();
    void purgeClauses(vec<CRef>& cs);
    bool cleanClauseAnyWhere(CRef cr);

    
    uint64_t optimal;

    struct LocalAct {
      CRef cr;
      double act;
      //  LocalAct(CRef cr_, double act_) : cr(cr_), act(act_) {}
    };

    inline LocalAct mkLocalAct(CRef cr_, double act_) {LocalAct la; la={cr_, act_}; return la;}
    
    vec<LocalAct> localActivity;
    vec<int> localIndex;
    void sortClausesByVarActs(vec<CRef>& cs, vec<double>& activity, unsigned learntType);
    
    struct localAct_lt {
      //vec<int>& localIndex;
      vec<LocalAct>& localActivity;
    localAct_lt(vec<LocalAct>& localActivity_) : localActivity(localActivity_) {}
      bool operator () (int i, int j) const { return localActivity[i].act < localActivity[j].act; }
    };

    vec<Lit> savedClauseLits, savedAllSoftLitsForCardC, savedAllSoftLits;
    int nbCompSoftLitPairs;

    //   inline Lit simplesubsume(const Clause& c, const Clause& d);
    inline Lit subsume(const Clause& c, const Clause& d);

    uint64_t sbsmTtlg, sbsmAbsFail, allsbsm, smeq, s_ticks;
    double totalsbsmTime, totalFLtime, totalelimTime;

    bool backwardSubsumeAndEliminateEqLits();

    vec<char> savedDecision;

    //inpreprocessing variable elimination
    bool eliminate(bool checkOcc=true);
    bool eliminate_();
    bool eliminateVar(Var v, int& savedTrailSize);
    void buildElimHeap();
    /* struct ElimLt { */
    /*   const vec<int>& n_occ; */
    /*   explicit ElimLt(const vec<int>& no) : n_occ(no) {} */
      
    /*   // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating */
    /*   // 32-bit implementation instead then, but this will have to do for now. */
    /*   uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; } */
    /*   bool operator()(Var x, Var y) const { return cost(x) < cost(y); } */
    /* }; */

    struct ElimLt {
      const vec<double>& activity;
      explicit ElimLt(const vec<double>& act) : activity(act) {}
      
      /* // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating */
      /* // 32-bit implementation instead then, but this will have to do for now. */
      /* uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; } */
      bool operator()(Var x, Var y) const { return activity[x] < activity[y]; }
    };

    /* struct ElimLt { */
    /*   const vec<double>& activity; */
    /*   const vec<int>& n_occ; */
    /*   explicit ElimLt(const vec<double>& act, const vec<int>& no) : activity(act), n_occ(no) {} */
    /*   // explicit ElimLt(const vec<double>& act) : activity(act) {} */
      
    /*   /\* // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating *\/ */
    /*   /\* // 32-bit implementation instead then, but this will have to do for now. *\/ */
    /*   //uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; } *\/ */
    /*    bool operator()(Var x, Var y) const { return (activity[x] < activity[y]) || */
    /* 	   (activity[x] == activity[y] && */
    /* 	    (( (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]) < */
    /* 	     ( (uint64_t)n_occ[toInt(mkLit(y))] * (uint64_t)n_occ[toInt(~mkLit(y))]))); } */
    /*   //bool operator()(Var x, Var y) const { return (activity[x] < activity[y]);} */
    /* }; */
    
    vec<double> curr_activity;

    vec<bool>           touched, eliminated;
    vec<Var>            touchedVars;
    vec<Var>            eliminatedVars;
    vec<int>            n_occ;
    Heap<ElimLt>        elim_heap;
    // vec<Lit>           elimclauses;
    vec<uint32_t>      elimclauses;
    vec<bool>          frozen;
    int                 grow;
    int clause_limit;
    void collectOriginalClauses(vec<CRef>& clauseSet);
    static void storeElimClause(vec<Lit>& elimclauses, Var v, Clause& c);
    bool merge(const Clause& _ps, const Clause& _qs, Var v, int& size);
    bool merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    void removeClauseForElim(CRef cr);
    static void mkElimClause(vec<uint32_t>& elimclauses, Lit x);
    static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c);
    void extendModel();
    bool addClauseByResolution(vec<Lit>& ps, int lbd=0);
    void gatherTouchedClauses();
    //    void eliminateLearntClausesContainingElimVar(vec<CRef>& learnts);
    bool isEliminated(Var v);
    void updateElimHeap(Var v);
    void checkGarbageForElimVars();
    int initTrail;

    vec<CRef> resolvents;
    bool simplifyResolvents();
    vec<int> litTrail;

    bool myAddClause_(vec<Lit>& ps, CRef& cr, int lbd=0);

    int nbUnitResolv=0, nbUnitViviResolv=0, shortened = 0, nbSimplifing = 0, nbRemovedLits=0, nbAllResolvs=0;
    uint64_t saved_s_up=0;

    int nbRemovedClausesByElim=0, nbSavedResolv=0, nb1stClauseSimp=0;
    
    int nbLearntResolvs=0, nb1stClauseSimpL=0, nbSavedResolvL=0, sbsmRslv, delLitRslv;

    void collectLocalClauses(vec<CRef>& clauseSet);
    OccLists<Var, vec<CRef>, ClauseDeleted>
      occurInLocal;

    void cancelUntilRecord(int record);
    bool propagateClauseAndAnalyze0(CRef cr, Var v, vec<Lit>& propagatedLits);
    bool propagateClauseAndAnalyze1(CRef cr, Var v, vec<Lit>& propagatedLits, bool& ttlg);
    //    bool cancelAndPropagateLitClause(Lit p, CRef cr, Var v, vec<Lit>& resolvent);
    bool crossResolvents(vec<CRef>& pos, vec<CRef>& neg, Var v);

    void simpleAnalyzeForElim(CRef confl, vec<Lit>& out_learnt, bool True_confl);
    bool crossResolventsL(vec<CRef>& posL, vec<CRef>& negL, Var v);
    //   bool elimEqBackWardSubsume();
    bool isSubsumed(vec<Lit>& resolvent, bool learnt=false);
    bool isSubsumed(CRef dr);
    int realNbVars, oriNbVars;
    //   int smeq=0;
    bool simplesubsumeClauses(CRef cr, int& subsumed, int& deleted_literals);
    bool simplebackwardSubsume_(int& savedTrailSize, bool verbose=true);
    Lit simplesubsume(const Clause& c, const Clause& d);

    void simplifyLearnt(Clause& c);

    int initNbEliminatedVars, initNbElimclauses, initNbEquivLits;
    int   initFeasibleNbEq, initPrevEquivLitsNb, //initMyDerivedCost,
      initNbSoftEq,
      initPrevNbSoftEq;

    int nbSatLits;
    bool initialization();

    void simpleSortClausesByVarActs(vec<CRef>& cs, vec<double>& activity, unsigned learntType);

    struct localAct_gt {
      //vec<int>& localIndex;
      vec<LocalAct>& localActivity;
    localAct_gt(vec<LocalAct>& localActivity_) : localActivity(localActivity_) {}
      bool operator () (int i, int j) const { return localActivity[i].act > localActivity[j].act; }
    };

    int nbOriClsLits, previousTrail;
    void checkOccV(Var v);
};



//=================================================================================================
// Implementation of inline methods:

  inline Lit Solver::simplesubsume(const Clause& c, const Clause& d) {
    allsbsm++;
   if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) !=0))
      return lit_Error;
   Lit ret = lit_Undef;
   counter++;
   for(int i=0; i<d.size(); i++)
     seen2[toInt(d[i])]=counter;
   
   for(int i=0; i<c.size(); i++) {
     if (seen2[toInt(~c[i])] == counter) {
       if (ret == lit_Undef)
	 ret = c[i];
       else {
	 sbsmTtlg++;
	 return lit_Error;
       }
     }
     else if (seen2[toInt(c[i])] != counter) {
       sbsmAbsFail++;
       return lit_Error;
     }
   }
   return ret;
 }

  inline Lit Solver::subsume(const Clause& c, const Clause& d) {
   if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) !=0))
      return lit_Error;
   Lit ret = lit_Undef;
   
   allsbsm++;
   counter++;
   for(int i=0; i<d.size(); i++)
     seen2[toInt(d[i])]=counter;
   
   for(int i=0; i<c.size(); i++) {
     if (seen2[toInt(~c[i])] == counter) {
       if (ret == lit_Undef)
 	 ret = c[i];
       else {
	 sbsmTtlg++;
 	 if (d.size()==2) {
 	   assert(c.size() == 2);
 	   Lit p=getRpr(d[0]);
 	   Lit q=getRpr(d[1]);
 	   if (var(p) != var(q)) {

	     if (auxiVar(var(q)) && !auxiVar(var(p))) {
	       Lit r=p; p=q; q=r;
	     }
	     smeq++; feasibleNbEq++;
 	     rpr[toInt(q)] = ~p;
 	     rpr[toInt(~q)] = p;
	     if (auxiVar(var(p)) && auxiVar(var(q)))
	       nbSoftEq++;
	     // printf("c smeq\n");
	     // if (auxiVar(var(p)) && auxiVar(var(q)))
	     //  myNbSoftEq++;

	     /* if (drup_file) { */
	     /*   vec<Lit> lits; */
	     /*   lits.push(p); lits.push(q); */
	     /*   writeClause2drup('a', lits, drup_file); */
	     /*   lits[0] = ~p; lits[1] = ~q; */
	     /*   writeClause2drup('a', lits, drup_file); */
	     /* } */

	     /* if (drup_file && (p != d[0] || q != d[1])) { */
	     /*   vec<Lit> lits1, lits2; */
	     /*   lits1.push(~q), lits1.push(~p);  lits2.push(q), lits2.push(p); */
	     /*   writeClause2drup('a', lits1, drup_file); */
	     /*   writeClause2drup('a', lits2, drup_file); */
	     /* } */
	     
	     /* 	if (equivLits.size() == 2798) */
	     /* 	  printf("&&&&&&&& "); */
	     
 	     equivLits.push(q);
 	   }
 	 }
 	 return lit_Error;
       }
     }
     else if (seen2[toInt(c[i])] != counter) {
       sbsmAbsFail++;
       return lit_Error;
     }
   }
   return ret;
 }

   inline void Solver::updateElimHeap(Var v) {
    // if (!frozen[v] && !isEliminated(v) && value(v) == l_Undef)
     if (elim_heap.inHeap(v) || (!auxiVar(v) && !isEliminated(v) && value(v) == l_Undef && !dynVar(v)))
        elim_heap.update(v); }

   inline bool Solver::isEliminated(Var v) {return eliminated[v];}

 inline bool Solver::dynVar(Var v) {return v >= staticNbVars;}

 inline bool Solver::auxiVar(Var v) {return softLits[v] != lit_Undef;} //{return v >= nbOrignalVars;}

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline int  Solver::level (Var x) const { return vardata[x].level; }

inline void Solver::insertVarOrder(Var x) {
  //  Heap<VarOrderLt>& order_heap =  DISTANCE ? order_heap_distance : (VSIDS ? order_heap_VSIDS : order_heap_CHB);
  Heap<VarOrderLt>& order_heap =  VSIDS ? order_heap_VSIDS : order_heap_CHB;
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() {
    var_inc *= (1 / var_decay); }

inline void Solver::varBumpActivity(Var v, double mult) {
    if ( (activity_VSIDS[v] += var_inc * mult) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity_VSIDS[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap_VSIDS.inHeap(v)) order_heap_VSIDS.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts_local.size(); i++)
                ca[learnts_local[i]].activity() *= 1e-20;
	    
	    for (int i = 0; i < learnts_core.size(); i++)
                ca[learnts_core[i]].activity() *= 1e-20;
	    
	    for (int i = 0; i < learnts_tier2.size(); i++)
                ca[learnts_tier2[i]].activity() *= 1e-20;
	    
	    for (int i = 0; i < cardinalityC.size(); i++)
                ca[cardinalityC[i]].activity() *= 1e-20;

	    for(int i=0; i<isetClauses.size(); i++)
	     ca[isetClauses[i]].activity() *= 1e-20;

	    for(int i=0; i<hardens.size(); i++)
	      ca[hardens[i]].activity() *= 1e-20;
	    
            cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver::locked          (const Clause& c) const {
    int i = c.size() != 2 ? 0 : (value(c[0]) == l_True ? 0 : 1);
    return value(c[i]) == l_True && reason(var(c[i])) != CRef_Undef && ca.lea(reason(var(c[i]))) == &c;
}
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts_core.size() + learnts_tier2.size() + learnts_local.size(); }
inline int      Solver::nVars         ()      const   { return vardata.size(); }
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver::setDecisionVar(Var v, bool b) 
{ 
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    if (b && !order_heap_CHB.inHeap(v)){
        order_heap_CHB.insert(v);
        order_heap_VSIDS.insert(v); 
	//	order_heap_distance.insert(v);
    }
    if (!orderHeapAuxi.inHeap(v))
      orderHeapAuxi.insert(v);
}
inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver::withinBudget() const {
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }


//=================================================================================================
// Debug etc:


//=================================================================================================
}

#endif
