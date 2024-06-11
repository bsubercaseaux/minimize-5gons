#include "core/Solver.h"
#include "mtl/Sort.h"
#include "utils/System.h"

using namespace Minisat;


// test if resolvent is subsumed by an existing clause
bool Solver::isSubsumed(vec<Lit>& resolvent, bool learnt) {
  uint32_t abstraction = 0;
  Var best = var(resolvent[0]);
  counter++;
  seen2[toInt(resolvent[0])]=counter;
  abstraction |= 1 << (var(resolvent[0]) & 31);
  
  for (int i = 1; i < resolvent.size(); i++) {
    Lit lit=resolvent[i];
    if (occurIn[var(lit)].size() < occurIn[best].size())
      best = var(lit);
    abstraction |= 1 << (var(lit) & 31);
    seen2[toInt(lit)]=counter;
  }
 
  vec<CRef>& cs = occurIn[best];
  int j;
  for (j = 0; j < cs.size(); j++) {
    CRef cr=cs[j];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    if ((!learnt && c.learnt()) ||
	(c.size() > resolvent.size()) ||
	((c.abstraction() & (~abstraction)) !=0))
      continue;
    Lit ret = lit_Undef;
    for(int i=0; i<c.size(); i++) {
      //if (seen2[toInt(~c[i])] == counter) {
      // 	if (ret == lit_Undef)
      // 	  ret = c[i];
      // 	else {
      // 	  // sbsmTtlg++;
      // 	  ret = lit_Error;
      // 	  break;
      // 	}
      // }
      // else
      if (seen2[toInt(c[i])] != counter) {
	//sbsmAbsFail++;
	ret = lit_Error;
	break;
      }
    }
    if (ret == lit_Undef) {
      // if (!learnt && c.learnt()) {
      // 	continue;
      // 	// if (resolvent.size() > c.size()) {
      // 	//   for(int k=0; k<c.size(); k++)
      // 	//     resolvent[k]=c[k];
      // 	//   resolvent.shrink(resolvent.size() - c.size());
      // 	//   // abstraction = 0; counter++;
      // 	//   // for (int i = 0; i < resolvent.size(); i++) {
      // 	//   //   Lit lit=resolvent[i];
      // 	//   //   abstraction |= 1 << (var(lit) & 31);
      // 	//   //   seen2[toInt(lit)]=counter;
      // 	//   // }
      // 	// }
      // 	// removeClause(cr);  removeClauseFromOccur(cr, true);
      // 	// return false;
      // }
      // else {
	sbsmRslv++;
	return true;
	// }
    }
    // else if (ret != lit_Error) {
    //   delLitRslv++;
    //   remove(resolvent, ~ret);
    //   if (resolvent.size() == 1)
    // 	return false;
    //   abstraction = 0; counter++;
    //   for (int i = 0; i < resolvent.size(); i++) {
    // 	Lit lit=resolvent[i];
    // 	abstraction |= 1 << (var(lit) & 31);
    // 	seen2[toInt(lit)]=counter;
    //   }
    // }
  }
  return false;
}

void Solver::gatherTouchedClauses() {
  
    if (touchedVars.size() == 0) return;

    int i,j;
    for (i = j = 0; i < subsumptionQueue.size(); i++) {
      assert(!ca[subsumptionQueue[i]].seen()); // && !ca[subsumptionQueue[i]].learnt())
	ca[subsumptionQueue[i]].seen(true);
    }

    for (i = 0; i < touchedVars.size(); i++) {
      Var v=touchedVars[i];
      const vec<CRef>& cs = occurIn.lookup(v);
      for (j = 0; j < cs.size(); j++)
	if (!ca[cs[j]].seen()) { //&& !ca[cs[j]].learnt()){
	  subsumptionQueue.push(cs[j]);
	  ca[cs[j]].seen(true);
	}
      touched[v] = 0;
    }
    touchedVars.clear();

    for (i = 0; i < subsumptionQueue.size(); i++)
      if (ca[subsumptionQueue[i]].seen()) // && !ca[subsumptionQueue[i]].learnt())
            ca[subsumptionQueue[i]].seen(false);
}

template<class Lits>
void printClause(Lits& ps) {
  for (int i = 0; i < ps.size(); i++)
    printf("%i ", (var(ps[i])) * (-2 * sign(ps[i]) + 1));
  printf("\n");
}

bool Solver::myAddClause_(vec<Lit>& ps, CRef& cr, int lbd) {
  cr = CRef_Undef;
  
  // if (drup_file){
  //   writeClause2drup('a', ps, drup_file);
  // }
  if (ps.size() == 0)
    return false;
  else if (ps.size() == 1){
    uncheckedEnqueue(ps[0]);
    return (propagate() == CRef_Undef && !softConflictFlag);
  }else{
    cr = ca.alloc(ps, lbd>0);
    if (lbd>0) {
      ca[cr].set_lbd(lbd);
      if (lbd <= core_lbd_cut){
	learnts_core.push(cr);
	ca[cr].mark(CORE);
      }else if (lbd <= tier2_lbd_cut){
	learnts_tier2.push(cr);
	ca[cr].mark(TIER2);
	ca[cr].touched() = conflicts;
      }else{
	learnts_local.push(cr);
	claBumpActivity(ca[cr]);
      }
    }
    else 
      clauses.push(cr);
    attachClause(cr);
  }
  return true;
}

// lbd>0 means that this is a learnt clause with lbd
bool Solver::addClauseByResolution(vec<Lit>& ps, int lbd) {
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    if (ps.size() > 1) {
      if (isSubsumed(ps, lbd>0))
	return true;
    }
    
    int savedTrail=trail.size();
    CRef cr;
    if (!myAddClause_(ps, cr, lbd))
        return false;
    if (trail.size() - savedTrail > 0) {
      nbUnitResolv++;
      //printf("**** unit clause produced by resolution****\n");
      //printClause(ps);
    }
    if (cr != CRef_Undef){
      const Clause& c  = ca[cr];
      // NOTE: the clause is added to the queue immediately and then
      // again during 'gatherTouchedClauses()'. If nothing happens
      // in between, it will only be checked once. Otherwise, it may
      // be checked twice unnecessarily. This is an unfortunate
      // consequence of how backward subsumption is used to mimic
      // forward subsumption.
      if (lbd > 0)
	nbLearntResolvs++;
      else
	nbAllResolvs++;
      if (lbd<=tier2_lbd_cut) {
	resolvents.push(cr);  subsumptionQueue.push(cr);
	for (int i = 0; i < c.size(); i++){
	  occurIn[var(c[i])].push(cr);
	  if (lbd==0)
	    n_occ[toInt(c[i])]++;
	  litTrail[toInt(~c[i])] = trail.size();
	  if (touched[var(c[i])] == 0) {
	    touched[var(c[i])] = 1;
	    touchedVars.push(var(c[i]));
	  }
	  if (lbd==0 && elim_heap.inHeap(var(c[i])))
	    elim_heap.increase(var(c[i]));
	}
      }
      else
	for (int i = 0; i < c.size(); i++){
	  occurInLocal[var(c[i])].push(cr);
	}
    }
    return true;
}

void Solver::mkElimClause(vec<uint32_t>& elimclauses, Lit x)
{
    elimclauses.push(toInt(x));
    elimclauses.push(1);
}


void Solver::mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
{
    int first = elimclauses.size();
    int v_pos = -1;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for (int i = 0; i < c.size(); i++){
        elimclauses.push(toInt(c[i]));
        if (var(c[i]) == v)
            v_pos = i + first;
    }
    assert(v_pos != -1);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    uint32_t tmp = elimclauses[v_pos];
    elimclauses[v_pos] = elimclauses[first];
    elimclauses[first] = tmp;

    // Store the length of the clause last:
    elimclauses.push(c.size());
}

void Solver::extendModel()
{
    int i, j;
    Lit x;

    for(i=0; i<eliminatedVars.size(); i++)
      assigns[eliminatedVars[i]] = l_Undef;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
	  if (value(getRpr(toLit(elimclauses[i]))) != l_False)
                goto next;

	//  x = toLit(elimclauses[i]);
	x = getRpr(toLit(elimclauses[i]));
        //model[var(x)] = lbool(!sign(x));
	assigns[var(x)] = lbool(!sign(x));
    next:;
    }
}

void Solver::removeClauseForElim(CRef cr)
{
    const Clause& c = ca[cr];

    if (c.learnt())
      for (int i = 0; i < c.size(); i++){
	occurIn.smudge(var(c[i]));
      }
    else
      for (int i = 0; i < c.size(); i++){
	n_occ[toInt(c[i])]--;
	updateElimHeap(var(c[i]));
	occurIn.smudge(var(c[i]));
      }
    if (!removed(cr))
      removeClause(cr);
}

// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool Solver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    out_clause.clear();
    assert(!_ps.learnt() && !_qs.learnt());

    counter++;
    for (int i = 0; i < _ps.size(); i++) {
      if (var(_ps[i]) != v) {
	if (value(_ps[i]) == l_True)
	  return false;
	else if (value(_ps[i]) != l_False) {
	  seen2[toInt(_ps[i])] = counter;
	  out_clause.push(_ps[i]);
	}
      }
    }
    for (int i = 0; i < _qs.size(); i++){
      if (var(_qs[i]) != v) {
	if (value(_qs[i]) == l_True)
	  return false;
	else if (value(_qs[i]) != l_False) {
	  if (seen2[toInt(~_qs[i])] == counter)
	    return false;
	  else if (seen2[toInt(_qs[i])] != counter)
	    out_clause.push(_qs[i]);
	}
      }
    }
    return true;
}

// Returns FALSE if clause is always satisfied.
bool Solver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size) {
  assert(!_ps.learnt() && !_qs.learnt());
  size=0;
  counter++;
  for (int i = 0; i < _ps.size(); i++) {
    if (var(_ps[i]) != v) {
      if (value(_ps[i]) == l_True)
	return false;
      else if (value(_ps[i]) != l_False) {
	seen2[toInt(_ps[i])] = counter;
	size++;
      }
    }
  }
  for (int i = 0; i < _qs.size(); i++){
    if (var(_qs[i]) != v) {
      if (value(_qs[i]) == l_True)
	return false;
      else if (value(_qs[i]) != l_False) {
	if (seen2[toInt(~_qs[i])] == counter)
	  return false;
	else if (seen2[toInt(_qs[i])] != counter)
	  size++;
      }
    }
  }
  return true;
}

// void Solver::storeElimClause(vec<Lit>& elimclauses, Var v, Clause& c)
// {
//   elimclauses.push(lit_Undef);
//   int first = elimclauses.size();
//   int v_pos = -1;
  
//   // Copy clause to elimclauses-vector. Remember position where the
//   // variable 'v' occurs:
//   for (int i = 0; i < c.size(); i++){
//     if (var(c[i]) == v)
//       v_pos = elimclauses.size();
//     elimclauses.push(c[i]);
//   }
//   assert(v_pos != -1);
  
//   // Swap the first literal with the 'v' literal, so that the literal
//   // containing 'v' will occur first in elimClauses for the clause:
//   Lit tmp = elimclauses[v_pos];
//   elimclauses[v_pos] = elimclauses[first];
//   elimclauses[first] = tmp;
// }

bool Solver::cleanClauseAnyWhere(CRef cr) {
  if (removed(cr))
    return false;
  bool sat=false, false_lit=false;
  Clause& c=ca[cr];
  for (int i = 0; i < c.size(); i++){
    if (value(c[i]) == l_True && level(var(c[i]))==0){
      sat = true;
      break;
    }
    else if (value(c[i]) == l_False && level(var(c[i])) == 0){
      false_lit = true;
    }
  }
  if (sat){
    removeClause(cr);
    return false;
  }
  else{
    if (false_lit){
      // vec<Lit> myadd_oc;
      // if (drup_file) {
      // 	for(int k=0; k<c.size(); k++)
      // 	  myadd_oc.push(c[k]);
      // }
      
      int li, lj;
      for (li = lj = 0; li < c.size(); li++){
	if (value(c[li]) != l_False || level(var(c[li])) > 0){
	  c[lj++] = c[li];
	}
	else assert(li>1);
      }
      if (lj==2) {
	assert(li>2);
	detachClause(cr, true);
	c.shrink(li - lj);
	attachClause(cr);
      }
      else {
	assert(lj>2);
	c.shrink(li - lj);
      }
      c.calcAbstraction();

      // if (drup_file) {
      // 	writeClause2drup('a', c, drup_file);
      // 	writeClause2drup('d', myadd_oc, drup_file);
      // }
      
    }
    return true;
  }
}

void Solver::cancelUntilRecord(int record) {
    for (int c = trail.size() - 1; c >= trailRecord; c--)
    {
        Var x = var(trail[c]);
        assigns[x] = l_Undef;
        
    }
    qhead = trailRecord;
    trail.shrink(trail.size() - trailRecord);
    falseLits.shrink(falseLits.size() - falseLitsRecord);

    for(int c = unLockedVars.size()-1; c >= 0; c--) {
      Var x = unLockedVars[c];
      incrementIsetLock(inConflicts[x]);
    }
    unLockedVars.shrink(unLockedVars.size());
    assert(trail.size() == 0 || level(var(trail.last())) == 0);
}

void Solver::simpleAnalyzeForElim(CRef confl, vec<Lit>& out_learnt, bool True_confl) {
  if (confl != CRef_Undef)
    simpleAnalyze(confl, out_learnt, True_confl, false);
  else {
    assert(softConflictFlag);
    simpleAnalyzeSoftConflict(out_learnt);
  }
}

// lits stores the simplified clause when it returns false.
bool Solver::propagateClauseAndAnalyze0(CRef cr, Var v, vec<Lit>& propagatedLits) {
  bool True_confl = false;
  CRef confl=CRef_Undef;
  Lit trueLit, vLit=lit_Undef;
  int i;
  Clause& c=ca[cr];
  vec<Lit> lits;
  lits.clear();
  for(int i=0; i<c.size(); i++) {
    if (var(c[i]) == v)
      vLit=c[i];
    else
      lits.push(c[i]);
  }
  assert(vLit != lit_Undef);
  propagatedLits.clear();
  for (i = 0; i < lits.size(); i++){
    if (value(lits[i]) == l_Undef) {
      simpleUncheckEnqueue(~lits[i]);
      confl = simplePropagate();
      if (confl != CRef_Undef  || softConflictFlag)
	break;
      propagatedLits.push(lits[i]);
    }
    else if (value(lits[i]) == l_True){
      assert(reason(var(lits[i])) != CRef_Undef);
      trueLit = lits[i];
      True_confl = true;
      confl = reason(var(trueLit));
      break;
    }
  }
  if (confl != CRef_Undef || True_confl || softConflictFlag){
    // simp_learnt_clause.clear();
    propagatedLits.clear();
    //   simp_reason_clause.clear();
    if (True_confl)
      propagatedLits.push(trueLit);
    // simpleAnalyze(confl, propagatedLits, simp_reason_clause, True_confl);
    simpleAnalyzeForElim(confl, propagatedLits, True_confl);
    return false;
  }
  assert(value(vLit) == l_True);
  return true;//all lits have been propagated except vLit that has been forced to be true
}

// lits stores the simplified clause when it returns false.
bool Solver::propagateClauseAndAnalyze1(CRef cr, Var v, vec<Lit>& propagatedLits, bool& ttlg) {
  bool True_confl = false;
  CRef confl=CRef_Undef;
  Lit trueLit=lit_Undef, vLit=lit_Undef;
  Clause& c=ca[cr];
  propagatedLits.clear(); ttlg=false;
  for(int i=0; i<c.size(); i++) {
    if (var(c[i]) == v)
      vLit=c[i];
    else if (value(c[i]) == l_True) {
      if (reason(var(c[i])) == CRef_Undef) {
	ttlg=true;
	break;
      }
      else if (!True_confl) {
	True_confl = true;
	trueLit = c[i];
	confl=reason(var(trueLit));
      }
    }
    else if (value(c[i]) == l_Undef)
      propagatedLits.push(c[i]);
  }

  if (!ttlg) {  
    assert(vLit != lit_Undef);
    assert(value(vLit) == l_False);
  }

  if (ttlg) {
    return true;
  }
  else if (True_confl) {
    assert(confl != CRef_Undef && trueLit != lit_Undef);
    propagatedLits.clear();
    propagatedLits.push(trueLit);
    simpleAnalyzeForElim(confl, propagatedLits, True_confl);
    return false;
  }
  else 
    return true;
}

struct clauseSize_lt {
    ClauseAllocator& ca;
    clauseSize_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {

      return ca[x].size() < ca[y].size();
    }
};

struct clauseLBDsize_lt {
    ClauseAllocator& ca;
    clauseLBDsize_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
      return (ca[x].lbd() < ca[y].lbd()) ||
	(ca[x].lbd() == ca[y].lbd() && ca[x].size() < ca[y].size());
    }
};

// // if return false and ok is also false, then the instance is unsatisfiable
// // if returns false but ok is true, then resolvent is a simplified clause
// // if returns true and cr is removed, then cr need not to be considered agin
// // if returns true and cr is not removed, then all lits in cr have been propagated.
// bool Solver::cancelAndPropagateLitClause(Lit p, CRef cr, Var v, vec<Lit>& resolvent) {
//   cancelUntilRecord(trailRecord);
//   assert(value(p) == l_Undef);
//   uncheckedEnqueue(p);
//   if (propagate() != CRef_Undef || softConflictFlag){
//     ok = false;
//     return false;
//   }
//   trailRecord = trail.size();
//   resolvent.clear();
//   if (cleanClauseAnyWhere(cr)) {
//     return propagateClauseAndAnalyze0(cr, v, resolvent);
//   }
//   else
//     return true;
// }

// void Solver:: getWatchedLits(vec<Lit>& resolvent) {
//   int j; // the first false lit in resolvent
//   if (value(resolvent[0]) != l_False) {
//     if (value(resolvent[1]) != l_False)
//       return;
//     else j=1;
//   }
//   else if (value(resolvent[1]) != l_False) {
//     Lit tmp=resolvent[1];
//     resolvent[1] = resolvent[0];
//     resolvent[0] = tmp; j=1;
//   }
//   else j=0;
			  
//   for(int i=j+1; i<resolvent.size(); i++) {
//     if (value(resolvent[i]) != l_False) {
//       Lit tmp=resolvent[i];
//       resolvent[i] = resolvent[j];
//       resolvent[j] = tmp;
//       if (++j > 1)
// 	return;
//     }
//   }
// }

//#define printResolvent

// Produce clauses in cross product of neg and pos containing v to eliminate v
bool Solver::crossResolvents(vec<CRef>& pos, vec<CRef>& neg, Var v) {
  vec<CRef>& small = pos.size() < neg.size() ? pos : neg;
  vec<CRef>& great = pos.size() < neg.size() ? neg : pos;
  vec<Lit> resolvent1, resolvent2;
  
  if (small.size() == 0)
    return true;
  // if (v==1877)
  //   printf("dsfs ");
  
  sort(small, clauseSize_lt(ca)); sort(great, clauseSize_lt(ca)); 
  assert(subsumptionQueue.size()==0);
  for (int i = 0; i < small.size(); i++) {
    trailRecord=trail.size(); falseLitsRecord=falseLits.size();
    if (value(v) != l_Undef)
      return true;
    CRef cr=small[i];
    if (!cleanClauseAnyWhere(cr))
      continue;
#ifdef printResolvent
    printf("\nc small(%d/%d), with v=%d: ", i, small.size(), v); printClause(ca[cr]);
    printf("-------------------------------------------\n");
#endif
    if (propagateClauseAndAnalyze0(cr, v, resolvent1)) {
      // the lits in cr have been negatively propagated normally
      assert(resolvent1.size() > 0);
      for (int j = 0; j < great.size(); j++) {
	CRef dr = great[j];
	if (cleanClauseAnyWhere(dr)) {
#ifdef printResolvent
	  printf("\nc great(%d/%d): ", j, great.size()); printClause(ca[dr]);
#endif
	  bool ttlg;
	  bool res=propagateClauseAndAnalyze1(dr, v, resolvent2, ttlg);
	  if (res) {
	    if (ttlg) {
#ifdef printResolvent
	      printf("c tautology resolvent \n");
#endif    
	      continue;
	    }
	    else {
	      // resolvent2 contains at least two free lits, otherwise
	      // the only free lit would be satisfied
	      assert(resolvent2.size() > 1);
	      for(int aa=0; aa<resolvent1.size(); aa++)
		resolvent2.push(resolvent1[aa]);
#ifdef printResolvent
	      printf("c resolvent from dr and cr: "); printClause(resolvent2);
#endif
	      bool added = addClauseByResolution(resolvent2);
	      assert(added);
	    }
	  }
	  else {
	    //resolvent2 contains the clause obtained from a true conflict of cr and dr
	    // a lit of dr is assigned true when propagating ~cr
	    assert(resolvent2.size() > 1);
#ifdef printResolvent
	    printf("c resolvent from a true conflict of cr and dr: ");
	    printClause(resolvent2);
#endif  
	    bool added = addClauseByResolution(resolvent2);
	    assert(added);
	  }
	}
      }
      cancelUntilRecord(trailRecord);
    }
    else {
      //resolvent1 contains a simplified clause obtained from propagating ~cr
      cancelUntilRecord(trailRecord);
#ifdef printResolvent
      printf("c resolvent from cr: "); printClause(resolvent1);
#endif
      nb1stClauseSimp++; nbSavedResolv += great.size();

      if (!addClauseByResolution(resolvent1))
	return false;
      removeClause(cr);
    }
  }
  trailRecord=trail.size(); falseLitsRecord=falseLits.size();
  return true;
}

#define learntLimit 40
//#define printResolventL

// Produce clauses in cross product of neg and pos containing v to eliminate v
bool Solver::crossResolventsL(vec<CRef>& posL, vec<CRef>& negL, Var v) {
  if (value(v) != l_Undef || posL.size() == 0 | negL.size()==0)
    return true;
  //  add_tmp.clear();
  sort(posL, clauseLBDsize_lt(ca)); sort(negL, clauseLBDsize_lt(ca));
  vec<CRef>& small = posL.size() < negL.size() ? posL : negL;
  vec<CRef>& great = posL.size() < negL.size() ? negL : posL;
  vec<Lit> resolvent1, resolvent2;
  int limitS=small.size() < learntLimit ? small.size() : learntLimit;
  int limitG=great.size() < learntLimit ? great.size() : learntLimit;

  // if (v==1877)
  //   printf("dsfs ");
  // assert(subsumptionQueue.size()==0);
  for (int i = 0; i < limitS; i++) {
    trailRecord=trail.size();  falseLitsRecord=falseLits.size();
    if (value(v) != l_Undef)
      return true;
    CRef cr=small[i];
    if (!cleanClauseAnyWhere(cr))
      continue;
#ifdef printResolventL
    printf("\nc small(%d/%d), (%d, %d)), with v=%d: ",
	   i, small.size(), ca[cr].lbd(), ca[cr].size(), v);
    printClause(ca[cr]);
    printf("-------------------------------------------\n");
#endif
    if (propagateClauseAndAnalyze0(cr, v, resolvent1)) {
      // the lits in cr have been negatively propagated normally
      assert(resolvent1.size() > 0);
      for (int j = 0; j < limitG; j++) {
	CRef dr = great[j];
	if (cleanClauseAnyWhere(dr)) {
#ifdef printResolventL
	  printf("\nc great(%d/%d), (%d, %d)): ", j, great.size(), ca[dr].lbd(), ca[dr].size());
	  printClause(ca[dr]);
#endif
	  bool ttlg;
	  bool res=propagateClauseAndAnalyze1(dr, v, resolvent2, ttlg);
	  if (res) {
	    if (ttlg) {
#ifdef printResolventL
	      printf("c tautology resolvent \n");
#endif    
	      continue;
	    }
	    else {
	      // resolvent2 contains at least two free lits, otherwise
	      // the only free lit would be satisfied
	      assert(resolvent2.size() > 1);
	      int resLength=resolvent2.size() + resolvent1.size();
	      int sumlbd = ca[dr].lbd() + ca[cr].lbd() - 1;
	      int newlbd = resLength-1 < sumlbd ? resLength-1 : sumlbd;
	      int maxLength = (ca[dr].size() > ca[cr].size()) ? ca[dr].size() : ca[cr].size();
	      if (newlbd <= 6 &&
		  ((resLength <= maxLength) ||
		   (resLength <= clause_limit))) {
		for(int aa=0; aa<resolvent1.size(); aa++)
		  resolvent2.push(resolvent1[aa]);
#ifdef printResolventL
		printf("c resolvent(lbd %d, size %d) from dr and cr: ", newlbd, resolvent2.size());
		printClause(resolvent2);
#endif
		bool added = addClauseByResolution(resolvent2, newlbd);
		assert(added);
	      }
#ifdef printResolventL
	      else printf("c toooo long resolvent (%d, %d+%d) from cr and dr:\n",
			  newlbd, resolvent1.size(), resolvent2.size());
#endif      
	    }
	  }
	  else {
	    //resolvent2 contains the clause obtained from a true conflict of cr and dr
	    // a lit of dr is assigned true when propagating ~cr
	    assert(resolvent2.size() > 1);
	    int newlbd = resolvent2.size()-1 < ca[cr].lbd() ? resolvent2.size()-1 : ca[cr].lbd();
#ifdef printResolventL
	    printf("c resolvent (%d %d) from a true conflict of cr and dr: ",
		   newlbd, resolvent2.size());
	    printClause(resolvent2);
#endif
	    
	    bool added = addClauseByResolution(resolvent2, newlbd);
	    assert(added);
	  }
	}
      }
      cancelUntilRecord(trailRecord);
    }
    else {
      //resolvent1 contains a simplified clause obtained from propagating ~cr
      cancelUntilRecord(trailRecord);
      int newlbd = ca[cr].lbd() < resolvent1.size()-1 ? ca[cr].lbd() : resolvent1.size()-1;
#ifdef printResolventL
      printf("c resolvent (lbd %d, size %d) from cr: ", newlbd, resolvent1.size());
      printClause(resolvent1);
#endif
      nb1stClauseSimpL++; nbSavedResolvL += great.size();
      if (!addClauseByResolution(resolvent1, newlbd))
	return false;
      removeClause(cr);
    }
  }
  trailRecord=trail.size();  falseLitsRecord=falseLits.size();
  //  cancelUntilRecord(trailRecord);
  // for(int i=0; i<add_tmp.size(); i++)
  //   if (value(add_tmp[i]) == l_Undef) {
  //     //  printf("c ----\n");
  //     uncheckedEnqueue(add_tmp[i]);
  //     if (propagate() != CRef_Undef)
  // 	return false;
  //   }
  //   else assert(value(add_tmp[i])==l_True);
  return true;
}

void Solver::checkOccV(Var v) {
  for(int i=0; i<clauses.size(); i++) {
    CRef cr=clauses[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    for(int j=0; j<c.size(); j++)
      assert(var(c[j]) != v);
  }
  for(int i=0; i<learnts_core.size(); i++) {
    CRef cr=learnts_core[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    for(int j=0; j<c.size(); j++)
      assert(var(c[j]) != v);
  }
  for(int i=0; i<learnts_tier2.size(); i++) {
    CRef cr=learnts_tier2[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    for(int j=0; j<c.size(); j++)
      assert(var(c[j]) != v);
  }
  for(int i=0; i<learnts_local.size(); i++) {
    CRef cr=learnts_local[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    for(int j=0; j<c.size(); j++)
      assert(var(c[j]) != v);
  }
  for(int i=0; i<hardens.size(); i++) {
    CRef cr=hardens[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    for(int j=0; j<c.size(); j++)
      assert(var(c[j]) != v);
  }
  for(int i=0; i<isetClauses.size(); i++) {
    CRef cr=isetClauses[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    for(int j=0; j<c.size(); j++)
      assert(var(c[j]) != v);
  }
}

bool Solver::eliminateVar(Var v, int& savedTrailSize)
 {

    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    vec<CRef>& cls = occurIn[v]; //.lookup(v);
    vec<CRef>        pos, neg, posL, negL;
    int nbLearnt=0, totalLits=0;
    pos.clear(); neg.clear();

    int i, j, k;
    for (i = j = 0; i < cls.size(); i++) {
      CRef cr=cls[i];
      if (!removed(cr)) {
	Clause& c=ca[cr];
	Lit p;
	for(k=0; k<c.size(); k++) {
	  if (var(c[k]) == v) {
	    p=c[k];
	    break;
	  }
	}
	if (k<c.size()) {
	  cls[j++] = cr;
	  if (c.learnt()) {
	    nbLearnt++;
	    if (sign(p))
	      negL.push(cr);
	    else posL.push(cr);
	  }
	  else {
	    if (sign(p))
	      neg.push(cr);
	    else pos.push(cr);
	    totalLits += c.size();
	  }
	}
      }
    }
    cls.shrink(i-j);

    // if (nbLearnt>=nbElim)
    //   return true;

    // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    //
    int cnt         = 0;
    int clause_size = 0;
    int limit = pos.size()+neg.size()+grow, resLits=0;

    if (grow<0) {
      for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
	  if (merge(ca[pos[i]], ca[neg[j]], v, clause_size)) {
	    cnt++;
	    resLits += clause_size;
	    if (resLits > totalLits)
	      return true;
	  }
    }
    else 
      for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) && 
                (++cnt > limit || (clause_limit != -1 && clause_size > clause_limit)))
                return true;

    if (cnt>0) {

      //   printf("c eliminating var %d, pos %d, neg %d...\n", v+1, pos.size(), neg.size());
      
      // int savedClauses=clauses.size(), savedResolvents=resolvents.size();
      int savedTouched=touchedVars.size();
      
      assert(subsumptionQueue.size()==0);
      
      if (!crossResolvents(pos, neg, v))
	return false;
      
      // if (!crossResolventsL(posL, negL, v))
      //   return false;
      
      // reset:
      if (value(v) != l_Undef) {
	for(int i=savedTouched; i<touchedVars.size(); i++)
	  touched[touchedVars[i]] = 0;
	touchedVars.shrink(touchedVars.size() - savedTouched);
	
	if (value(v) == l_True) {
	  for(int i=0; i<pos.size(); i++)
	    removeClauseForElim(pos[i]);
	  for(int i=0; i<posL.size(); i++)
	    removeClauseForElim(posL[i]);
	}
	else {
	  for(int i=0; i<neg.size(); i++)
	    removeClauseForElim(neg[i]);
	  for(int i=0; i<negL.size(); i++)
	    removeClauseForElim(negL[i]);
	}
	
	if (!simplebackwardSubsume_(savedTrailSize, false))
	  return false;
	
	if (!simplifyResolvents())
	  return false;
	
	//  int savedTrailSize = trail.size();
	return simplebackwardSubsume_(savedTrailSize, false);
      }
    }
    
        // Delete and store old clauses:
    eliminated[v] = true;
    eliminatedVars.push(v);
    setDecisionVar(v, false);

    if (pos.size() > neg.size()){
      for (int i = 0; i < neg.size(); i++)
	mkElimClause(elimclauses, v, ca[neg[i]]);
      mkElimClause(elimclauses, mkLit(v));
    }else{
      for (int i = 0; i < pos.size(); i++)
	mkElimClause(elimclauses, v, ca[pos[i]]);
      mkElimClause(elimclauses, ~mkLit(v));
    }
    
    for (int i = 0; i < cls.size(); i++)
      removeClauseForElim(cls[i]);
    occurIn.cleanAll();

    nbRemovedClausesByElim += pos.size() + neg.size();

    vec<CRef>& clsLocal = occurInLocal[v];
    for (int i = 0; i < clsLocal.size(); i++)
      if (!removed(clsLocal[i]))
	removeClause(clsLocal[i]);

    // if (v == 33822) {
    //   printf("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n");
    //   checkOccV(v);
    // }

    // Free occurs list for this variable:
    occurIn[v].clear(true);
    occurInLocal[v].clear(true);
    
    // Free watchers lists for this variable, if possible:
    watches_bin[ mkLit(v)].clear(true);
    watches_bin[~mkLit(v)].clear(true);
    watches[ mkLit(v)].clear(true);
    watches[~mkLit(v)].clear(true);

    // if (starts == 1713 && v == 1270) {
    //   printf("\n1111 size %d, value v %d, value 15319 %d, resolvents %d\n",
    // 	     occurIn[15319].size(), toInt(value(v)), toInt(value(15319)), resolvents.size());
    //   for(int i=0; i<occurIn[15319].size(); i++)
    // 	printf("%u ", occurIn[15319][i]);
    // }

    if (!simplebackwardSubsume_(savedTrailSize, false))
      return false;

    //  if (starts == 1713 && v == 1270) {
    //   printf("\n2222 size %d, value v %d, value 15319 %d, resolvents %d\n",
    // 	     occurIn[15319].size(), toInt(value(v)), toInt(value(15319)), resolvents.size());
    //   for(int i=0; i<occurIn[15319].size(); i++)
    // 	printf("%u ", occurIn[15319][i]);
    // }

    if (!simplifyResolvents())
      return false;

    // if (starts == 1713 && v == 1270) {
    //   printf("\n3333 size %d, value v %d, value 15319 %d, resolvents %d, savedTrail %d, trail %d\n",
    // 	     occurIn[15319].size(), toInt(value(v)), toInt(value(15319)), resolvents.size(), savedTrailSize, trail.size());
    //   for(int i=0; i<occurIn[15319].size(); i++)
    // 	printf("%u ", occurIn[15319][i]);
    // }
    
    //  int savedTrailSize = trail.size();
    return simplebackwardSubsume_(savedTrailSize, false);
}

#define simplifyTicksLimit 1000000000

bool Solver::eliminate_() {
  int trail_size_last = trail.size();
  uint64_t saved_s_ticks = s_ticks;
  bool res=true;

  // if (starts == 1713) // && occurIn[15319] == 0));
  //   printf("*****");

  // Main simplification loop:
  while(!elim_heap.empty() || trail_size_last < trail.size()) {
    if (!simplebackwardSubsume_(trail_size_last, false))
      return false;
    
    for (int cnt = 0; !elim_heap.empty(); cnt++){
      Var elim = elim_heap.removeMin();
      
      if (isEliminated(elim) || value(elim) != l_Undef || dynVar(elim) || auxiVar(elim)) continue;
      
      // At this point, the variable may have been set by assymetric branching, so check it
      // again. Also, don't eliminate frozen variables:
      if (value(elim) == l_Undef && !eliminateVar(elim, trail_size_last)){
	res = false; goto cleanup; }
      
      checkGarbageForElimVars();
      if (s_ticks - saved_s_ticks > simplifyTicksLimit)
	elim_heap.clear();
    }
  }
  
  gatherTouchedClauses();
  if (!simplebackwardSubsume_(trail_size_last))
    return false;
  
 cleanup:
  // To get an accurate number of clauses.
  if (trail_size_last != trail.size()) {
    removeSatisfied(learnts_core); // Should clean core first.
    removeSatisfied(cardinalityC);
    safeRemoveSatisfied(learnts_tier2, TIER2);
    safeRemoveSatisfied(learnts_local, LOCAL);
    safeRemoveSatisfied(hardens, LOCAL);
    safeRemoveSatisfied(isetClauses, LOCAL);
    removeSatisfied(clauses);
  }
  else{
    purgeClauses(learnts_core);
    purgeClauses(learnts_tier2);
    purgeClauses(learnts_local);
    purgeClauses(cardinalityC);
    purgeClauses(isetClauses);
    purgeClauses(hardens);
    purgeClauses(clauses);
  }
  
  checkGarbageForElimVars();
#ifndef NDEBUG
  if (elimclauses.size() > 0)
    printf("c |  Eliminated clauses:     %10.2f Mb  grow %d                                    |\n", 
	   double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024), grow);
#endif
  return res;
}

void Solver::collectOriginalClauses(vec<CRef>& clauseSet) {
  int i, j;
  for(i=0, j=0; i<clauseSet.size(); i++)
    if (cleanClause(clauseSet[i])) {
      CRef cr = clauseSet[i];
      Clause& c=ca[cr];
      for(int k=0; k<c.size(); k++) {
	occurIn[var(c[k])].push(cr);
	n_occ[toInt(c[k])]++;
      }
      clauseSet[j++] = cr;
      // subsumptionQueue.insert(cr);
      //    subsumptionQueue.push(cr);
    }
  clauseSet.shrink(i-j);
}

void Solver::buildElimHeap() {
    vec<Var> vs;
    vec<double>& activity = VSIDS ? activity_VSIDS : activity_CHB;
    for (Var v = 0; v < staticNbVars; v++)
      if (!auxiVar(v) && value(v) == l_Undef && (!isEliminated(v)) &&
	  (n_occ[toInt(mkLit(v))] > 0 || n_occ[toInt(~mkLit(v))] > 0)) {
	vs.push(v); curr_activity[v] = activity[v];
      }
    elim_heap.build(vs);
#ifndef NDEBUG
    printf("c %d vars (over %d) to eliminate\n", vs.size(), staticNbVars);
#endif
}

void Solver::collectLocalClauses(vec<CRef>& clauseSet) {
  int i, j;

  for(i=0, j=0; i<clauseSet.size(); i++) {
    CRef cr = clauseSet[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    assert(c.learnt());
    if (c.mark() != LOCAL)
      continue;
    if (cleanClause(cr)) {
      for(int k=0; k<c.size(); k++) {
	occurInLocal[var(c[k])].push(cr);
      }
      clauseSet[j++] = cr;
    }
  }
  clauseSet.shrink(i-j);
}

bool Solver::eliminate(bool checkOcc) {
  //  bool res = true;
  //  int iter = 0;
  //  int n_cls, n_cls_init, n_vars;

  static uint64_t prevUB=0;
  static int prevNbOriClsLits=0; //INT32_MAX;
  static int nbElim=0;
  static int growLimit=4;
  
  // static int previousTrail=initTrail;

  // checkOccV(33822);

  if (prevUB < UB) 
    previousTrail=initTrail;
  if (prevUB != UB)
    prevUB = UB;
  
  nbOriClsLits=0;
  if (!backwardSubsumeAndEliminateEqLits())
    return false;
  else if (checkOcc) {
    // if (UB != prevUB) {
    //   prevUB = UB;
    //   prevNbOriClsLits = nbOriClsLits;
    // }
    if (prevNbOriClsLits < nbOriClsLits)
      prevNbOriClsLits = nbOriClsLits;
    if (previousTrail > trail.size())
      previousTrail = trail.size();
#ifndef NDEBUG
    if (prevNbOriClsLits > 0)
      printf("\nc prevNbOriClsLits %d, nbOriClsLits %d, percent %4.3f, fixedVars %d(%d)\n",
	     prevNbOriClsLits, nbOriClsLits, ((float)(prevNbOriClsLits - nbOriClsLits))/prevNbOriClsLits,
	     trail.size() - previousTrail, trail.size());
#endif
    if ((prevNbOriClsLits - nbOriClsLits) < prevNbOriClsLits/100 && starts>0)
      return true;
  }
  prevNbOriClsLits = nbOriClsLits;
  previousTrail = trail.size();

  nbUnitViviResolv=0, shortened = 0, nbSimplifing = 0, nbRemovedLits=0;
  saved_s_up = s_propagations;
  
#ifndef NDEBUG
  double elimTime = cpuTime();
#endif
  
  uint64_t saved_s_ticks = s_ticks;

  //  int nv = cardinalityC.size() > 0 ? nVars() : staticNbVars;
  occurInLocal.init(nVars()); 

  for(int i=0; i<nVars(); i++) {
    occurIn[i].clear(); occurInLocal[i].clear();
    n_occ[toInt(mkLit(i))] = 0; n_occ[toInt(~mkLit(i))] = 0;
  }
  
  collectClauses(clauses);
  // if (clauses.size() > 1000000) {
  //   subsumptionQueue.clear();
  //   if (clauses.size() < 10000000)
  //     for(int i=0; i<clauses.size(); i++) {
  // 	CRef cr=clauses[i];
  // 	if (ca[cr].size()==2)
  // 	  subsumptionQueue.push(cr);
  //     }
  //  }
  
  collectClauses(learnts_core, CORE);
  collectClauses(learnts_tier2, TIER2);
  collectClauses(cardinalityC, CORE);

  collectLocalClauses(learnts_local);
  collectLocalClauses(hardens);
  collectLocalClauses(isetClauses);

  subsumptionQueue.clear(); resolvents.clear(); nbAllResolvs=0;     nbElim++;

#ifndef NDEBUG
    printf("c before variable elimination....\n"); 
    printf("c nbElim %d, original clauses %d, learnts_core %d, learnts_tier2 %d, learnts_local %d, hardens %d, trail %d\n",
	   nbElim, clauses.size(), learnts_core.size(), learnts_tier2.size(), learnts_local.size(), hardens.size(), trail.size());
#endif

    int mySavedEliminatedVars=eliminatedVars.size();

    for(grow = -2; grow<growLimit && s_ticks - saved_s_ticks <= simplifyTicksLimit; grow+=2) {
      int savednbRemovedClausesByElim=nbRemovedClausesByElim,
	savedEliminatedVars=eliminatedVars.size(), savednbAllResolvs=nbAllResolvs,
	savednbSavedResolv=nbSavedResolv, savednb1stClauseSimp=nb1stClauseSimp,
	savednbLearntResolvs=nbLearntResolvs, savednb1stClauseSimpL=nb1stClauseSimpL, savednbSavedResolvL=nbSavedResolvL;
      //  int  savedsbsmRslv=sbsmRslv, saveddelLitRslv=delLitRslv;
      uint64_t savedUp=s_propagations;
    buildElimHeap();
    if (!eliminate_())
      return false;

#ifndef NDEBUG
    printf("c %d(%d) vars eliminated, %d(%d) clauses removed, %d(%d) resolvs added, nbLnResolvs %d(%d)\n",
	   eliminatedVars.size()-savedEliminatedVars, eliminatedVars.size(),
	   nbRemovedClausesByElim - savednbRemovedClausesByElim,
	   nbRemovedClausesByElim, nbAllResolvs-savednbAllResolvs, nbAllResolvs, nbLearntResolvs-savednbLearntResolvs, nbLearntResolvs);
    printf("c %d(%d) nb1stClauseSimpL, %d(%d) nbSavedResolvL\n",
	   nb1stClauseSimpL-savednb1stClauseSimpL, nb1stClauseSimpL,
	   nbSavedResolvL-savednbSavedResolvL, nbSavedResolvL);
    printf("c %d(%d) 1stClauseSimp, %d(%d) nbSavedResolv, s_up %llu, s_ticks %llu\n",
	   nb1stClauseSimp-savednb1stClauseSimp, nb1stClauseSimp,
	   nbSavedResolv-savednbSavedResolv, nbSavedResolv, s_propagations-savedUp, s_ticks-saved_s_ticks);
    //  printf("c sbsmRslv %d(%d), delLitRslv %d(%d)\n",
    //	   sbsmRslv-savedsbsmRslv, sbsmRslv, delLitRslv-saveddelLitRslv, delLitRslv);
#endif
    }
    if (mySavedEliminatedVars==eliminatedVars.size() && growLimit < 16)
      growLimit += 4;
    // else if (growLimit > 4)
    //    growLimit -= 4;
    
    assert(subsumptionQueue.size() == 0);
    
    // int trail_size_last = trail.size();
    // if (!simplifyResolvents())
    //   return false;

    // if (!backwardSubsume_(trail_size_last))
    //   return false;
    
    //    eliminateLearntClausesContainingElimVar(learnts_local);
    //    eliminateLearntClausesContainingElimVar(auxiLearnts);

    for(int i=0; i<nVars(); i++) {
      occurIn[i].clear(); occurInLocal[i].clear();
    }
    subsumptionQueue.clear();
    
    checkGarbage();

#ifndef NDEBUG
    printf("c after variable elimination....\n"); 
    printf("c original clauses %d, learnts_core %d, learnts_tier2 %d, learnts_local %d, trail %d\n",
	   clauses.size(), learnts_core.size(), learnts_tier2.size(), learnts_local.size(), trail.size());
    printf("c hardens %d, cardinalityC %d, isetClauses %d\n\n",
	   hardens.size(), cardinalityC.size(), isetClauses.size());

    //#ifndef NDEBUG
    double avgRemovedLits = shortened > 0 ? (double)nbRemovedLits/shortened : 0;
    printf("c resolvents %d, nbSimplifing: %d, nbShortened: %d\n",
	   nbAllResolvs, nbSimplifing, shortened);
    printf("c avgRemovedLits %4.3lf, nbUnits %d, s_up %llu, elimTime %5.2lfs, s_ticks %llu\n",
	   avgRemovedLits, nbUnitViviResolv, s_propagations-saved_s_up, cpuTime() - elimTime,  s_ticks-saved_s_ticks);
    totalelimTime += cpuTime() - elimTime;
#endif
    
    //#endif
    return true;
}

bool Solver::isSubsumed(CRef dr) {
  Clause& d=ca[dr];
  counter++;
  for (int i = 0; i < d.size(); i++) {
    seen2[toInt(d[i])]=counter;
  }
  for(int i=0; i<subsumptionQueue.size(); i++) {
    CRef cr=subsumptionQueue[i];
    if (removed(cr))
      continue;
    Clause& c=ca[cr];
    if ((c.size() > d.size()) || ((c.abstraction() & (~d.abstraction())) !=0))
      continue;
    Lit ret = lit_Undef;
    for(int k=0; k<c.size(); k++) {
      // if (seen2[toInt(~c[k])] == counter) {
      // 	if (ret == lit_Undef)
      // 	  ret = c[k];
      // 	else {
      // 	  // sbsmTtlg++;
      // 	  ret = lit_Error;
      // 	  break;
      // 	}
      // }
      // else
      if (seen2[toInt(c[k])] != counter) {
	ret = lit_Error;
	break;
      }
    }
    if (ret == lit_Undef) {
      if (!d.learnt() && c.learnt()) {
	if (d.size() > c.size()) {
	  // if (drup_file)
	  //   writeClause2drup('d', d, drup_file);
	  detachClause(dr, true);
	  for(int k=0; k<c.size(); k++)
	    d[k]=c[k];
	  d.shrink(d.size() - c.size());
	  attachClause(dr);
	  // if (drup_file)
	  //   writeClause2drup('a', d, drup_file);
	}
	removeClause(cr);  removeClauseFromOccur(cr, true);
	subsumptionQueue[i] = dr;
      }
      else {
	removeClause(dr);  removeClauseFromOccur(dr, true);
      }
      sbsmRslv++;
      return true;
    }
    // else if (ret != lit_Error) {
    //   delLitRslv++;
    //   if (d.size() == 2){
    // 	removeClause(dr);  removeClauseFromOccur(dr);
    // 	d.strengthen(~ret);
    //   }
    //   else {
    // 	detachClause(dr, true);
    // 	d.strengthen(~ret);
    // 	attachClause(cr);
    // 	remove(occurIn[var(ret)], cr);
    //   }
    // }
  }
  return false;
}

#define simplifyUPlimit 200000000

void Solver::simplifyLearnt(Clause& c) {
    trailRecord = trail.size();// record the start pointer
    falseLitsRecord = falseLits.size();

    //sort(&c[0], c.size(), VarOrderLevelLt(vardata));

    bool True_confl = false;
    //    int beforeSize, afterSize;
    //beforeSize = c.size();
    int i, j;
    CRef confl;

    for (i = 0, j = 0; i < c.size(); i++){
      if (value(c[i]) == l_Undef){
	//printf("///@@@ uncheckedEnqueue:index = %d. l_Undef\n", i);
	simpleUncheckEnqueue(~c[i]);
	c[j++] = c[i];
	confl = simplePropagate();
	if (confl != CRef_Undef || softConflictFlag){
	  break;
	}
      }
      else{
	if (value(c[i]) == l_True){
	  //printf("///@@@ uncheckedEnqueue:index = %d. l_True\n", i);
	  c[j++] = c[i];
	  True_confl = true;
	  confl = reason(var(c[i]));
	  assert(confl  != CRef_Undef);
	  break;
	}
      }
    }
    if (j<c.size())
      c.shrink(c.size() - j);

    if (confl != CRef_Undef || True_confl == true || softConflictFlag){
      simp_learnt_clause.clear();
      if (softConflictFlag) {
	simpleAnalyzeSoftConflict(simp_learnt_clause);
	softConflictFlag = false;
      }      
      else {
	if (True_confl == true){
	  simp_learnt_clause.push(c.last());
        }
        simpleAnalyze(confl, simp_learnt_clause, True_confl);
      }
      if (simp_learnt_clause.size() < c.size()){
	for (i = 0; i < simp_learnt_clause.size(); i++){
	  c[i] = simp_learnt_clause[i];
	}
	c.shrink(c.size() - i);
      }
    }
    cancelUntilTrailRecord();
}

bool Solver::simplifyResolvents() {
  //  static int nb=0;
  int ci; //shortened = 0, nbSimplifing = 0, nbRemovedLits=0, nbUnits=0;
  // uint64_t saved_s_up = s_propagations;
  vec<Lit> lits, myadd_occ;
  assert(decisionLevel() == 0);
  sort(resolvents, clauseSize_lt(ca));
  for (ci = 0; ci < resolvents.size() && (starts > 0 || s_propagations - saved_s_up <= simplifyUPlimit); ci++){
    CRef cr = resolvents[ci];
    Clause& c = ca[cr];
    int savedSize=c.size();
    if (starts>0) {
      lits.clear();
      for(int i=0; i<c.size(); i++)
	lits.push(c[i]);
    }
    if (cleanClause(cr)) {
      if (c.size() == 2 &&
	  (litTrail[toInt(~c[0])] >= trail.size() && litTrail[toInt(~c[1])] >= trail.size())) {
	if (starts>0 && c.size() < savedSize) {
	  counter++;
	  for(int i=0; i<c.size(); i++)
	    seen2[var(c[i])] = counter;
	  for(int i=0; i<lits.size(); i++)
	    if (seen2[var(lits[i])] != counter) {
	      remove(occurIn[var(lits[i])], cr);
	      n_occ[toInt(lits[i])]--;
	      updateElimHeap(var(lits[i]));
	    }
	}
	continue;
      }
      if (starts>0 && isSubsumed(cr))
	continue;
      // int saved_size=c.size();
      
      // if (drup_file){
      // 	myadd_occ.clear();
      // 	for (int i = 0; i < c.size(); i++) myadd_occ.push(c[i]);
      // }
      
      nbSimplifing++;
      
      int beforeSize = c.size();
      assert(c.size() > 1);
      detachClause(cr, true);
      // simplify a learnt clause c
      simplifyLearnt(c);
      assert(c.size() > 0);
      int afterSize = c.size();
      
      // if(drup_file && saved_size !=c.size()){
      // 	writeClause2drup('a', c, drup_file);
      // 	writeClause2drup('d', myadd_occ, drup_file);
      // }
      
      //printf("beforeSize: %2d, afterSize: %2d\n", beforeSize, afterSize);
      if (c.size() == 1){
	for(int i=0; i<lits.size(); i++)
	  remove(occurIn[var(lits[i])], cr);
	  // when unit clause occur, enqueue and propagate
	nbUnitViviResolv++;
	uncheckedEnqueue(c[0]);
	// delete the clause memory in logic
	c.mark(1);
	ca.free(cr);
	if (propagate() != CRef_Undef || softConflictFlag){
	  return false;
	}
      }
      else{
	if (afterSize < beforeSize) {
	  shortened++; nbRemovedLits += beforeSize - afterSize;
	}
	if (afterSize < savedSize) {
	  c.calcAbstraction(); subsumptionQueue.push(cr);
	  if (starts>0) {
	    counter++;
	    for(int i=0; i<c.size(); i++)
	      seen2[var(c[i])] = counter;
	    for(int i=0; i<lits.size(); i++)
	      if (seen2[var(lits[i])] != counter) {
		remove(occurIn[var(lits[i])], cr);
		n_occ[toInt(lits[i])]--;
		updateElimHeap(var(lits[i]));
	      }
	  }
	}
	attachClause(cr);
      }
    }
  }
// #ifndef NDEBUG
//   double avgRemovedLits = shortened > 0 ? (double)nbRemovedLits/shortened : 0;
//   printf("c resolvents %d, nbSimplifing: %d, nbShortened: %d\n",
// 	 resolvents.size(), nbSimplifing, shortened);
//   printf("c avgRemovedLits %4.3lf, nbUnits %d, s_up %llu\n",
// 	 avgRemovedLits, nbUnits, s_propagations-saved_s_up);
// #endif
  resolvents.clear();
  return true;
}

void Solver::checkGarbageForElimVars() {
  if (ca.wasted() > ca.size() * garbage_frac) {
    
    // ClauseAllocator to(ca.size() - ca.wasted());
    ClauseAllocator to(ca.wasted() > ca.size()/2 ? ca.size()/2 : ca.size() - ca.wasted()); 
    relocAll(to);
    occurIn.cleanAll();
    int i, j;
    for(i=0; i<nVars(); i++) {
      vec<CRef>& cls=occurIn[i];
      for(j=0; j<cls.size(); j++) {
	ca.reloc(cls[j], to);
	
	// if (cls[j] == 436670)
	//   printf("***** ");
      }
      
      vec<CRef>& clsLocal=occurInLocal[i];
      for(j=0; j<clsLocal.size(); j++)
	ca.reloc(clsLocal[j], to);
    }
    for(i=j=0; i<subsumptionQueue.size(); i++)
      if (!removed(subsumptionQueue[i])) {
	ca.reloc(subsumptionQueue[i], to);
	subsumptionQueue[j++]=subsumptionQueue[i];
      }
    subsumptionQueue.shrink(i-j);
    
    for(i=j=0; i<resolvents.size(); i++) {
      if (!removed(resolvents[i])) {
	ca.reloc(resolvents[i], to);
	resolvents[j++] = resolvents[i];
      }
    }
    resolvents.shrink(i-j);
    
    to.moveTo(ca);
  }
}

bool Solver::simplesubsumeClauses(CRef cr, int& subsumed, int& deleted_literals) {
  Clause& c  = ca[cr];
  assert(c.size() > 1 || value(c[0]) == l_True);// Unit-clauses should have been propagated before this point.
  // Find best variable to scan:
  Var best = var(c[0]);
  for (int i = 1; i < c.size(); i++)
    if (occurIn[var(c[i])].size() < occurIn[best].size())
      best = var(c[i]);
  
  // Search all candidates:
  vec<CRef>& _cs = occurIn.lookup(best);
  for (int j = 0; j < _cs.size(); j++) {
    assert(!removed(cr));
    CRef dr=_cs[j];
    if (dr != cr && !removed(dr)){
      Clause& d=ca[dr];
      // Lit l1 = c.subsumes(d);
      Lit l = simplesubsume(c, d);
      // assert(l==l1);
      if (l == lit_Undef) {
	if (c.learnt() && !d.learnt()) {
	  if (c.size() < d.size()) {
	    // if (drup_file)
	    //   writeClause2drup('d', d, drup_file);
	    detachClause(dr, true); removeClauseFromOccur(dr, true);
	    for(int k=0; k<c.size(); k++) {
	      d[k] = c[k];
	      vec<CRef>& cls=occurIn[var(d[k])];
	      int m;
	      for(m=0; m<cls.size(); m++)
		if (cls[m] == cr) {
		  cls[m]=dr; break;
		}
	      assert(m<cls.size());
	    }
	    d.shrink(d.size() - c.size());
	    d.setAbs(c.abstraction());
	    d.setSimplified(c.simplified());
	    d.set_lbd(c.lbd());
	    attachClause(dr);
	    // if (drup_file)
	    //   writeClause2drup('a', d, drup_file);
	  }
	  else removeClauseFromOccur(cr);
	  subsumed++; removeClause(cr); subsumptionQueue.push(dr); 
	  return true;
	}
	else {
	  subsumed++, removeClause(dr); removeClauseFromOccur(dr);
	}
      }
      else if (l != lit_Error){
	deleted_literals++;
	if (!simpleStrengthenClause(dr, ~l))
	  return false;
	// Did current candidate get deleted from cs? Then check candidate at index j again:
	if (var(l) == best)
	  j--;
      }
    }
  }
  return true;
}

// struct clauseSize_lt {
//     ClauseAllocator& ca;
//     clauseSize_lt(ClauseAllocator& ca_) : ca(ca_) {}
//     bool operator () (CRef x, CRef y) {

//       return ca[x].size() < ca[y].size();
//     }
// };

#define sbsmLimit 5000000

bool Solver::simplebackwardSubsume_(int& savedTrailSize, bool verbose) {
  //  int savedTrail=trail.size();
  int mySavedTrail=trail.size();
  //int savedOriginal;
  // int cnt = 0;
  int subsumed = 0, deleted_literals = 0, nbSubsumes=0;

  //  int mysbsmLimit=sbsmLimit;
  sbsmTtlg=0; sbsmAbsFail=0; allsbsm=0;

#ifndef NDEBUG
  double sbsmTime;
  if (verbose)
    sbsmTime = cpuTime();
#endif

  sort(subsumptionQueue, clauseSize_lt(ca));
  // savedOriginal = clauses.size();
  assert(decisionLevel() == 0);
  int initQueueSize=subsumptionQueue.size();
  while (subsumptionQueue.size() > 0 || savedTrailSize < trail.size()) {
    // Check top-level assignments by creating a dummy clause and placing it in the queue:
    if (subsumptionQueue.size() == 0 && savedTrailSize < trail.size()){
      Lit l = trail[savedTrailSize++];
      ca[bwdsub_tmpunit][0] = l;
      ca[bwdsub_tmpunit].calcAbstraction();
      //subsumptionQueue.insert(bwdsub_tmpunit);
      subsumptionQueue.push(bwdsub_tmpunit);
      // if (allsbsm > mysbsmLimit)
      // 	mysbsmLimit += sbsmLimit;
    }

    //  int initQueueSize=subsumptionQueue.size();
    for(int i=0; i<subsumptionQueue.size(); i++) {
      //  if (sbsmAbsFail > mysbsmLimit)
      if (sbsmAbsFail > sbsmLimit)
      	break;
      else if (i==initQueueSize) {
	initQueueSize=subsumptionQueue.size();
	//	printf("c subsumption queue grows to %d\n", initQueueSize);
	int j, k;
	for(j=0, k=i+1; k<subsumptionQueue.size(); k++)
	  subsumptionQueue[j++] = subsumptionQueue[k];
	subsumptionQueue.shrink(k-j);
	sort(subsumptionQueue, clauseSize_lt(ca));
	//	printf("\n");
	i=-1;
	continue;
      }
      CRef    cr = subsumptionQueue[i]; //subsumptionQueue.peek(); subsumptionQueue.pop();
      if (removed(cr)) continue;
      nbSubsumes++;
      if (!simplesubsumeClauses(cr, subsumed, deleted_literals)) {
	printf("c a conflict is found during backwardSubsumptionCheck\n");
	occurIn.cleanAll();
	return false;
      }
    }
    subsumptionQueue.clear();
  }
#ifndef NDEBUG
  if (verbose) {
    printf("c %d subsumptions, %d subsumed, %d delLits, %d(%d) fixedVars\n", nbSubsumes, subsumed, deleted_literals, trail.size() - mySavedTrail, trail.size());
    float rate1, rate2;
    if (allsbsm==0) {
      rate1=0; rate2=0;
    }
    else {
      rate1=(float)(sbsmTtlg)/(allsbsm);
      rate2=(float)(sbsmAbsFail)/(allsbsm);
    }
  printf("c allsbsm %llu, sbsmTtlg %llu (%5.4f), sbsmAbsFail %llu(%5.4f)\n",
	 allsbsm, sbsmTtlg, rate1, sbsmAbsFail, rate2);
  }
  //#ifndef NDEBUG
  if (verbose) {
    double thissbsmtime = cpuTime()-sbsmTime;
    printf("c sbsmTime %5.2lfs\n",  thissbsmtime);
    totalsbsmTime += thissbsmtime;
  }
#endif
  
  occurIn.cleanAll();
  return true;
}
