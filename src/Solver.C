/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

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

#include "Solver.h"
#include "Sort.h"
#include <cmath>
#include "constants.h"
#include <iostream>
#include <fstream>
#include <sstream>

double  nof_learnts;
//=================================================================================================
// Constructor/Destructor:
int nbclausesbeforereduce = NBCLAUSESBEFOREREDUCE;

//#define DEBUG_CONFLICTS
//#define DEBUG_DECLEVELGAIN


static inline void removeW(vec<Watched> &ws,Clause *c) {
  int j = 0;
  for (; j < ws.size() && ws[j].wcl != c; j++);
  assert(j < ws.size());
  for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
  ws.pop();

}

static inline void removeBin(vec<Binaire> &ws,Clause *c) {
  int j = 0;
  for (; j < ws.size() && ws[j].clause != c; j++);
  assert(j < ws.size());
  for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
  ws.pop();

}

void Solver::saveState()
{
    for (int i = 0; i < watchBackup.changed.size(); i++) {
        const int which = watchBackup.changed[i];

        assert(watchBackup.flags[which] == true);
        watchBackup.flags[which] = false;
    }
    watchBackup.changed.clear();

    backup.touchedClauses.clear();
    backup.sublevel = trail.size();
    backup.level = decisionLevel();
}

//#define RESTORE
//#define RESTORE_FULL


Solver::Solver() :

    // Parameters: (formerly in 'SearchParams')
    var_decay(1 / 0.95), clause_decay(1 / 0.999), random_var_freq(0.02)
  , restart_first(100), restart_inc(1.5), learntsize_factor((double)1/(double)3), learntsize_inc(1)

    // More parameters:
    //
  , expensive_ccmin  (true)
  , polarity_mode    (polarity_user)
  , verbosity        (0)

    // Statistics: (formerly in 'SolverStats')
    //
  , nbDL2(0),nbBin(0),nbUn(0) , nbReduceDB(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), bogoProps(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok               (true)
  , cla_inc          (1)
  , var_inc          (1)
  , qhead            (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , backup           (VarOrderLt(activity))
  , random_seed      (91648253)
  , progress_estimate(0)
  , remove_satisfied (true)
  , clIndex(0)
{
    MYFLAG = 0; //No comment ;)
}

void Solver::setFileName(const char* filename)
{
    std::stringstream ss;
    ss << filename << "-usefulness-dump.gz";
    dumpFile.open(ss.str().c_str());
}



Solver::~Solver()
{
    for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    watchesBin   .push();          // (list for negative literal)
    watchesBin   .push();          // (list for negative literal)

    watchBackup.ws.push();
    watchBackup.ws.push();
    watchBackup.flags.push(false);
    watchBackup.flags.push(false);

    reason    .push(NULL);
    assigns   .push(toInt(l_Undef));
    level     .push(-1);
    activity  .push(0);
    seen      .push(0);
    permDiff  .push(0);

    polarity    .push((char)sign);
    decision_var.push((char)dvar);

    insertVarOrder(v);
    return v;
}


bool Solver::addClause(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);

    if (!ok)
        return false;
    else{
        // Check if clause is satisfied and remove false/duplicate literals:
        sort(ps);
        Lit p; int i, j;
        for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
            if (value(ps[i]) == l_True || ps[i] == ~p)
                return true;
            else if (value(ps[i]) != l_False && ps[i] != p)
                ps[j++] = p = ps[i];
        ps.shrink(i - j);
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        assert(value(ps[0]) == l_Undef);
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == NULL);
    }else{
        Clause* c = Clause_new(ps, clIndex++, false);
        clauses.push(c);
        attachClause(*c);
    }

    return true;
}


void Solver::attachClause(Clause& c) {
    assert(c.size() > 1);
    if(c.size()==2) {
      watchesBin[toInt(~c[0])].push();
      watchesBin[toInt(~c[1])].push();
      watchesBin[toInt(~c[0])].last().clause = &c;
      watchesBin[toInt(~c[0])].last().implied = c[1];
      watchesBin[toInt(~c[1])].last().clause = &c;
      watchesBin[toInt(~c[1])].last().implied = c[0];

    } else {
      watches[toInt(~c[0])].push();
      watches[toInt(~c[1])].push();
      watches[toInt(~c[0])].last().wcl = &c;
      watches[toInt(~c[0])].last().blocked = c[c.size()/2];
      watches[toInt(~c[1])].last().wcl = &c;
      watches[toInt(~c[1])].last().blocked = c[c.size()/2];
    }
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size();
}

void Solver::detachClause(Clause& c) {
    assert(c.size() > 1);
    //    assert(find(watches[toInt(~c[0])], &c));
    //assert(find(watches[toInt(~c[1])], &c));

    if(c.size()==2) {
      removeBin(watchesBin[toInt(~c[0])],&c);
      removeBin(watchesBin[toInt(~c[1])],&c);
    } else {
      removeW(watches[toInt(~c[0])], &c);
      removeW(watches[toInt(~c[1])], &c);
    }
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(Clause& c) {
    detachClause(c);
    free(&c); }


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    #ifdef RESTORE
    printf("------------    Canceling until level %d\n", level);
    #endif
  if (decisionLevel() > level){
    for (int c = trail.size()-1; c >= trail_lim[level]; c--){
      Var     x  = var(trail[c]);
      assigns[x] = toInt(l_Undef);
      insertVarOrder(x);
      #ifdef RESTORE
      printf("Canceling lit ");printLit(trail[c]); printf("\n");
      #endif
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  }
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::fullCancelUntil(int level, int sublevel)
{
    assert(backup.running);
    #ifdef RESTORE_FULL
        printf("Full cancelling until sublevel %d, level: %d .:. currentsubDeclevel: %d, currentDeclevel: %d\n", sublevel, level, trail.size(), decisionLevel());
    #endif
    for (int c = trail.size()-1; c >= sublevel; c--){
        Var     x  = var(trail[c]);
        const Lit lit = trail[c];

        //Restore assignements
        assigns[x] = toInt(l_Undef);

        //Don't need the line below, because we restore the _full_ order heap
        //insertVarOrder(x);
    }
    for (int i = 0; i < watchBackup.changed.size(); i++) {
        const int which = watchBackup.changed[i];

        assert(watchBackup.flags[which]);
        #ifdef RESTORE
        printf("Restoring watch number %d\n", i);
        #endif
        watches[which] = watchBackup.ws[which];
        watchBackup.flags[which] = false;
    }
    watchBackup.changed.clear();

    //Restore clauses
    for (std::set<Clause*>::const_iterator it = backup.touchedClauses.begin(), end = backup.touchedClauses.end(); it != end; it++) {
        (*it)->restoreLiterals();;
    }

    qhead = sublevel-1;
    trail.shrink(trail.size() - sublevel);
    trail_lim.shrink(trail_lim.size() - level);
    #ifdef RESTORE
    printf("Full cancel finished. Sublevel: %d, level: %d, qhead:%d\n", trail.size(), decisionLevel(), qhead);
    #endif
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;
    /*if (backup.stage == 0) {
        assert(order_heap.heapProperty());
        for(int i = 0; i < std::min(order_heap.size(), 10); i++) {
            printf("order_heap %d has var %d, has activity %lf\n", i, order_heap[i], activity[order_heap[i]]);
        }
    }*/

    // Random decision:
    if (drand(random_seed) < random_var_freq
        && !order_heap.empty()
    ){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (toLbool(assigns[next]) == l_Undef && decision_var[next])
            rnd_decisions++;
    }

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next])
      if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_user:  if(next!=var_Undef) sign = polarity[next]; break;
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    default: assert(false); }

    #ifdef RESTORE
    if (backup.stage == 0) {
        printf("--> Picking decision lit "); printLit(Lit(next, sign)); printf(" at decision level: %d, sublevel: %d\n", decisionLevel(), trail.size());
    }
    #endif

    return next == var_Undef ? lit_Undef : Lit(next, sign);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel,int &nbl,int &mer)
{
    int pathC = 0;
    Lit p     = lit_Undef;


    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    do{
      assert(confl != NULL);          // (otherwise should be UIP)
      Clause& c = *confl;

      // The first one has to be SAT
      if( p != lit_Undef && c.size()==2 && value(c[0])==l_False) {
        assert(value(c[1])==l_True);
        Lit tmp = c[0];
        c[0] =  c[1], c[1] = tmp;
      }

      for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
        Lit q = c[j];

            if (!seen[var(q)] && level[var(q)] > 0){

                varBumpActivity(var(q));

                seen[var(q)] = 1;
                if (level[var(q)] >= decisionLevel()){
                    pathC++;
#ifdef UPDATEVARACTIVITY
                    if((reason[var(q)]!=NULL)  && (reason[var(q)]->learnt()))
                      lastDecisionLevel.push(q);
#endif
                }
                else{
                    out_learnt.push(q);
                    if (level[var(q)] > out_btlevel)
                        out_btlevel = level[var(q)];
                }
            }
        }
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason[var(p)];
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;


    // Simplify conflict clause:
    //
    int i, j;
    if (expensive_ccmin){
      uint32_t abstract_level = 0;
      for (i = 1; i < out_learnt.size(); i++)
        abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

      out_learnt.copyTo(analyze_toclear);
      for (i = j = 1; i < out_learnt.size(); i++)
        if (reason[var(out_learnt[i])] == NULL || !litRedundant(out_learnt[i], abstract_level))
          out_learnt[j++] = out_learnt[i];
    }else{
      out_learnt.copyTo(analyze_toclear);
      for (i = j = 1; i < out_learnt.size(); i++){
        Clause& c = *reason[var(out_learnt[i])];
        if(c.size()==2 && value(c[0])==l_False) {
          assert(value(c[1])==l_True);
          Lit tmp = c[0];
          c[0] =  c[1], c[1] = tmp;
        }

        for (int k = 1; k < c.size(); k++)
          if (!seen[var(c[k])] && level[var(c[k])] > 0){
            out_learnt[j++] = out_learnt[i];
            break; }
      }
    }
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();





    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        for (int i = 2; i < out_learnt.size(); i++)
            if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
                max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level[var(p)];
    }


    nbl = 0;mer = 0;
    MYFLAG++;
    for(int i=0;i<out_learnt.size();i++) {

      int l = level[var(out_learnt[i])];
      if (permDiff[l] != MYFLAG) {
                  permDiff[l] = MYFLAG;
                  nbl++;
                  mer +=nbPropagated(l);
      }
    }


#ifdef UPDATEVARACTIVITY
    if(lastDecisionLevel.size()>0) {
      for(int i = 0;i<lastDecisionLevel.size();i++) {
        if(reason[var(lastDecisionLevel[i])]->activity()<nbl)
          varBumpActivity(var(lastDecisionLevel[i]));
      }
      lastDecisionLevel.clear();
    }
#endif




    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();
        if(c.size()==2 && value(c[0])==l_False) {
          assert(value(c[1])==l_True);
          Lit tmp = c[0];
          c[0] =  c[1], c[1] = tmp;
        }


        for (int i = 1; i < c.size(); i++){
          Lit p  = c[i];
          if (!seen[var(p)] && level[var(p)] > 0){
            if (reason[var(p)] != NULL && (abstractLevel(var(p)) & abstract_levels) != 0){
              seen[var(p)] = 1;
              analyze_stack.push(p);
              analyze_toclear.push(p);
            }else{
              for (int j = top; j < analyze_toclear.size(); j++)
                seen[var(analyze_toclear[j])] = 0;
              analyze_toclear.shrink(analyze_toclear.size() - top);
              return false;
                }
          }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason[x] == NULL){
                assert(level[x] > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = *reason[x];
                for (int j = 1; j < c.size(); j++)
                    if (level[var(c[j])] > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, Clause* from)
{
    #ifdef RESTORE
    if (backup.stage == 0) {
        printf("setting lit "); printLit(p); printf(" decLevel: %d flag: %d detachedClause: %p\n", decisionLevel(), backup.stage, backup.detachedClause);
    }
    #endif

    assert(value(p) == l_Undef);
    assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
    level   [var(p)] = decisionLevel();
    reason  [var(p)] = from;
    polarity[var(p)] = sign(p);
    trail.push(p);
}

bool Solver::handleConflict(Clause& c, int& num_props)
{
    if (backup.running
        && c.learnt()
        && backup.stage == 0
        && decisionLevel() > 0
    ) {
        #ifdef DEBUG_CONFLICTS
        printf("clause orig:");printClause(c);
        //printf("orig pointer: %p\n", &c);
        #endif //#ifdef DEBUG_CONFLICTS

        #ifdef RESTORE_FULL
        printf("Learnt clause %p wanted to make a conflict! declevel: %d trail: %d\n", &c, decisionLevel(), trail.size());
        //printClause(c);
        #endif
        backup.order_heap = order_heap;
        backup.detachedClause = &c;
        backup.stage = 1;

        //Save misc state
        backup.propagations = propagations;
        backup.bogoProps = bogoProps;
        backup.decisions = decisions;
        backup.simpDB_props = simpDB_props;
        backup.num_props = num_props;
        backup.random_seed = random_seed;
        backup.polarity = polarity;
        return false;
    }

    if (backup.running
        && c.learnt()
        && backup.stage == 1
        && decisionLevel() > 0
        && &c == backup.detachedClause
    ) {
        #ifdef RESTORE_FULL
        printf("Skipping over conflicting with clause %p\n", backup.detachedClause);
        #endif
        return false;
    }

    if (backup.running
        && c.learnt()
        && backup.stage == 2
        && decisionLevel() > 0
    ) {
        #ifdef DEBUG_CONFLICTS
        printf("clause final:");
        printClause(c);
        #endif //#ifdef DEBUG_CONFLICTS

        //printf("final pointer: %p\n", &c);
        assert(&c == backup.detachedClause);
        backup.stage = 0;
        #ifdef RESTORE_FULL
        printf("Now clause %p is making the conflict it wanted to make earlier. declevel: %d trail: %d \n", backup.detachedClause, decisionLevel(), trail.size());
        //printClause(*backup.detachedClause);
        #endif
        assert(backup.decisions <= decisions);
        assert(backup.propagations <= propagations);

        c.getGainedProps() += (propagations + num_props - backup.propagations - backup.num_props);
        c.getGainedBogoProps() += (bogoProps - backup.bogoProps);
        c.getGainedDecisions() += (decisions - backup.decisions);
        #ifdef DEBUG_DECLEVELGAIN
        if (backup.decisions < decisions) {
            fprintf(stderr, "gained declevel: %d\n", (int)(decisions - backup.decisions));
        }
        #endif //DEBUG_DECLEVELGAIN
        c.getNumConflicted()++;

        //Restore misc state
        propagations = backup.propagations;
        bogoProps = backup.bogoProps;
        decisions = backup.decisions;
        simpDB_props = backup.simpDB_props;
        random_seed = backup.random_seed;
        polarity = backup.polarity;
        num_props = backup.num_props;

        order_heap = backup.order_heap;
        backup.detachedClause = NULL;
    }

    if (backup.stage == 1) {
        #ifdef DEBUG_CONFLICTS
        printf("clause middle:");
        printClause(c);
        //printf("middle pointer: %p\n", &c);
        #endif //#ifdef DEBUG_CONFLICTS
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause* Solver::propagate() {
  Clause* confl     = NULL;
  int     num_props = 0;

  while (qhead < trail.size()){
    const Lit      p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
    vec<Watched>&  ws  = watches[toInt(p)];
    Watched         *i, *j, *end;
    num_props++;

    #ifdef RESTORE
    printf("Propagating lit "); printLit(p); printf(" number: %d\n", toInt(p));
    #endif

    const vec<Binaire> & wbin = watchesBin[toInt(p)];

    bogoProps += wbin.size();
    for(int k = 0;k<wbin.size();k++) {
      Lit imp = wbin[k].implied;
      if(value(imp) == l_False) {
        if (handleConflict(*wbin[k].clause, num_props))
            return wbin[k].clause;
      }

      if(value(imp) == l_Undef) {
        uncheckedEnqueue(imp,wbin[k].clause);
      }
    }

    if (backup.running
        && watchBackup.flags[toInt(p)] == false
    ) {
        watchBackup.ws[toInt(p)] = watches[toInt(p)];
        watchBackup.flags[toInt(p)] = true;
        watchBackup.changed.push(toInt(p));
    }

    bogoProps += ws.size();
    for (i = j = (Watched*)ws, end = i + ws.size();  i != end;){
      if(value(i->blocked)==l_True) { // Clause is sat
        *j++ = *i++;
        continue;
      }
      Lit bl = i->blocked;
      Clause& c = *(i->wcl);
      i++;
      bogoProps += 5;

      if (backup.running
          && backup.touchedClauses.find(&c) == backup.touchedClauses.end()
      ) {
          backup.touchedClauses.insert(&c);
          c.saveLiterals();
      }

      // Make sure the false literal is data[1]:
      Lit false_lit = ~p;
      if (c[0] == false_lit)
        c[0] = c[1], c[1] = false_lit;

      assert(c[1] == false_lit);

      // If 0th watch is true, then clause is already satisfied.
      Lit first = c[0];
      if (value(first) == l_True){
        j->wcl = &c;
        j->blocked = first;
        j++;
      }else{
        // Look for new watch:
        for (int k = 2; k < c.size(); k++)
          if (value(c[k]) != l_False){
            c[1] = c[k]; c[k] = false_lit;

            const int wsNum = toInt(~c[1]);
            //Save ws before changing it
            if (backup.running
                && watchBackup.flags[wsNum] == false
            ) {
                watchBackup.ws[wsNum] = watches[wsNum];
                watchBackup.flags[wsNum] = true;
                watchBackup.changed.push(wsNum);
            }

            watches[wsNum].push();
            watches[wsNum].last().wcl = &c;
            watches[wsNum].last().blocked = c[0];
            goto FoundWatch; }

        // Did not find watch -- clause is unit under assignment:
        j->wcl = &c;
        j->blocked = bl;
        j++;

        if (value(first) == l_False){
            if (handleConflict(c, num_props)) {
                confl = &c;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            } else {
                goto FoundWatch;
            }
        } else {
            uncheckedEnqueue(first, &c);
            #ifdef DYNAMICNBLEVEL
            if(backup.stage == 0
                && c.learnt()
                && c.activity()>2
            ) {
                MYFLAG++;
                int nblevels =0;
                for(int i=0;i<c.size();i++) {
                    int l = level[var(c[i])];
                    if (permDiff[l] != MYFLAG) {
                        permDiff[l] = MYFLAG;
                        nblevels++;
                    }
                }
                if(nblevels+1<c.activity()) {
                    c.setActivity(nblevels);
                }
           }
            #endif
        }
      }
      FoundWatch:;
    }
    ws.shrink(i - j);
  }
  propagations+=num_props;
  simpDB_props-=num_props;

  return confl;
}



/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
  bool operator () (Clause* x, Clause* y) {
    // First criteria
    if(x->size()> 2 && y->size()==2) return 1;

    if(y->size()>2 && x->size()==2) return 0;
    if(x->size()==2 && y->size()==2) return 0;

    // Second one
    if(x->activity()> y->activity()) return 1;
    if(x->activity()< y->activity()) return 0;

    return x->size() < y->size();
  }};

struct gainedSorter {
    bool operator () (Clause* x, Clause* y) {
        //int64_t actX = x->getGainedBogoProps() + x->getGainedDecisions()*200;
        //int64_t actY = y->getGainedBogoProps() + y->getGainedDecisions()*200;
        //if (actX > actY) return 0;
        //if (actX < actY) return 1;
        return (x->getGainedBogoProps() > y->getGainedBogoProps());
    }
};

void Solver::printClauseUsefulnessStats()
{
    static int cleanNo = 0;
    vec<Clause*> backupLearnts;
    backupLearnts = learnts;
    sort(backupLearnts, gainedSorter());

    fprintf(stderr, "c Cleaning clauses (clean number %d). Current Clause usefulness stats:\n", cleanNo);
    for(int i = 0; i < backupLearnts.size(); i++) {
        Clause* c = backupLearnts[i];
        dumpFile << "INSERT INTO data(cleanno, idx, size, glue, conflicts, props, bogoprops, decisions) VALUES("
        << cleanNo << " , "
        << c->getIndex() << " , "
        << c->size() << " , "
        << c->activity()  << " , "
        << c->getNumConflicted()  << " , "
        << c->getGainedProps()  << " , "
        << c->getGainedBogoProps() << " , "
        << c->getGainedDecisions()
        << ");" << std::endl;

        c->clearStats();
    }
    fprintf(stderr, "c End of this round of database cleaning\n");
    cleanNo++;
}


void Solver::reduceDB()
{
  int     i, j;


    nbReduceDB++;
    printClauseUsefulnessStats();

    sort(learnts, reduceDB_lt());

    for (i = j = 0; i < learnts.size() / RATIOREMOVECLAUSES; i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity()>2){
          removeClause(*learnts[i]);
        }
        else
          learnts[j++] = learnts[i];
      }
      for (; i < learnts.size(); i++){
        learnts[j++] = learnts[i];
    }
      learnts.shrink(i - j);
      nof_learnts   *= learntsize_inc;
}


void Solver::removeSatisfied(vec<Clause*>& cs)
{
    int i,j;
    for (i = j = 0; i < cs.size(); i++){
        if (satisfied(*cs[i]))
            removeClause(*cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != NULL)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.

|________________________________________________________________________________________________@*/

static long curRestart = 1,cons=0,conf4Stats=0;

lbool Solver::search(int nof_conflicts, int nof_learnts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictsC = 0;
    vec<Lit>    learnt_clause;
    int nblevels=0,nbCC=0,merged=0;
    starts++;
    bool first = true;

    for (;;){
        Clause* confl = propagate();

        //Conflict at a later stage.
        if (backup.running
            && confl != NULL
            && backup.stage == 1
        ) {
            #ifdef RESTORE_FULL
            printf("Somebody else (maybe bin clause) did the conflict -- stage is one, going 2\n");
            #endif
            fullCancelUntil(backup.level, backup.sublevel);
            backup.stage = 2;
            continue;
        }

        if (confl != NULL){
            assert(backup.stage == 0);

            // CONFLICT
            conflicts++; conflictsC++;cons++;nbCC++;
            if (decisionLevel() == 0) return l_False;

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level,nblevels,merged);


            conf4Stats++;
            nbDecisionLevelHistory.push(nblevels);
            totalSumOfDecisionLevel += nblevels;

            cancelUntil(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
              assert(decisionLevel() == 0);
              uncheckedEnqueue(learnt_clause[0]);
              nbUn++;
            }else{
              Clause* c = Clause_new(learnt_clause, clIndex++, true);
              learnts.push(c);
              c->setActivity(nblevels); // LS
              if(nblevels<=2) nbDL2++;
              if(c->size()==2) nbBin++;
              attachClause(*c);

              uncheckedEnqueue(learnt_clause[0], c);

              if (backup.running
                  && backup.stage == 0
              ) {
                  saveState();
                  #ifdef RESTORE
                  printf("Saving state after conflict at dec level: %d, sublevel: %d\n", decisionLevel(), trail.size());
                  #endif
              }
            }
              varDecayActivity();
        }else{
            if (backup.stage == 0
              && nbDecisionLevelHistory.isvalid()
              && ((nbDecisionLevelHistory.getavg()*0.7) > (totalSumOfDecisionLevel / conf4Stats))
            ) {
              nbDecisionLevelHistory.fastclear();
              progress_estimate = progressEstimate();
              cancelUntil(0);
              return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (backup.stage == 0
                && decisionLevel() == 0 && !simplify()
            ) {
                return l_False;
            }

            Lit next = lit_Undef;

            if (backup.stage == 0
                && ((cons-curRestart * nbclausesbeforereduce) >=0)
            ) {
                curRestart = (conflicts/ nbclausesbeforereduce)+1;
                reduceDB();
                nbclausesbeforereduce += 500;
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);

            if (backup.running
                && backup.stage == 0
            ) {
                saveState();
                #ifdef RESTORE
                printf("Saving state after pickbranch at dec level: %d, sublevel: %d\n", decisionLevel(), trail.size());
                printf("sublevel: %d, level: %d, qhead:%d\n", trail.size(), decisionLevel(), qhead);
                #endif
            }
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


bool Solver::solve(const vec<Lit>& assumps)
{
    model.clear();
    conflict.clear();

    nbDecisionLevelHistory.initSize(100);
    totalSumOfDecisionLevel = 0;

    if (!ok) return false;

    assumps.copyTo(assumptions);

    double nof_conflicts = restart_first;
    nof_learnts   = nClauses() * learntsize_factor;

    if(nof_learnts <nbclausesbeforereduce) {
      nbclausesbeforereduce = (nof_learnts/2 < 5000) ? 5000 : nof_learnts/2;
    }
    lbool   status        = l_Undef;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    // Search:
    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= restart_inc;
 //LS mis dans reduceDB lui meme       nof_learnts   *= learntsize_inc;


    }

    if (verbosity >= 1)
        reportf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
#ifndef NDEBUG
        verifyModel();
#endif
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }
#ifdef LS_STATS_NBBUMP
        for(int i=0;i<learnts.size();i++)
                printf("## %d %d %d\n",learnts[i]->size(),learnts[i]->activity(),(unsigned int)learnts[i]->nbBump());
#endif
    cancelUntil(0);
    return status == l_True;
}

//=================================================================================================
// Debug methods:


void Solver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++){
        assert(clauses[i]->mark() == 0);
        Clause& c = *clauses[i];
        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        reportf("unsatisfied clause: ");
        printClause(*clauses[i]);
        reportf("\n");
        failed = true;
    next:;
    }

    assert(!failed);

    reportf("Verified %d original clauses.\n", clauses.size());
}


void Solver::checkLiteralCount()
{
    // Check that sizes are calculated correctly:
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0)
            cnt += clauses[i]->size();

    if ((int)clauses_literals != cnt){
        fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
        assert((int)clauses_literals == cnt);
    }
}

