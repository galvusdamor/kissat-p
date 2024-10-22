#include "decide.h"
#include "inlineframes.h"
#include "inlineheap.h"
#include "inlinequeue.h"

#include <inttypes.h>

static unsigned
last_enqueued_unassigned_variable (kissat * solver)
{
  assert (solver->unassigned);
  const links *const links = solver->links;
  const value *const values = solver->values;
  unsigned res = solver->queue.search.idx;
  if (values[LIT (res)])
    {
      do
	{
	  res = links[res].prev;
	  assert (!DISCONNECTED (res));
	}
      while (values[LIT (res)]);
      kissat_update_queue (solver, links, res);
    }
#ifdef LOGGING
  const unsigned stamp = links[res].stamp;
  LOG ("last enqueued unassigned %s stamp %u", LOGVAR (res), stamp);
#endif
#ifdef CHECK_QUEUE
  for (unsigned i = links[res].next; !DISCONNECTED (i); i = links[i].next)
    assert (VALUE (LIT (i)));
#endif
  return res;
}

static unsigned
largest_score_unassigned_variable (kissat * solver)
{
  unsigned res = kissat_max_heap (&solver->scores);
  const value *const values = solver->values;
  while (values[LIT (res)])
    {
      kissat_pop_max_heap (solver, &solver->scores);
      res = kissat_max_heap (&solver->scores);
    }
#if defined(LOGGING) || defined(CHECK_HEAP)
  const double score = kissat_get_heap_score (&solver->scores, res);
#endif
  LOG ("largest score unassigned %s score %g", LOGVAR (res), score);
#ifdef CHECK_HEAP
  for (all_variables (idx))
    {
      if (!ACTIVE (idx))
	continue;
      if (VALUE (LIT (idx)))
	continue;
      const double idx_score = kissat_get_heap_score (&solver->scores, idx);
      assert (score >= idx_score);
    }
#endif
  return res;
}



int (*kissat_external_decision) (kissat *, int*) = 0;

void
kissat_set_external_decision_function(int (*function) (kissat *, int*)){
	kissat_external_decision = function;
}

int kissat_get_truth_of_external_var(kissat * solver, int external_var){
	if (external_var <= 0) return 2; // error
	if (external_var >= SIZE_STACK (solver->import)) return 2; // error
	const import *const import = &PEEK_STACK (solver->import, external_var);
	if (!import->imported) return 2; // error
	
	if (import->eliminated){
		return -2; // variable has been eliminated
	} else {
		const unsigned ilit = import->lit;
		return VALUE (ilit);
	}
}

int kissat_internal_from_external_var(kissat * solver, int external_var){
	if (external_var <= 0) return -1; // error
	if (external_var >= SIZE_STACK (solver->import)) return -1; // error
	const import *const import = &PEEK_STACK (solver->import, external_var);
	if (!import->imported) return -1; // error
	
	if (import->eliminated){
		return -2; // variable has been eliminated
	}

	return import->lit;
}


int kissat_phase_advice;

unsigned
kissat_next_decision_variable (kissat * solver)
{
  kissat_phase_advice = 0;
  if (kissat_external_decision != 0){
	int made_decision;
  	int chosen_var = kissat_external_decision(solver, &made_decision);

	// if the external procedure has made a suggestion that is valid, take it
	if (made_decision){
		int internal_var = kissat_internal_from_external_var(solver,ABS(chosen_var));
		if (internal_var >= 0){
			//printf("Taking external advice %d from %d\n", internal_var, chosen_var);
			
			if (chosen_var < 0)
				kissat_phase_advice = -1;
			else
				kissat_phase_advice = 1;
			
			if (VALUE(internal_var)) printf("ERROR\n", internal_var, chosen_var);

			return IDX(internal_var);
		}
	}
	// otherwise, we default to kissat's own heuristic
  }
  unsigned res;
  if (solver->stable)
    res = largest_score_unassigned_variable (solver);
  else
    res = last_enqueued_unassigned_variable (solver);

  LOG ("next decision %s", LOGVAR (res));

  return res;
}

static inline value
decide_phase (kissat * solver, unsigned idx)
{
  value res = 0;
  if (kissat_phase_advice){
  	res = kissat_phase_advice;
	return res;
  } 
  
  
  bool force = GET_OPTION (forcephase);

  value *target;
  if (force)
    target = 0;
  else if (!GET_OPTION (target))
    target = 0;
  else if (solver->stable || GET_OPTION (target) > 1)
    target = solver->phases.target + idx;
  else
    target = 0;

  value *saved;
  if (force)
    saved = 0;
  else if (GET_OPTION (phasesaving))
    saved = solver->phases.saved + idx;
  else
    saved = 0;


  if (!res && target && (res = *target))
    {
      LOG ("%s uses target decision phase %d", LOGVAR (idx), (int) res);
      INC (target_decisions);
    }

  if (!res && saved && (res = *saved))
    {
      LOG ("%s uses saved decision phase %d", LOGVAR (idx), (int) res);
      INC (saved_decisions);
    }

  if (!res)
    {
      res = INITIAL_PHASE;
      LOG ("%s uses initial decision phase %d", LOGVAR (idx), (int) res);
      INC (initial_decisions);
    }
  assert (res);

  return res;
}

void
kissat_decide (kissat * solver)
{
  START (decide);
  assert (solver->unassigned);
  INC (decisions);
  if (solver->stable)
    INC (stable_decisions);
  else
    INC (focused_decisions);
  solver->level++;
  assert (solver->level != INVALID_LEVEL);
  const unsigned idx = kissat_next_decision_variable (solver);
  const value value = decide_phase (solver, idx);
  unsigned lit = LIT (idx);
  if (value < 0)
    lit = NOT (lit);
  kissat_push_frame (solver, lit);
  assert (solver->level < SIZE_STACK (solver->frames));
  LOG ("decide literal %s", LOGLIT (lit));
  kissat_assign_decision (solver, lit);
  STOP (decide);
}

void
kissat_internal_assume (kissat * solver, unsigned lit)
{
  assert (solver->unassigned);
  assert (!VALUE (lit));
  solver->level++;
  assert (solver->level != INVALID_LEVEL);
  kissat_push_frame (solver, lit);
  assert (solver->level < SIZE_STACK (solver->frames));
  LOG ("assuming literal %s", LOGLIT (lit));
  kissat_assign_decision (solver, lit);
}
