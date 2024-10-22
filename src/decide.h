#ifndef _decide_h_INCLUDED
#define _decide_h_INCLUDED

struct kissat;

void kissat_decide (struct kissat *);
void kissat_internal_assume (struct kissat *, unsigned lit);
unsigned kissat_next_decision_variable (struct kissat *);

void kissat_set_external_decision_function(int (*function) (struct kissat *, int *));

#define INITIAL_PHASE (GET_OPTION (phase) ? 1 : -1)

#endif
