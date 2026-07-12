#pragma once

// TODO: same way as kissat?
// TODO: different way of printing?
// TODO: more statistics
// TODO: calculated statistics

#define STATISTICS(X) \
	X(minimized, int) \
	X(clauses_removed, int) \
	X(clauses_reduced, int) \
	X(variables_eliminated, int) \
	X(probed, int) \
	X(probing_attempts, int) \
	X(solutions, int) \
	X(conflicts, int) \
	X(decisions, int) \
	X(cleaned, int) \
	X(propagations, int) \
	X(units, int) \
	X(length_sum, int) \



struct statistics {
#define CREATE_VARIABLE(name, type) type name;
	STATISTICS(CREATE_VARIABLE)
#undef CREATE_VARIABLE
};


void print_statistics(struct statistics);
