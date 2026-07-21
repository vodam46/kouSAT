#pragma once

// TODO: same way as kissat?
// TODO: different way of printing?
// TODO: more statistics
// TODO: calculated statistics

#define GET_CHAR(x) (_Generic((x), \
	int: "%d", \
	float: "%f" \
	))

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

// TODO: do it without GET_STAT, and just assume that the user defines the variables?
#define CALCULATED(X, GET_STAT) \
	X(average_learned_length, float, (float)GET_STAT(length_sum)/GET_STAT(conflicts)) \
	X(average_minimized, float, (float)GET_STAT(minimized)/GET_STAT(conflicts)) \




struct statistics {
#define CREATE_VARIABLE(name, type) type name;
	STATISTICS(CREATE_VARIABLE)
#undef CREATE_VARIABLE
};


void print_statistics(struct statistics);
