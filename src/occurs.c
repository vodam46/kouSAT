#include <stdbool.h>
#include <stdlib.h>

#include "int_arr.h"
#include "solver.h"
#include "clause.h"
#include "occurs.h"

void free_occurs(struct solver* solver, struct int_arr** occurs) {
	for (int i = 1; i < solver->len_variables+1; i++) {
		free(occurs[0][i].arr);
		free(occurs[1][i].arr);
	}
	free(occurs[0]);
	free(occurs[1]);
	free(occurs);
}

void add_occurence(struct clause clause, int index, struct int_arr** occurs) {
	for (int var_i = 0; var_i < clause.length; var_i++) {
		value var = clause.values[var_i];
		extend_int_arr(&occurs[var>0][abs(var)], index);
	}
}

struct int_arr** build_occurence_list(struct clauses problem, int len_variables) {
	struct int_arr** occurs;
	occurs = malloc(2*sizeof(struct int_arr*));

	occurs[0] = malloc((len_variables+1)*sizeof(struct int_arr));
	occurs[1] = malloc((len_variables+1)*sizeof(struct int_arr));
	for (int i = 0; i < len_variables+1; i++)
		for (int p = 0; p < 2; p++)
			occurs[p][i] = nil_int_arr;

	for (int clause_i = 0; clause_i < problem.length; clause_i++)
		add_occurence(problem.clauses[clause_i], clause_i, occurs);

	return occurs;
}

void delete_occurence(struct clauses problem, struct int_arr** occurs, int index) {
	struct clause clause = problem.clauses[index];
	for (int i = 0; i < clause.length; i++) {
		value v = clause.values[i];
		remove_int_arr_value(&occurs[v>0][abs(v)], index);
	}
}

void remove_clause_occurence(struct clauses* problem, struct int_arr** occurs, int index) {
	delete_occurence(*problem, occurs, index);
	if (index != problem->length-1) {
		delete_occurence(*problem, occurs, problem->length-1);
		remove_clauses_unord(problem, index);
		add_occurence(problem->clauses[index], index, occurs);
	} else {
		remove_clauses_unord(problem, index);
	}
}

