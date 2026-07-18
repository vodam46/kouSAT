#include <stdbool.h>
#include <stdlib.h>

#include "int_arr.h"
#include "solver.h"
#include "clause.h"
#include "occurs.h"

void free_occurs(struct solver* solver) {
	for (int i = 1; i < solver->len_variables+1; i++) {
		free(solver->occurs[0][i].arr);
		free(solver->occurs[1][i].arr);
	}
	free(solver->occurs[0]);
	free(solver->occurs[1]);
}

void add_occurence(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int var_i = 0; var_i < clause.length; var_i++) {
		value var = clause.values[var_i];
		extend_int_arr(&solver->occurs[var>0][abs(var)], index);
	}
}

void build_occurence_list(struct solver* solver) {
	struct int_arr** occurs = solver->occurs;

	occurs[0] = malloc((solver->len_variables+1)*sizeof(struct int_arr));
	occurs[1] = malloc((solver->len_variables+1)*sizeof(struct int_arr));
	for (int i = 0; i < solver->len_variables+1; i++)
		for (int p = 0; p < 2; p++)
			occurs[p][i] = nil_int_arr;

	for (int clause_i = 0; clause_i < solver->problem.length; clause_i++)
		add_occurence(solver, clause_i);
}

void delete_occurence(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int i = 0; i < clause.length; i++) {
		value v = clause.values[i];
		remove_int_arr_value(&solver->occurs[v>0][abs(v)], index);
	}
}
