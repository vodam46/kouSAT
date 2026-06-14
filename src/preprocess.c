#include <stdlib.h>
#include <limits.h>
#include <string.h>

#include "solver.h"
#include "clause.h"
#include "preprocess.h"
#include "occurs.h"

bool unit_check(struct solver* solver, struct clause clause) {
	if (clause.length > 1) return false;
	if (clause.length == 0) {
		// TODO: isnt needed, but i dont want to remove this
		unsat(solver);
		return true;
	}
	value v = clause.values[0];
	if (solver->variables[abs(v)] == vundef) {
		extend_clause(&solver->units, v);
		assign(solver, v, -1);
		return false;
	}
	if (solver->variables[abs(v)] == get_vbool(v)) return false;
	unsat(solver);
	return true;
}

bool preprocess_unit_propagate(struct solver* solver, struct clause** occurs) {
	// printf("preprocess unit propagation\n");
	bool change = false;

	for (int unit_i = 0; unit_i < solver->units.length; unit_i++) {
		value v = solver->units.values[unit_i];
		if (occurs[0][abs(v)].length == 0 && occurs[1][abs(v)].length == 0) continue;
		for (int i = 0; i < occurs[v<0][abs(v)].length; i++) {
			int index = occurs[v<0][abs(v)].values[i];
			solver->clauses_reduced++;
			remove_clause_value(&solver->problem.clauses[index], -v);
			if (unit_check(solver, solver->problem.clauses[index])) return true;
		}

		while (occurs[v>0][abs(v)].length) {
			solver->clauses_removed++;
			remove_clause_occurence(&solver->problem, occurs, occurs[v>0][abs(v)].values[0]);
		}

		for (int b = 0; b < 2; b++) {
			free(occurs[b][abs(v)].values);
			occurs[b][abs(v)].values = NULL;
			occurs[b][abs(v)].length = 0;
		}
	}

	return change;
}

bool preprocess_pure_literals(struct solver* solver, struct clause** occurs) {
	// printf("preprocess pure literals\n");
	bool change = false;

	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] != vundef) continue;
		if (occurs[0][i].length == 0 && occurs[1][i].length >= 1) {
			// printf("pure %d\n", i);
			assign(solver, i, -1);
			extend_clause(&solver->units, i);
			change = true;
		}
		if (occurs[0][i].length >= 1 && occurs[1][i].length == 0) {
			// printf("pure %d\n", -i);
			assign(solver, -i, -1);
			extend_clause(&solver->units, -i);
			change = true;
		}
	}

	return change;
}

bool preprocess_subsume_clauses(struct solver* solver, struct clause** occurs) {
	// printf("preprocess subsume clauses\n");
	bool change = false;

	for (int ci = 0; ci < solver->problem.length; ci++) {
		struct clause clause = solver->problem.clauses[ci];
		value lit = 0;
		int count = INT_MAX;
		for (int i = 0; i < clause.length; i++) {
			value l = clause.values[i];
			if (occurs[l>0][abs(l)].length < count) {
				lit = l;
				count = occurs[l>0][abs(l)].length;
			}
		}

		int true_ci = ci;
		struct clause* occ = &occurs[lit>0][abs(lit)];
		for (int i = occ->length-1; i >= 0; i--) {
			int index = occ->values[i];
			struct clause other = solver->problem.clauses[index];
			if (index == true_ci) continue;
			if(subsumes(clause, other)) {
				solver->clauses_removed++;
				if (true_ci == solver->problem.length-1) true_ci = index;
				remove_clause_occurence(&solver->problem, occurs, index);
				change = true;
			}
		}
	}

	return change;
}

bool extra_clauses_under_limit(int count, int c) {
	return count <= 10 || count < (c + (c>>1) + 1);
}
// TODO: make this better
bool maybe_eliminate(
	struct solver* solver,
	value var,
	struct clause** occurs
) {
	struct clause* occurs_neg = &occurs[0][var];
	struct clause* occurs_pos = &occurs[1][var];

	if (occurs_neg->length > 2 || occurs_pos->length > 2) {
		int count = 0;
		int c = occurs_neg->length + occurs_pos->length;
		for (int l = 0; l < occurs_neg->length; l++) {
			struct clause left = solver->problem.clauses[occurs_neg->values[l]];
			for (int r = 0; r < occurs_pos->length; r++) {
				if (extra_clauses_under_limit(
							count + occurs_pos->length-1-r + (occurs_neg->length-1-l)*occurs_pos->length,
							c
							)) goto variable_eliminate;
				struct clause right = solver->problem.clauses[occurs_pos->values[r]];
				if (!resolve_trivial(left, right, var)
						&& !extra_clauses_under_limit(++count, c))
					return false;
			}
		}
		if (!extra_clauses_under_limit(count, c)) return false;
	}
variable_eliminate:;

	struct clauses pos = {NULL, 0};
	struct clauses neg = {NULL, 0};

	while (occurs_pos->length) {
		struct clause clause;
		int index = occurs_pos->values[0];
		copy_clause(&clause, solver->problem.clauses[index]);
		extend_clauses(&pos, clause);
		for (int i = 0; i < clause.length; i++) {
			if (clause.values[i] == var) {
				clause.values[i] = clause.values[0];
				clause.values[0] = var;
				break;
			}
		}
		extend_clauses(&solver->preprocessing_stack, clause);
		remove_clause_occurence(&solver->problem, occurs, index);
	}
	while (occurs_neg->length) {
		struct clause clause;
		int index = occurs_neg->values[0];
		copy_clause(&clause, solver->problem.clauses[index]);
		extend_clauses(&neg, clause);
		for (int i = 0; i < clause.length; i++) {
			if (clause.values[i] == -var) {
				clause.values[i] = clause.values[0];
				clause.values[0] = -var;
				break;
			}
		}
		extend_clauses(&solver->preprocessing_stack, clause);
		remove_clause_occurence(&solver->problem, occurs, index);
	}

	for (int p = 0; p < pos.length; p++) {
		struct clause pc = pos.clauses[p];
		for (int n = 0; n < neg.length; n++) {
			struct clause nc;
			copy_clause(&nc, neg.clauses[n]);
			if (resolve_trivial(pc, nc, var)) {
				free(nc.values);
				continue;
			}
			resolve(&nc, pc, var);
			if (nc.length == 0) {
				unsat(solver);
				break;
			}
			if (nc.length == 1) {
				if (unit_check(solver, nc)) {
					free(nc.values);
					free(neg.clauses);
					free(pos.clauses);
					return true;
				}
				free(nc.values);
			} else {
				add_occurence(nc, solver->problem.length, occurs);
				extend_clauses(&solver->problem, nc);
			}
		}
	}

	free(neg.clauses);
	free(pos.clauses);

	return true;
}

int qsort_func(const void* l, const void* r) {
	int res = ((int*)l)[1] - ((int*)r)[1];
	return res != 0 ? res : ((int*)l)[0] - ((int*)r)[0];
}
bool preprocess_variable_elimination(struct solver* solver, struct clause** occurs) {
	// printf("preprocess variable elimination\n");
	bool change = false;

	int skip = 0;
	int* variables = malloc(solver->len_variables * sizeof(int)*2);
	for (int i = 0; i < solver->len_variables; i++) {
		value var = i+1;
		if (solver->variables[i+1] != vundef
				|| occurs[0][var].length == 0
				|| occurs[1][var].length == 0
				|| (occurs[0][var].length >= 10 && occurs[1][var].length >= 10)) {
			skip++;
			continue;
		}
		variables[2*(i-skip)] = i+1;
		variables[2*(i-skip)+1] = occurs[0][i+1].length * occurs[1][i+1].length;
	}
	qsort(variables, solver->len_variables-skip, sizeof(int)*2, qsort_func);

	for (int i = 0; !solver->solved && i < solver->len_variables-skip; i++) {
		int var = variables[2*i];
		if (solver->variables[var] != vundef) continue;
		if (occurs[0][var].length == 0 || occurs[1][var].length == 0) continue;
		if (occurs[0][var].length >= 10 && occurs[1][var].length >= 10) continue;
		if (maybe_eliminate(solver, var, occurs)) {
			solver->variables_eliminated++;
			change = true;
		}
	}

	free(variables);

	return change;
}

// TODO: TAKES UP THE MAJORITY OF TIME ON SOME PROBLEMS
// FIX THIS
// like in SatElite - dont go through all the clauses every time
bool preprocess_self_subsume(struct solver* solver, struct clause** occurs) {
	// printf("preprocess self subsume\n");
	bool change = false;

	for (int ci = 0; ci < solver->problem.length; ci++) {
		struct clause clause = solver->problem.clauses[ci];
		if (clause.length > 10) continue;

		value lit = 0;
		value other = 0;
		int count = INT_MAX;
		for (int i = 0; i < clause.length; i++) {
			value l = clause.values[i];
			if (occurs[l>0][abs(l)].length < count) {
				other = lit;
				lit = l;
				count = occurs[l>0][abs(l)].length;
			}
		}

		for (int pi = 0; pi < clause.length; pi++) {
			value p = clause.values[pi];
			clause.values[pi] = -p;

			struct clause* occur;
			if (lit != p) occur = &occurs[lit<0][abs(lit)];
			else occur = &occurs[other<0][abs(other)];
			if (occurs[p<0][abs(p)].length < occur->length)
				occur = &occurs[p<0][abs(p)];

			for (int oi = occur->length-1; oi >= 0; oi--) {
				int index = occur->values[oi];
				if (index == ci) continue;
				struct clause* other = &solver->problem.clauses[index];
				if (subsumes(clause, *other)) {
					solver->clauses_reduced++;
					remove_clause_value(other, -p);
					remove_clause_value(occur, index);
					change = true;
					if (other->length == 0) {
						unsat(solver);
						return true;
					}
					if (unit_check(solver, *other)) return true;
				}
			}

			clause.values[pi] = p;
		}
	}

	return change;
}

void preprocess(struct solver* solver) {
	printf("preprocessing\n");
	solver->variables = malloc((solver->len_variables+1) * sizeof(enum vbool));
	solver->level = malloc((solver->len_variables+1) * sizeof(int));
	for (int i = 1; i < solver->len_variables+1; i++) solver->variables[i] = vundef;
	solver->reason = malloc((solver->len_variables+1) * sizeof(int));
	solver->phase = malloc((solver->len_variables+1) * sizeof(bool));
	memset(solver->phase, solver->len_variables+1, sizeof(bool));

	for (int i = 0; i < solver->units.length; i++) {
		value unit = solver->units.values[i];
		int index = abs(unit);
		enum vbool v = get_vbool(unit);
		if (solver->variables[index] == vundef) {
			assign(solver, unit, -1);
		} else if (solver->variables[index] != v) {
			unsat(solver);
			return;
		}
	}

	// TODO: more preprocessing
	// TODO: fix this loop -> dont run preprocessing that isnt needed
	printf("before %d\n", solver->problem.length);
	struct clause** occurs = build_occurence_list(solver->problem, solver->len_variables);
	while (
			!solver->solved
			&& (
				preprocess_unit_propagate(solver, occurs)
				|| preprocess_pure_literals(solver, occurs)

				// TODO: optimize
				|| preprocess_subsume_clauses(solver, occurs)
				|| preprocess_variable_elimination(solver, occurs)
				|| preprocess_self_subsume(solver, occurs)
			   )
		  );

	for (int i = 1; i < solver->len_variables+1; i++) {
		free(occurs[0][i].values);
		free(occurs[1][i].values);
	}
	free(occurs[0]);
	free(occurs[1]);
	free(occurs);

	printf("after  %d\n", solver->problem.length);
	printf("variables %d\n", solver->len_variables);
}
