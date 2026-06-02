// TODO: memset? how does it work
// TODO: with learning new clauses, it must be the last two assigned literals that are watched
// TODO: levels

#include <assert.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "solver.h"


enum vbool get_vbool(value v) {
	return v>0 ? vtrue : vfalse;
}

void print_clause(struct clause clause) {
	for (int i = 0; i < clause.length; i++) {
		printf("%d ", clause.values[i]);
	}
	printf("\n");
}

void print_clauses(struct clauses clauses) {
	for (int i = 0; i < clauses.length; i++) {
		printf("[%d] ", i);
		print_clause(clauses.clauses[i]);
	}
}

void print_variables(struct solver* solver) {
	if (solver->variables == NULL) {
		printf("unallocated\n");
		return;
	}
	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] == vundef) printf("?%d? ", i);
		if (solver->variables[i] == vfalse) printf("-%d ", i);
		if (solver->variables[i] == vtrue) printf("%d ", i);
	}
	printf("\n");
}

void print_watched(struct solver* solver) {
	for (int i = 1; i < solver->len_variables+1; i++) {
		printf("-%d = ", i);
		print_clause(solver->watched_clauses[0].clauses[i]);
		printf("%d = ", i);
		print_clause(solver->watched_clauses[1].clauses[i]);
	}
}

void print_level(struct solver* solver) {
	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] != vundef) {
			printf("(%d=%d) ", i, solver->level[i]);
		}
	}
}

void print_solver(struct solver* solver) {
	printf("---\n");
	printf("solutions %d\n", solver->solutions);
	printf("conflicts %d\n", solver->conflicts);

	// printf("problem\n");
	// print_clauses(solver->problem);
	// printf("units ");
	// print_clause(solver->units);

	// printf("watched\n");
	// print_watched(solver);

	printf("variables\n");
	print_variables(solver);

	printf("trail\n");
	print_clause(solver->trail);

	printf("decisions\n");
	print_clause(solver->decisions);

	printf("level\n");
	print_level(solver);

	printf("tocheck\n");
	print_clause(solver->tocheck);
	printf("---\n");
}

void new_solution(struct solver* solver) {
	solver->solutions++;
	printf("\nv ");
	print_variables(solver);
}

void unsat(struct solver* solver) {
	print_solver(solver);

	printf("\ns UNSAT\n");
	exit(0);
}
void sat(struct solver* solver) {
	print_solver(solver);

	printf("\ns SAT\n");
	exit(0);
}


// TODO: do it better - custom clause allocator?
// arena style allocate?
// instead of pointers store only indices of the start
// proper dynamic array with resizing

void extend_clause(struct clause* clause, value value) {
	clause->length++;
	clause->values = realloc(clause->values, clause->length * sizeof(value));
	clause->values[clause->length-1] = value;
}

void remove_clause_unord(struct clause* clause, unsigned index) {
	clause->length--;
	clause->values[index] = clause->values[clause->length];
	clause->values = realloc(clause->values, clause->length * sizeof(value));
}

// void remove_clause_ord(struct clause* clause, unsigned index) {

// }

void extend_clauses(struct clauses* clauses, struct clause clause) {
	clauses->length++;
	clauses->clauses = realloc(clauses->clauses, clauses->length * sizeof(struct clause));
	clauses->clauses[clauses->length-1] = clause;
}

// TODO: reason
void assign(struct solver* solver, value value, int reason) {
	int index = abs(value);
	enum vbool val = get_vbool(value);
	solver->variables[index] = val;
	solver->level[index] = solver->decisions.length;
	solver->reason[index] = reason;
	extend_clause(&solver->trail, value);
	extend_clause(&solver->tocheck, value);
}

void parse(FILE* file, struct solver* solver) {
	// TODO: make this different?
	char* line = NULL;
	size_t size = 0;
	getline(&line, &size, file);
	while (line[0] != 'p') {
		getline(&line, &size, file);
	}

	if (strncmp(line, "p cnf ", 6)) {
		printf("invalid problem line\n\"%s\"", line);
		exit(1);
	}
	int length;
	sscanf(line, "p cnf %d %d", &solver->len_variables, &length);
	free(line);

	int loaded = 0;
	struct clause clause = {NULL, 0};
	while (loaded < length) {
		value value = 0;
		fscanf(file, "%d", &value);
		if (value == 0) {
			if (clause.length == 1)
				extend_clause(&solver->units, clause.values[0]);
			else
				extend_clauses(&solver->problem, clause);

			clause = (struct clause){NULL, 0};
			loaded++;
		} else {
			extend_clause(&clause, value);
		}
	}

	fclose(file);
}

void preprocess(struct solver* solver) {
	solver->variables = malloc((solver->len_variables+1) * sizeof(enum vbool));
	solver->level = malloc((solver->len_variables+1) * sizeof(int));
	for (int i = 1; i < solver->len_variables+1; i++) solver->variables[i] = vundef;
	solver->reason = malloc((solver->len_variables+1) * sizeof(int));

	for (int i = 0; i < solver->units.length; i++) {
		value unit = solver->units.values[i];
		int index = abs(unit);
		enum vbool v = get_vbool(unit);
		if (solver->variables[index] == vundef) {
			assign(solver, unit, -1);
		} else if (solver->variables[index] != v) {
			unsat(solver);
		}
	}

	// TODO: actual preprocessing
}

int unit_propagate(struct solver* solver) {
	while (solver->tocheck.length > 0) {
		value check = solver->tocheck.values[0];
		remove_clause_unord(&solver->tocheck, 0);
		struct clause clauses_i = solver->watched_clauses[check<0].clauses[abs(check)];
		struct clause to_remove = {NULL, 0};

		for (int var_i = 0; var_i < clauses_i.length; var_i++) {
			int clause_i = clauses_i.values[var_i];
			struct clause clause = solver->problem.clauses[clause_i];
			if (clause.values[0] == -check) {
				clause.values[0] = clause.values[1];
				clause.values[1] = -check;
			}

			// first is true, can skip
			value first = clause.values[0];
			if (solver->variables[abs(first)] == get_vbool(first)) continue;

			// look for a new watched literal
			for (int i = 2; i < clause.length; i++) {
				value v = clause.values[i];
				if (solver->variables[abs(v)] != vfalse) {
					extend_clause(&to_remove, var_i);
					clause.values[1] = v;
					clause.values[i] = -check;
					extend_clause(&solver->watched_clauses[v>0].clauses[abs(v)], clause_i);
					goto unit_propagate_next;
				}
			}

			// couldnt find any, is unit
			if (solver->variables[abs(first)] != vundef) {
				free(solver->tocheck.values);
				solver->tocheck = (struct clause){NULL, 0};
				for (int i = to_remove.length-1; i >= 0; i--) {
					int rem = to_remove.values[i];
					remove_clause_unord(&solver->watched_clauses[check<0].clauses[abs(check)], rem);
				}
				return clause_i;
			} else {
				assign(solver, first, clause_i);
			}
unit_propagate_next:
		}
		for (int i = to_remove.length-1; i >= 0; i--) {
			int rem = to_remove.values[i];
			remove_clause_unord(&solver->watched_clauses[check<0].clauses[abs(check)], rem);
		}
	}


	return -1;
}

value guess(struct solver* solver) {
	// TODO: make proper guessing
	for (int i = 1; i < solver->len_variables+1; i++)
		if (solver->variables[i] == vundef)
			return i;

	exit(1);
	return 0;
}

void assign_guess(struct solver* solver, value guess) {
	extend_clause(&solver->decisions, solver->trail.length);
	assign(solver, guess, -1);
}

void undo_decision(struct solver* solver) {
	int index = solver->decisions.values[solver->decisions.length-1];
	remove_clause_unord(&solver->decisions, solver->decisions.length-1);

	while (solver->trail.length > index) {
		value val = solver->trail.values[solver->trail.length-1];
		solver->variables[abs(val)] = vundef;
		remove_clause_unord(&solver->trail, solver->trail.length-1);
	}
}

void backtrack_decision(struct solver* solver) {
	int decision_index = solver->decisions.values[solver->decisions.length-1];
	value value = solver->trail.values[decision_index];
	undo_decision(solver);
	assign(solver, -value, -1);
}

void backtrack_learnt(struct solver* solver, struct clause new) {
	int decision_index = solver->decisions.values[solver->decisions.length-1];
	value value = solver->trail.values[decision_index];
	undo_decision(solver);
	assign(solver, -value, -1);
}


void add_watched_clause(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int j = 0; j < 2; j++) {
		value v = clause.values[j];
		extend_clause(&solver->watched_clauses[v>0].clauses[abs(v)], index);
	}
}

void init_two_watched(struct solver* solver) {
	for (int i = 0; i < 2; i++){
		solver->watched_clauses[i].clauses = malloc((solver->len_variables+1) * sizeof(struct clause));
		solver->watched_clauses[i].length = solver->len_variables+1;
		for (int j = 0; j < solver->len_variables+1; j++) {
			solver->watched_clauses[i].clauses[j] = (struct clause){NULL, 0};
		}
	}

	for (int i = 0; i < solver->problem.length; i++) {
		add_watched_clause(solver, i);
	}
}

int count_cur_level(struct solver* solver, struct clause clause) {
	int n = 0;
	for (int i = 0; i < clause.length; i++)
		if (solver->level[clause.values[i]] == solver->decisions.length)
			n++;
	return n;
}

bool should_resolve(struct clause clause, value literal) {
	for (int i = 0; i < clause.length; i++)
		if (clause.values[i] == -literal)
			return true;
	return false;
}

void resolve(struct clause* left, struct clause right, value literal) {

}

struct clause analyze(struct solver* solver, int conflict) {
	struct clause ret;
	ret.length = solver->problem.clauses[conflict].length;
	ret.values = malloc(ret.length*sizeof(value));
	memcpy(ret.values, solver->problem.clauses[conflict].values, ret.length*sizeof(value));

	int index = solver->trail.length-1;

	// TODO:
	while (count_cur_level(solver, ret) > 1) {
		value literal = solver->trail.values[index];
		if (should_resolve(ret, literal)) {
			resolve(&ret, solver->problem.clauses[solver->reason[abs(literal)]], literal);
		}
	}

	return ret;
}

void cdcl(struct solver* solver) {
	// TODO: cdcl
	// TODO: simplify

	solver->solutions = 0;
	solver->conflicts = 0;

	init_two_watched(solver);

	while (true) {
		int conflict;
		while ((conflict = unit_propagate(solver)) != -1) {

			solver->conflicts++;
			if (solver->conflicts%solver->len_variables == 0) printf(".");

			if (solver->decisions.length == 0) {
				if (solver->solutions) sat(solver);
				else unsat(solver);
			}


			// struct clause new = analyze(solver, conflict);
			// if (new.length == 0) {
			// 	if (solver->solutions) sat(solver);
			// 	else unsat(solver);
			// }
			// if (new.length == 1) {
			// 	extend_clause(&solver->units, new.values[0]);
			// 	backtrack_learnt(solver, new);
			// }
			// else {
			// 	extend_clauses(&solver->problem, new);
			// 	add_watched_clause(solver, solver->problem.length-1);
			// 	backtrack_learnt(solver, new);
			// }
			backtrack_decision(solver);

		}

		if (solver->trail.length == solver->len_variables) {
			new_solution(solver);

			if (solver->decisions.length == 0) sat(solver);
			backtrack_decision(solver);

		} else {
			assign_guess(solver, guess(solver));
		}
	}
}

void solve(FILE* file) {
	struct solver solver = {
		.problem={NULL, 0},
		.units={NULL, 0},
		.variables=NULL,
		.len_variables=0,
		.reason=NULL,
		.level=NULL,
		.watched_clauses={NULL, 0},
		.tocheck={NULL, 0},
		.trail={NULL, 0},
		.decisions={NULL, 0},
	};

	parse(file, &solver);
	preprocess(&solver);
	cdcl(&solver);
}
