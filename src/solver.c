// TODO: all solutions, not just the first one it finds -> add negative of choices as new clause
// TODO: check that everything is correct
// TODO: conflict clause minimization
// TODO: probing -> some sort of way to do it along side preprocessing
// TODO: restarts
// TODO: clause deleting

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
		// if (clauses.clauses[i].length > 1) continue;
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
	if (solver->watched_clauses[0].clauses == NULL) return;
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
	printf("\n");
}

void print_reason(struct solver* solver) {
	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] != vundef) {
			printf("%d -> %d\n", solver->reason[i], i);
		}
	}
	printf("\n");
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

	// printf("level\n");
	// print_level(solver);

	// printf("reason\n");
	// print_reason(solver);

	printf("queue %d\n", solver->queue);

	printf("---\n");
}

void destroy_solver(struct solver* solver) {
	for (int i = 0; i < solver->problem.length; i++)
		free(solver->problem.clauses[i].values);
	free(solver->problem.clauses);
	free(solver->units.values);

	free(solver->variables);
	free(solver->reason);
	free(solver->level);
	for (int b = 0; b < 2; b++) {
		for (int i = 1; i < solver->len_variables+1; i++)
			free(solver->watched_clauses[b].clauses[i].values);
		free(solver->watched_clauses[b].clauses);
	}
	free(solver->trail.values);
	free(solver->decisions.values);

	free(solver);
}

void new_solution(struct solver* solver) {
	solver->solutions++;
	printf("\nv ");
	print_variables(solver);
}

void unsat(struct solver* solver) {
	solver->solved = true;
	solver->result = false;

	printf("\ns UNSAT\n");
}
void sat(struct solver* solver) {
	solver->solved = true;
	solver->result = true;

	new_solution(solver);

	printf("\ns SAT\n");
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

void extend_clauses(struct clauses* clauses, struct clause clause) {
	clauses->length++;
	clauses->clauses = realloc(clauses->clauses, clauses->length * sizeof(struct clause));
	clauses->clauses[clauses->length-1] = clause;
}

void remove_clauses_unord(struct clauses* clauses, unsigned index) {
	clauses->length--;
	clauses->clauses[index] = clauses->clauses[clauses->length];
	clauses->clauses = realloc(clauses->clauses, clauses->length * sizeof(struct clause));
}

bool clause_contains(struct clause clause, value literal) {
	for (int i = 0; i < clause.length; i++)
		if (clause.values[i] == literal)
			return true;
	return false;
}

void assign(struct solver* solver, value value, int reason) {
	int index = abs(value);
	enum vbool val = get_vbool(value);
	solver->variables[index] = val;
	solver->level[index] = solver->decisions.length;
	solver->reason[index] = reason;
	extend_clause(&solver->trail, value);
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

bool preprocess_unit_propagate(struct solver* solver) {
	bool change = false;

	for (int clause_i = 0; clause_i < solver->problem.length; clause_i++) {
		struct clause* clause = &solver->problem.clauses[clause_i];
		for (int i = 0; i < clause->length; i++) {
			value l = clause->values[i];
			if (solver->variables[abs(l)] == get_vbool(l)) {
				// satisfied
				remove_clauses_unord(&solver->problem, clause_i--);
				change = true;
				break;
			} else if (solver->variables[abs(l)] == get_vbool(-l)) {
				// variable is false
				remove_clause_unord(clause, i--);
				change = true;
				if (clause->length == 1) {
					// unit clause
					value unit = clause->values[0];
					if (solver->variables[abs(unit)] == get_vbool(-unit)) {
						unsat(solver);
						return true;
					}
					if (solver->variables[abs(unit)] == vundef) {
						extend_clause(&solver->units, unit);
						assign(solver, unit, -1);
						solver->queue++;
					}
					remove_clauses_unord(&solver->problem, clause_i--);
					break;
				}
			}
		}
	}

	return change;
}

bool preprocess_pure_literals(struct solver* solver) {
	bool change = false;

	int* counts[2];
	counts[0] = calloc((solver->len_variables+1), sizeof(int));
	counts[1] = calloc((solver->len_variables+1), sizeof(int));

	for (int i = 0; i < solver->units.length; i++) {
		counts[0][i]++;
		counts[1][i]++;
	}

	for (int clause_i = 0; clause_i < solver->problem.length; clause_i++) {
		struct clause clause = solver->problem.clauses[clause_i];
		for (int i = 0; i < clause.length; i++) {
			value l = clause.values[i];
			counts[l>0][abs(l)]++;
		}
	}
	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] != vundef) continue;
		if (counts[0][i] == 0) {
			assign(solver, i, -1);
			extend_clause(&solver->units, i);
			change = true;
		} else if (counts[1][i] == 0) {
			assign(solver, -i, -1);
			extend_clause(&solver->units, -i);
			change = true;
		}
	}

	free(counts[0]);
	free(counts[1]);

	return change;
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
			return;
		}
	}

	// TODO: more preprocessing
	printf("%d\n", solver->problem.length);
	while (
			!solver->solved
			&& (
				preprocess_unit_propagate(solver)

				// comment out when finding all solutions
				|| preprocess_pure_literals(solver)

				// TODO: (X | Y) & (X | -Y) -> X = failed literal probing (how?)
				// TODO: subsumed clauses?
			   )
		  );
	printf("%d\n", solver->problem.length);
}

int unit_propagate(struct solver* solver) {
	while (solver->queue < solver->trail.length) {
		value check = solver->trail.values[solver->queue++];
		struct clause clauses_i = solver->watched_clauses[check<0].clauses[abs(check)];
		struct clause to_remove = {NULL, 0};

		for (int var_i = 0; var_i < clauses_i.length; var_i++) {
			int clause_i = clauses_i.values[var_i];
			struct clause clause = solver->problem.clauses[clause_i];

			// make sure the literal is in [1]
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
				if (solver->variables[abs(v)] != get_vbool(-v)) {
					extend_clause(&to_remove, var_i);
					clause.values[1] = v;
					clause.values[i] = -check;
					extend_clause(&solver->watched_clauses[v>0].clauses[abs(v)], clause_i);
					goto unit_propagate_next;
				}
			}

			// couldnt find any, is unit
			if (solver->variables[abs(clause.values[0])] != vundef) {
				for (int i = to_remove.length-1; i >= 0; i--) {
					int rem = to_remove.values[i];
					remove_clause_unord(&solver->watched_clauses[check<0].clauses[abs(check)], rem);
				}
				return clause_i;
			} else {
				assign(solver, first, clause_i);
			}
unit_propagate_next:;
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

	printf("guessing error\n");
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

int backtrack_level(struct solver* solver, struct clause new) {
	if (new.length == 1) return 0;
	int highest = 0;
	int second = 0;
	for (int i = 0; i < new.length; i++) {
		int level = solver->level[abs(new.values[i])];
		if (level > highest) {
			second = highest;
			highest = level;
		} else if (level > second) {
			second = level;
		}
	}
	return second;
}

void backtrack_learnt(struct solver* solver, struct clause new) {
	int level = backtrack_level(solver, new);
	while (solver->decisions.length > level) undo_decision(solver);
	solver->queue = solver->trail.length;

	if (new.length == 1) {
		assign(solver, new.values[0], -1);
	} else {
		// TODO: optimize

		// put the unit in [0] and a current level literal in [1]
		for (int i = 1; i < new.length; i++) {
			value l = new.values[i];
			if (solver->variables[abs(l)] == vundef) {
				new.values[i] = new.values[0];
				new.values[0] = l;
			} else if (solver->level[abs(l)] > solver->level[abs(new.values[1])]) {
				new.values[i] = new.values[1];
				new.values[1] = l;
			}
		}
		add_watched_clause(solver, solver->problem.length-1);
		assign(solver, new.values[0], solver->problem.length-1);
	}
}


int count_cur_level(struct solver* solver, struct clause clause) {
	int n = 0;
	for (int i = 0; i < clause.length; i++)
		if (solver->level[abs(clause.values[i])] == solver->decisions.length)
			n++;
	return n;
}

void resolve(struct clause* left, struct clause right, value literal) {
	for (int i = 0; i < left->length; i++) {
		if (left->values[i] == -literal) {
			remove_clause_unord(left, i);
			break;
		}
	}

	for (int i = 0; i < right.length; i++) {
		value l = right.values[i];
		if (l != literal && !clause_contains(*left, l)) {
			extend_clause(left, l);
		}
	}
}

struct clause analyze(struct solver* solver, int conflict) {
	struct clause ret;
	ret.length = solver->problem.clauses[conflict].length;
	ret.values = malloc(ret.length*sizeof(value));
	memcpy(ret.values, solver->problem.clauses[conflict].values, ret.length*sizeof(value));

	int index = solver->trail.length-1;

	while (count_cur_level(solver, ret) > 1) {
		value literal = solver->trail.values[index--];
		if (clause_contains(ret, -literal)) {
			resolve(&ret, solver->problem.clauses[solver->reason[abs(literal)]], literal);
		}
	}

	// TODO: minimize

	return ret;
}

void probe(struct solver* solver) {
	// TODO: for each literal - try true/false
	// if conflict -> that literal is opposite, learn the conflict (if good/short)
	// if variable true in both cases -> new unit
}

struct solver* cdcl(struct solver* solver) {
	// TODO: clean up goto
	if (solver->solved) return solver;

	init_two_watched(solver);
	probe(solver);

	while (!solver->solved) {
		int conflict;
		while ((conflict = unit_propagate(solver)) != -1) {

			if (++solver->conflicts%solver->len_variables == 0) {
				printf(".");
				// printf("%d\n", solver->problem.length);
				fflush(stdout);
			}

			if (solver->decisions.length == 0) {
				unsat(solver);
				goto cdcl_end;
			}

			struct clause new = analyze(solver, conflict);
			if (new.length == 0) {
				unsat(solver);
				goto cdcl_end;
			}

			if (new.length == 1) extend_clause(&solver->units, new.values[0]);
			else extend_clauses(&solver->problem, new);

			backtrack_learnt(solver, new);
		}

		if (solver->trail.length == solver->len_variables) sat(solver);
		else assign_guess(solver, guess(solver));
	}
cdcl_end:
	return solver;
}

struct solver* solve(FILE* file) {
	struct solver* solver = malloc(sizeof(struct solver));

	struct clause  nilclause  = {NULL, 0};
	struct clauses nilclauses = {NULL, 0};

	solver->solved				= false;
	solver->problem				= nilclauses;
	solver->units				= nilclause;
	solver->variables			= NULL;
	solver->len_variables		= 0;
	solver->reason				= NULL;
	solver->level				= NULL;
	solver->watched_clauses[0]	= nilclauses;
	solver->watched_clauses[1] 	= nilclauses;
	solver->queue				= 0;
	solver->trail				= nilclause;
	solver->decisions			= nilclause;
	solver->solutions			= 0;
	solver->conflicts 			= 0;


	parse(file, solver);
	preprocess(solver);
	return cdcl(solver);
}
