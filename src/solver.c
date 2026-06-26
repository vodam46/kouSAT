// TODO: check that everything is correct
// TODO: probing -> some sort of way to do it alongside preprocessing
// TODO: clause deleting
// TODO: vsids queue
// TODO: harden parsing - fault tolerant
// TODO: clean up the code

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "solver.h"
#include "clause.h"
#include "dimacs.h"
#include "preprocess.h"

#define LUBY_MULT (1<<7)

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
	printf("0 \n");
}

void print_watched(struct solver* solver) {
	if (solver->watched_clauses[0] == NULL) return;
	for (int i = 1; i < solver->len_variables+1; i++) {
		printf("-%d = ", i);
		print_clause(solver->watched_clauses[0][i]);
		printf("%d = ", i);
		print_clause(solver->watched_clauses[1][i]);
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

void print_occur(struct solver* solver, struct clause** occur) {
	for (int b = 0; b < 2; b++) {
		printf("b %b\n", b);
		for (int i = 1; i < solver->len_variables+1; i++) {
			printf("%d = ", i);
			print_clause(occur[b][i]);
		}
	}
}

void print_solver(struct solver* solver) {
	printf("---\n");
	printf("solutions %d\n", solver->solutions);
	printf("conflicts %d\n", solver->conflicts);

	printf("problem\n");
	print_clauses(solver->problem);
	printf("units ");
	print_clause(solver->units);

	printf("watched\n");
	print_watched(solver);

	printf("variables\n");
	print_variables(solver);

	printf("trail\n");
	print_clause(solver->trail);

	printf("decisions\n");
	print_clause(solver->decisions);

	printf("level\n");
	print_level(solver);

	printf("reason\n");
	print_reason(solver);

	printf("queue %d\n", solver->queue);

	printf("preprocessing stack\n");
	print_clauses(solver->preprocessing_stack);

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
		if (solver->watched_clauses[b] == NULL) continue;
		for (int i = 1; i < solver->len_variables+1; i++)
			free(solver->watched_clauses[b][i].values);
		free(solver->watched_clauses[b]);
	}
	free(solver->trail.values);
	free(solver->decisions.values);
	if (solver->vsids != NULL)
		free(solver->vsids);
	if (solver->phase != NULL)
		free(solver->phase);

	for (int i = 0; i < solver->preprocessing_stack.length; i++)
		free(solver->preprocessing_stack.clauses[i].values);
	free(solver->preprocessing_stack.clauses);

	free(solver->ignore);
	free(solver->remove);

	free(solver);
}

void new_solution(struct solver* solver) {
	for (int i = 1; i < solver->len_variables+1; i++)
		if (solver->variables[i] == vundef)
			solver->variables[i] = vtrue;
	// reconstruct solution after variable elimination
	for (int pre_i = solver->preprocessing_stack.length-1; pre_i >= 0; pre_i--) {
		struct clause c = solver->preprocessing_stack.clauses[pre_i];
		value v = c.values[0];
		if (solver->variables[abs(v)] == get_vbool(v)) continue;
		for (int i = 1; i < c.length; i++) {
			int pv = c.values[i];
			if (solver->variables[abs(pv)] == get_vbool(pv)) goto reassign_skip;
		}
		solver->variables[abs(v)] = get_vbool(v);
reassign_skip:;
	}


	solver->solutions++;
	printf("\nv ");
	print_variables(solver);
}

void print_stats(struct solver* solver) {
	printf("\n");
	printf("minimized %d\n", solver->minimized);
	printf("conflicts %d\n", solver->conflicts);
	printf("restarts %d\n", solver->restarts);
	printf("clauses reduced %d\n", solver->clauses_reduced);
	printf("clauses removed %d\n", solver->clauses_removed);
	printf("variables eliminated %d\n", solver->variables_eliminated);
	printf("probed %d\n", solver->probed);
}

void unsat(struct solver* solver) {
	solver->solved = true;
	solver->result = false;

	print_stats(solver);
	printf("\ns UNSAT\n");
}
void sat(struct solver* solver) {
	solver->solved = true;
	solver->result = true;

	new_solution(solver);
	print_stats(solver);
	printf("\ns SAT\n");
}


void assign(struct solver* solver, value value, int reason) {
	int index = abs(value);
	enum vbool val = get_vbool(value);
	solver->variables[index] = val;
	solver->level[index] = solver->decisions.length;
	solver->reason[index] = reason;
	solver->phase[index] = val == vfalse ? false : true;
	solver->trail.values[solver->trail.length++] = value;
	// extend_clause(&solver->trail, value);
}

int unit_propagate(struct solver* solver) {
	while (solver->queue < solver->trail.length) {
		value check = solver->trail.values[solver->queue++];
		struct clause* clauses_i = &solver->watched_clauses[check<0][abs(check)];
		int left, right;

		for (left = right = 0; right < clauses_i->length;) {
			int clause_i = clauses_i->values[right];
			struct clause clause = solver->problem.clauses[clause_i];

			// make sure the literal is in [1]
			if (clause.values[0] == -check) {
				clause.values[0] = clause.values[1];
				clause.values[1] = -check;
			}
			right++;

			// first is true, can skip
			value first = clause.values[0];
			if (solver->variables[abs(first)] == get_vbool(first)) {
				clauses_i->values[left++] = clause_i;
				continue;
			}

			// look for a new watched literal
			int index = 0;
			for (int i = 2; i < clause.length; i++) {
				value v = clause.values[i];
				enum vbool val = solver->variables[abs(v)];

				if (val == vundef) index = i;
				else if (val == get_vbool(v)) { index = i; break; }
			}

			if (index) {
				value v = clause.values[index];
				clause.values[index] = clause.values[1];
				clause.values[1] = v;
				extend_clause(&solver->watched_clauses[v>0][abs(v)], clause_i);
				continue;
			}

			// couldnt find any, is unit
			clauses_i->values[left++] = clause_i;
			if (solver->variables[abs(clause.values[0])] != vundef) {
				while (right < clauses_i->length)
					clauses_i->values[left++] = clauses_i->values[right++];
				reduce_clause(clauses_i, right-left);
				return clause_i;
			} else {
				assign(solver, first, clause_i);
			}
		}
		reduce_clause(clauses_i, right-left);
	}

	return -1;
}

void init_vsids(struct solver* solver) {
	solver->vsids_factor = 0.95;
	for (int ci = 0; ci < solver->problem.length; ci++) {
		struct clause c = solver->problem.clauses[ci];
		for (int i = 0; i < c.length; i++) {
			solver->vsids[abs(c.values[i])] += 1.0/solver->problem.length;
		}
	}
}

void update_vsids(struct solver* solver, struct clause new) {
	for (int i = 1; i < solver->len_variables+1; i++) {
		solver->vsids[i] *= solver->vsids_factor;
	}
	for (int i = 0; i < new.length; i++) {
		solver->vsids[abs(new.values[i])] += 1.0-solver->vsids_factor;
	}
}

value guess(struct solver* solver) {
	double score = -1;
	value var = 0;
	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] == vundef && solver->vsids[i] > score) {
			score = solver->vsids[i];
			var = i;
		}
	}
	if (var == 0) {
		print_solver(solver);
		printf("guessing error\n");
		exit(1);
	}
	return solver->phase ? var : -var;
}

void assign_guess(struct solver* solver, value guess) {
	extend_clause(&solver->decisions, solver->trail.length);
	assign(solver, guess, -1);
}

void undo_decision(struct solver* solver) {
	int index = solver->decisions.values[solver->decisions.length-1];
	reduce_clause(&solver->decisions, 1);

	while (solver->trail.length > index) {
		value val = solver->trail.values[solver->trail.length-1];
		solver->variables[abs(val)] = vundef;
		solver->trail.length--;
		// reduce_clause(&solver->trail, 1);
	}
	solver->queue = solver->trail.length;
}

void add_watched_clause(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int j = 0; j < 2; j++) {
		value v = clause.values[j];
		extend_clause(&solver->watched_clauses[v>0][abs(v)], index);
	}
}

void init_two_watched(struct solver* solver) {
	for (int i = 0; i < solver->problem.length; i++) {
		add_watched_clause(solver, i);
	}
}

int backtrack_level(struct solver* solver, struct clause new) {
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

	int reason = -1;
	if (new.length != 1) {
		add_watched_clause(solver, solver->problem.length-1);
		reason = solver->problem.length-1;
	}
	assign(solver, new.values[0], reason);
}


int count_cur_level(struct solver* solver, struct clause clause) {
	int n = 0;
	for (int i = 0; i < clause.length; i++)
		if (solver->level[abs(clause.values[i])] == solver->decisions.length)
			n++;
	return n;
}

void minimize(struct solver* solver, struct clause* clause) {
	struct clause ret = *clause;

	// TODO: speed this up - dont go through the whole trail every time
	memset(solver->ignore, false, (solver->len_variables+1)*sizeof(bool));
	memset(solver->remove, false, (solver->len_variables+1)*sizeof(bool));
	for (int i = 0; i < ret.length; i++) solver->ignore[abs(ret.values[i])] = true;
	for (int lit_i = 0; lit_i < solver->trail.length; lit_i++) {
		value l = solver->trail.values[lit_i];
		int index = abs(l);
		if (solver->level[index] == 0) {
			solver->ignore[index] = true;
			solver->remove[index] = true;
			continue;
		}
		if (solver->reason[index] == -1) continue;
		struct clause reason = solver->problem.clauses[solver->reason[index]];
		bool can_ignore = true;
		for (int i = 0; i < reason.length; i++) {
			if (!solver->ignore[abs(reason.values[i])]) {
				can_ignore = false;
				break;
			}
		}
		if (can_ignore) {
			solver->ignore[index] = true;
			solver->remove[index] = true;
		}
	}
	for (int i = 0; i < ret.length; i++) {
		if (solver->remove[abs(ret.values[i])]) {
			solver->minimized++;
			remove_clause_unord(&ret, i--);
		}
	}
	*clause = ret;
}

struct clause analyze(struct solver* solver, int conflict) {
	struct clause ret;
	copy_clause(&ret, solver->problem.clauses[conflict]);

	int index = solver->trail.length-1;
	int count;
	while ((count = count_cur_level(solver, ret)) > 1) {
analyze_loop:;
		value literal = solver->trail.values[index--];
		if (clause_contains(ret, -literal)) {
			resolve(&ret, solver->problem.clauses[solver->reason[abs(literal)]], literal);
			count--;
		}
		if (count > 1) goto analyze_loop;
	}

	minimize(solver, &ret);

	// TODO: optimize
	for (int i = 1; i < ret.length; i++) {
		value l = ret.values[i];
		if (solver->level[abs(l)] == solver->decisions.length) {
			ret.values[i] = ret.values[0];
			ret.values[0] = l;
		} else if (solver->level[abs(l)] > solver->level[abs(ret.values[1])]) {
			ret.values[i] = ret.values[1];
			ret.values[1] = l;
		}
	}

	return ret;
}

void probe(struct solver* solver) {
	// TODO: optimize same way as preprocessing?
	// TODO: clean this up
	printf("probing\n");

	bool* seen[2];
	seen[0] = malloc(solver->len_variables*sizeof(bool));
	seen[1] = malloc(solver->len_variables*sizeof(bool));

	enum vbool* values[2];
	values[0] = malloc(solver->len_variables*sizeof(enum vbool));
	values[1] = malloc(solver->len_variables*sizeof(enum vbool));

probe_restart:
	bool change = false;

	if (unit_propagate(solver) != -1) {
		free(seen[0]);
		free(seen[1]);
		free(values[0]);
		free(values[1]);
		unsat(solver);
		return;
	}

	memset(seen[0], false, solver->len_variables*sizeof(bool));
	memset(seen[1], false, solver->len_variables*sizeof(bool));

	for (int i = 1; i < solver->len_variables+1; i++) {

		if (seen[0][i-1] && seen[1][i-1]) continue;
		if (solver->watched_clauses[0][i].length == 0
				&& solver->watched_clauses[1][i].length == 0) continue;
		if (solver->variables[i] != vundef) continue;

		bool check_extra = true;
		struct clause var_list[2];
		var_list[0] = (struct clause){NULL, 0};
		var_list[1] = (struct clause){NULL, 0};

		for (int p = 0; p < 2; p++) {
			if (solver->variables[i] != vundef) continue;
			if (solver->watched_clauses[!p][i].length == 0) continue;

			value var = p ? i : -i;

			assign_guess(solver, var);

			int conflict = unit_propagate(solver);

			if (conflict == -1) {
				if (solver->trail.length == solver->len_variables - solver->variables_eliminated) {
					free(seen[0]);
					free(seen[1]);
					free(values[0]);
					free(values[1]);
					free(var_list[0].values);
					free(var_list[1].values);
					sat(solver);
					return;
				}

				for (int j = 0; j < solver->len_variables; j++) {
					values[p][j] = vundef;
				}
				for (int j = solver->decisions.values[0]; j < solver->trail.length; j++) {
					int index = abs(solver->trail.values[j]);
					enum vbool val = solver->variables[index];
					seen[val==vtrue][index-1] = true;
					values[p][index-1] = val;
					extend_clause(&var_list[p], index);
				}
				undo_decision(solver);
				continue;
			}

			struct clause new = analyze(solver, conflict);
			value unit = new.values[0];
			free(new.values);

			undo_decision(solver);

			int now = solver->trail.length;

			extend_clause(&solver->units, unit);
			assign(solver, unit, -1);

			conflict = unit_propagate(solver);

			solver->probed += solver->trail.length - now;
			solver->conflicts++;
			change = true;
			check_extra = false;

			if (conflict != -1) {
				free(seen[0]);
				free(seen[1]);
				free(values[0]);
				free(values[1]);
				free(var_list[0].values);
				free(var_list[1].values);
				unsat(solver);
				return;
			}
		}
		if (check_extra) {
			struct clause arr;
			if (var_list[0].length < var_list[1].length)
				arr = var_list[0];
			else
				arr = var_list[1];
			for (int index = 0; index < arr.length; index++) {
				int i = arr.values[index];
				if (solver->variables[i+1] != vundef
						|| values[0][i] == vundef
						|| values[1][i] == vundef
						|| values[0][i] != values[1][i]) continue;
				int now = solver->trail.length;
				value var = i+1;
				if (values[0][i] == vtrue) {
					extend_clause(&solver->units, var);
					assign(solver, var, -1);
				} else if (values[0][i] == vfalse) {
					extend_clause(&solver->units, -var);
					assign(solver, -var, -1);
				}
				change = true;
				int conflict = unit_propagate(solver);
				solver->probed += solver->trail.length - now;
				if (conflict != -1) {
					free(seen[0]);
					free(seen[1]);
					free(values[0]);
					free(values[1]);
					free(var_list[0].values);
					free(var_list[1].values);
					unsat(solver);
					return;
				}
				if (solver->trail.length == solver->len_variables - solver->variables_eliminated) {
					free(seen[0]);
					free(seen[1]);
					free(values[0]);
					free(values[1]);
					free(var_list[0].values);
					free(var_list[1].values);
					sat(solver);
					return;
				}
			}
		}
		free(var_list[0].values);
		free(var_list[1].values);
	}

	if (change) {
		memset(seen[0], false, solver->len_variables*sizeof(bool));
		memset(seen[1], false, solver->len_variables*sizeof(bool));
		goto probe_restart;
	}
	free(seen[0]);
	free(seen[1]);
	free(values[0]);
	free(values[1]);
}

int luby(int i) {
	int k;
	if (__builtin_popcount(i+1) == 1)
		return 1 << (__builtin_popcount(i)-1);
	for (k = 1;; k++)
		if ((1 << (k - 1)) <= i && i < (1 << k) - 1)
			return luby (i - (1 << (k-1)) + 1);
}

void restart(struct solver* solver) {
	printf("r");
	fflush(stdout);
	solver->conflicts_until_restart = luby(++solver->restarts)*LUBY_MULT;
	while (solver->decisions.length > 0) undo_decision(solver);
}

bool resolve_conflict(struct solver* solver, int conflict) {
	if (++solver->conflicts%LUBY_MULT == 0) {
		printf(".");
		// printf("%d\n", solver->problem.length);
		fflush(stdout);
	}

	if (solver->decisions.length == 0) {
		unsat(solver);
		return true;
	}

	struct clause new = analyze(solver, conflict);

	if (new.length == 0) {
		free(new.values);
		unsat(solver);
		return true;
	}

	if (new.length == 1) {
		printf("(u %d)", new.values[0]);
		fflush(stdout);
		extend_clause(&solver->units, new.values[0]);
	} else {
		update_vsids(solver, new);
		extend_clauses(&solver->problem, new);
	}

	// TODO: clean this up?
	if (--solver->conflicts_until_restart == 0) {
		restart(solver);
		if (new.length == 1) assign(solver, new.values[0], -1);
		else add_watched_clause(solver, solver->problem.length-1);
	} else backtrack_learnt(solver, new);

	if (new.length == 1) free(new.values);

	return false;
}

struct solver* cdcl(struct solver* solver) {
	printf("searching\n");
	init_vsids(solver);

	while (!solver->solved) {
		int conflict;
		while ((conflict = unit_propagate(solver)) != -1)
			if (resolve_conflict(solver, conflict)) return solver;

		if (solver->trail.length == solver->len_variables - solver->variables_eliminated) sat(solver);
		else assign_guess(solver, guess(solver));
	}
	return solver;
}

void allocate_data(struct solver* solver) {
	printf("allocating data\n");
	solver->variables = malloc((solver->len_variables+1) * sizeof(enum vbool));
	solver->level = malloc((solver->len_variables+1) * sizeof(int));
	for (int i = 1; i < solver->len_variables+1; i++) solver->variables[i] = vundef;
	solver->reason = malloc((solver->len_variables+1) * sizeof(int));
	solver->phase = malloc((solver->len_variables+1) * sizeof(bool));
	memset(solver->phase, solver->len_variables+1, sizeof(bool));

	for (int i = 0; i < 2; i++){
		solver->watched_clauses[i] = malloc((solver->len_variables+1) * sizeof(struct clause));
		for (int j = 0; j < solver->len_variables+1; j++) {
			solver->watched_clauses[i][j] = (struct clause){NULL, 0};
		}
	}

	solver->vsids = malloc((solver->len_variables+1) * sizeof(double));
	for (int i = 1; i < solver->len_variables+1; i++) solver->vsids[i] = 0;

	solver->ignore = malloc((solver->len_variables+1)*sizeof(bool));
	solver->remove = malloc((solver->len_variables+1)*sizeof(bool));

	solver->trail.values = malloc((solver->len_variables-solver->variables_eliminated) * sizeof(value));
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
	solver->watched_clauses[0]	= NULL;
	solver->watched_clauses[1] 	= NULL;
	solver->queue				= 0;
	solver->trail				= nilclause;
	solver->decisions			= nilclause;
	solver->solutions			= 0;
	solver->conflicts 			= 0;
	solver->minimized			= 0;
	solver->vsids				= NULL;
	solver->phase				= NULL;
	solver->problem_len			= 0;
	solver->preprocessing_stack	= nilclauses;
	solver->clauses_removed		= 0;
	solver->clauses_reduced		= 0;
	solver->variables_eliminated= 0;
	solver->probed				= 0;

	solver->restarts				= 0;
	solver->conflicts_until_restart	= LUBY_MULT;


	parse(file, solver);
	allocate_data(solver);
	preprocess(solver);
	if (solver->solved) return solver;

	init_two_watched(solver);

	probe(solver);
	if (solver->solved) return solver;

	print_stats(solver);
	return cdcl(solver);
}
