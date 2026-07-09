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
#include "watch.h"

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
		print_watches(solver->watched_clauses[0][i]);
		printf("%d = ", i);
		print_watches(solver->watched_clauses[1][i]);
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

void print_occur(struct solver* solver, struct int_arr** occur) {
	for (int b = 0; b < 2; b++) {
		printf("b %b\n", b);
		for (int i = 1; i < solver->len_variables+1; i++) {
			printf("%d = ", i);
			print_int_arr(occur[b][i]);
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
	print_int_arr(solver->units);

	printf("watched\n");
	print_watched(solver);

	printf("variables\n");
	print_variables(solver);

	printf("trail\n");
	print_int_arr(solver->trail);

	printf("decisions\n");
	print_int_arr(solver->decisions);

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
	free(solver->units.arr);

	free(solver->variables);
	free(solver->reason);
	free(solver->level);
	for (int b = 0; b < 2; b++) {
		if (solver->watched_clauses[b] == NULL) continue;
		for (int i = 1; i < solver->len_variables+1; i++)
			free(solver->watched_clauses[b][i].arr);
		free(solver->watched_clauses[b]);
	}
	free(solver->trail.arr);
	free(solver->decisions.arr);
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
	solver->trail.arr[solver->trail.length++] = value;
}

int unit_propagate(struct solver* solver) {
	while (solver->queue < solver->trail.length) {
		value check = solver->trail.arr[solver->queue++];
		struct watches* watches_p = &solver->watched_clauses[check<0][abs(check)];
		struct watches watches = solver->watched_clauses[check<0][abs(check)];
		int left, right;

		for (left = right = 0; right < watches.length;) {
			struct watch watcher = watches.arr[right];

			enum vbool var = solver->variables[abs(watcher.blocker)];
			enum vbool block = get_vbool(watcher.blocker);

			// TODO: separate into functions
			switch (watcher.type) {
				case long_clause:
					if (var == block) {
						watches.arr[left++] = watcher;
						right++;
						continue;
					}

					struct clause clause = solver->problem.clauses[watcher.index];

					// make sure the literal is in [1]
					if (clause.values[0] == -check) {
						clause.values[0] = clause.values[1];
						clause.values[1] = -check;
					}
					right++;

					// first is true, can skip
					value first = clause.values[0];
					struct watch w = create_watcher(clause, watcher.index, first);
					if (solver->variables[abs(first)] == get_vbool(first)) {
						watches.arr[left++] = w;
						continue;
					}

					// look for a new watched literal
					int index = 0;
					int level = INT_MAX;
					for (int i = 2; level > 0 && i < clause.length; i++) {
						value v = clause.values[i];
						enum vbool val = solver->variables[abs(v)];

						if (val == vundef) index = i;
						else if (val == get_vbool(v) && solver->level[abs(v)] < level) {
							index = i;
							level = solver->level[abs(v)];
						}
					}

					if (index) {
						value v = clause.values[index];
						clause.values[index] = clause.values[1];
						clause.values[1] = v;
						extend_watches(&solver->watched_clauses[v>0][abs(v)], w);
						continue;
					}

					// couldnt find any, is unit
					watches.arr[left++] = w;
					if (solver->variables[abs(first)] != vundef) {
						while (right < watches.length)
							watches.arr[left++] = watches.arr[right++];
						reduce_watches(watches_p, right-left);
						return w.index;
					} else {
						assign(solver, first, w.index);
					}
					break;

				case binary_clause:
					// first is undefined, assign it immediately
					if (var == vundef) {
						watches.arr[left++] = watcher;
						right++;
						assign(solver, watcher.blocker, watcher.index);
						// TODO: swap the literals in clause so the blocker is in [0]?

					// is true, can continue
					} else if (var == block) {
						watches.arr[left++] = watcher;
						right++;

					// is conflict
					} else {
						while (right < watches.length)
							watches.arr[left++] = watches.arr[right++];
						reduce_watches(watches_p, right-left);
						return watcher.index;
					}
					break;
			}

		}
		reduce_watches(watches_p, right-left);
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
	return solver->phase[var] ? -var : var;
}

void assign_guess(struct solver* solver, value guess) {
	extend_int_arr(&solver->decisions, solver->trail.length);
	assign(solver, guess, -1);
}

void undo_decision(struct solver* solver) {
	int index = solver->decisions.arr[solver->decisions.length-1];
	reduce_int_arr(&solver->decisions, 1);

	while (solver->trail.length > index) {
		value val = solver->trail.arr[solver->trail.length-1];
		solver->variables[abs(val)] = vundef;
		solver->trail.length--;
	}
	solver->queue = solver->trail.length;
}

void add_watched_clause(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int j = 0; j < 2; j++) {
		value v = clause.values[j];
		extend_watches(&solver->watched_clauses[v>0][abs(v)], create_watcher(clause, index, clause.values[1-j]));
	}
}
void remove_watched_clause(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int j = 0; j < 2; j++) {
		value v = clause.values[j];
		remove_watches_index(&solver->watched_clauses[v>0][abs(v)], index);
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
	int length = ret.length;

	// TODO: speed this up - dont go through the whole trail every time
	memset(solver->ignore, false, (solver->len_variables+1)*sizeof(bool));
	memset(solver->remove, false, (solver->len_variables+1)*sizeof(bool));

	for (int i = 0; i < ret.length; i++) solver->ignore[abs(ret.values[i])] = true;
	for (int i = 0; i < solver->decisions.arr[0]; i++) {
		int index = abs(solver->trail.arr[i]);
		solver->ignore[index] = true;
		solver->remove[index] = true;
	}

	for (int lit_i = solver->decisions.arr[0]; lit_i < solver->trail.length; lit_i++) {
		value l = solver->trail.arr[lit_i];
		int index = abs(l);
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
			if (solver->ignore[index] && !solver->remove[index])
				length--;
			solver->ignore[index] = true;
			solver->remove[index] = true;
		}
	}

	// self subsuming resolution on conflict clause
	// https://www.msoos.org/2010/08/on-the-fly-self-subsuming-resolution/
	if (length > 1) {
		for (int i = 1; i < ret.length; i++) {
			value l = ret.values[i];
			if (solver->remove[abs(l)]) continue;
			struct watches arr = solver->watched_clauses[l<0][abs(l)];
			for (int j = 0; j < arr.length; j++) {
				struct watch w = arr.arr[j];
				if (w.type != binary_clause) continue;
				if (!solver->remove[abs(w.blocker)] && solver->ignore[abs(w.blocker)] && clause_contains(ret, w.blocker)) {
					solver->remove[abs(l)] = true;
					length--;
					break;
				}
			}
			if (length == 1) break;
		}
	}

	int i = 0, r = 0;
	uint64_t mask = 0;
	for (; r < ret.length; r++) {
		if (!solver->remove[abs(ret.values[r])]) {
			mask |= get_mask(ret.values[r]);
			ret.values[i++] = ret.values[r];
		} else solver->minimized++;
	}
	reduce_clause(&ret, r-i);
	ret.mask = mask;

	*clause = ret;
}

struct clause analyze(struct solver* solver, int conflict) {
	struct clause ret;
	copy_clause(&ret, solver->problem.clauses[conflict]);
	ret.learned = true;

	int index = solver->trail.length-1;
	int count;
	while ((count = count_cur_level(solver, ret)) > 1) {
analyze_loop:;
		value literal = solver->trail.arr[index--];
		if (clause_contains(ret, -literal)) {
			resolve(&ret, solver->problem.clauses[solver->reason[abs(literal)]], literal);
			count--;
		}
		if (count > 1) goto analyze_loop;
	}

	// TODO: do this during resolution?
	// TODO: sort the literals according to their level?
	for (int i = 1; i < ret.length; i++) {
		value l = ret.values[i];
		if (solver->level[abs(l)] == solver->decisions.length) {
			ret.values[i] = ret.values[0];
			ret.values[0] = l;
			break;
		}
	}

	minimize(solver, &ret);

	for (int i = 2; i < ret.length; i++) {
		value l = ret.values[i];
		if (solver->level[abs(l)] > solver->level[abs(ret.values[1])]) {
			ret.values[i] = ret.values[1];
			ret.values[1] = l;
		}
	}

	return ret;
}

void probe(struct solver* solver) {
	// TODO: optimize same way as preprocessing?
	// TODO: only literals that are in a 2 length clause
	// TODO: clean this up
	// TODO: dont allocate all the time
	printf("(P %d ", solver->probed);
	fflush(stdout);

	bool* seen[2];
	seen[0] = malloc(solver->len_variables*sizeof(bool));
	seen[1] = malloc(solver->len_variables*sizeof(bool));

	enum vbool* values = malloc(solver->len_variables*sizeof(enum vbool));

probe_restart:
	bool change = false;

	if (unit_propagate(solver) != -1) {
		free(seen[0]);
		free(seen[1]);
		free(values);
		unsat(solver);
		return;
	}

	memset(seen[0], false, solver->len_variables*sizeof(bool));
	memset(seen[1], false, solver->len_variables*sizeof(bool));

	for (int var_i = 1; var_i < solver->len_variables+1; var_i++) {

		if (seen[0][var_i-1] && seen[1][var_i-1]) continue;
		if (solver->watched_clauses[0][var_i].length == 0
				&& solver->watched_clauses[1][var_i].length == 0) continue;
		if (solver->variables[var_i] != vundef) continue;

		bool check_extra = true;
		struct int_arr var_list = nil_int_arr;

		// TODO: dont reassign every time? - how
		for (int j = 0; j < solver->len_variables; j++) values[j] = vundef;

		for (int p = 0; p < 2; p++) {
			if (solver->variables[var_i] != vundef) continue;
			if (solver->watched_clauses[!p][var_i].length == 0) continue;

			value var = p ? var_i : -var_i;

			assign_guess(solver, var);

			int conflict = unit_propagate(solver);

			if (conflict == -1) {
				if (solver->trail.length == solver->len_variables - solver->variables_eliminated) {
					free(seen[0]);
					free(seen[1]);
					free(values);
					free(var_list.arr);
					sat(solver);
					return;
				}

				for (int j = solver->decisions.arr[0]; j < solver->trail.length; j++) {
					int index = abs(solver->trail.arr[j]);
					enum vbool val = solver->variables[index];
					seen[val==vtrue][index-1] = true;
					if (p == 0)
						values[index-1] = val;
					else if (p == 1 && values[index-1] == val)
						extend_int_arr(&var_list, index);
				}
				undo_decision(solver);
				continue;
			}

			struct clause new = analyze(solver, conflict);
			value unit = new.values[0];
			free(new.values);

			undo_decision(solver);

			int now = solver->trail.length;

			extend_int_arr(&solver->units, unit);
			assign(solver, unit, -1);

			conflict = unit_propagate(solver);

			solver->probed += solver->trail.length - now;
			solver->conflicts++;
			change = true;
			check_extra = false;

			if (conflict != -1) {
				free(seen[0]);
				free(seen[1]);
				free(values);
				free(var_list.arr);
				unsat(solver);
				return;
			}
		}
		if (check_extra) {
			for (int index = 0; index < var_list.length; index++) {
				value var = var_list.arr[index];
				int now = solver->trail.length;
				if (values[var-1] == vtrue) {
					extend_int_arr(&solver->units, var);
					assign(solver, var, -1);
				} else if (values[var-1] == vfalse) {
					extend_int_arr(&solver->units, -var);
					assign(solver, -var, -1);
				}
				values[var-1] = vundef;

				change = true;
				unit_propagate(solver);
				solver->probed += solver->trail.length - now;
				if (solver->trail.length == solver->len_variables - solver->variables_eliminated) {
					free(seen[0]);
					free(seen[1]);
					free(values);
					free(var_list.arr);
					sat(solver);
					return;
				}
				if (solver->variables[var] != vundef) break;
			}
		}
		free(var_list.arr);
	}

	// looping actually makes it slower - look into why
	// rewrite to use an int_arr?
	if (change) goto probe_restart;
	free(seen[0]);
	free(seen[1]);
	free(values);
	printf("%d)", solver->probed);
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

bool resolve_conflict(struct solver* solver, int conflict, bool* should_probe) {
	if (++solver->conflicts%LUBY_MULT == 0) {
		printf(".");
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

	*should_probe = new.length <= 2;

	if (new.length == 1) {
		printf("(u %d)", new.values[0]);
		fflush(stdout);
		extend_int_arr(&solver->units, new.values[0]);
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

// TODO: this code sucks, fix this - separate into functions
// remove_watched_clause, unwatch (?), is_toplevel_satisfied, ...
// TODO: keep cleaned clauses for probing?
void clean_database(struct solver* solver) {
	printf("(C %d ", solver->problem.length);
	fflush(stdout);
	for (int i = solver->problem.length-1; i >= 0; i--) {
		struct clause c = solver->problem.clauses[i];

		// if clause is original -> continue
		bool toplevel_satisfied = false;
		for (int j = 0; j < c.length; j++) {
			value v = c.values[j];
			if (solver->variables[abs(v)] == get_vbool(v) && solver->level[abs(v)] == 0) {
				toplevel_satisfied = true;
				break;
			}
		}

		if (!toplevel_satisfied) {
			if (!c.learned) {
				continue;
			} else {
				// keep binary clauses
				if (c.length == 2) continue;

				// if clause is reason for [0] -> continue
				if (solver->reason[abs(c.values[0])] == i) continue;
				if (solver->reason[abs(c.values[1])] == i) continue;
			}
		}

		// delete watches
		remove_watched_clause(solver, i);

		if (i != solver->problem.length-1) {
			struct clause new = solver->problem.clauses[solver->problem.length-1];

			remove_watched_clause(solver, solver->problem.length-1);
			remove_clauses_unord(&solver->problem, i);

			add_watched_clause(solver, i);

			if (solver->reason[abs(new.values[0])] == solver->problem.length)
				solver->reason[abs(new.values[0])] = i;
			if (solver->reason[abs(new.values[1])] == solver->problem.length)
				solver->reason[abs(new.values[1])] = i;

		} else {
			remove_clauses_unord(&solver->problem, i);
		}
	}
	printf("%d)", solver->problem.length);
}

struct solver* cdcl(struct solver* solver) {
	printf("searching\n");
	init_vsids(solver);

	// TODO: rewrite these as solver attributes
	bool should_probe = true;
	int allowed = solver->problem.length*2;

	while (!solver->solved) {
		int conflict;
		while ((conflict = unit_propagate(solver)) != -1)
			if (resolve_conflict(solver, conflict, &should_probe)) return solver;

		// TODO: less probing, slows down solver too much
		if (should_probe && solver->decisions.length == 0) {
			should_probe = false;
			probe(solver);
			if (solver->solved) return solver;
		}

		if (solver->problem.length > allowed) {
			allowed = solver->problem.length*2;
			clean_database(solver);
		}

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
	memset(solver->phase, false, (solver->len_variables+1)*sizeof(bool));

	for (int i = 0; i < 2; i++){
		solver->watched_clauses[i] = malloc((solver->len_variables+1) * sizeof(struct int_arr));
		for (int j = 0; j < solver->len_variables+1; j++) {
			solver->watched_clauses[i][j] = nil_watches;
		}
	}

	solver->vsids = malloc((solver->len_variables+1) * sizeof(double));
	for (int i = 1; i < solver->len_variables+1; i++) solver->vsids[i] = 0;

	solver->ignore = malloc((solver->len_variables+1)*sizeof(bool));
	solver->remove = malloc((solver->len_variables+1)*sizeof(bool));

	solver->trail.arr = malloc((solver->len_variables-solver->variables_eliminated) * sizeof(value));
}

struct solver* solve(FILE* file) {

	struct solver* solver = malloc(sizeof(struct solver));

	struct int_arr nilarr     = {NULL, 0};
	struct clauses nilclauses = {NULL, 0};

	solver->solved				= false;
	solver->problem				= nilclauses;
	solver->units				= nilarr;
	solver->variables			= NULL;
	solver->len_variables		= 0;
	solver->reason				= NULL;
	solver->level				= NULL;
	solver->watched_clauses[0]	= NULL;
	solver->watched_clauses[1] 	= NULL;
	solver->queue				= 0;
	solver->trail				= nilarr;
	solver->decisions			= nilarr;
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

	print_stats(solver);
	return cdcl(solver);
}
