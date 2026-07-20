// TODO: check that everything is correct
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
#include "int_arr.h"
#include "preprocess.h"
#include "watch.h"
#include "statistics.h"
#include "occurs.h"

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
	printf("solutions %d\n", solver->statistics.solutions);
	printf("conflicts %d\n", solver->statistics.conflicts);

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

	free(solver->values);
	free(solver->seen[0]);
	free(solver->seen[1]);

	free(solver->levels);

	free_occurs(solver);

	free(solver);
}

// TODO: recursive?
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


	solver->statistics.solutions++;
	printf("\n\nv ");
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


void assign(struct solver* solver, value value, int reason) {
	int index = abs(value);
	enum vbool val = get_vbool(value);
	solver->variables[index] = val;
	solver->level[index] = solver->decisions.length;
	solver->reason[index] = reason;
	solver->phase[index] = val;
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
						solver->statistics.propagations++;
						assign(solver, first, w.index);

						int old_glue = clause.glue;
						int glue = 0;
						bool* levels = solver->levels;
						memset(levels, false, (solver->decisions.length+1)*sizeof(bool));
						for (int i = 0; i < clause.length && glue < old_glue; i++) {
							value v = clause.values[i];
							int level = solver->level[abs(v)];
							if (levels[level]) continue;
							levels[level] = true;
							glue++;
						}
						if (glue < old_glue)
							solver->problem.clauses[watcher.index].glue = glue;

					}
					break;

				case binary_clause:
					// first is undefined, assign it immediately
					if (var == vundef) {
						watches.arr[left++] = watcher;
						right++;
						solver->statistics.propagations++;
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
	// TODO: is this the proper place to put it?
	solver->statistics.decisions++;
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

void learn_clause(struct solver* solver, struct clause clause) {
	if (clause.length > 1) {
		extend_clauses(&solver->problem, clause);
		int index = solver->problem.length-1;
		add_watched_clause(solver, index);
		add_occurence(solver, index);
	} else {
		value unit = clause.values[0];
		extend_int_arr(&solver->units, unit);
	}
}

void clean_clause(struct solver* solver, int index) {
	// delete watches
	struct clause new = solver->problem.clauses[solver->problem.length-1];
	if (index != solver->problem.length-1) {
		delete_occurence(solver, solver->problem.length-1);
		remove_watched_clause(solver, solver->problem.length-1);

		remove_clauses_unord(&solver->problem, index);

		add_occurence(solver, index);
		add_watched_clause(solver, index);

		if (new.length > 0 && solver->reason[abs(new.values[0])] == solver->problem.length)
			solver->reason[abs(new.values[0])] = index;
		if (new.length > 1 && solver->reason[abs(new.values[1])] == solver->problem.length)
			solver->reason[abs(new.values[1])] = index;
	} else {
		remove_clauses_unord(&solver->problem, index);
	}
}

void forget_clause(struct solver* solver, int index) {
	// delete watches
	delete_occurence(solver, index);
	remove_watched_clause(solver, index);

	clean_clause(solver, index);
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
		if (solver->ignore[index]) length--;
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

	int l = 0, r = 0;
	uint64_t mask = 0;
	for (; r < ret.length; r++) {
		if (!solver->remove[abs(ret.values[r])]) {
			mask |= get_mask(ret.values[r]);
			ret.values[l++] = ret.values[r];
		} else solver->statistics.minimized++;
	}
	reduce_clause(&ret, r-l);
	ret.mask = mask;

	// self subsuming resolution on conflict clause
	// https://www.msoos.org/2010/08/on-the-fly-self-subsuming-resolution/
	if (length > 1) {
		for (int i = 1; i < ret.length; i++) {
			value l = ret.values[i];
			struct watches arr = solver->watched_clauses[l<0][abs(l)];
			for (int j = 0; j < arr.length; j++) {
				struct watch w = arr.arr[j];
				if (w.type != binary_clause) continue;

				// TODO: do this without clause_contains
				if (!solver->remove[abs(w.blocker)] && solver->ignore[abs(w.blocker)] && clause_contains(ret, w.blocker)) {
					solver->remove[abs(l)] = true;
					length--;
					break;
				}
			}
			if (length == 1) break;
		}
	}

	l = 0, r = 0;
	mask = 0;
	for (; r < ret.length; r++) {
		if (!solver->remove[abs(ret.values[r])]) {
			mask |= get_mask(ret.values[r]);
			ret.values[l++] = ret.values[r];
		} else solver->statistics.minimized++;
	}
	reduce_clause(&ret, r-l);
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

	int glue = 0;
	bool* levels = solver->levels;
	memset(levels, false, (solver->decisions.length+1)*sizeof(bool));
	for (int i = 0; i < ret.length; i++) {
		value v = ret.values[i];
		int level = solver->level[abs(v)];
		if (levels[level]) continue;
		levels[level] = true;
		glue++;
	}
	ret.glue = glue;

	solver->statistics.length_sum += ret.length;
	return ret;
}

void replace_variable(struct solver* solver, value to_replace, value var_i) {
	for (int j = 0; j < 2; j++) {
		struct clause c = nilclause;
		extend_clause(&c, to_replace);
		extend_clause(&c, var_i);
		c.values[j] *= -1;
		extend_clauses(&solver->preprocessing_stack, c);
	}

	for (int b = 0; b < 2; b++) {
		int mult = b ? 1 : -1;
		int var_p = (var_i*mult)>0;
		for (int j = solver->occurs[b][to_replace].length-1; j >= 0; j--) {
			int ci = solver->occurs[b][to_replace].arr[j];
			remove_int_arr_value(&solver->occurs[b][to_replace], ci);

			struct clause* c = &solver->problem.clauses[ci];
			int index = -1;
			int other =  0;
			for (int i = 0; i < c->length; i++) {
				value v = c->values[i];
				if (abs(v) == to_replace) index = i;
				if (abs(v) == abs(var_i)) other = v;
			}

			if (other == 0) {
				if (index < 2) remove_watched_clause(solver, ci);
				c->values[index] = var_i*mult;
				if (index < 2) add_watched_clause(solver, ci);
				recalculate_mask(c);
				extend_int_arr(&solver->occurs[var_p][abs(var_i)], ci);
				continue;
			}

			if (other != var_i*mult) {
				forget_clause(solver, ci);
				continue;
			}

			if (index < 2) remove_watched_clause(solver, ci);
			remove_clause_unord(c, index);
			recalculate_mask(c);

			if (c->length != 1) {
				// TODO: what to do if the replacement is assigned false?
				if (index < 2) add_watched_clause(solver, ci);
				continue;
			}

			// TODO: shouldnt be possible?
			// wouldve already been seen during regular probing
			printf("c new unit %d\n", c->values[0]);
			value unit = c->values[0];
			if (solver->variables[abs(unit)] == vundef) {
				assign(solver, unit, -1);
				extend_int_arr(&solver->units, unit);
				forget_clause(solver, ci);
				continue;
			}

			if (solver->variables[abs(unit)] == get_vbool(unit)) {
				forget_clause(solver, ci);
			} else {
				unsat(solver);
				return;
			}
		}
	}
}

void probe(struct solver* solver) {
	// TODO: optimize same way as preprocessing?
	// TODO: only literals that are in a 2 length clause
	// TODO: clean this up
	// TODO: dont allocate all the time
	// TODO: equivalent literals
	printf("(P %d ", solver->statistics.probed);
	fflush(stdout);

	for (int j = 0; j < solver->len_variables; j++) solver->values[j] = vundef;

	solver->statistics.probing_attempts++;

probe_restart:;
	bool change = false;

	if (unit_propagate(solver) != -1) {
		unsat(solver);
		return;
	}

	memset(solver->seen[0], false, solver->len_variables*sizeof(bool));
	memset(solver->seen[1], false, solver->len_variables*sizeof(bool));

	// TODO: go through all clauses - if theres a binary clause - mark the literals as "probeable"?

	for (int var_i = 1; var_i < solver->len_variables+1; var_i++) {

		if (solver->seen[0][var_i-1] && solver->seen[1][var_i-1]) continue;
		if (solver->watched_clauses[0][var_i].length == 0
				&& solver->watched_clauses[1][var_i].length == 0) continue;
		if (solver->variables[var_i] != vundef) continue;

		bool check_extra = true;
		struct int_arr probed_units = nil_int_arr;
		struct int_arr equivalent_lits = nil_int_arr;
		struct int_arr values_arr = nil_int_arr;

		for (int p = 0; p < 2; p++) {
			if (solver->variables[var_i] != vundef) continue;
			if (solver->watched_clauses[!p][var_i].length == 0) continue;

			value var = p ? var_i : -var_i;

			assign_guess(solver, var);

			int conflict = unit_propagate(solver);

			if (conflict == -1) {
				if (solver->trail.length == solver->len_variables - solver->statistics.variables_eliminated) {
					free(probed_units.arr);
					free(equivalent_lits.arr);
					free(values_arr.arr);
					sat(solver);
					return;
				}

				for (int j = solver->decisions.arr[0]+1; j < solver->trail.length; j++) {
					int index = abs(solver->trail.arr[j]);
					enum vbool val = solver->variables[index];
					solver->seen[val==vtrue][index-1] = true;
					if (p == 0) {
						solver->values[index-1] = val;
						extend_int_arr(&values_arr, index-1);
					}
					else {
						if (solver->values[index-1] == vundef) continue;

						if (solver->values[index-1] == val)
							extend_int_arr(&probed_units, index);
						if (solver->values[index-1] != val)
							extend_int_arr(&equivalent_lits, solver->trail.arr[j]);
					}
				}
				undo_decision(solver);
				continue;
			}

			struct clause new = analyze(solver, conflict);
			if (new.length == 0) {
				free(probed_units.arr);
				free(equivalent_lits.arr);
				free(values_arr.arr);
				unsat(solver);
				return;
			}
			value unit = new.values[0];
			free(new.values);

			undo_decision(solver);

			int now = solver->trail.length;

			extend_int_arr(&solver->units, unit);
			assign(solver, unit, -1);

			conflict = unit_propagate(solver);

			solver->statistics.probed += solver->trail.length - now;
			solver->statistics.conflicts++;
			change = true;
			check_extra = false;

			if (conflict != -1) {
				free(probed_units.arr);
				free(equivalent_lits.arr);
				free(values_arr.arr);
				unsat(solver);
				return;
			}
		}
		if (check_extra) {
			for (int index = 0; index < probed_units.length; index++) {
				value var = probed_units.arr[index];
				int now = solver->trail.length;
				if (solver->values[var-1] == vtrue) {
					extend_int_arr(&solver->units, var);
					assign(solver, var, -1);
				} else if (solver->values[var-1] == vfalse) {
					extend_int_arr(&solver->units, -var);
					assign(solver, -var, -1);
				}

				change = true;
				unit_propagate(solver);
				solver->statistics.probed += solver->trail.length - now;
				if (solver->trail.length == solver->len_variables - solver->statistics.variables_eliminated) {
					free(probed_units.arr);
					free(equivalent_lits.arr);
					free(values_arr.arr);
					sat(solver);
					return;
				}
				if (solver->variables[var] != vundef) break;
			}

			for (int eq_i = 0; eq_i < equivalent_lits.length; eq_i++) {
				int to_replace = equivalent_lits.arr[eq_i];
				if (solver->variables[abs(to_replace)] != vundef) continue;
				replace_variable(solver, abs(to_replace), to_replace>0 ? var_i : -var_i);
				change = true;
				solver->statistics.probed++;

				if (solver->solved) return;
			}
		}

		while (values_arr.length) {
			solver->values[values_arr.arr[--values_arr.length]] = vundef;
		}

		free(values_arr.arr);
		free(probed_units.arr);
		free(equivalent_lits.arr);
	}

	// looping actually makes it slower - look into why
	// rewrite to use an int_arr?
	if (change) goto probe_restart;
	printf("%d)", solver->statistics.probed);
	fflush(stdout);
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
	if (++solver->statistics.conflicts%LUBY_MULT == 0) {
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

	solver->should_probe = new.length <= 2;

	if (new.length == 1) {
		printf("(u %d)", new.values[0]);
		fflush(stdout);
		extend_int_arr(&solver->units, new.values[0]);
	} else {
		update_vsids(solver, new);
		extend_clauses(&solver->problem, new);
		add_occurence(solver, solver->problem.length-1);
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

// TODO: keep cleaned clauses for probing?
// TODO: once conflict is found, compare new conflict clause with cleaned clauses?
// - could be extremely slow, and not work
void clean_database(struct solver* solver) {
	printf("(C %d ", solver->problem.length);
	fflush(stdout);

	for (int i = solver->problem.length-1; i >= 0; i--) {
		struct clause* c = &solver->problem.clauses[i];
		c->keep = true;

		// TODO: only check if there were any new units?
		bool toplevel_satisfied = false;
		int l = 0, r = 0;
		for (; r < c->length; r++) {
			value v = c->values[r];
			enum vbool var = solver->variables[abs(v)];
			if (var != vundef && solver->level[abs(v)] == 0) {
				enum vbool vbool = get_vbool(v);
				if (var == vbool) {
					toplevel_satisfied = true;
					break;
				}

				if (r >= 2) continue;
			}
			c->values[l++] = c->values[r];
		}

		if (!toplevel_satisfied) {
			reduce_clause(c, r-l);
			recalculate_mask(c);

			if (r != l) {
				solver->statistics.clauses_reduced += (r-l);

				if (c->length == 2) {
					for (int j = 0; j < 2; j++) {
						value v = c->values[j];
						struct watches w = solver->watched_clauses[v>0][abs(v)];
						for (int k = 0; k < w.length; k++) {
							if (w.arr[k].index == i) {
								w.arr[k].type = binary_clause;
								break;
							}
						}
					}
				}
			}

			if (!c->learned) {
				continue;
			} else {
				// keep binary clauses
				if (c->length <= 2 || c->glue <= 2) continue;

				// if clause is reason for [0] -> continue
				if (solver->reason[abs(c->values[0])] == i) continue;
				if (solver->reason[abs(c->values[1])] == i) continue;
			}
		}

		solver->statistics.cleaned++;

		c->keep = false;
	}

	for (int var_i = 1; var_i < solver->len_variables+1; var_i++) {
		for (int b = 0; b < 2; b++) {
			struct int_arr* occ = &solver->occurs[b][var_i];
			int l = 0, r = 0;
			for (; r < occ->length; r++) {
				int o = occ->arr[r];
				if (solver->problem.clauses[o].keep)
					occ->arr[l++] = occ->arr[r];
			}
			reduce_int_arr(occ, r-l);

			struct watches* watch = &solver->watched_clauses[b][var_i];
			l = 0, r = 0;
			for (; r < watch->length; r++) {
				int w = watch->arr[r].index;
				if (solver->problem.clauses[w].keep)
					watch->arr[l++] = watch->arr[r];
			}
			reduce_watches(watch, r-l);
		}
	}

	for (int i = solver->problem.length-1; i >= 0; i--) {
		if (!solver->problem.clauses[i].keep) {
			clean_clause(solver, i);
		}
	}


	printf("%d)", solver->problem.length);
}

void cdcl(struct solver* solver) {
	printf("c searching\nc ");
	init_vsids(solver);

	// TODO: rewrite these as solver attributes
	while (!solver->solved) {
		int conflict;
		while ((conflict = unit_propagate(solver)) != -1)
			if (resolve_conflict(solver, conflict)) return;

		// TODO: do more probing?
		if (solver->should_probe && solver->decisions.length == 0) {
			solver->should_probe = false;
			probe(solver);
			if (solver->solved) return;
		}

		if (solver->problem.length > solver->allowed) {
			solver->allowed = solver->problem.length*2;
			clean_database(solver);
		}

		if (solver->trail.length == solver->len_variables - solver->statistics.variables_eliminated) sat(solver);
		else assign_guess(solver, guess(solver));
	}
	return;
}

void allocate_data(struct solver* solver) {
	printf("c allocating data\n");
	solver->variables = malloc((solver->len_variables+1) * sizeof(enum vbool));
	solver->level = malloc((solver->len_variables+1) * sizeof(int));
	for (int i = 1; i < solver->len_variables+1; i++) solver->variables[i] = vundef;
	memset(solver->level, 0, (solver->len_variables+1)*sizeof(int));
	solver->reason = malloc((solver->len_variables+1) * sizeof(int));
	memset(solver->reason, 0, (solver->len_variables+1)*sizeof(int));
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

	solver->values = malloc((solver->len_variables+1) * sizeof(enum vbool));
	for (int i = 0; i < 2; i++)
		solver->seen[i] = malloc((solver->len_variables+1) * sizeof(bool));

	solver->trail.arr = malloc((solver->len_variables-solver->statistics.variables_eliminated) * sizeof(value));

	solver->levels = malloc((solver->len_variables+1)*sizeof(bool));

	build_occurence_list(solver);

	for (int i = 0; i < solver->problem.length; i++) solver->problem.clauses[i].keep = true;
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
	solver->vsids				= NULL;
	solver->phase				= NULL;
	solver->allowed				= 0;
	solver->preprocessing_stack	= nilclauses;
	solver->should_probe		= true;
	solver->allowed				= solver->problem.length*2;


#define INITIALIZE(name, type) solver->statistics.name = 0;
	STATISTICS(INITIALIZE)
#undef INITIALIZE

	solver->restarts				= 0;
	solver->conflicts_until_restart	= LUBY_MULT;


	parse(file, solver);

	allocate_data(solver);
	init_two_watched(solver);

	preprocess(solver);
	if (solver->solved) {
		print_statistics(solver->statistics);
		return solver;
	}

	cdcl(solver);

	// TODO: is this the best place to put it?
	if (solver->result)
		for (int i = 1; i < solver->len_variables+1; i++)
			solver->statistics.units += solver->level[i] == 0;
	print_statistics(solver->statistics);

	return solver;
}
