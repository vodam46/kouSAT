// TODO: multiple passes of variable elimination, starting with strictly less clauses than at the start

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
		extend_int_arr(&solver->units, v);
		assign(solver, v, -1);
		return false;
	}
	if (solver->variables[abs(v)] == get_vbool(v)) return false;
	unsat(solver);
	return true;
}

void preprocess_unit_propagate(
		struct solver* solver,
		struct int_arr** occurs,
		bool* strengthened,
		bool** arr,
		bool* touched
		) {
	// printf("preprocess unit propagation\n");
	for (; solver->queue < solver->units.length; solver->queue++) {
		value v = solver->units.arr[solver->queue];
		if (occurs[0][abs(v)].length == 0 && occurs[1][abs(v)].length == 0) continue;
		for (int i = 0; i < occurs[v<0][abs(v)].length; i++) {
			int index = occurs[v<0][abs(v)].arr[i];
			solver->clauses_reduced++;

			if (strengthened != NULL)
				strengthened[index] = true;

			if (touched != NULL)
				for (int i = 0; i < solver->problem.clauses[index].length; i++)
					touched[abs(solver->problem.clauses[index].values[i])] = true;

			remove_clause_value(&solver->problem.clauses[index], -v);
			if (unit_check(solver, solver->problem.clauses[index])) return;
		}

		while (occurs[v>0][abs(v)].length) {
			solver->clauses_removed++;
			int index = occurs[v>0][abs(v)].arr[0];

			if (arr != NULL)
				for (int i = 0; arr[i]; i++)
					arr[i][index] = arr[i][solver->problem.length-1];

			if (touched != NULL)
				for (int i = 0; i < solver->problem.clauses[index].length; i++)
					touched[abs(solver->problem.clauses[index].values[i])] = true;

			remove_clause_occurence(&solver->problem, occurs, index);
		}

		for (int b = 0; b < 2; b++) {
			free(occurs[b][abs(v)].arr);
			occurs[b][abs(v)].arr = NULL;
			occurs[b][abs(v)].length = 0;
		}
	}
}

bool preprocess_pure_literals(struct solver* solver, struct int_arr** occurs) {
	// printf("preprocess pure literals\n");
	bool change = false;

	for (int i = 1; i < solver->len_variables+1; i++) {
		if (solver->variables[i] != vundef) continue;
		if (occurs[0][i].length == 0 && occurs[1][i].length >= 1) {
			// printf("pure %d\n", i);
			assign(solver, i, -1);
			extend_int_arr(&solver->units, i);
			change = true;
		}
		if (occurs[0][i].length >= 1 && occurs[1][i].length == 0) {
			// printf("pure %d\n", -i);
			assign(solver, -i, -1);
			extend_int_arr(&solver->units, -i);
			change = true;
		}
	}

	return change;
}

void preprocess_subsume_clauses(
		struct solver* solver,
		struct int_arr** occurs,
		int ci,
		bool* strengthened,
		bool* touched
		) {
	// printf("preprocess subsume clauses\n");
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

	struct int_arr* occ = &occurs[lit>0][abs(lit)];
	for (int i = occ->length-1; i >= 0; i--) {
		int index = occ->arr[i];
		struct clause other = solver->problem.clauses[index];
		if (index == ci) continue;
		if(subsumes(clause, other)) {
			solver->clauses_removed++;
			strengthened[index] = strengthened[solver->problem.length-1];
			for (int i = 0; i < other.length; i++)
				touched[abs(other.values[i])] = true;
			if (ci == solver->problem.length-1) ci = index;
			remove_clause_occurence(&solver->problem, occurs, index);
		}
	}
}

bool extra_clauses_under_limit(int count, int c) {
	return count <= 25 || count <= c + (c>>1);
}
bool maybe_eliminate(
	struct solver* solver,
	value var,
	struct int_arr** occurs,
	bool* touched,
	bool** added
) {
	struct int_arr* occurs_neg = &occurs[0][var];
	struct int_arr* occurs_pos = &occurs[1][var];

	if (!extra_clauses_under_limit(
		occurs_neg->length*occurs_pos->length,
		occurs_neg->length+occurs_pos->length
	)) {
		int count = 0;
		int c = occurs_neg->length + occurs_pos->length;
		for (int l = 0; l < occurs_neg->length; l++) {
			struct clause left = solver->problem.clauses[occurs_neg->arr[l]];
			for (int r = 0; r < occurs_pos->length; r++) {
				if (extra_clauses_under_limit(
							count + occurs_pos->length-1-r + (occurs_neg->length-1-l)*occurs_pos->length,
							c
							)) goto variable_eliminate;
				struct clause right = solver->problem.clauses[occurs_pos->arr[r]];
				if (!resolve_trivial(left, right, var))
					count++;
				if (!extra_clauses_under_limit(count, c))
					return false;
			}
		}
		if (!extra_clauses_under_limit(count, c)) return false;
	}
variable_eliminate:;
	struct clauses pos = {NULL, 0};
	struct clauses neg = {NULL, 0};

	for (int m = 0; m < 2; m++) {
		struct clauses* mc = m ? &pos : &neg;
		struct int_arr* occ = m ? occurs_pos : occurs_neg;
		value v = m ? var : -var;
		while (occ->length) {
			struct clause clause;
			int index = occ->arr[0];
			copy_clause(&clause, solver->problem.clauses[index]);
			extend_clauses(mc, clause);
			for (int i = 0; i < clause.length; i++) {
				if (clause.values[i] == v) {
					clause.values[i] = clause.values[0];
					clause.values[0] = v;
					break;
				}
			}
			extend_clauses(&solver->preprocessing_stack, clause);
			(*added)[index] = (*added)[solver->problem.length-1];
			for (int i = 0; i < clause.length; i++)
				touched[abs(clause.values[i])] = true;
			remove_clause_occurence(&solver->problem, occurs, index);
		}
	}
	int new_len = solver->problem.length + pos.length*neg.length + 1;
	if (new_len)
		*added = realloc(*added, new_len*sizeof(bool));

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
				// TODO: shouldnt ever happen? - would be cleared by self subsumtion
				if (unit_check(solver, nc)) {
					free(nc.values);
					free(neg.clauses);
					free(pos.clauses);
					return true;
				}
				free(nc.values);
			} else {
				add_occurence(nc, solver->problem.length, occurs);
				(*added)[solver->problem.length] = true;
				extend_clauses(&solver->problem, nc);
			}
		}
	}

	free(neg.clauses);
	free(pos.clauses);

	return true;
}

void preprocess_self_subsume(
		struct solver* solver,
		struct int_arr** occurs,
		int ci,
		bool* strengthened,
		bool* touched
		) {
	// printf("preprocess self subsume\n");
	struct clause clause = solver->problem.clauses[ci];

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

		struct int_arr* occur;
		if (lit != p) occur = &occurs[lit<0][abs(lit)];
		else occur = &occurs[other<0][abs(other)];
		if (occurs[p<0][abs(p)].length < occur->length)
			occur = &occurs[p<0][abs(p)];

		for (int oi = occur->length-1; oi >= 0; oi--) {
			int index = occur->arr[oi];
			if (index == ci) continue;
			struct clause* other = &solver->problem.clauses[index];
			if (subsumes(clause, *other)) {
				solver->clauses_reduced++;
				for (int i = 0; i < other->length; i++)
					touched[abs(other->values[i])] = true;
				remove_clause_value(other, -p);
				remove_int_arr_value(occur, index);
				strengthened[index] = true;
				if (other->length == 0) {
					unsat(solver);
					return;
				}
				if (unit_check(solver, *other)) return;
			}
		}

		clause.values[pi] = p;
	}
}

void toplevel_propagate(
		struct solver* solver,
		struct int_arr** occurs,
		bool* strengthened,
		bool** arr,
		bool* touched
		) {
	do {
		preprocess_unit_propagate(solver, occurs, strengthened, arr, touched);
	} while (preprocess_pure_literals(solver, occurs));
}

bool is_all_false(bool* arr, int length) {
	if (length == 0) return true;
	if (length == 1) return arr[0] == false;
	return arr[0] == false && memcmp(arr, arr+1, (length-1)*sizeof(bool)) == 0;
}

int qsort_preprocess(const void* l, const void* r) {
	int res = ((int*)l)[1] - ((int*)r)[1];
	return res != 0 ? res : ((int*)l)[0] - ((int*)r)[0];
}

// TODO: figure out some more complex preprocessing
void preprocess(struct solver* solver) {
	printf("preprocessing\n");
	for (int i = 0; i < solver->units.length; i++) {
		value unit = solver->units.arr[i];
		int index = abs(unit);
		enum vbool v = get_vbool(unit);
		if (solver->variables[index] == vundef) {
			assign(solver, unit, -1);
		} else if (solver->variables[index] != v) {
			unsat(solver);
			return;
		}
	}
	printf("before %d\n", solver->problem.length);
	struct int_arr** occurs = build_occurence_list(solver->problem, solver->len_variables);

	toplevel_propagate(solver, occurs, NULL, NULL, NULL);
	printf("toplevel %d\n" ,solver->problem.length);
	if (solver->problem.length == 0) {
		sat(solver);
		free_occurs(solver, occurs);
		return;
	}

	bool* touched = malloc((solver->len_variables+1) * sizeof(bool));
	bool* s  = malloc((solver->len_variables+1) * sizeof(bool));

	bool* added = malloc(solver->problem.length * sizeof(bool));
	bool* strengthened = malloc(solver->problem.length * sizeof(bool));
	bool* s0 = malloc(solver->problem.length * sizeof(bool));
	bool* s1 = malloc(solver->problem.length * sizeof(bool));

	bool* marked[2];
	marked[0] = malloc((solver->len_variables+1) * sizeof(bool));
	marked[1] = malloc((solver->len_variables+1) * sizeof(bool));

	memset(touched, true, (solver->len_variables+1)*sizeof(bool));
	memset(added, true, solver->problem.length*sizeof(bool));
	memset(strengthened, false, solver->problem.length*sizeof(bool));

	// TODO: backwards subsumtion?
	// check if a newly added clause is subsumed by an already added clause
	// TODO: separate into functions
	int round = 0;
	do {
		round++;
		s0 = realloc(s0, solver->problem.length * sizeof(bool));
		memcpy(s0, added, solver->problem.length*sizeof(bool));
		for (int i = 0; i < solver->problem.length; i++) {
			if (!added[i]) continue;
			struct clause clause = solver->problem.clauses[i];
			for (int j = 0; j < clause.length; j++) {
				value v = clause.values[j];
				marked[v>0][abs(v)] = true;
			}
		}
		for (int i = 0; i < solver->problem.length; i++) {
			if (s0[i]) continue;
			struct clause clause = solver->problem.clauses[i];
			for (int j = 0; j < clause.length; j++) {
				value v = clause.values[j];
				if (marked[v>0][abs(v)]) {
					s0[i] = true;
					break;
				}
			}
		}

		do {
			s1 = realloc(s1, solver->problem.length * sizeof(bool));
			memcpy(s1, strengthened, solver->problem.length*sizeof(bool));
			for (int i = 0; i < solver->problem.length; i++) {
				s1[i] |= added[i];
				if (s1[i]) continue;
				struct clause clause = solver->problem.clauses[i];
				for (int j = 0; j < clause.length; j++) {
					value v = clause.values[j];
					if (marked[v<0][abs(v)]) {
						s1[i] = true;
						break;
					}
				}
			}

			memset(marked[0], false, solver->len_variables+1);
			memset(marked[1], false, solver->len_variables+1);

			memset(added, false, solver->problem.length * sizeof(bool));
			memset(strengthened, false, solver->problem.length * sizeof(bool));

			// int count = 0;
			// for (int i = 0; i < solver->problem.length; i++) count += s1[i];
			// printf("self %d/%d\n", count, solver->problem.length);

			// TODO: speed up self subsumtion
			for (int i = 0; i < solver->problem.length; i++) {
				if (!s1[i]) continue;
				preprocess_self_subsume(solver, occurs, i, strengthened, touched);
				if (solver->solved) goto preprocess_end;
			}

	 		bool* self_subsume_arr[] = {strengthened, s0, NULL};
			toplevel_propagate(solver, occurs, strengthened, self_subsume_arr, touched);
			if (solver->solved) goto preprocess_end;
			if (solver->problem.length == 0) {
				sat(solver);
				goto preprocess_end;
			}

			added = realloc(added, solver->problem.length * sizeof(bool));
			strengthened = realloc(strengthened, solver->problem.length * sizeof(bool));
		} while (!is_all_false(strengthened, solver->problem.length));

		// int count = 0;
		// for (int i = 0; i < solver->problem.length; i++) count += s0[i];
		// printf("subsume %d/%d\n", count, solver->problem.length);

		for (int i = solver->problem.length-1; i >= 0; i--) {
			if (!s0[i]) continue;
			preprocess_subsume_clauses(solver, occurs, i, strengthened, touched);
			if (i >= solver->problem.length) i = solver->problem.length;
			if (solver->solved) goto preprocess_end;
		}

		do {
			// printf("eliminate\n");
			memcpy(s, touched, (solver->len_variables+1)*sizeof(bool));
			memset(touched, false, (solver->len_variables+1)*sizeof(bool));

			int skip = 0;
			int* arr = malloc(2 * solver->len_variables * sizeof(int));
			for (int i = 0; i < solver->len_variables; i++) {
				if (!s[i+1]) {
					skip++;
					continue;
				}
				if (solver->variables[i+1] != vundef) {
					skip++;
					continue;
				}
				arr[2*(i-skip)] = i+1;
				arr[2*(i-skip)+1] = occurs[0][i+1].length * occurs[1][i+1].length;
			}
			// TODO: qsort_r? or my own function?
			qsort(arr, solver->len_variables-skip, sizeof(int)*2, qsort_preprocess);

			for (int i = 0; i < solver->len_variables-skip; i++) {
				int var = arr[2*i];
				if (!s[var]) continue;
				if (solver->variables[var] != vundef) continue;
				if (occurs[0][var].length == 0 || occurs[1][var].length == 0) continue;
				if (occurs[0][var].length > 50 && occurs[1][var].length > 50) continue;

				if (maybe_eliminate(solver, var, occurs, touched, &added)) {
					solver->variables_eliminated++;
					if (solver->solved) goto preprocess_end;
					if (solver->problem.length == 0) {
						free(arr);
						sat(solver);
						goto preprocess_end;
					}

					added = realloc(added, solver->problem.length * sizeof(bool));
					strengthened = realloc(strengthened, solver->problem.length * sizeof(bool));
					memset(strengthened, false, solver->problem.length*sizeof(bool));
				}
			}
			free(arr);
		} while (!is_all_false(touched, solver->len_variables+1));
	} while (!is_all_false(added, solver->problem.length));

preprocess_end:;
	printf("preprocessing %d rounds\n", round);
	free_occurs(solver, occurs);

	free(touched);
	free(added);
	free(strengthened);
	free(s);
	free(s0);
	free(s1);
	free(marked[0]);
	free(marked[1]);

	printf("after  %d\n", solver->problem.length);
	solver->problem_len = solver->problem.length;
}
