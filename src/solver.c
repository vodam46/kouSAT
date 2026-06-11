// TODO: all solutions, not just the first one it finds -> add negative of choices as new clause
// TODO: check that everything is correct
// TODO: probing -> some sort of way to do it alongside preprocessing
// TODO: restarts
// TODO: clause deleting
// TODO: phase saving
// TODO: better separation of initialization and logic (preprocess)
// TODO: specialized data structures, not just clause(s) for everything
// TODO: vsids queue
// TODO: harden parsing - fault tolerant
// TODO: clean up the code

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "solver.h"

#define LUBY_MULT (1<<7)

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

	free(solver);
}

void new_solution(struct solver* solver) {
	// reconstruct solution after variable elimination

	// TODO: some better way to do this?
	for (int i = 1; i < solver->len_variables+1; i++)
		if (solver->variables[i] == vundef)
			solver->variables[i] = vtrue;

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
	if (clause->length)
		clause->values = realloc(clause->values, clause->length * sizeof(value));
	else {
		free(clause->values);
		clause->values = NULL;
	}
}

void reduce_clause(struct clause* clause, unsigned length) {
	clause->length -= length;
	if (clause->length)
		clause->values = realloc(clause->values, clause->length * sizeof(int));
	else {
		free(clause->values);
		clause->values = NULL;
	}
}

void extend_clauses(struct clauses* clauses, struct clause clause) {
	clauses->length++;
	clauses->clauses = realloc(clauses->clauses, clauses->length * sizeof(struct clause));
	clauses->clauses[clauses->length-1] = clause;
}

void remove_clauses_unord(struct clauses* clauses, unsigned index) {
	clauses->length--;
	free(clauses->clauses[index].values);
	clauses->clauses[index] = clauses->clauses[clauses->length];
	if (clauses->length)
		clauses->clauses = realloc(clauses->clauses, clauses->length * sizeof(struct clause));
	else {
		free(clauses->clauses);
		clauses->clauses = NULL;
	}
}

bool clause_contains(struct clause clause, value literal) {
	for (int i = 0; i < clause.length; i++)
		if (clause.values[i] == literal)
			return true;
	return false;
}

bool resolve_trivial(struct clause left, struct clause right, value v) {
	for (int l = 0; l < left.length; l++) {
		if (abs(left.values[l]) == abs(v)) continue;
		for (int r = 0; r < right.length; r++)
			if (left.values[l] == -right.values[r])
				return true;

	}
	return false;
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


void assign(struct solver* solver, value value, int reason) {
	int index = abs(value);
	enum vbool val = get_vbool(value);
	solver->variables[index] = val;
	solver->level[index] = solver->decisions.length;
	solver->reason[index] = reason;
	solver->phase[index] = val == vfalse ? false : true;
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
	sscanf(line, "p cnf %d %d", &solver->len_variables, &solver->problem_len);
	free(line);

	int loaded = 0;
	bool ignore = false;
	struct clause clause = {NULL, 0};
	while (loaded < solver->problem_len) {
		value value = 0;
		fscanf(file, "%d", &value);
		if (value == 0) {
			if (!ignore) {
				if (clause.length == 1) {
					extend_clause(&solver->units, clause.values[0]);
					free(clause.values);
				} else extend_clauses(&solver->problem, clause);
			}

			ignore = false;
			clause = (struct clause){NULL, 0};
			loaded++;
		} else {
			if (clause_contains(clause, value)) continue;
			if (clause_contains(clause, -value)) ignore = true;
			extend_clause(&clause, value);
		}
	}

	fclose(file);
}

void add_occurence(struct clause clause, int index, struct clause** occurs) {
	for (int var_i = 0; var_i < clause.length; var_i++) {
		value var = clause.values[var_i];
		extend_clause(&occurs[var>0][abs(var)], index);
	}
}

struct clause** build_occurence_list(struct solver* solver) {
	struct clause** occurs;
	occurs = malloc(2*sizeof(struct clause*));

	occurs[0] = malloc((solver->len_variables+1)*sizeof(struct clause));
	occurs[1] = malloc((solver->len_variables+1)*sizeof(struct clause));
	for (int i = 0; i < solver->len_variables+1; i++)
		for (int p = 0; p < 2; p++)
			occurs[p][i] = (struct clause){NULL, 0};

	for (int clause_i = 0; clause_i < solver->problem.length; clause_i++)
		add_occurence(solver->problem.clauses[clause_i], clause_i, occurs);


	return occurs;
}

void remove_clause_value(struct clause* clause, value value) {
	for (int i = 0; i < clause->length; i++)
		if (clause->values[i] == value)
			return remove_clause_unord(clause, i);
	// printf("clause does not contain %d\n", value);
	// print_clause(*clause);
}

void delete_occurence(struct solver* solver, struct clause** occurs, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int i = 0; i < clause.length; i++) {
		value v = clause.values[i];
		remove_clause_value(&occurs[v>0][abs(v)], index);
	}
}

void remove_clause_occurence(struct solver* solver, struct clause** occurs, int index) {
	delete_occurence(solver, occurs, index);
	if (index != solver->problem.length-1) {
		delete_occurence(solver, occurs, solver->problem.length-1);
		remove_clauses_unord(&solver->problem, index);
		add_occurence(solver->problem.clauses[index], index, occurs);
	} else {
		remove_clauses_unord(&solver->problem, index);
	}
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
			if (solver->problem.clauses[index].length == 1) {
				value v = solver->problem.clauses[index].values[0];
				if (solver->variables[abs(v)] == get_vbool(-v)) {
					unsat(solver);
					return true;
				}
				if (solver->variables[abs(v)] == vundef) {
					extend_clause(&solver->units, v);
					assign(solver, v, -1);
				}
			}
			if (solver->problem.clauses[index].length == 0) {
				unsat(solver);
				return true;
			}
		}

		while (occurs[v>0][abs(v)].length) {
			solver->clauses_removed++;
			remove_clause_occurence(solver, occurs, occurs[v>0][abs(v)].values[0]);
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

bool subsumes(struct clause left, struct clause right) {
	if (left.length > right.length) return false;
	for (int i = 0; i < left.length; i++)
		if (!clause_contains(right, left.values[i]))
			return false;
	return true;
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
				count = occurs[l>0][abs(i)].length;
			}
		}

		struct clause* occ = &occurs[lit>0][abs(lit)];
		for (int i = occ->length-1; i >= 0; i--) {
			int index = occ->values[i];
			struct clause other = solver->problem.clauses[index];
			if (index == ci) continue;
			if(subsumes(clause, other)) {
				solver->clauses_removed++;
				if (ci == solver->problem.length-1) ci = index;
				remove_clause_occurence(solver, occurs, index);
				change = true;
			}
		}
	}

	return change;
}

void copy_clause(struct clause* dest, struct clause orig) {
	dest->length = orig.length;
	dest->values = malloc(orig.length * sizeof(value));
	memcpy(dest->values, orig.values, orig.length * sizeof(value));
}
bool maybe_eliminate(
	struct solver* solver,
	value var,
	struct clause** occurs
) {
	struct clause* occurs_neg = &occurs[0][var];
	struct clause* occurs_pos = &occurs[1][var];

	if (occurs_neg->length > 2 || occurs_pos->length > 2) {
		int count = 0;
		for (int l = 0; l < occurs_neg->length; l++) {
			struct clause left = solver->problem.clauses[occurs_neg->values[l]];
			for (int r = 0; r < occurs_pos->length; r++) {
				struct clause right = solver->problem.clauses[occurs_pos->values[r]];
				if (!resolve_trivial(left, right, var))
					count++;
			}
		}
		int c = occurs_neg->length + occurs_pos->length;
		if (count > (c + (c>>1) + 1)) return false;
	}


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
		remove_clause_occurence(solver, occurs, index);
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
		remove_clause_occurence(solver, occurs, index);
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
				value unit = nc.values[0];
				free(nc.values);
				if (solver->variables[abs(unit)] == vundef) {
					assign(solver, unit, -1);
					extend_clause(&solver->units, unit);
				} else if (solver->variables[abs(unit)] != get_vbool(unit)) {
					unsat(solver);
					goto variable_elim_end;
				}
			} else {
				add_occurence(nc, solver->problem.length, occurs);
				extend_clauses(&solver->problem, nc);
			}
		}
	}
variable_elim_end:

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
		if (solver->variables[i+1] != vundef) {
			skip++;
			continue;
		}
		variables[2*(i-skip)] = i+1;
		variables[2*(i-skip)+1] = occurs[0][i+1].length * occurs[1][i+1].length;
	}
	qsort(variables, solver->len_variables-skip, sizeof(int)*2, qsort_func);

	for (int i = 0; i < solver->len_variables-skip; i++) {
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

void preprocess(struct solver* solver) {
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
	struct clause** occurs = build_occurence_list(solver);
	while (
			!solver->solved
			&& (
				preprocess_unit_propagate(solver, occurs)
				|| preprocess_pure_literals(solver, occurs)

				// TODO: (X | Y) & (X | -Y) -> X = self subsumtion?

				// TODO: subsumed clauses - optimize
				|| preprocess_subsume_clauses(solver, occurs)

				// TODO: bounded variable elimination - OPTIMIZE
				|| preprocess_variable_elimination(solver, occurs)
			   )
		  );

	for (int i = 1; i < solver->len_variables+1; i++) {
		free(occurs[0][i].values);
		free(occurs[1][i].values);
	}
	free(occurs[0]);
	free(occurs[1]);
	free(occurs);

	printf("after %d\n", solver->problem.length);
	printf("variables %d\n", solver->len_variables);
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
			for (int i = 2; i < clause.length; i++) {
				value v = clause.values[i];
				if (solver->variables[abs(v)] != get_vbool(-v)) {
					clause.values[1] = v;
					clause.values[i] = -check;
					extend_clause(&solver->watched_clauses[v>0][abs(v)], clause_i);
					goto unit_propagate_next;
				}
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
unit_propagate_next:;
		}
		reduce_clause(clauses_i, right-left);
	}

	return -1;
}

void init_vsids(struct solver* solver) {
	solver->vsids_factor = 0.9;
	solver->vsids = malloc((solver->len_variables+1) * sizeof(double));
	for (int i = 1; i < solver->len_variables+1; i++) solver->vsids[i] = 0;
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
		reduce_clause(&solver->trail, 1);
	}
}

void add_watched_clause(struct solver* solver, int index) {
	struct clause clause = solver->problem.clauses[index];
	for (int j = 0; j < 2; j++) {
		value v = clause.values[j];
		extend_clause(&solver->watched_clauses[v>0][abs(v)], index);
	}
}

void init_two_watched(struct solver* solver) {
	for (int i = 0; i < 2; i++){
		solver->watched_clauses[i] = malloc((solver->len_variables+1) * sizeof(struct clause));
		for (int j = 0; j < solver->len_variables+1; j++) {
			solver->watched_clauses[i][j] = (struct clause){NULL, 0};
		}
	}

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

	// minimize
	// mark all clause as ignore
	// go throuh the trail
	// - if level == 0 -> can remove, ignore
	// - if dependents (ignore/remove) -> can remove, ignore

	// TODO: check if its actually faster
	// TODO: dont allocate them all the time

	bool* ignore = calloc(solver->len_variables+1, sizeof(bool));
	bool* remove = calloc(solver->len_variables+1, sizeof(bool));
	for (int i = 0; i < ret.length; i++) ignore[abs(ret.values[i])] = true;
	for (int lit_i = 0; lit_i < solver->trail.length; lit_i++) {
		value l = solver->trail.values[lit_i];
		int index = abs(l);
		if (solver->level[index] == 0) {
			ignore[index] = true;
			remove[index] = true;
			continue;
		}
		if (solver->reason[index] == -1) continue;
		struct clause reason = solver->problem.clauses[solver->reason[index]];
		bool can_ignore = true;
		for (int i = 0; i < reason.length; i++) {
			if (!ignore[abs(reason.values[i])]) {
				can_ignore = false;
				break;
			}
		}
		if (can_ignore) {
			ignore[index] = true;
			remove[index] = true;
		}
	}
	for (int i = 0; i < ret.length; i++) {
		if (remove[abs(ret.values[i])]) {
			solver->minimized++;
			remove_clause_unord(&ret, i--);
		}
	}
	free(ignore);
	free(remove);

	return ret;
}

void probe(struct solver* solver) {
	// TODO: for each literal - try true/false
	// if conflict -> that literal is opposite, learn the conflict (if good/short)
	// if variable true in both cases -> new unit
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
	solver->queue = solver->trail.length;
}

struct solver* cdcl(struct solver* solver) {
	// TODO: clean up goto
	init_two_watched(solver);
	init_vsids(solver);

	while (!solver->solved) {
		int conflict;
		while ((conflict = unit_propagate(solver)) != -1) {
			// TODO: simplify this into a function call?

			if (++solver->conflicts%LUBY_MULT == 0) {
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
				free(new.values);
				unsat(solver);
				goto cdcl_end;
			}

			update_vsids(solver, new);

			if (new.length == 1) extend_clause(&solver->units, new.values[0]);
			else extend_clauses(&solver->problem, new);

			if (--solver->conflicts_until_restart == 0) restart(solver);
			else backtrack_learnt(solver, new);

			if (new.length == 1) free(new.values);
		}

		if (solver->trail.length == solver->len_variables - solver->variables_eliminated) sat(solver);
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

	solver->restarts				= 0;
	solver->conflicts_until_restart	= LUBY_MULT;


	parse(file, solver);
	preprocess(solver);
	if (solver->solved) return solver;
	return cdcl(solver);
}
