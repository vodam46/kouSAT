#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "clause.h"

struct clause nilclause = {
	.values=NULL,
	.length=0,
	.learned=false,
	.keep=true,
	.glue=-1,
	.mask=(uint64_t)0
};


int get_mask_index(value v) {
	return abs(v)%64;
}

uint64_t get_mask(value v) {
	return ((uint64_t)1)<<get_mask_index(v);
}

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


// TODO: do it better - custom clause allocator?
// arena style allocate?
// instead of pointers store only indices of the start
// proper dynamic array with resizing

void extend_clause(struct clause* clause, value value) {
	clause->length++;
	clause->values = realloc(clause->values, clause->length * sizeof(value));
	clause->values[clause->length-1] = value;

	clause->mask |= get_mask(value);
}

void remove_clause_unord(struct clause* clause, unsigned index) {
	clause->length--;
	clause->values[index] = clause->values[clause->length];
	if (clause->length) {
		clause->values = realloc(clause->values, clause->length * sizeof(value));
	} else {
		free(clause->values);
		clause->values = NULL;
	}
}

void reduce_clause(struct clause* clause, unsigned length) {
	clause->length -= length;
	if (clause->length) {
		clause->values = realloc(clause->values, clause->length * sizeof(value));
	} else {
		free(clause->values);
		clause->values = NULL;
	}
}

void recalculate_mask(struct clause* clause) {
	clause->mask = 0;
	for (int i = 0; i < clause->length; i++) {
		clause->mask |= get_mask(clause->values[i]);
		if (~clause->mask == 0) {
			return;
		}
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
	if (~clause.mask & get_mask(literal)) return false;
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
	recalculate_mask(left);
}

void remove_clause_value(struct clause* clause, value value) {
	int l = 0, r = 0;
	uint64_t mask = 0;
	for (; r < clause->length; r++) {
		if (clause->values[r] != value) {
			clause->values[l++] = clause->values[r];
			mask |= get_mask(clause->values[r]);
		}
	}
	clause->mask = mask;
	reduce_clause(clause, r-l);
}

bool subsumes(struct clause left, struct clause right) {
	if (left.length > right.length) return false;
	if (left.mask & ~right.mask) return false;
	for (int i = 0; i < left.length; i++)
		if (!clause_contains(right, left.values[i]))
			return false;
	return true;
}

void copy_clause(struct clause* dest, struct clause orig) {
	dest->length = orig.length;
	dest->mask = orig.mask;
	dest->learned = orig.learned;
	dest->keep = orig.keep;
	dest->glue = orig.glue;

	dest->values = malloc(orig.length * sizeof(value));
	memcpy(dest->values, orig.values, orig.length * sizeof(value));
}
