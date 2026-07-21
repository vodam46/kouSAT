#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <string.h>

typedef int value;

enum vbool {
	vtrue = 1,
	vfalse = 0,
	vundef = -1
};

struct clause {
	uint64_t mask;

	bool learned;
	bool keep;
	bool useful;

	int glue;
	// TODO: other attributes?

	value* values;
	int length;
};

struct clauses {
	struct clause* clauses;
	int length;
};

extern struct clause nilclause;

uint64_t get_mask(value);

enum vbool get_vbool(value);
void print_clause(struct clause);
void print_clauses(struct clauses);

void extend_clause(struct clause*, value);
void remove_clause_unord(struct clause*, unsigned);
void reduce_clause(struct clause*, unsigned);

void recalculate_mask(struct clause*);

void extend_clauses(struct clauses*, struct clause);
void remove_clauses_unord(struct clauses*, unsigned);

bool clause_contains(struct clause clause, value);
bool resolve_trivial(struct clause, struct clause, value);
void resolve(struct clause*, struct clause, value);
void remove_clause_value(struct clause*, value);

bool subsumes(struct clause, struct clause);
void copy_clause(struct clause*, struct clause);
