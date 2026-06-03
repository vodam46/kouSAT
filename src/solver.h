#pragma once

#include <stdio.h>

typedef int value;

enum vbool {
	vtrue,
	vfalse,
	vundef
};

struct clause {
	value* values;
	int length;
};

struct clauses {
	struct clause* clauses;
	int length;
};

struct solver {
	int solutions;
	int conflicts;

	struct clauses problem;
	struct clause units;
	// TODO: implications?

	enum vbool* variables;
	int len_variables;

	int* reason;
	int* level;

	// for each literal, a list of clauses
	// the watched literals are always in [0] and [1] in the clause
	// [0] is false, [1] is true
	struct clauses watched_clauses[2];

	// index into trail of literals that need to be checked
	int queue;

	struct clause trail;

	struct clause decisions;
};

void solve(FILE*);
