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
	// TODO: level
	int* level;

	// for each literal, a list of clauses
	// the watched literals are always in [0] and [1] in the clause
	// [0] is false, [1] is true
	struct clauses watched_clauses[2];

	// TODO: do it with an index into trail?
	// would have to keep track of it for backtracking too
	// just like minisat does it
	// but would be simpler
	struct clause tocheck;

	struct clause trail;

	struct clause decisions;
};

void solve(FILE*);
