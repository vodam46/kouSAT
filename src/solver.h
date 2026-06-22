#pragma once

#include <stdio.h>
#include <stdbool.h>

#include "clause.h"

struct solver {
	bool solved;
	bool result;

	int solutions;
	int conflicts;

	int restarts;
	int conflicts_until_restart;

	// statistics
	int minimized;
	int clauses_removed;
	int clauses_reduced;
	int variables_eliminated;

	int problem_len;
	struct clauses problem;
	struct clause units;
	// TODO: binary clauses - built into the watched list?

	double* vsids;
	double vsids_factor;
	bool* phase;
	enum vbool* variables;
	int len_variables;

	int* reason;
	int* level;

	// for minimizing
	bool* ignore;
	bool* remove;

	// for each literal, a list of clauses
	// the watched literals are always in [0] and [1] in the clause
	// [0] is false, [1] is true
	struct clause* watched_clauses[2];

	// index into trail of literals that need to be checked
	int queue;

	struct clause trail;

	struct clause decisions;

	struct clauses preprocessing_stack;
};

struct solver* solve(FILE*);
void destroy_solver(struct solver*);

void assign(struct solver*, value, int);

void unsat(struct solver*);
void sat(struct solver*);
