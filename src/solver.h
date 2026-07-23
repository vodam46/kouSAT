#pragma once

#include <stdio.h>
#include <stdbool.h>

struct solver;

#include "clause.h"
#include "int_arr.h"
#include "watch.h"
#include "statistics.h"

struct solver {
	bool solved;
	bool result;

	bool should_probe;

	int restarts;
	int conflicts_until_restart;

	int allowed;
	struct clauses problem;
	struct int_arr units;

	double* vsids;
	double vsids_factor;
	bool* phase;
	enum vbool* variables;
	int len_variables;

	int* reason;
	int* level;

	bool* levels;

	// for minimizing
	bool* ignore;
	bool* remove;

	// for probing
	enum vbool* values;
	bool* seen[2];

	// for each literal, a list of clauses
	// the watched literals are always in [0] and [1] in the clause
	struct watches* watched_clauses[2];

	struct int_arr* occurs[2];

	// index into trail of literals that need to be checked
	int queue;

	struct int_arr trail;

	struct int_arr decisions;

	struct clauses preprocessing_stack;

	struct statistics statistics;
};

struct solver* solve(FILE*);
void destroy_solver(struct solver*);

void assign(struct solver*, value, int);

void learn_clause(struct solver*, struct clause);
void forget_clause(struct solver*, int);

void unsat(struct solver*);
void sat(struct solver*);
