#pragma once

#include "clause.h"

enum watch_type {
	long_clause,
	binary_clause
};

struct watch {
	value blocker;
	int index;
	enum watch_type type;
};

struct watches {
	struct watch* arr;
	int length;
};

extern struct watches nil_watches;

struct watch create_watcher(struct clause, int, value);

void extend_watches(struct watches*, struct watch);
void remove_watches_unord(struct watches*, int);
void reduce_watches(struct watches*, int);

void print_watches(struct watches);
