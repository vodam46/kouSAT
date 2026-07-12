#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "dimacs.h"

// TODO: make this different?
// TODO: put some basic unit propagation in parsing
void parse(FILE* file, struct solver* solver) {
	printf("c parsing\n");
	char* line = NULL;
	size_t size = 0;
	getline(&line, &size, file);
	while (line[0] != 'p') {
		getline(&line, &size, file);
	}

	if (strncmp(line, "p cnf ", 6)) {
		printf("c invalid problem line\n\"%s\"", line);
		exit(1);
	}
	printf("c problem %s\n", line);
	sscanf(line, "p cnf %d %d", &solver->len_variables, &solver->allowed);
	free(line);

	int loaded = 0;
	bool ignore = false;
	struct clause clause = nilclause;
	while (loaded < solver->allowed) {
		value value = 0;
		fscanf(file, "%d", &value);
		if (value == 0) {
			if (!ignore) {
				if (clause.length == 1) {
				extend_int_arr(&solver->units, clause.values[0]);
					free(clause.values);
				} else extend_clauses(&solver->problem, clause);
			}

			ignore = false;
			clause = nilclause;
			loaded++;
		} else {
			if (clause_contains(clause, value)) continue;
			if (clause_contains(clause, -value)) ignore = true;
			extend_clause(&clause, value);
		}
	}

	fclose(file);
}

