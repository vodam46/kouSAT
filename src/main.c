#include <stdio.h>

#include "test.h"
#include "solver.h"

int main(int argc, char** argv) {
#ifdef TEST
	test_all();

#else
	FILE* file;
	if (argc == 1) {
		file = stdin;
	} else {
		file = fopen(argv[1], "r");
	}
	// TODO: parse args, if any
	solve(file);

#endif
	return 0;
}
