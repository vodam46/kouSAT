#include <stdio.h>
#ifdef TEST
#include <string.h>
#endif

#include "test.h"
#include "solver.h"

int main(int argc, char** argv) {
#ifdef TEST
	if (argc == 1 || strcmp(argv[1], "--test") == 0) {
		test_all();
		return 0;
	}
	printf("\nc COMPILED FOR TESTING\n\n");
#endif
	FILE* file;
	if (argc == 1) {
		file = stdin;
	} else {
		file = fopen(argv[1], "r");
	}
	// TODO: parse args, if any
	destroy_solver(solve(file));

	return 0;
}
