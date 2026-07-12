#include <stdio.h>

#include "statistics.h"

void print_statistics(struct statistics statistics) {
	printf("\n");
#define PRINT_STAT(name, type) printf("c " #name ": %d\n", statistics.name);
	STATISTICS(PRINT_STAT)
#undef PRINT_STAT
	printf("\n");

	printf("average learned length %f\n", (float)statistics.length_sum / statistics.conflicts);
	printf("average minimized %f\n", (float)statistics.minimized / statistics.conflicts);
	printf("\n\n");
}
