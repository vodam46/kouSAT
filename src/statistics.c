#include <stdio.h>

#include "statistics.h"

void print_statistics(struct statistics statistics) {
	printf("\n");
#define PRINT_STAT(name, type) \
	printf("c " #name ": "); \
	printf(GET_CHAR(statistics.name), statistics.name); \
	printf("\n");

	STATISTICS(PRINT_STAT)
#undef PRINT_STAT
	printf("\n");

#define GET_STAT(name) statistics.name
#define PRINT_CALCULATED(name, type, calc) \
	printf("c " #name ": "); \
	printf(GET_CHAR((type)0), calc); \
	printf("\n");

	CALCULATED(PRINT_CALCULATED, GET_STAT)
#undef PRINT_CALCULATED
#undef GET_STAT

	printf("\n\n");
}
