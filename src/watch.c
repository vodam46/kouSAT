#include <stdio.h>
#include <stdlib.h>

#include "watch.h"

struct watches nil_watches = {NULL, 0};

struct watch create_watcher(struct clause clause, int index, value blocker) {
	struct watch watch;
	watch.blocker = blocker;
	watch.index = index;
	watch.type = clause.length <= 2 ? binary_clause : long_clause;
	return watch;
}

void extend_watches(struct watches* watches, struct watch watch) {
	watches->length++;
	watches->arr = realloc(watches->arr, watches->length * sizeof(struct watch));
	watches->arr[watches->length-1] = watch;
}

void remove_watches_unord(struct watches* watches, int index) {
	watches->length--;
	watches->arr[index] = watches->arr[watches->length];
	if (watches->length)
		watches->arr = realloc(watches->arr, watches->length * sizeof(struct watch));
	else {
		free(watches->arr);
		watches->arr = NULL;
	}
}

void reduce_watches(struct watches* watches, int length) {
	watches->length -= length;
	if (watches->length)
		watches->arr = realloc(watches->arr, watches->length * sizeof(struct watch));
	else {
		free(watches->arr);
		watches->arr = NULL;
	}
}

void print_watches(struct watches watches) {
	for (int i = 0; i < watches.length; i++) {
		struct watch watch = watches.arr[i];
		printf("{b: %d i: %d t:", watch.blocker, watch.index);
		switch (watch.type) {
			case long_clause:
				printf("long");
				break;
			case binary_clause:
				printf("bin");
				break;
		}
		printf("} ");
	}
}
