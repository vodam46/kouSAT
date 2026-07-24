#include <stdlib.h>
#include <stdio.h>

#include "int_arr.h"

struct int_arr nil_int_arr = {
	.arr=NULL,
	.length=0,
	.allocated=0
};

void extend_int_arr(struct int_arr* int_arr, int val) {
	if (int_arr->length >= int_arr->allocated-1) {
		int_arr->allocated *= 1.5;
		int_arr->allocated += 1;
		int_arr->arr = realloc(int_arr->arr, int_arr->allocated * sizeof(int));
	}
	int_arr->arr[int_arr->length++] = val;
}

// TODO: reallocating to smaller arrays?
void remove_int_arr_unord(struct int_arr* int_arr, int index) {
	int_arr->length--;
	int_arr->arr[index] = int_arr->arr[int_arr->length];
	if (!int_arr->length) {
		free(int_arr->arr);
		int_arr->arr = NULL;
		int_arr->allocated = 0;
	}
}

void reduce_int_arr(struct int_arr* int_arr, int length) {
	int_arr->length -= length;
	if (!int_arr->length) {
		free(int_arr->arr);
		int_arr->arr = NULL;
		int_arr->allocated = 0;
	}
}

void remove_int_arr_value(struct int_arr* int_arr, int val) {
	for (int i = 0; i < int_arr->length; i++)
		if (int_arr->arr[i] == val) {
			remove_int_arr_unord(int_arr, i);
			return;
		}
}

void print_int_arr(struct int_arr int_arr) {
	for (int i = 0; i < int_arr.length; i++)
		printf("%d ", int_arr.arr[i]);
	printf("\n");
}
