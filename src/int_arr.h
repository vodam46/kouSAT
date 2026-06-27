#pragma once

struct int_arr {
	int* arr;
	int length;
};

extern struct int_arr nil_int_arr;

void extend_int_arr(struct int_arr*, int);
void remove_int_arr_unord(struct int_arr*, int);
void reduce_int_arr(struct int_arr*, int);
void remove_int_arr_value(struct int_arr*, int);

void print_int_arr(struct int_arr);
