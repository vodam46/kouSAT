#pragma once

void free_occurs(struct solver*, struct int_arr**);
void add_occurence(struct clause, int, struct int_arr**);
void remove_clause_occurence(struct clauses*, struct int_arr**, int);
struct int_arr** build_occurence_list(struct clauses problem, int len_variables);
