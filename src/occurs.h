#pragma once

void add_occurence(struct clause, int, struct clause**);
void remove_clause_occurence(struct clauses*, struct clause**, int);
struct clause** build_occurence_list(struct clauses problem, int len_variables);
