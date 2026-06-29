CC=gcc
# CC=clang
NAME=kouSAT
OUT=bin/$(NAME)
OUT_DEBUG=bin/$(NAME)-debug
OUT_TEST=bin/$(NAME)-test
CFLAGS=-Wall -Wextra -pedantic -DPROJECT_DIR='"$(shell pwd)"' -Wunreachable-code -g -O3 -flto
CLIBS=

FILE=

sources = $(subst src/,,$(wildcard src/*.c))

.PHONY: clean count debug debug-build default run valgrind test check

default: $(OUT)
build: $(OUT)

clean:
	-rm -Rf obj dep bin profile.txt gmon.out

run: $(OUT)
	time ./$(OUT) $(FILE)

check: $(OUT)
	./$(OUT) $(FILE) | grep '^v ' | luajit check_result.lua $(FILE)


debug-build: CFLAGS := $(filter-out -O3,$(CFLAGS))

debug-build: CFLAGS+=-g

debug-build: CFLAGS+=-pg -ggdb
debug-build: CFLAGS+=-fsanitize=address
debug-build: CFLAGS+=-fsanitize=alignment
debug-build: CFLAGS+=-fsanitize=bool
debug-build: CFLAGS+=-fsanitize=bounds
debug-build: CFLAGS+=-fsanitize=enum
debug-build: CFLAGS+=-fsanitize=float-cast-overflow
debug-build: CFLAGS+=-fsanitize=float-divide-by-zero
debug-build: CFLAGS+=-fsanitize=integer-divide-by-zero
debug-build: CFLAGS+=-fsanitize=leak
debug-build: CFLAGS+=-fsanitize=null
debug-build: CFLAGS+=-fsanitize=object-size
debug-build: CFLAGS+=-fsanitize=return
debug-build: CFLAGS+=-fsanitize=shift
debug-build: CFLAGS+=-fsanitize=signed-integer-overflow
debug-build: CFLAGS+=-fsanitize=undefined
debug-build: CFLAGS+=-fsanitize=unreachable
debug-build: CFLAGS+=-fsanitize=vla-bound

debug-build:  | obj dep bin
	$(CC) $(CFLAGS) $(addprefix src/, $(sources)) -o $(OUT_DEBUG) $(CLIBS)

debug: debug-build
	gdb $(OUT_DEBUG)

profile: CFLAGS := $(filter-out -O3,$(CFLAGS)) -O0
profile: CFLAGS := $(filter-out -pg,$(CFLAGS))
profile: OUT=$(OUT_TEST)
profile: $(OUT)
	time valgrind -s --log-file="valgrind" --tool=callgrind ./$(OUT) $(FILE)

valgrind: CFLAGS := $(filter-out -O3,$(CFLAGS)) -Og
valgrind: CFLAGS := $(filter-out -pg,$(CFLAGS))
valgrind: $(OUT)
	time valgrind -s --log-file="valgrind" --track-fds=yes --track-origins=yes --leak-check=full ./$(OUT) $(FILE)

count:
	cloc src/*

test: CFLAGS+=-DTEST
test: OUT=$(OUT_TEST)
test: $(OUT)
test:
	time ./$(OUT)

ifeq (,$(filter $(MAKECMDGOALS), clean count test))
include $(addprefix dep/, $(sources:.c=.d))
endif

dep/%.d: src/%.c | dep
	$(CC) $(CFLAGS) -M $^ > $@

obj/%.o: src/%.c | obj
	$(CC) $(CFLAGS) -c -o $@ $(realpath $<)

obj dep bin:
	mkdir -p $@

$(OUT): $(addprefix obj/, $(sources:.c=.o)) | bin
	echo $(sources)
	$(CC) $(CFLAGS) -o $(OUT) $^ $(CLIBS)
