# ralt - Tripon toolchain (bootstrap compiler in C99, zero deps).
CC ?= cc
CFLAGS ?= -std=c99 -O2 -Wall -Wextra

SRC := $(wildcard src/*.c)
HDR := $(wildcard src/*.h)

build/ralt: $(SRC) $(HDR)
	@mkdir -p build
	$(CC) $(CFLAGS) -o $@ $(SRC)

.PHONY: all test clean
all: build/ralt

clean:
	rm -rf build
