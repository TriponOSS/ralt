#!/bin/sh
set -e
cd "$(dirname "$0")/.."
make
./build/ralt check examples/hello.tp
out=$(./build/ralt run examples/hello.tp)
printf '%s\n' "$out" | grep -q "hello from tripon"
echo "smoke ok"
