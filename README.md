# ralt

The Tripon toolchain: a single, dependency-free C99 binary that compiles
`.tp` programs.

- Build: `make` (produces `build/ralt`)
- Test: `make test`
- Clean: `make clean`

## Requirements

- A C99 toolchain (gcc or clang)
- make

## Usage

```sh
./build/ralt run examples/hello.tp
./build/ralt check examples/hello.tp --json
./build/ralt --help
```

## Layout

```
src/       compiler passes (lex, parse, typecheck, codegen, native, ...)
examples/  smoke programs
tests/     smoke tests
```

Language spec, full test suite, and self-host sources live in
[TriponOSS/tripon](https://github.com/TriponOSS/tripon).

## License

MIT. See [LICENSE](LICENSE).
