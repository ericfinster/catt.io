
# Introduction

Catt.io is an experimental typechecker for weak higher dimensional
categories.

# Requirements

Catt.io has two dependencies for building the parser and lexer:

1. Menhir
2. ocamllex

These can be installed from opam.

# Build

The project builds with dune.  A simple

```
dune build
```

should build the project.  A top level Makefile is also provided for
convenience.

# Semistrictness

Semistrictness can be turned on by using the `--su` or `--sua` flags for strict units or strict units and associators respectively.
