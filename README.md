
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

# Toplevel

If you have utop installed, you can launch an interactive session with
the catt.io libraries loaded by running

```
dune utop lib
```

The catt.io library modules should then be available as Catt__*.  So,
for example, in utop,

```
open Catt__Expr;;
```

will give access to the expression syntax and routines.

# Examples

The example folder contains some `catt` files that can be typechecked by the tool. To typecheck all the examples the following commands can be run:

```
catt examples/example_4_1.catt -su
catt examples/example_4_2.catt -su
catt examples/example_4_3_catt.catt
catt examples/example_4_3_cattsu.catt -su
catt examples/example_4_4.catt -su
```
In these commands the `-su` flag turns on strict normalisation.
