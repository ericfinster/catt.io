
# Requirements

Catt.io has two dependencies for building the parser and lexer:

1. Menhir
2. ocamllex

These can be installed from opam.

# Build

The system is currently configured to build with
[Bucklescript](http://bucklescript.github.io).  The easiest
setup is to install Bucklescript globally with

```
npm instll -g bs-platform
```

Once this is done, then in the repo directory

```
npm install
bsb -make-world
```
should make everything.

# To Run

The typechecker can be run with node.js.  For example:

```
node src/catt.bs.js examples/demo.catt
```