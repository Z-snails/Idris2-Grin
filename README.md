# Idris2grin
GRIN backend for Idris2.  
Designed to use [this](https://github.com/grin-compiler/grin) grin compiler.

This only works with recent versions of idris2 (v0.3.0 +)
because it relies on recently added laziness annotations.

## Help wanted
I don't know the grin compiler very well (or really at all) and I greatly appreciate any help with command line options for running the compiler.
Possibly I will rewrite some of the optimisations in Idris so I'll also need to work out how to disable certain optimisations.
This will also be important to disable SimpleDeadParameterElimination beacuse it is currently broken.

## Todo
- [x] Finish unfinished functions
  - [x] primitive related functions
  - [x] `unwrap`/`wrap` literals
- [x] Fix literals so they are wrapped in appropriate Constructor (see `getConstTag`)
- [ ] Tests
- [ ] Add missing primitives (probably define the AST then add to beginning of defs)
