# Idris2grin
GRIN backend for Idris2.  
Designed to use [this](https://github.com/grin-compiler/grin) grin compiler.

This only works with recent versions of idris2 (v0.3.0 +)
because it relies on recently added laziness annotations.

## Todo
- [x] Finish unfinished functions
  - [x] primitive related functions
  - [x] `unwrap`/`wrap` literals
- [x] Fix literals so they are wrapped in appropriate Constructor (see `getConstTag`)
- [ ] Tests
- [ ] Add missing primitives (probably define the AST then add to beginning of defs)
