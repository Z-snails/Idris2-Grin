# Idris2-Grin
GRIN backend for Idris2.  
Designed to use [this](https://github.com/grin-compiler/grin) grin compiler.

This only works with recent versions of idris2 (v0.3.0 +)
because it relies on recently added laziness annotations.

## Contributions wanted
- [ ] Finish partial functions
  - [ ] `PrimFn_` functions
  - [ ] `getConstTag`
- [ ] Fix literals so they are wrapped in appropriate Constructor (see `getConstTag`)
- [ ] Tests
