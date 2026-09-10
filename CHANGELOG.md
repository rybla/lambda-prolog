# Changelog for `lambda-prolog`

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## 0.1.0.0

### Added

- Kernel: simply-typed spine terms, de Bruijn substitution, higher-order
  pattern unification, uniform proof search for hereditary Harrop goals
- Surface language: Teyjus-style parser, mixfix, elaboration, `accumulate`
- CLI and REPL (`lambda-prolog`)
- Example programs under `examples/`
- Static website builder (`build-website`) with semantic highlighting

## 0.2.0.0

### Added

- Example programs expanded into a small standard library: lists (including
  sorting and difference lists), maps/folds/qsort, control, integers
  (factorial, Fibonacci, expression evaluator), finite sets (powerset),
  association lists, binary search trees, strings, options, formulas
  (nnf + prenex + occurs), HOAS λ-calculus (Church numerals, combinators),
  STLC with pairs and booleans, and tacticals — each file includes
  commented REPL examples
- Builtin integer comparison goals (`<`, `>`, `=<`, `>=`) and string
  concatenation via `is` / `^`
- Anonymous `_` wildcards; n-ary `pi` / `sigma` (`pi x y\ G` and `pi x\ y\ G`)
- Website: hover tips on keywords, types, punctuation, binders, and comment
  metadata keys (`title:`, `tags:`, `summary:`)
- Website visual language: high-contrast colours, 1px dark rules, square
  corners, STIX / math fonts

### Fixed

- `:-` after a capital identifier was parsed as a typed λ (`K : -pi x\ …`)
- `prefix` as a user predicate collided with the mixfix keyword
- `true` / `fail` used as higher-order goal arguments (`once true`) did not
  succeed or fail as goals
- Compound goal terms (`once (true, true)`, `once (pi x\ …)`) were searched
  as ordinary atoms instead of being reread as connectives
- `^` was not a symbolic identifier, so `"ab" ^ "cd"` would not parse
