# lambda-prolog

A Haskell interpreter for **λProlog**, the higher-order hereditary Harrop (hohh) logic programming language of Miller and Nadathur. Computation is uniform proof search: conjunction, disjunction, existential choice, backchaining, plus the two connectives that make the language hierarchical —

- `D => G` — install clause `D` while proving `G`
- `pi x\ G` — introduce a fresh eigenvariable

Terms are simply-typed λ-terms. Unification is **higher-order pattern unification** (the Lλ fragment). The surface language follows Teyjus `.mod` / `.sig` syntax.

Inspired by [*Programming with Higher-Order Logic*](https://sites.google.com/site/proghol/), [Teyjus](https://teyjus.cs.umn.edu), and [ELPI](https://github.com/LPCIC/elpi).

## Build

This is a Haskell Stack project.

```sh
stack build
stack test
stack run lambda-prolog -- examples/lists.mod
stack run lambda-prolog -- --query 'append (1::2::nil) (3::nil) L' examples/lists.mod
stack run build-website
```

The website builder writes a static GitHub Pages site into `website/`.

## CLI

```
lambda-prolog [OPTIONS] [FILE.mod]
```

| Option | Meaning |
|---|---|
| `-e`, `--query GOAL` | Run a query and exit |
| `-b`, `--batch` | Do not start a REPL |
| `--max N` | Stop after N solutions |
| `--expect N` | Exit 1 unless at least N solutions |
| `-I`, `--path DIR` | Module search path (for `accumulate`) |
| `--parse-only` | Parse and exit |
| `--elab-only` | Elaborate and exit |

With a file and no `--query`, an interactive REPL starts (`λΠ>`). Type a goal followed by `.`, or `:help`.

```
λΠ> append (1 :: 2 :: nil) (3 :: nil) L.
The answer substitution:
  X0 = [1, 2, 3]
```

## Language (what is implemented)

- Higher-order hereditary Harrop goals: `true`, `fail`, `,`, `;`, `:-`, `=>`, `pi`, `sigma`, `=`, `is`, `!`, `not`
- Simply-typed λ-terms, lists (`nil`, `::`, `[1,2|T]`), integers, strings
- Pattern unification with eigenvariable levels and pruning
- Modules: `kind`, `type`, mixfix (`infixl` / `infixr` / …), `accumulate`, `local`
- Extra-logical: cut and negation-as-failure (as in Teyjus)

**Not implemented:** Teyjus bytecode VM; ELPI CHR/constraints, spilling, macros; full Huet unification (non-pattern problems fail with `NotPattern`).

## Layout

| Path | Role |
|---|---|
| `src/LambdaProlog/Kernel/` | Terms, substitution, unification, proof search |
| `src/LambdaProlog/Surface/` | Parser, mixfix, elaboration, modules |
| `src/LambdaProlog/Cli.hs` | CLI and REPL |
| `examples/` | Tutorial and example programs |
| `build-website/` | Static site with semantic highlighting |
| `test/` | Kernel, surface, and example tests |

## Implementation notes

The kernel is an abstract interpreter, not a compiler. Search is depth-first, left-to-right, clause-order, with an undo trail. Hypothetical clauses are consed onto the front of the relevant predicate and popped on failure. Cut redirects the fail register to the enclosing atomic call.

Pattern unification follows Miller/Nipkow: a flexible term must be a meta applied to distinct bound variables or eigenconstants. `pi x\ X = x` fails (scope); `pi x\ F x = x` binds `F` to the identity.

Module accumulation is source-level inlining, which is the logical reading of modules in the book.

## Examples

See `examples/`. The tutorial covers syntax; `hypothetical.mod`, `hidden_reverse.mod`, `typeinf.mod`, and `prenex.mod` are the ones that actually use nested programs (`pi` / `=>`) and HOAS.

## References

- Dale Miller and Gopalan Nadathur, *Programming with Higher-Order Logic*, CUP, 2012
- Gopalan Nadathur and Dale Miller, *Higher-Order Logic Programming*, Handbook of Logic in AI and LP
- [Teyjus](https://teyjus.cs.umn.edu)
- [ELPI](https://github.com/LPCIC/elpi)
