# leanout

A clean-room exporter from Lean 4 environments to the lean4export NDJSON format (version 3.1.0).
Apache-2.0.

It was written from the published format description alone; no source of any other exporter was read.
It is written in Lean, because only Lean can read its own `.olean` environments. Other kernels (Lean's
own, [Tenet](https://github.com/keithadler/tenet), and so on) can then re-check what it writes.

## Build and use

Needs [elan](https://github.com/leanprover/elan). Supported toolchains: Lean 4.33.0 and later
(built and smoke-tested on 4.33.0, 4.33.1, 4.34.0, 4.34.1, 4.35.0-rc4, 4.35.0 and a 2026-10-08 nightly).

    lake build
    .lake/build/bin/leanout Init > init.ndjson               # a module and everything it imports
    .lake/build/bin/leanout Init -- Nat.add_comm             # one constant plus its dependencies
    .lake/build/bin/leanout --validate init.ndjson           # structural check, no kernel needed

Run it under the toolchain that built the `.olean` files you are importing, with `LEAN_PATH` pointing at them
(for a Lake project, `lake env path/to/leanout Module`).

## Options

    -o FILE        write to FILE (a name ending in .gz is compressed with gzip)
    --prefix P     only roots whose name starts with P (their dependencies are still exported)
    --exclude P    drop roots whose name starts with P
    --module M     only constants declared in module M (plus their dependencies)
    --unsafe       include unsafe and partial declarations
    --stats        declaration counts to stderr
    --axioms       list every axiom in the export (a trust report)
    --validate F   kernel-independent structural check of an existing export

## What the output looks like

- Dependency-ordered and deterministic: roots are sorted by name, so the same input gives identical bytes.
- Inductive groups (types, constructors, recursors, nested `rec_N` auxiliaries) are emitted as one unit.
- Literals count as dependencies on `Nat`, `String`, `String.ofList` and friends, so checkers that expand
  literals always see them declared first.
- `mdata` is preserved, including its payload (strings, bools, names, numbers; syntax as its printed form).
- By default unsafe and partial declarations, `_unsafe_rec` helpers and anything that refers to them are
  skipped. They cannot be checked without trusting compiled code, and mutually recursive unsafe groups have
  no representation in the format. `--unsafe` includes them.

Compared with another exporter's output for `Init`, this one is a superset: it also exports helper constants
such as `_flat_ctor` and `_inherited_default`, and keeps `mdata` wrappers; otherwise terms are identical.

## Verification

Every export below was accepted with no failures by both Lean's own kernel (`Environment.replay`) and Tenet 0.11.1.

| Export | Constants |
|---|---|
| Init (Lean 4.35.0-rc4) | 65,371 |
| Std | 111,932 |
| Lean (whole package) | 204,383 |
| Mathlib.Data.Real.Basic (Lean 4.34.1) | 216,288 |
| Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic (Lean 4.34.1) | 338,334 |

`--unsafe` on Init (65,972 constants): Lean's kernel accepts all of it; Tenet rejects 535 definitions because they
refer to themselves (unsafe recursion). That is why the default skips them.

Memory grows with the number of distinct expressions. The 338k-constant Mathlib closure exports in about two
minutes using 3.4 GB; whole-Mathlib has not been tried and would need considerably more.

## Tests

    lake build Fixtures
    tests/run.sh [path-to-lean-replay-binary]

`tests/fixtures/Fixtures.lean` exercises mutual, nested, reflexive and indexed inductives, structures,
quotients, big and Unicode literals, well-founded recursion, universe `max`/`imax`, and skipped unsafe code.
The script checks determinism, option behaviour and the validator, and runs Tenet and Lean's kernel when they
are available. It includes negative tests: swapped theorem types and swapped recursor rules must be rejected by
both kernels, and a deleted name line must be rejected by `--validate`.

## License

Apache-2.0, see `LICENSE` and `NOTICE`.
