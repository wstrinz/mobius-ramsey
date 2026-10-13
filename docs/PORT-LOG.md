# Port log: OpenAI's EuclideanRamsey closure and the Möbius development, Lean v4.35.0-rc2

**Pins.**
- OpenAI: openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the 28 modules of
  `OAI.Combinatorics.EuclideanRamsey.Main`'s import closure (listed in `NOTICE`), copied byte-exact
  from upstream (checked against their SHA-256 sums before the port).
- From: Lean v4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (OpenAI's pin).
- To: Lean **v4.35.0-rc2** / Mathlib **`065356127b1dc0016f66b7283ce0ce2c4055aa55`** (Mathlib tag
  `v4.35.0-rc2`, the PalomarTemplate pin). All nine Lake packages are pinned to full SHAs in
  `lake-manifest.json`.

Why: Palomar requires every `.lean` file to use the Lean module system and a toolchain of at least
v4.35.0-rc2, and its judge is the toolchain's own `lake comparator`.

## 1. OpenAI's files: header-only changes

`python3 scripts/port_to_modules.py --notice-oai OAI/Combinatorics/EuclideanRamsey/*.lean` (run once,
on the byte-exact upstream files) made,
in each of the 28 files:

| Change | Lines per file | Why |
|---|---|---|
| Apache-2.0 modification notice, a plain comment before `module` | +8 | Apache-2.0 §4(b); Palomar allows ordinary comments before the header |
| `module` before the imports | +1 | every file must use the module system |
| `import X` → `public import X` | ±1 per import (each OpenAI file has one) | dependants see the imported declarations |
| `@[expose] public section` after the imports | +1 | every declaration stays public and every definition keeps its body visible downstream: the pre-module behaviour |
| blank lines around those | +2 | layout |

**No other line changed.** Checked mechanically: with comments, blank lines and the header lines
removed, each ported file's code equals the upstream file's code, line for line. All 28 modules
built at the new pin with no proof edits, no errors and no new warnings; the Mathlib drift between
the two pins touches no name that OpenAI's files use.

## 2. This project's files (`MobiusRamsey/`)

Written at Lean v4.34.1 / Mathlib `d13f23b7` on top of OpenAI's unmodified files, then:

1. **Renamed** (and their imports rewritten by `scripts/port_to_modules.py`):

   | Before | Module now |
   |---|---|
   | `Rope.MobiusDefs` | `MobiusRamsey.Defs` |
   | `Rope.MobiusTransport` | `MobiusRamsey.Transport` |
   | `Rope.MobiusFullTransport` | `MobiusRamsey.FullTransport` |
   | `Rope.MobiusFull` | `MobiusRamsey.Theorem` |
   | `Rope.MobiusCorCircle` | `MobiusRamsey.Circle` |
   | `Rope.MobiusCor` | `MobiusRamsey.Corollaries` |
   | `Rope.MobiusSanity` | `MobiusRamsey.Sanity` |
   | `Rope.AlgebraicRamsey` | `MobiusRamsey.AlgebraicRamsey` |

2. **Ported** to the module system by the same header pass (without the Apache notice).
3. **Unused declarations removed.** An earlier form of Theorem C carried an affine-spanning
   hypothesis. Once the span-free theorem (`ramsey_iff_ramsey_mobius_full`) was proved, the
   following declarations were used by nothing else and were deleted whole: `Nondeg`,
   `nondeg_of_span`, `span_of_nondeg`, `nondeg_mobius`, `quadric_eq_lorentz` (`Defs`) and
   `realCriterion_mobius` (`Transport`), 177 code lines in total. The spanning form of Theorem C
   is not shipped: it is the special case of the span-free theorem with one more hypothesis.
4. **Comments and docstrings** were edited to describe this package (references to working files
   removed). No statement, proof, `open`, `variable` or option of any retained declaration was
   changed.

5. **`circ` moved** from `MobiusRamsey/Circle.lean` to `MobiusRamsey/Defs.lean`, directly after
   `mobiusMap`, unchanged. Reason: under the module system, Lean abstracts the proof of
   `Nat.AtLeastTwo 2` inside the literal `2` of `WithLp.toLp 2` into an auxiliary constant, and
   reuses one such constant per module. In `Challenge.lean`, where `circ` follows `mobiusMap`,
   `circ`'s body refers to `mobiusMap._proof_1`; in a separate module it referred to
   `circ._proof_1`, and Comparator rejected the bodies as different
   ("Const does not match ... 'OAI.EuclideanRamsey.Mobius.circ'"). Defining `circ` in the same
   module and position as in the challenge makes the compiled bodies identical.

Checked mechanically, as for OpenAI's files: with comments and header lines removed, no code line
was added to any of the eight files except the two lines of `circ` moved between them, and the
only removed code lines are the six declarations of item 3 (and `circ`'s two lines in `Circle`).

## 3. New files

| File | What |
|---|---|
| `Challenge.lean` | Mathlib-only statement surface: OpenAI's `Space`, `Congruent`, `Ramsey` verbatim from `Model.lean`; `lorentzForm`, `aug`, `mobiusMap`, `circ` verbatim from `MobiusRamsey/Defs.lean`, in the same order; the four advertised statements with `sorry` |
| `Solution.lean` | `public import MobiusRamsey.Theorem` and `MobiusRamsey.Corollaries` |
| `comparator.json` | the four theorems, no definition holes, the three standard axioms |
| `tests/controls/` | five negative controls, each `Challenge.lean` with one edit, and their runner |
| `scripts/port_to_modules.py` | the header pass above |
| `scripts/check-lean-sources.py`, `scripts/verify-comparator.sh` | PalomarTemplate `2891de4c`, unmodified |

## 4. Replay of the OpenAI part

The replay commands are in `REPRODUCE.md` §5. They download the 28 upstream files from
openai/math at `fd4aeeb2` into a fresh scratch directory (`mktemp -d`), run
`python3 scripts/port_to_modules.py --notice-oai` on them there (the script rewrites the files it
is given in place, so it must not be pointed at the files in this repository), and compare the
result with `OAI/Combinatorics/EuclideanRamsey/` by `diff -r`: no differences.
