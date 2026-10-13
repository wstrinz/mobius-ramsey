# Fidelity of the advertised statements

This file checks, one line per item, that the four advertised Lean statements in
`Challenge.lean` say what `README.md` and `note/mobius.tex` say they do. Each line ends with how it
was checked:
- **Lean**: a named theorem in this package, built with the three standard axioms only;
- **inspection**: reading the statement text in `Challenge.lean`;
- **hand**: a short written argument, given in the line;
- **cited**: classical, cited in the note, not formalized.

The statements: `ramsey_iff_ramsey_mobius_full` (Theorem C), `ramsey_mobius_of_algebraic`,
`ramsey_circ_mul_rat`, `ramsey_circ_add_rat` (namespace `OAI.EuclideanRamsey.Mobius`).

## Definitions

| Item | Finding | Checked by |
|---|---|---|
| `Space`, `Congruent`, `Ramsey` | OpenAI's definitions, character for character, from their `Model.lean` at `fd4aeeb2` (which is also the text of OpenAI's own Comparator challenge for result 172). Nothing here redefines them | inspection; `note/check_verbatim.py` (Model excerpt); Comparator's definition match (control `redef-ramsey` is refused) |
| `lorentzForm`, `aug`, `mobiusMap`, `circ` | Nine code lines beyond Mathlib and OpenAI. `lorentzForm d = diag(−1, 1, …, 1)` indexed by `Option (Fin d)` (`none` is the time coordinate); `aug x = (1, x)`; `mobiusMap L x` is the spatial part of `L (1, x)` divided by its time coordinate; `circ t = ((1 − t²)/(1 + t²), 2t/(1 + t²))` | inspection; Comparator's definition match (controls `redef-lorentz` and `redef-circ` are refused) |

## Checklist items

| Item | Finding | Checked by |
|---|---|---|
| **Ordered versus unordered pairs** | `Congruent a b` is `∀ i j, dist (b i) (b j) = dist (a i) (a j)`, over ordered pairs including `i = j`. Since `dist` is symmetric and `dist x x = 0`, this is the same as the condition on unordered pairs of distinct indices. A configuration is an indexed family `Fin s → Space d`, as in OpenAI's development; with injectivity it is the same as a set of `s` distinct points | inspection; hand (symmetry of `dist`) |
| **Metric** | `Space d` is `EuclideanSpace ℝ (Fin d)`, so `dist` is the Euclidean distance (not the sup metric of `Fin d → ℝ` or `ℝ × ℝ`). `Metric.sphere (0 : Space d) 1` is therefore the Euclidean unit sphere. `circ` lands in `Space 2` by `WithLp.toLp 2` | inspection; Lean (`norm_circ`: `‖circ t‖ = 1`) |
| **Injectivity and distinctness** | Theorem C and `ramsey_mobius_of_algebraic` assume `Function.Injective a` (the note's "distinct points"). The circle corollaries assume `Function.Injective t` for the rational parameters; the points are then distinct because `circ` is injective, `k ≠ 0`, and `u ↦ u + c` is injective. Images are distinct too: `φ_L` is injective on the sphere. Without the injectivity hypothesis Theorem C is a different, stronger statement (probably true), and Comparator refuses it as not the advertised one (control `drop-injective`) | inspection; Lean (`circ_injective`, `mobiusMap_injOn`); control |
| **Faithful versus non-faithful embeddings** | (1) `Ramsey` quantifies over every dimension `D ≥ 1` and every congruent copy in `Space D`, measured by `dist`; no embedding `Space d → Space D` is chosen, so none can be unfaithful. (2) The Möbius model: `L ↦ φ_L` is not injective (`L` and `−L` give the same map), which is harmless, since the theorem quantifies over all `L`; what matters is that every Möbius transformation is some `φ_L`. For `d ≥ 2` that is the classical isomorphism `PO(1,d) ≅ Möb(S^{d−1})`. It contains every rotation and reflection of the sphere, and each `φ_L` is a bijection of the sphere | cited (note §2: Ratcliffe, Beardon; `docs/CITATION-SOURCES.md`); Lean (`liftO_lorentz`, `mobiusMap_liftO`, `mobiusMap_bijOn` in `MobiusRamsey/Sanity.lean`) |
| **Junk values** (division, `sSup`) | There is no `sSup`, `iSup` or `BddAbove` in the statements. Two real divisions: `mobiusMap` divides by the time coordinate of `L (1, x)`, which can be `0` off the sphere (then Lean's `x / 0 = 0` gives junk), but the theorems only evaluate `mobiusMap` at points of the unit sphere, where the divisor is proved nonzero; `circ` divides by `1 + t² > 0`, never zero | inspection; Lean (`time_ne_zero`, `mulVec_aug`, `norm_mobiusMap`) |
| **ℕ subtraction and division** | None in the statements. The only ℕ arithmetic is the inequalities `2 ≤ r` and `1 ≤ D` in OpenAI's `Ramsey` | inspection |
| **Vacuous or contradictory hypotheses** | Every hypothesis is satisfiable together with a nonempty configuration whenever `d ≥ 1`: `L = 1` satisfies `Lᵀ S L = S`; the standard basis vectors `e_j` and `−e_j` are distinct points of the unit sphere; rational `tᵢ` can be any distinct rationals; `k = 1`, `c = 0`. The algebraic corollary is non-vacuous for the same `e_j`, whose coordinates are `0` and `±1`. Any `L` with `Lᵀ S L = S` is invertible, with inverse `S Lᵀ S` | hand; Lean (`inv_mul`, `mul_inv`) |

## Edge cases in `d`

| Case | Finding | Checked by |
|---|---|---|
| `d ≥ 2` | The intended case: `φ_L` ranges over the whole Möbius group of `S^{d−1}`, orientation-reversing maps included | cited (note §2) |
| `d = 1` | `S⁰ = {±1}`. Every boost `[[cosh θ, sinh θ], [sinh θ, cosh θ]]` maps `(1, ±1)` to `e^{±θ}(1, ±1)`, so it fixes both points; the maps `φ_L` are just the two permutations of `S⁰`, and `PO(1,1) → Sym(S⁰)` is not injective. So for `d = 1` the Lean model is not a faithful model of a Möbius group, and the Möbius identification is not claimed there. The Lean theorem is still true and proved for `d = 1` (every subset of `S⁰` is Ramsey: a singleton is, and every two-point set is, by OpenAI's Cor. 7.4); it just says nothing about Möbius maps | hand; Lean (the statement has no restriction on `d`) |
| `d = 0` | `Space 0` has the single point `0`, of norm `0 ≠ 1`, so the unit sphere is empty. The hypothesis `hsph` then forces `s = 0`, and the theorem is the true statement that the empty family is Ramsey iff the empty family is Ramsey. Vacuous in content, not contradictory | hand |
| `s = 0`, `s = 1` | The empty family and a singleton are Ramsey (for `s = 1`, every colouring is constant on a one-point copy), so Theorem C is trivially true there; for the circle corollaries, `s ≥ 2` is not assumed and not needed | hand |

## What is not formalized

- That the maps `φ_L` are the Möbius transformations of `S^{d−1}` (for `d ≥ 2`): cited.
- Spheres other than the unit sphere centred at `0`: a similarity reduces them to it, by hand
  (note, Remark 1). The regular-polygon case of Corollary 1(c) is by hand.
- The cross-ratio and triangle corollaries of the note: by hand.

## Review

The statements were reviewed for fidelity by an AI agent that did not build the package (see
`DISCLOSURE.md`); this table was written afterwards, to record that review item by item. The table was then read
line by line by a second AI agent that did not write it (2026-10-13). That agent re-derived the
`d = 1` boost argument, the `d = 0` vacuity, the inverse `S Lᵀ S` and the junk-value argument,
and found no errors. No human expert has reviewed it.
