# mobius-ramsey

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23339522.svg)](https://doi.org/10.5281/zenodo.23339522)

Archived on Zenodo. Cite all versions with the concept DOI [10.5281/zenodo.23339522](https://doi.org/10.5281/zenodo.23339522); v1.0.0 specifically is [10.5281/zenodo.23339523](https://doi.org/10.5281/zenodo.23339523).

**Möbius invariance of the Ramsey property for finite spherical sets, proved in Lean 4.**

A finite set of points in Euclidean space is *Ramsey* if for every number of colours `r ≥ 2`
there is a dimension `D` such that every `r`-colouring of `ℝ^D` contains a monochromatic congruent
copy of the set. OpenAI's result 172 classified the finite Ramsey configurations by a tensor
condition over their coordinate field. This repository proves that the condition is transported
by the Lorentz group, so that:

> **Theorem C.** Let `a₁, …, a_s` be distinct points of the unit sphere `S^{d-1} ⊂ ℝ^d` and let
> `φ` be a Möbius transformation of `S^{d-1}`. Then `{a₁, …, a_s}` is Ramsey if and only if
> `{φ(a₁), …, φ(a_s)}` is Ramsey.

In Lean, `φ` is the map `φ_L` of a matrix `L ∈ O(1,d)`; that for `d ≥ 2` these maps are the
Möbius transformations is classical and cited (see Limitations). There is no hypothesis that the
points affinely span `ℝ^d`. On a circle, Ramsey-ness therefore depends only on cross-ratios (by
hand, in the note).

**Corollaries** (also proved in Lean):
- every Möbius image of a finite set of distinct points of the unit sphere with real algebraic
  coordinates is Ramsey;
- for distinct rationals `t₁, …, t_s` and **any** real `k ≠ 0` and `c` (transcendental or not),
  the circle points `circ(k tᵢ)` and `circ(tᵢ + c)` form Ramsey sets, where
  `circ(t) = ((1 − t²)/(1 + t²), 2t/(1 + t²))` is the stereographic chart of the unit circle.

The deep work is OpenAI's: Theorem C is a short consequence of their classification, and the Lean
proof here builds on their Lean proof. The note `note/mobius.tex` gives the hand proof, the
corollaries, and the verification status of every statement.

## The statements, verbatim

Definitions (`Challenge.lean`; `Space`, `Congruent`, `Ramsey` are OpenAI's, verbatim from their
`Model.lean`):

```lean
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

def lorentzForm (d : ℕ) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  Matrix.diagonal fun α => Option.elim α (-1) fun _ => 1

def aug (x : Space d) : Option (Fin d) → ℝ
  | none => 1
  | some j => x j

def mobiusMap (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (x : Space d) : Space d :=
  WithLp.toLp 2 fun j => (L *ᵥ aug x) (some j) / (L *ᵥ aug x) none

def circ (t : ℝ) : Space 2 :=
  WithLp.toLp 2 ![(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)]
```

`lorentzForm d` is `S = diag(−1, 1, …, 1)` on `ℝ^{1+d}` (the `none` index is the extra
coordinate), `aug x = (1, x)`, and for `L ∈ O(1,d)` (that is, `Lᵀ S L = S`), `mobiusMap L` is the
action of `L` on the unit sphere seen as the projectivized null cone of `S`.

The four advertised theorems (namespace `OAI.EuclideanRamsey.Mobius`; `comparator.json`):

```lean
theorem ramsey_iff_ramsey_mobius_full {s d : ℕ} (a : Fin s → Space d)
    (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hL : Lᵀ * lorentzForm d * L = lorentzForm d) (ha : Function.Injective a)
    (hsph : ∀ i, a i ∈ Metric.sphere (0 : Space d) 1) :
    Ramsey a ↔ Ramsey (mobiusMap L ∘ a)

theorem ramsey_mobius_of_algebraic {s d : ℕ} (a : Fin s → Space d)
    (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hL : Lᵀ * lorentzForm d * L = lorentzForm d) (ha : Function.Injective a)
    (hsph : ∀ i, a i ∈ Metric.sphere (0 : Space d) 1)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    Ramsey (mobiusMap L ∘ a)

theorem ramsey_circ_mul_rat {s : ℕ} (t : Fin s → ℚ) (ht : Function.Injective t) (k : ℝ)
    (hk : k ≠ 0) : Ramsey (fun i => circ (k * (t i : ℝ)))

theorem ramsey_circ_add_rat {s : ℕ} (t : Fin s → ℚ) (ht : Function.Injective t) (c : ℝ) :
    Ramsey (fun i => circ ((t i : ℝ) + c))
```

`MobiusRamsey/Corollaries.lean` also proves `ramsey_circ_mul` and `ramsey_circ_add` for algebraic
(not only rational) `tᵢ`, and `MobiusRamsey/AlgebraicRamsey.lean` proves Theorem A,
`ramsey_of_algebraic` (a finite spherical set with real algebraic coordinates is Ramsey), which
the corollaries use.

## What is checked, and how

- **Kernels and statements.** The toolchain's own `lake comparator` (Lean v4.35.0-rc2) compiles
  `Challenge.lean` (Mathlib only: the definitions above and the four statements with `sorry`) and
  `Solution.lean` (the proofs), checks that every advertised theorem has exactly the challenge's
  statement and that every definition it mentions has exactly the challenge's body, checks that
  only `propext`, `Classical.choice` and `Quot.sound` are used, and replays the whole proof
  (about 63,600 declarations, including the Mathlib ones it uses) through three independent
  kernels: Lean's own, NanoDa and con-ron. It accepts: "Your solution is okay!".
  `scripts/verify-comparator.sh` is
  PalomarTemplate's script, unmodified; it runs this check in a bubblewrap sandbox, as the
  Palomar registry does.
- **Negative controls.** `tests/controls/` holds five altered challenges. Each is refused for
  its expected reason: the challenge as its own solution (`sorryAx`), `Ramsey` with `3 ≤ r`,
  `lorentzForm` replaced by the identity, a changed `circ`, and Theorem C without the
  injectivity hypothesis. The last is a stronger statement, probably true; it is refused because
  it is not the statement that was proved.
- **Axioms.** `lake build` prints `#print axioms` for every theorem above and for the main
  lemmas: `[propext, Classical.choice, Quot.sound]` throughout. There is no `sorry`, `admit` or
  `native_decide` outside the statement-only `Challenge.lean`.
- **The trusted surface** is `Challenge.lean`: OpenAI's three definitions, nine lines of further
  definitions (`lorentzForm`, `aug`, `mobiusMap`, `circ`), and the four statements. Read it.
- **CI.** `.github/workflows/verify.yml` is configured to run all of this on a fresh GitHub
  runner. It has not run yet: it needs the public repository.
- **Fidelity.** `docs/FIDELITY.md` goes through the statements item by item: pairs, metric,
  injectivity, embeddings, junk values, vacuity and the edge cases `d = 0` and `d = 1`.

### Independence

**This work trusts OpenAI's Lean proof of result 172.** OpenAI's 28 Lean files (the import closure
of their `Main.lean`) are included and replayed by the kernels here, but the classification
itself is theirs, not re-proved. The files were ported to the Lean module system by header-only
changes (a `module` line, `public import`, `@[expose] public section`, and an Apache-2.0
modification notice); no statement or proof line changed (`docs/PORT-LOG.md`).

## Prior work

- **OpenAI**, *A classification of finite Euclidean Ramsey configurations* (openai/math, commit
  `fd4aeeb2`, result 172): the foundation, and the Lean proof this one builds on.
- **Pálvölgyi**, *A cyclic non-Ramsey heptagon* (arXiv:2609.23327). By its arXiv comments and its
  own disclosure, the whole manuscript was written by ChatGPT; its appendix, labelled unchecked,
  holds further ChatGPT results that he has not verified. The appendix's Lemma A.5 proves that
  the existence of his derivation certificates is invariant under real Möbius maps, and says
  explicitly that the lemma "does not assert that the Ramsey property itself is Möbius
  invariant". Theorem C is that stronger assertion. The appendix's Theorem A.10 is the
  certificate-level analogue on the circle of the first corollary: a finite subset of the unit
  circle that a Möbius map sends to algebraic points, apart from at most three, has no
  certificate of his non-Ramsey criterion.
- **Theorem A** (algebraic coordinates ⇒ Ramsey), used for the first corollary, is prior work:
  JD-Jones-ASES/six-concyclic-lean (Lean, criterion level, Ramsey conclusion conditional on a
  hypothesis `hsuff`), Rogerhu12/openai-math-extensions (TeX), and atimics/math2 (Lean, end to
  end for algebraic configurations with full affine span; its written derivation also covers
  sets similar to algebraic ones). `ramsey_of_algebraic` here is a further proof, not a first one.
- **No prior statement of Theorem C was found.** The search log is `docs/PRIOR-WORK-SEARCH.md`.
  The corollaries are derivable by an expert from Theorem C and known results, and are not claimed
  as independently new.

## Limitations

- **The Möbius model.** A Möbius transformation of `S^{d-1}` is modelled as `mobiusMap L` with
  `L ∈ O(1,d)`. That for `d ≥ 2` these maps are exactly the Möbius group
  (`Möb(S^{d-1}) ≅ PO(1,d)`, orientation reversing maps included) is classical and **cited, not
  formalized**. For `d = 1` the identification fails (boosts fix both points of `S⁰`, and the
  maps `φ_L` are just the two permutations of `S⁰`); the Lean theorem is still true there, but
  it is not a statement about a Möbius group. For `d = 0` the unit sphere is empty. The model
  contains every rotation and reflection of the sphere (`MobiusRamsey/Sanity.lean`), and each
  `φ_L` is a bijection of the sphere.
- **Unit sphere.** The Lean statements are for points of the unit sphere centred at `0`. A
  general sphere reduces to it by a similarity, which preserves Ramsey-ness; that step is by hand
  (note, Remark 1).
- `mobiusMap` divides by a coordinate that is nonzero on the sphere (proved); off the sphere
  `mobiusMap` is not meaningful, and the theorems only evaluate it on the sphere.
- The cross-ratio and triangle corollaries of the note are by hand, not in Lean.
- **Review.** No human expert has reviewed this work. The author's read of the hand proof is an
  owner's read. The proofs and checks were produced by AI agents; see `DISCLOSURE.md`.

## Reproduce

Full instructions, with the exact commands and expected output, are in `REPRODUCE.md`. In short,
on Linux with [elan](https://github.com/leanprover/elan) on `PATH`
(`export PATH="$HOME/.elan/bin:$PATH"`) and `bwrap` installed:

```sh
python3 scripts/check-lean-sources.py     # Palomar's source rules: exit 0
lake exe cache get                        # Mathlib's prebuilt files (about 5 GB)
lake build                                # prints the axioms lines
bash scripts/verify-comparator.sh         # "Your solution is okay!"
bash tests/controls/run-controls.sh       # five "REFUSED as expected" lines
```

**Time and memory.** With Mathlib's files cached, on a shared desktop machine: the build took
8.5 minutes on Linux (8 threads) and 32 minutes on Windows (12 threads), most of it OpenAI's
28-module chain, which builds one module at a time; the sandboxed Comparator run took 8 minutes
and the five controls 12 minutes. On a heavily loaded machine plan on **2 to 4 hours**, and on
**about 16 GB of RAM**. The build prints four expected warnings, `declaration uses 'sorry'`, for
the statement-only `Challenge.lean`, and two linter warnings (`This simp argument is unused`) in
`MobiusRamsey/AlgebraicRamsey.lean`.

## Licence and citation

This is a mixed tree. MIT (`LICENSE`) for this project's files. Apache-2.0
(`LICENSES/Apache-2.0.txt`) for OpenAI's files under `OAI/`, modified in their headers only (listed
in `NOTICE` and `docs/PORT-LOG.md`), and for the two unmodified PalomarTemplate scripts under
`scripts/`. `NOTICE` says which file is under which licence.
Cite with `CITATION.cff`. Archive: DOI to be added after the first release.

## Authorship

Will Strinz is the sole human author. AI agents (Claude Opus 5.5 and Claude Sonnet 5.5,
Anthropic) produced the proofs, the port, the checks and the documentation under his direction.
`DISCLOSURE.md` says who did what and which reviews were AI reviews.
