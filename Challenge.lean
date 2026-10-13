module

public import Mathlib

@[expose] public section

/-!
# Advertised statements: Möbius invariance of the Ramsey property (Theorem C) and corollaries

Mathlib-only. The trusted surface is the seven definitions below and the four theorem statements.

* `Space`, `Congruent`, `Ramsey` are restated verbatim from OpenAI's
  `OAI/Combinatorics/EuclideanRamsey/Model.lean` (openai/math fd4aeeb2, Apache-2.0), which is also
  the text of OpenAI's own Comparator challenge for result 172. A finite configuration
  `a : Fin s → ℝ^d` is *Ramsey* if for every number of colours `r ≥ 2` there is a dimension `D`
  such that every `r`-colouring of `ℝ^D` contains a monochromatic congruent copy of `a`.
* `lorentzForm d` is `S = diag(-1, 1, …, 1)` on `ℝ^{1+d}`, indexed by `Option (Fin d)` (`none` is
  the extra coordinate). `aug x` is the vector `(1, x)`. For `L` with `Lᵀ S L = S` (that is,
  `L ∈ O(1,d)`), `mobiusMap L x` is the spatial part of `L (1, x)` divided by its `none`
  coordinate: the action of `L` on the unit sphere `S^{d-1}` viewed as the projectivized null cone
  of `S`.
* `circ t = ((1 - t²)/(1 + t²), 2t/(1 + t²))` is the stereographic chart of the unit circle from
  the pole `(-1, 0)`.

**Fidelity.** That the maps `mobiusMap L`, `L ∈ O(1,d)`, are exactly the Möbius transformations
of `S^{d-1}` is the classical identification `Möb(S^{d-1}) ≅ PO(1,d)`; it is cited, not proved.
Off the unit sphere `mobiusMap` is not meaningful (Lean's `x / 0 = 0`), and the theorems only
evaluate it on the sphere, where the divisor is nonzero. There is no affine-spanning hypothesis.
-/

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def Congruent {s d D : ℕ} (a : Fin s → Space d) (b : Fin s → Space D) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

def Ramsey {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ c : Space D → Fin r, ∃ b : Fin s → Space D,
      Congruent a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

namespace Mobius

open Matrix

variable {d : ℕ}

/-- The Lorentz form `S = diag(-1, 1, …, 1)` on `ℝ^{1+d}`, indexed by `Option (Fin d)`. -/
def lorentzForm (d : ℕ) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  Matrix.diagonal fun α => Option.elim α (-1) fun _ => 1

/-- The augmented vector `(1, x)`, as OAI's `realAugmented`. -/
def aug (x : Space d) : Option (Fin d) → ℝ
  | none => 1
  | some j => x j

/-- The point map of `L ∈ O(1,d)` on the unit sphere: the spatial part of `L (1, x)` divided by
its `none` coordinate (nonzero on the sphere, `time_ne_zero`). -/
def mobiusMap (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (x : Space d) : Space d :=
  WithLp.toLp 2 fun j => (L *ᵥ aug x) (some j) / (L *ᵥ aug x) none

/-- The stereographic chart of the unit circle, from the pole `(-1, 0)`. -/
def circ (t : ℝ) : Space 2 :=
  WithLp.toLp 2 ![(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)]

/-- **Theorem C.** For finitely many distinct points `a` on the unit sphere of `ℝ^d` and any
`L ∈ O(1,d)` (`Lᵀ S L = S`, `S = diag(-1, 1, …, 1)`), `a` is Ramsey iff its image under the
Möbius map `φ_L` is Ramsey. No spanning hypothesis. -/
theorem ramsey_iff_ramsey_mobius_full {s d : ℕ} (a : Fin s → Space d)
    (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hL : Lᵀ * lorentzForm d * L = lorentzForm d) (ha : Function.Injective a)
    (hsph : ∀ i, a i ∈ Metric.sphere (0 : Space d) 1) :
    Ramsey a ↔ Ramsey (mobiusMap L ∘ a) := by
  sorry

/-- **Möbius images of algebraic spherical sets are Ramsey.** Distinct points of the unit sphere
with real algebraic coordinates, moved by any `L ∈ O(1,d)`. -/
theorem ramsey_mobius_of_algebraic {s d : ℕ} (a : Fin s → Space d)
    (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hL : Lᵀ * lorentzForm d * L = lorentzForm d) (ha : Function.Injective a)
    (hsph : ∀ i, a i ∈ Metric.sphere (0 : Space d) 1)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    Ramsey (mobiusMap L ∘ a) := by
  sorry

/-- **circ(k t) is Ramsey**: for distinct rationals `tᵢ` and any real `k ≠ 0`. -/
theorem ramsey_circ_mul_rat {s : ℕ} (t : Fin s → ℚ) (ht : Function.Injective t) (k : ℝ)
    (hk : k ≠ 0) : Ramsey (fun i => circ (k * (t i : ℝ))) := by
  sorry

/-- **circ(t + c) is Ramsey**: for distinct rationals `tᵢ` and any real `c`. -/
theorem ramsey_circ_add_rat {s : ℕ} (t : Fin s → ℚ) (ht : Function.Injective t) (c : ℝ) :
    Ramsey (fun i => circ ((t i : ℝ) + c)) := by
  sorry

end Mobius
end EuclideanRamsey
end
end OAI
