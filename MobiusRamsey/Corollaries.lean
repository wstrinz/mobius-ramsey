module

public import MobiusRamsey.Theorem
public import MobiusRamsey.Circle
public import MobiusRamsey.AlgebraicRamsey

@[expose] public section

/-!
# Corollaries of Theorem C

* `ramsey_mobius_of_algebraic`: a Möbius image of a finite set of distinct points of the unit
  sphere with real algebraic coordinates is Ramsey (Theorem C +
  `ramsey_of_algebraic`, `MobiusRamsey.AlgebraicRamsey`). Scope `MOBIUS_ORBIT_OF(ALGEBRAIC)`; no spanning hypothesis, any `d`.
* The circle chart `circ t = ((1 - t²)/(1 + t²), 2t/(1 + t²))` (from the pole
  `(-1, 0)`): `t ↦ k t` (`k ≠ 0`) and `t ↦ t + c` are Möbius maps of the unit circle, given by
  explicit `L ∈ O(1,2)` (`exists_mobius_circ_mul`, `exists_mobius_circ_add`). Hence
  `circ (k tᵢ)` and `circ (tᵢ + c)` are Ramsey for distinct algebraic (e.g. rational) `tᵢ` and
  arbitrary real `k ≠ 0`, `c` (`ramsey_circ_mul`, `ramsey_circ_add`).
-/

namespace OAI
noncomputable section
namespace EuclideanRamsey
namespace Mobius

open Matrix

/-- **Möbius images of algebraic spherical sets are Ramsey.** -/
theorem ramsey_mobius_of_algebraic {s d : ℕ} (a : Fin s → Space d)
    (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hL : Lᵀ * lorentzForm d * L = lorentzForm d) (ha : Function.Injective a)
    (hsph : ∀ i, a i ∈ Metric.sphere (0 : Space d) 1)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j)) :
    Ramsey (mobiusMap L ∘ a) := by
  by_cases hs : 2 ≤ s
  · refine (ramsey_iff_ramsey_mobius_full a L hL ha hsph).mp ?_
    exact ramsey_of_algebraic a hs (one_le_dim hs ha) ha halg
      ⟨0, 1, fun i => Metric.mem_sphere.mp (hsph i)⟩
  · exact ramsey_of_lt_two _ (by omega)

/-- **circ(k t) is Ramsey**: for distinct algebraic (e.g. rational) parameters `tᵢ` and any real
`k ≠ 0`, the points `circ (k tᵢ)` form a Ramsey set (a Möbius image of an algebraic set). -/
theorem ramsey_circ_mul {s : ℕ} (t : Fin s → ℝ) (ht : Function.Injective t)
    (halg : ∀ i, IsAlgebraic ℚ (t i)) (k : ℝ) (hk : k ≠ 0) :
    Ramsey (fun i => circ (k * t i)) := by
  obtain ⟨L, hL, hLc⟩ := exists_mobius_circ_mul k hk
  have e : (fun i => circ (k * t i)) = mobiusMap L ∘ (circ ∘ t) :=
    funext fun i => (hLc (t i)).symm
  rw [e]
  exact ramsey_mobius_of_algebraic _ L hL (circ_injective.comp ht)
    (fun i => mem_sphere_zero_iff_norm.mpr (norm_circ _)) (fun i j => circ_isAlgebraic (halg i) j)

/-- **circ(t + c) is Ramsey**: for distinct algebraic (e.g. rational) parameters `tᵢ` and any
real `c`, the points `circ (tᵢ + c)` form a Ramsey set (a Möbius image of an algebraic set). -/
theorem ramsey_circ_add {s : ℕ} (t : Fin s → ℝ) (ht : Function.Injective t)
    (halg : ∀ i, IsAlgebraic ℚ (t i)) (c : ℝ) :
    Ramsey (fun i => circ (t i + c)) := by
  obtain ⟨L, hL, hLc⟩ := exists_mobius_circ_add c
  have e : (fun i => circ (t i + c)) = mobiusMap L ∘ (circ ∘ t) :=
    funext fun i => (hLc (t i)).symm
  rw [e]
  exact ramsey_mobius_of_algebraic _ L hL (circ_injective.comp ht)
    (fun i => mem_sphere_zero_iff_norm.mpr (norm_circ _)) (fun i j => circ_isAlgebraic (halg i) j)

/-- Rational parameters, as the note states it. -/
theorem ramsey_circ_mul_rat {s : ℕ} (t : Fin s → ℚ) (ht : Function.Injective t) (k : ℝ)
    (hk : k ≠ 0) : Ramsey (fun i => circ (k * (t i : ℝ))) :=
  ramsey_circ_mul (fun i => (t i : ℝ)) (Rat.cast_injective.comp ht)
    (fun i => by simpa using isAlgebraic_algebraMap (A := ℝ) (t i)) k hk

theorem ramsey_circ_add_rat {s : ℕ} (t : Fin s → ℚ) (ht : Function.Injective t) (c : ℝ) :
    Ramsey (fun i => circ ((t i : ℝ) + c)) :=
  ramsey_circ_add (fun i => (t i : ℝ)) (Rat.cast_injective.comp ht)
    (fun i => by simpa using isAlgebraic_algebraMap (A := ℝ) (t i)) c

end Mobius
end EuclideanRamsey
end
end OAI

#print axioms OAI.EuclideanRamsey.Mobius.ramsey_mobius_of_algebraic
#print axioms OAI.EuclideanRamsey.Mobius.ramsey_circ_mul
#print axioms OAI.EuclideanRamsey.Mobius.ramsey_circ_add
#print axioms OAI.EuclideanRamsey.Mobius.ramsey_circ_mul_rat
#print axioms OAI.EuclideanRamsey.Mobius.ramsey_circ_add_rat
#print axioms OAI.EuclideanRamsey.Mobius.exists_mobius_circ_mul
#print axioms OAI.EuclideanRamsey.Mobius.exists_mobius_circ_add
