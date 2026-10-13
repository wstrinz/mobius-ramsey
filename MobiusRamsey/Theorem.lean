module

public import MobiusRamsey.FullTransport
public import OAI.Combinatorics.EuclideanRamsey.Main

@[expose] public section

/-!
# Theorem C: Möbius invariance of the Ramsey property

`Ramsey` is OpenAI's own definition (`Model.lean`, openai/math @ fd4aeeb2). The theorem holds
for every finite set of distinct points of the unit sphere: there is no affine-spanning
hypothesis.

**Route** (nothing is restricted to a subsphere and no `O(1,k)` matrix is induced):
* Ramsey ⇒ real criterion without spanning (`realCriterion_of_ramsey`): OAI's
  `full_affine_representative` gives a congruent spanning copy `b`, OAI's necessity
  `ramsey_realCriterion` applies to `b`, OAI's `congruent_linearIsometry` writes
  `a = t + Q b`, and `realCriterion_of_isometry` transfers the criterion to `a`.
* The Lorentz transport `realCriterion_mobius_full` needs no spanning hypothesis.
* Back to Ramsey: OAI's descent `realCriterion_fieldCriterion` and sufficiency
  `fieldCriterion_ramsey`; neither needs spanning. The converse is the same for `L⁻¹ = S Lᵀ S`.

**Fidelity notes.** Möbius maps of `S^{d-1}` are modelled by
`mobiusMap L`, `Lᵀ S L = S`, through the classical identification `Möb(S^{d-1}) ≅ PO(1,d)`
(cited, not proved); the points are distinct (`a` injective) and lie on the unit sphere
centred at `0`. No other hypothesis.
-/

namespace OAI
noncomputable section
namespace EuclideanRamsey
namespace Mobius

open Matrix

/-- OAI's necessity direction without the spanning hypothesis: a Ramsey configuration of at
least two distinct points satisfies OAI's real criterion in its own coordinates. -/
theorem realCriterion_of_ramsey {s d : ℕ} (a : Fin s → Space d) (hs : 2 ≤ s)
    (ha : Function.Injective a) (hR : Ramsey a) : RealCriterion a := by
  obtain ⟨k, -, b, -, hab, hspan⟩ := full_affine_representative a hs ha
  have hb : RealCriterion b :=
    ramsey_realCriterion b (by omega) hspan ((ramsey_congruent_iff hab).mp hR)
  obtain ⟨Q, t, ht⟩ :=
    congruent_linearIsometry b a ⟨0, by omega⟩ hspan (fun i j => (hab i j).symm)
  exact realCriterion_of_isometry Q t ht hb

/-- At most one point: every configuration is Ramsey. -/
theorem ramsey_of_lt_two {s d : ℕ} (a : Fin s → Space d) (hs : s < 2) : Ramsey a := by
  interval_cases s
  · intro r hr
    exact ⟨1, le_rfl, fun _ => ⟨fun i => i.elim0, fun i => i.elim0, ⟨0, by omega⟩,
      fun i => i.elim0⟩⟩
  · exact singleton_ramsey a

/-- Two distinct points force `1 ≤ d`. -/
theorem one_le_dim {s d : ℕ} {a : Fin s → Space d} (hs : 2 ≤ s) (ha : Function.Injective a) :
    1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exfalso
    have h01 : (⟨0, by omega⟩ : Fin s) = ⟨1, by omega⟩ := ha (PiLp.ext fun j => j.elim0)
    simp at h01
  · exact h

/-- **Theorem C.** For finitely many distinct points `a` on the unit sphere of
`ℝ^d` and any `L ∈ O(1,d)` (`Lᵀ S L = S`, `S = diag(-1, 1, …, 1)`), `a` is Ramsey iff its
image under the Möbius map `φ_L` is Ramsey. No spanning hypothesis. -/
theorem ramsey_iff_ramsey_mobius_full {s d : ℕ} (a : Fin s → Space d)
    (L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (hL : Lᵀ * lorentzForm d * L = lorentzForm d) (ha : Function.Injective a)
    (hsph : ∀ i, a i ∈ Metric.sphere (0 : Space d) 1) :
    Ramsey a ↔ Ramsey (mobiusMap L ∘ a) := by
  by_cases hs : 2 ≤ s
  · have hn : ∀ i, ‖a i‖ = 1 := fun i => mem_sphere_zero_iff_norm.mp (hsph i)
    have hd : 1 ≤ d := one_le_dim hs ha
    have hb : ∀ i, ‖(mobiusMap L ∘ a) i‖ = 1 := fun i => norm_mobiusMap hL (hn i)
    have hbinj : Function.Injective (mobiusMap L ∘ a) := fun i j h =>
      ha (mobiusMap_injOn hL (hn i) (hn j) h)
    have hback : mobiusMap (lorentzForm d * Lᵀ * lorentzForm d) ∘ (mobiusMap L ∘ a) = a :=
      funext fun i => mobiusMap_left_inv (inv_lorentz hL) hL (inv_mul hL) (hn i)
    constructor
    · intro hR
      exact fieldCriterion_ramsey _ hs hd hbinj (realCriterion_fieldCriterion _
        (realCriterion_mobius_full hL hn (realCriterion_of_ramsey a hs ha hR)))
    · intro hR
      have h := realCriterion_mobius_full (inv_lorentz hL) hb
        (realCriterion_of_ramsey _ hs hbinj hR)
      rw [hback] at h
      exact fieldCriterion_ramsey a hs hd ha (realCriterion_fieldCriterion a h)
  · exact ⟨fun _ => ramsey_of_lt_two _ (by omega), fun _ => ramsey_of_lt_two _ (by omega)⟩

end Mobius
end EuclideanRamsey
end
end OAI

#print axioms OAI.EuclideanRamsey.Mobius.realCriterion_of_ramsey
#print axioms OAI.EuclideanRamsey.Mobius.ramsey_iff_ramsey_mobius_full
#print axioms OAI.EuclideanRamsey.Mobius.realCriterion_mobius_full
#print axioms OAI.EuclideanRamsey.Mobius.realCriterion_of_isometry
