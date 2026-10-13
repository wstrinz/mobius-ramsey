module

public import OAI.Combinatorics.EuclideanRamsey.Main

@[expose] public section

/-!
# Spherical configurations with algebraic coordinates are Euclidean Ramsey (checked)

Builds on OpenAI's own Lean proof (openai/math @ fd4aeeb2, `lean/OAI/Combinatorics/EuclideanRamsey`,
result 172), using its definitions directly; those definitions are identical to the Comparator
challenge `lean/ComparatorChallenges/EuclideanRamsey.lean`.
No `sorry`; `#print axioms ramsey_of_algebraic` = [propext, Classical.choice, Quot.sound].

Statement: a finite spherical configuration (≥ 2 distinct points, dimension ≥ 1) all of whose
coordinates are real algebraic numbers is Euclidean Ramsey. So Graham's spherical conjecture holds
over the algebraic numbers, and every non-Ramsey spherical set (Pálvölgyi's heptagon with
transcendental r, OpenAI's 9- and 12-point examples) needs a transcendental coordinate.
In Pálvölgyi's family {(0,0)} ∪ {(j, ±√(j(2r−j))) : j = 1,3,4}, r > 2: Ramsey iff r is algebraic.
-/

namespace OAI
noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

/-! ## Beyond OpenAI's development

Theorem A is prior work, not new here: JD-Jones-ASES/six-concyclic-lean (Lean, criterion
level), Rogerhu12/openai-math-extensions (TeX) and atimics/math2 (Lean, end to end for
configurations with full affine span). This file is a further Lean proof on OpenAI's
development. -/

section Algebraic

variable {s d : ℕ} (a : Fin s → Space d)

/-- Descent of the sphere equation to the coordinate field: a real solution `(ℓ, k)` of
`∑ⱼ aᵢⱼ² + ∑ⱼ ℓⱼ aᵢⱼ + k = 0` yields one with entries in `F`, via an `F`-linear
retraction `ℝ → F`. -/
lemma sphere_equation_descends
    (hsph : ∃ c : Space d, ∃ ρ : ℝ, ∀ i, dist (a i) c = ρ) :
    ∃ ℓ : Fin d → Coeff a, ∃ k : Coeff a, ∀ i : Fin s,
      ∑ j, coordinate a i j * coordinate a i j + ∑ j, ℓ j * coordinate a i j + k = 0 := by
  obtain ⟨c, ρ, hρ⟩ := hsph
  -- the real sphere equation
  have hreal : ∀ i, ∑ j, a i j * a i j + ∑ j, (-2 * c j) * a i j
      + (∑ j, c j * c j - ρ ^ 2) = 0 := by
    intro i
    have h1 := hρ i
    rw [EuclideanSpace.dist_eq] at h1
    have hnn : 0 ≤ ∑ j, dist (a i j) (c j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h2 : ∑ j, dist (a i j) (c j) ^ 2 = ρ ^ 2 := by
      rw [← h1, Real.sq_sqrt hnn]
    simp only [Real.dist_eq, sq_abs] at h2
    have : ∑ j, (a i j - c j) ^ 2
        = ∑ j, a i j * a i j + ∑ j, (-2 * c j) * a i j + ∑ j, c j * c j := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    linarith
  -- an F-linear retraction ℝ → F
  let ι : Coeff a →ₗ[Coeff a] ℝ := Algebra.linearMap (Coeff a) ℝ
  have hι : Function.Injective ι := (algebraMap (Coeff a) ℝ).injective
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ι
    (LinearMap.ker_eq_bot.mpr hι)
  have hπx : ∀ x : Coeff a, π (x : ℝ) = x := fun x => by
    have := LinearMap.congr_fun hπ x
    simpa [ι] using this
  refine ⟨fun j => π (-2 * c j), π (∑ j, c j * c j - ρ ^ 2), fun i => ?_⟩
  have key := congrArg π (hreal i)
  rw [map_zero, map_add, map_add, map_sum, map_sum] at key
  have e1 : ∀ j, π (a i j * a i j) = coordinate a i j * coordinate a i j := by
    intro j
    have : (a i j * a i j : ℝ) = ((coordinate a i j * coordinate a i j : Coeff a) : ℝ) := rfl
    rw [this, hπx]
  have e2 : ∀ j, π ((-2 * c j) * a i j) = π (-2 * c j) * coordinate a i j := by
    intro j
    have : ((-2 * c j) * a i j : ℝ) = (coordinate a i j) • (-2 * c j) := by
      rw [Algebra.smul_def]
      simp [coordinate, mul_comm]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  simp only [e1, e2] at key
  exact key

theorem fieldCriterion_of_algebraic
    (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsph : ∃ c : Space d, ∃ ρ : ℝ, ∀ i, dist (a i) c = ρ) :
    FieldCriterion a := by
  -- `F` is a number field, hence unramified over `ℚ`
  have : FiniteDimensional ℚ (Coeff a) := by
    unfold Coeff coordinateField
    have : Finite (Set.range (fun ij : Fin s × Fin d => a ij.1 ij.2)) := Set.finite_range _
    refine IntermediateField.finiteDimensional_adjoin (fun x hx => ?_)
    obtain ⟨ij, rfl⟩ := hx
    exact (halg ij.1 ij.2).isIntegral
  have : Algebra.FormallyUnramified ℚ (Coeff a) :=
    Algebra.FormallyUnramified.of_isSeparable ℚ (Coeff a)
  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := ℚ) (S := Coeff a)).mp
      inferInstance
  have hswap : ∀ x : Coeff a, t * ((1 : Coeff a) ⊗ₜ[ℚ] x) = t * (x ⊗ₜ[ℚ] (1 : Coeff a)) := by
    intro x
    have := ht x
    rw [sub_mul] at this
    rw [mul_comm t, mul_comm t]
    exact sub_eq_zero.mp this
  -- the sphere equation over `F`, as a quadratic-form matrix `h`
  obtain ⟨ℓ, k, hk⟩ := sphere_equation_descends a hsph
  let h : Matrix (Option (Fin d)) (Option (Fin d)) (Coeff a) := fun α β =>
    match α, β with
    | none, none => k
    | none, some j => ℓ j
    | some _, none => 0
    | some j, some j' => if j = j' then 1 else 0
  have hquad : ∀ i, ∑ α, ∑ β, augmented a i α * h α β * augmented a i β = 0 := by
    intro i
    simp only [Fintype.sum_option, h, augmented]
    simp only [mul_one, one_mul, zero_mul, mul_ite, ite_mul, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, add_zero, zero_add, Finset.sum_const_zero]
    linear_combination hk i
  refine ⟨fun α β => t * (h α β ⊗ₜ[ℚ] (1 : Coeff a)), fun i => ?_, fun α β => ?_⟩
  · have term : ∀ α β,
        (augmented a i α ⊗ₜ[ℚ] (1 : Coeff a)) * (t * (h α β ⊗ₜ[ℚ] (1 : Coeff a))) *
          ((1 : Coeff a) ⊗ₜ[ℚ] augmented a i β)
        = t * ((augmented a i α * h α β * augmented a i β) ⊗ₜ[ℚ] (1 : Coeff a)) := by
      intro α β
      calc (augmented a i α ⊗ₜ[ℚ] (1 : Coeff a)) * (t * (h α β ⊗ₜ[ℚ] (1 : Coeff a))) *
            ((1 : Coeff a) ⊗ₜ[ℚ] augmented a i β)
          = (t * ((1 : Coeff a) ⊗ₜ[ℚ] augmented a i β)) *
              ((augmented a i α * h α β) ⊗ₜ[ℚ] (1 : Coeff a)) := by
            rw [show (augmented a i α * h α β) ⊗ₜ[ℚ] (1 : Coeff a)
                = (augmented a i α ⊗ₜ[ℚ] (1 : Coeff a)) * (h α β ⊗ₜ[ℚ] (1 : Coeff a)) by
                  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
            ring
        _ = (t * (augmented a i β ⊗ₜ[ℚ] (1 : Coeff a))) *
              ((augmented a i α * h α β) ⊗ₜ[ℚ] (1 : Coeff a)) := by rw [hswap]
        _ = t * ((augmented a i α * h α β * augmented a i β) ⊗ₜ[ℚ] (1 : Coeff a)) := by
            rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm _ (augmented a i β),
              ← mul_assoc, mul_comm (augmented a i β)]
    simp only [term, ← Finset.mul_sum, ← TensorProduct.sum_tmul, hquad, TensorProduct.zero_tmul,
      mul_zero]
  · simp only [multiply, map_mul, ht1, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul, h]

/-- **Graham's spherical conjecture holds for algebraic configurations.** Fully checked: uses OpenAI's
proved sufficiency direction `fieldCriterion_ramsey` of the classification. -/
theorem ramsey_of_algebraic
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (halg : ∀ i j, IsAlgebraic ℚ (a i j))
    (hsph : ∃ c : Space d, ∃ ρ : ℝ, ∀ i, dist (a i) c = ρ) :
    Ramsey a :=
  fieldCriterion_ramsey a hs hd ha (fieldCriterion_of_algebraic a halg hsph)

end Algebraic

end EuclideanRamsey
end
end OAI

#print axioms OAI.EuclideanRamsey.ramsey_of_algebraic
