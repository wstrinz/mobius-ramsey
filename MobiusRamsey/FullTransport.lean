module

public import MobiusRamsey.Transport

@[expose] public section

/-!
# The real criterion, transported without a spanning hypothesis

Two transports of OpenAI's `RealCriterion` (openai/math @ fd4aeeb2, `TensorNecessity.lean`), neither of which needs the configuration to affinely span its ambient space.

* `realCriterion_mobius_full`: along a Lorentz matrix `L`, for any configuration on the unit
  sphere. The symmetrized multiplied matrix is `S + E` with
  `E = e₀ wᵀ + w e₀ᵀ` for an affine function `w` vanishing on the points; the rank-one arrays
  `e₀ ⊗ w + w ⊗ e₀` (zero evaluations, multiplied matrix `E`) are subtracted before transporting.
* `realCriterion_of_isometry`: along an affine isometric embedding `a i = t + Q (b i)`,
  `Q : Space k →ₗᵢ Space d`. With `R` the matrix of `Q` (`RᵀR = 1`) and `Pr = 1 - R Rᵀ`, the
  array is `Aᵀ P_b A + ∑ₘ (m-th coordinate of Pr (x - t))^{⊗2}`, where `A (1, x) = (1, Rᵀ(x - t))`;
  its spatial block is `R Rᵀ + Pr = 1`.
-/

namespace OAI
noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey
namespace Mobius

open Matrix

variable {d : ℕ}

local notation "S" => lorentzForm d

/-- The transport identity for a rectangular real matrix. -/
theorem sandwich_rect {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R] (f g : ℝ →+* R)
    (A : Matrix κ ι ℝ) (P : Matrix κ κ R) (u : ι → ℝ) :
    (f ∘ u) ⬝ᵥ ((A.map f)ᵀ * P * A.map g) *ᵥ (g ∘ u) =
      (f ∘ (A *ᵥ u)) ⬝ᵥ P *ᵥ (g ∘ (A *ᵥ u)) := by
  have hf : f ∘ (A *ᵥ u) = A.map f *ᵥ (f ∘ u) := funext fun i => RingHom.map_mulVec f A u i
  have hg : g ∘ (A *ᵥ u) = A.map g *ᵥ (g ∘ u) := funext fun i => RingHom.map_mulVec g A u i
  rw [hf, hg, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (f ∘ u) (A.map f)ᵀ,
    vecMul_transpose]

/-- Evaluation of the rank-one array with entries `f (x α) * g (y β)`. -/
theorem eval_rankOne {ι R : Type*} [Fintype ι] [CommRing R] (f g : ℝ →+* R)
    (x y u : ι → ℝ) :
    (f ∘ u) ⬝ᵥ (Matrix.of fun α β => f (x α) * g (y β)) *ᵥ (g ∘ u) =
      f (u ⬝ᵥ x) * g (y ⬝ᵥ u) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Function.comp_apply, map_sum, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun β _ => by ring

/-- Normalization without spanning: an array with zero evaluations on unit-sphere
points, whose multiplied matrix is symmetric with spatial block `I`, can be corrected (by
rank-one arrays with zero evaluations) to one whose multiplied matrix is exactly `S`. -/
theorem exists_lorentz_normal {s : ℕ} {a : Fin s → Space d} (hsph : ∀ i, ‖a i‖ = 1)
    (Q : RealArray d) (hev : ∀ i, (ι₁ ∘ aug (a i)) ⬝ᵥ Q *ᵥ (ι₂ ∘ aug (a i)) = 0)
    (hsym : ∀ α β, μ (Q β α) = μ (Q α β))
    (hsp : ∀ j k, μ (Q (some j) (some k)) = (1 : Matrix (Fin d) (Fin d) ℝ) j k) :
    ∃ Q' : RealArray d, (∀ i, (ι₁ ∘ aug (a i)) ⬝ᵥ Q' *ᵥ (ι₂ ∘ aug (a i)) = 0) ∧
      Q'.map μ = S := by
  set E := Q.map μ - S with hE
  have hEab : ∀ α β, E α β = μ (Q α β) - S α β := fun α β => rfl
  have hEs : ∀ α β, E β α = E α β := by
    intro α β
    have h2 := congrFun (congrFun (lorentzForm_transpose (d := d)) α) β
    simp only [transpose_apply] at h2
    rw [hEab, hEab, hsym, h2]
  have hEsp : ∀ j k, E (some j) (some k) = 0 := by
    intro j k
    rw [hEab, hsp, lorentzForm, diagonal_apply, one_apply]
    split_ifs <;> simp_all
  have hEq : ∀ i, aug (a i) ⬝ᵥ E *ᵥ aug (a i) = 0 := by
    intro i
    rw [hE, sub_mulVec, dotProduct_sub, ← μ_eval, hev i, map_zero, quad_aug, hsph i]
    ring
  have hEs' : ∀ j, E (some j) none = E none (some j) := fun j => hEs none (some j)
  have hexp : ∀ x : Space d,
      aug x ⬝ᵥ E *ᵥ aug x = E none none + ∑ j, 2 * E none (some j) * x j := by
    intro x
    simp only [dotProduct, mulVec, Fintype.sum_option, aug, hEsp, hEs', zero_mul,
      Finset.sum_const_zero, add_zero, mul_one, one_mul]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  let w : Option (Fin d) → ℝ := fun
    | none => E none none / 2
    | some j => E none (some j)
  have hw : ∀ i, aug (a i) ⬝ᵥ w = 0 := by
    intro i
    have h := hEq i
    rw [hexp] at h
    have h2 : ∑ j, 2 * E none (some j) * a i j = 2 * ∑ j, a i j * E none (some j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [dotProduct, Fintype.sum_option, aug, w, one_mul]
    linarith
  refine ⟨Q - ((Matrix.of fun α β => ι₁ (aug 0 α) * ι₂ (w β)) +
    Matrix.of fun α β => ι₁ (w α) * ι₂ (aug 0 β)), fun i => ?_, ?_⟩
  · rw [sub_mulVec, dotProduct_sub, hev i, add_mulVec, dotProduct_add, eval_rankOne,
      eval_rankOne, dotProduct_comm w, hw i]
    simp
  · ext α β
    have hQ : μ (Q α β) = E α β + S α β := by rw [hEab]; ring
    simp only [map_apply, Matrix.sub_apply, Matrix.add_apply, of_apply, map_sub, map_add, map_mul, μ_ι₁,
      μ_ι₂, hQ]
    rcases α with _ | j <;> rcases β with _ | k
    · simp only [aug, w]; ring
    · simp only [aug, w, PiLp.zero_apply]; ring
    · simp only [aug, w, PiLp.zero_apply, hEs']; ring
    · simp only [aug, w, PiLp.zero_apply, hEsp]; ring

/-- **Transport of the real criterion along a Lorentz matrix, for any unit-sphere
configuration** (no spanning or nondegeneracy hypothesis). -/
theorem realCriterion_mobius_full {L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ}
    (hL : Lᵀ * S * L = S) {s : ℕ} {a : Fin s → Space d} (hsph : ∀ i, ‖a i‖ = 1)
    (h : RealCriterion a) : RealCriterion (mobiusMap L ∘ a) := by
  obtain ⟨P, hev, hm⟩ := h
  set Q := symmetrize P with hQ
  have hQev : ∀ i, (ι₁ ∘ aug (a i)) ⬝ᵥ Q *ᵥ (ι₂ ∘ aug (a i)) = 0 := by
    intro i
    have h0 := hev i
    rw [eval_eq] at h0
    rw [hQ, eval_symmetrize, h0, map_zero, add_zero, mul_zero]
  have hspP : ∀ j k, μ (P (some j) (some k)) = (1 : Matrix (Fin d) (Fin d) ℝ) j k :=
    fun j k => by rw [← spatial_apply, hm]
  obtain ⟨Q', hQ'ev, hMS⟩ := exists_lorentz_normal hsph Q hQev
    (fun α β => by simp only [hQ, μ_symmetrize]; ring)
    (fun j k => by
      simp only [hQ, μ_symmetrize, hspP, one_apply]
      by_cases hjk : j = k
      · subst hjk; norm_num
      · simp [hjk, Ne.symm hjk])
  set N := S * Lᵀ * S with hNdef
  refine ⟨(N.map ι₁)ᵀ * Q' * N.map ι₂, ?_, ?_⟩
  · intro i
    rw [eval_eq, sandwich]
    have hNL : N * L = 1 := inv_mul hL
    have h0 := time_ne_zero hL (hsph i)
    have e := mulVec_aug hL (hsph i)
    have hN : N *ᵥ aug ((mobiusMap L ∘ a) i) = ((L *ᵥ aug (a i)) none)⁻¹ • aug (a i) := by
      calc N *ᵥ aug (mobiusMap L (a i))
          = ((L *ᵥ aug (a i)) none)⁻¹ •
              (N *ᵥ (((L *ᵥ aug (a i)) none) • aug (mobiusMap L (a i)))) := by
            rw [mulVec_smul, smul_smul, inv_mul_cancel₀ h0, one_smul]
        _ = _ := by rw [← e, mulVec_mulVec, hNL, one_mulVec]
    rw [hN, eval_smul, hQ'ev i, mul_zero]
  · have hid1 : (⇑μ ∘ ⇑ι₁) = id := funext μ_ι₁
    have hid2 : (⇑μ ∘ ⇑ι₂) = id := funext μ_ι₂
    have hmap : ((N.map ι₁)ᵀ * Q' * N.map ι₂).map μ = Nᵀ * S * N := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_map, Matrix.map_map, Matrix.map_map, hid1,
        hid2, Matrix.map_id, hMS]
    ext j k
    have hjk := congrFun (congrFun hmap (some j)) (some k)
    have hinv : Nᵀ * S * N = S := inv_lorentz hL
    rw [map_apply, hinv] at hjk
    rw [spatial_apply, hjk]
    simp [lorentzForm, diagonal_apply, one_apply]

/-- **Transport of the real criterion along an affine isometric embedding**
`a i = t + Q (b i)`, `Q : Space k →ₗᵢ Space d` (no spanning hypothesis on `a`). -/
theorem realCriterion_of_isometry {s k : ℕ} {b : Fin s → Space k} {a : Fin s → Space d}
    (Q : Space k →ₗᵢ[ℝ] Space d) (t : Space d) (hab : ∀ i, a i = t + Q (b i))
    (h : RealCriterion b) : RealCriterion a := by
  classical
  obtain ⟨P, hev, hm⟩ := h
  let R : Matrix (Fin d) (Fin k) ℝ := Matrix.of fun j α => isometryRows Q j α
  have hRR : Rᵀ * R = 1 := by
    ext α β
    simp only [mul_apply, transpose_apply, R, of_apply, one_apply]
    exact isometryRows_gram Q α β
  have haj : ∀ i j, a i j - t j = ∑ β, R j β * b i β := by
    intro i j
    have e0 : ∀ x y : ℝ, x + y - x = y := fun x y => by ring
    rw [hab i, PiLp.add_apply, isometryRows_apply, e0]
    simp only [R, of_apply]
    exact Finset.sum_congr rfl fun β _ => mul_comm _ _
  -- the projection onto the orthogonal complement of the range of `Q`
  let Pr : Matrix (Fin d) (Fin d) ℝ := 1 - R * Rᵀ
  have hPrR : Pr * R = 0 := by
    simp only [Pr, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hRR, Matrix.mul_one,
      sub_self]
  have hPrPr : Prᵀ * Pr = Pr := by
    have hT : Prᵀ = Pr := by
      simp only [Pr, transpose_sub, transpose_one, transpose_mul, transpose_transpose]
    rw [hT]
    have e : R * Rᵀ * (R * Rᵀ) = R * Rᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hRR, Matrix.one_mul]
    simp only [Pr, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e]
    abel
  -- the affine left inverse `A (1, x) = (1, Rᵀ (x - t))`
  let A : Matrix (Option (Fin k)) (Option (Fin d)) ℝ := Matrix.of fun α β =>
    match α, β with
    | none, none => 1
    | none, some _ => 0
    | some α, none => -∑ j, R j α * t j
    | some α, some j => R j α
  have hA : ∀ i, A *ᵥ aug (a i) = aug (b i) := by
    intro i
    funext α
    rcases α with _ | α
    · simp [A, of_apply, mulVec, dotProduct, Fintype.sum_option, aug]
    · simp only [A, of_apply, mulVec, dotProduct, Fintype.sum_option, aug, mul_one]
      have e1 : -∑ j, R j α * t j + ∑ j, R j α * a i j = ∑ j, R j α * (a i j - t j) := by
        rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1]
      simp only [haj, Finset.mul_sum]
      rw [Finset.sum_comm]
      have e2 : ∀ β, ∑ j, R j α * (R j β * b i β) = (Rᵀ * R) α β * b i β := by
        intro β
        rw [mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [transpose_apply]; ring
      simp only [e2, hRR, one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
  -- the rank-one correction: squares of the coordinates of `Pr (x - t)`
  let v : Fin d → ℝ := fun m => -∑ j, Pr m j * t j
  let u : Fin d → Space d := fun m => WithLp.toLp 2 fun j => Pr m j
  let C : RealArray d := ∑ m, diagonalArray (v m) (u m)
  have hCev : ∀ i, arrayEvaluation a i C = 0 := by
    intro i
    have h0 : ∀ m, affineEvaluation a i (v m) (u m) = 0 := by
      intro m
      have e1 : affineEvaluation a i (v m) (u m) = ∑ j, Pr m j * (a i j - t j) := by
        simp only [affineEvaluation, v, u]
        rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1]
      simp only [haj, Finset.mul_sum]
      rw [Finset.sum_comm]
      have e2 : ∀ β, ∑ j, Pr m j * (R j β * b i β) = (Pr * R) m β * b i β := by
        intro β
        rw [mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [e2, hPrR, Matrix.zero_apply, zero_mul, Finset.sum_const_zero]
    simp only [C, map_sum, arrayEvaluation_diagonal, h0, TensorProduct.tmul_zero,
      Finset.sum_const_zero]
  have hCsp : spatialMultiply C = Pr := by
    simp only [C, map_sum, spatialMultiply_diagonal]
    rw [← hPrPr]
    ext j l
    simp only [Matrix.sum_apply, gradientRankOne, u, mul_apply, transpose_apply]
  -- the transferred array `Aᵀ P_b A`
  have hP₁ev : ∀ i, arrayEvaluation a i ((A.map ι₁)ᵀ * P * A.map ι₂) = 0 := by
    intro i
    rw [eval_eq, sandwich_rect, hA i, ← eval_eq b i P, hev i]
  have hP₁sp : spatialMultiply ((A.map ι₁)ᵀ * P * A.map ι₂) = R * Rᵀ := by
    have hid1 : (⇑μ ∘ ⇑ι₁) = id := funext μ_ι₁
    have hid2 : (⇑μ ∘ ⇑ι₂) = id := funext μ_ι₂
    have hmap : ((A.map ι₁)ᵀ * P * A.map ι₂).map μ = Aᵀ * P.map μ * A := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_map, Matrix.map_map, Matrix.map_map, hid1,
        hid2, Matrix.map_id]
    have hPsp : ∀ α β, μ (P (some α) (some β)) = (1 : Matrix (Fin k) (Fin k) ℝ) α β :=
      fun α β => by rw [← spatial_apply, hm]
    ext j l
    rw [spatial_apply]
    have hjl := congrFun (congrFun hmap (some j)) (some l)
    rw [map_apply] at hjl
    rw [hjl]
    simp only [mul_apply, transpose_apply, Fintype.sum_option, A, of_apply, map_apply, hPsp,
      zero_mul, mul_zero, zero_add, one_apply, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  refine ⟨(A.map ι₁)ᵀ * P * A.map ι₂ + C, fun i => ?_, ?_⟩
  · rw [map_add, hP₁ev i, hCev i, add_zero]
  · rw [map_add, hP₁sp, hCsp]
    simp only [Pr]
    abel

end Mobius
end EuclideanRamsey
end
end OAI
