module

public import MobiusRamsey.Defs

@[expose] public section

/-!
# The circle chart and two explicit Möbius maps of the unit circle

Real-matrix geometry only (imports `MobiusRamsey.Defs`, hence OpenAI's `Model` only).
`circ t = ((1 - t²)/(1 + t²), 2t/(1 + t²))` is the stereographic chart, from the
pole `(-1, 0)`. In null coordinates `(1, circ t) ∝ (1 + t², 1 - t², 2t) = C (1, t, t²)`, so the
affine maps `t ↦ k t` and `t ↦ t + c` of the parameter act by explicit `L ∈ O(1,2)`.
-/

namespace OAI
noncomputable section
namespace EuclideanRamsey
namespace Mobius

open Matrix

/-- A point map is determined by `L (1, x) = c (1, y)` with `c ≠ 0`. -/
theorem mobiusMap_eq_of_mulVec {d : ℕ} {L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ}
    {x y : Space d} {c : ℝ} (hc : c ≠ 0) (h : L *ᵥ aug x = c • aug y) :
    mobiusMap L x = y := by
  apply PiLp.ext
  intro j
  simp only [mobiusMap, PiLp.toLp_apply, h, Pi.smul_apply, smul_eq_mul, aug, mul_one]
  field_simp

theorem circ_zero (t : ℝ) : circ t 0 = (1 - t ^ 2) / (1 + t ^ 2) := rfl
theorem circ_one (t : ℝ) : circ t 1 = 2 * t / (1 + t ^ 2) := rfl

theorem norm_circ (t : ℝ) : ‖circ t‖ = 1 := by
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  have h2 : ‖circ t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, circ_zero, circ_one]
    field_simp
    ring
  have hn := norm_nonneg (circ t)
  nlinarith

theorem circ_injective : Function.Injective circ := by
  intro t t' h
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  have hp' : 1 + t' ^ 2 ≠ 0 := by positivity
  have h1 := congrArg (fun x : Space 2 => x 0) h
  have h2 := congrArg (fun x : Space 2 => x 1) h
  simp only [circ_zero, circ_one] at h1 h2
  rw [div_eq_div_iff hp hp'] at h1 h2
  have hsq : t ^ 2 = t' ^ 2 := by linear_combination (-1 / 2 : ℝ) * h1
  have hm : (t - t') * (1 + t ^ 2) = 0 := by linear_combination (1 / 2 : ℝ) * h2 + t * hsq
  rcases mul_eq_zero.mp hm with h0 | h0
  · linarith
  · exact absurd h0 hp

theorem circ_isAlgebraic {t : ℝ} (ht : IsAlgebraic ℚ t) (j : Fin 2) :
    IsAlgebraic ℚ (circ t j) := by
  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have hden : IsAlgebraic ℚ (1 + t ^ 2)⁻¹ := (h1.add (ht.pow 2)).inv
  fin_cases j
  · show IsAlgebraic ℚ ((1 - t ^ 2) / (1 + t ^ 2))
    rw [div_eq_mul_inv]
    exact (h1.sub (ht.pow 2)).mul hden
  · show IsAlgebraic ℚ (2 * t / (1 + t ^ 2))
    rw [div_eq_mul_inv, two_mul]
    exact (ht.add ht).mul hden

/-- `t ↦ k t` (`k ≠ 0`) is a Möbius map of the unit circle: an explicit boost in `O(1,2)`. -/
theorem exists_mobius_circ_mul (k : ℝ) (hk : k ≠ 0) :
    ∃ L : Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ,
      Lᵀ * lorentzForm 2 * L = lorentzForm 2 ∧ ∀ t, mobiusMap L (circ t) = circ (k * t) := by
  have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk
  refine ⟨Matrix.of fun α β =>
    match α, β with
    | none, none => (1 + k ^ 2) / (2 * k)
    | none, some j => ![(1 - k ^ 2) / (2 * k), 0] j
    | some j, none => ![(1 - k ^ 2) / (2 * k), 0] j
    | some j, some l => !![(1 + k ^ 2) / (2 * k), 0; 0, 1] j l, ?_, fun t => ?_⟩
  · ext α β
    rcases α with _ | j <;> rcases β with _ | l <;> (try fin_cases j) <;> (try fin_cases l) <;>
      simp [mul_apply, Fintype.sum_option, Fin.sum_univ_two, lorentzForm, diagonal_apply] <;>
      (try field_simp) <;> ring
  · have hp : 1 + t ^ 2 ≠ 0 := by positivity
    have hq : 1 + (k * t) ^ 2 ≠ 0 := by positivity
    have hc : (1 + (k * t) ^ 2) / (k * (1 + t ^ 2)) ≠ 0 :=
      div_ne_zero hq (mul_ne_zero hk hp)
    apply mobiusMap_eq_of_mulVec hc
    funext α
    rcases α with _ | j <;> (try fin_cases j) <;>
      simp [mulVec, dotProduct, Fintype.sum_option, Fin.sum_univ_two, aug, circ_zero,
        circ_one] <;>
      field_simp <;> ring

/-- `t ↦ t + c` is a Möbius map of the unit circle: an explicit parabolic element of
`O(1,2)`. -/
theorem exists_mobius_circ_add (c : ℝ) :
    ∃ L : Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ,
      Lᵀ * lorentzForm 2 * L = lorentzForm 2 ∧ ∀ t, mobiusMap L (circ t) = circ (t + c) := by
  refine ⟨Matrix.of fun α β =>
    match α, β with
    | none, none => 1 + c ^ 2 / 2
    | none, some j => ![c ^ 2 / 2, c] j
    | some j, none => ![-(c ^ 2 / 2), c] j
    | some j, some l => !![1 - c ^ 2 / 2, -c; c, 1] j l, ?_, fun t => ?_⟩
  · ext α β
    rcases α with _ | j <;> rcases β with _ | l <;> (try fin_cases j) <;> (try fin_cases l) <;>
      simp [mul_apply, Fintype.sum_option, Fin.sum_univ_two, lorentzForm, diagonal_apply] <;>
      ring
  · have hp : 1 + t ^ 2 ≠ 0 := by positivity
    have hq : 1 + (t + c) ^ 2 ≠ 0 := by positivity
    have hc : (1 + (t + c) ^ 2) / (1 + t ^ 2) ≠ 0 := div_ne_zero hq hp
    apply mobiusMap_eq_of_mulVec hc
    funext α
    rcases α with _ | j <;> (try fin_cases j) <;>
      simp [mulVec, dotProduct, Fintype.sum_option, Fin.sum_univ_two, aug, circ_zero,
        circ_one] <;>
      field_simp <;> ring

end Mobius
end EuclideanRamsey
end
end OAI
