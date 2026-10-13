module

public import MobiusRamsey.Defs

@[expose] public section

/-!
# Fidelity checks for `mobiusMap` (not used by the proof of Theorem C)

* `mobiusMap_bijOn`: each `φ_L`, `L ∈ O(1,d)`, is a bijection of the unit sphere.
* `liftO_lorentz`, `mobiusMap_liftO`: every orthogonal `Q` lies in the model, as
  `L = diag(1, Q)`, and acts as `x ↦ Q x`. So the rotations and reflections of the sphere are
  among the maps of Theorem C.
-/

namespace OAI
noncomputable section
namespace EuclideanRamsey
namespace Mobius

open Matrix

variable {d : ℕ}

local notation "S" => lorentzForm d

/-- `φ_L` is a bijection of the unit sphere, with inverse `φ_{S Lᵀ S}`. -/
theorem mobiusMap_bijOn {L : Matrix (Option (Fin d)) (Option (Fin d)) ℝ}
    (hL : Lᵀ * S * L = S) :
    Set.BijOn (mobiusMap L) (Metric.sphere 0 1) (Metric.sphere 0 1) := by
  have hN := inv_lorentz hL
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_sphere_zero_iff_norm] at hx ⊢
    exact norm_mobiusMap hL hx
  · intro x hx y hy h
    rw [Metric.mem_sphere, dist_zero_right] at hx hy
    exact mobiusMap_injOn hL hx hy h
  · intro y hy
    rw [Metric.mem_sphere, dist_zero_right] at hy
    refine ⟨mobiusMap (S * Lᵀ * S) y, ?_, mobiusMap_left_inv hL hN (mul_inv hL) hy⟩
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_mobiusMap hN hy

/-- The block matrix `diag(1, Q)`. -/
def liftO (Q : Matrix (Fin d) (Fin d) ℝ) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  Matrix.of fun α β => match α, β with
    | none, none => 1
    | some i, some j => Q i j
    | _, _ => 0

theorem liftO_lorentz {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) :
    (liftO Q)ᵀ * S * liftO Q = S := by
  ext α β
  rcases α with _ | i <;> rcases β with _ | k
  · simp [liftO, mul_apply, lorentzForm, Fintype.sum_option]
  · simp [liftO, mul_apply, lorentzForm, Fintype.sum_option]
  · simp [liftO, mul_apply, lorentzForm, Fintype.sum_option]
  · have h := congrFun (congrFun hQ i) k
    simp only [mul_apply, transpose_apply] at h
    simp [liftO, mul_apply, lorentzForm, diagonal_apply, Fintype.sum_option]
    simpa [one_apply] using h

theorem mobiusMap_liftO (Q : Matrix (Fin d) (Fin d) ℝ) (x : Space d) :
    mobiusMap (liftO Q) x = WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x) := by
  refine PiLp.ext fun j => ?_
  simp [mobiusMap, liftO, mulVec, dotProduct, Fintype.sum_option, aug]

end Mobius
end EuclideanRamsey
end
end OAI
