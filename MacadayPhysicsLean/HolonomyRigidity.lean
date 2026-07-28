/-
Holonomy Rigidity (Paper M).

The boost factor of a non-trivial Lorentzian holonomy is `cosh β`
for some rapidity `β`.  Strict positivity of rapidity (`β ≠ 0`)
gives `cosh β > 1`, so the only fixed direction is the identity —
the holonomy is forced trivial.  This is the "cosh(β) > 1 ⇒
trivial holonomy" line of Paper M.

The mathematical core is the half-line:
  `cosh β = 1 ⟺ β = 0`.
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace MacadayPhysicsLean.HolonomyRigidity

open Matrix

/-- For every non-zero rapidity `β`, the boost factor `cosh β`
strictly exceeds 1. -/
theorem cosh_gt_one_of_ne_zero (β : ℝ) (hβ : β ≠ 0) :
    1 < Real.cosh β := by
  rw [Real.cosh_eq]
  -- `x + 1 < exp x` whenever `x ≠ 0`
  have h₁ : β + 1 < Real.exp β := Real.add_one_lt_exp hβ
  have h₂ : -β + 1 < Real.exp (-β) := Real.add_one_lt_exp (neg_ne_zero.mpr hβ)
  linarith

/-- The boost factor `cosh β` equals 1 exactly when `β = 0`. -/
theorem cosh_eq_one_iff_eq_zero (β : ℝ) :
    Real.cosh β = 1 ↔ β = 0 := by
  refine ⟨?_, fun h => h ▸ Real.cosh_zero⟩
  contrapose!
  intro h
  exact (cosh_gt_one_of_ne_zero β h).ne'

/-- Trivial-holonomy corollary: if `cosh β ≤ 1` (i.e., a non-strict
boost), then the rapidity is zero — the holonomy element is the
identity. -/
theorem rapidity_zero_of_cosh_le_one (β : ℝ) (h : Real.cosh β ≤ 1) :
    β = 0 := by
  rcases eq_or_ne β 0 with hβ | hβ
  · exact hβ
  · exact absurd h (not_le.mpr (cosh_gt_one_of_ne_zero β hβ))

/-! ### Full ℂ² holonomy rigidity (Paper M Proposition, spec 3c)

The letter's rigidity runs on arbitrary `(c₀, c₁) ∈ ℂ²` — no Ricci/proportionality
hypothesis.  A non-trivial SO(1,1) boost (or SO(2) rotation) acting on `ℂ²` fixes
only the zero vector, because `det(R − I) ≠ 0`.  This closes the recorded m7(iv)
gap: the scalar core above is upgraded to the full 2×2 statement. -/

/-- The SO(1,1) boost `R(β) = [[cosh β, sinh β],[sinh β, cosh β]]` on `ℂ²`. -/
noncomputable def boostMatrix (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cosh β : ℂ), (Real.sinh β : ℂ); (Real.sinh β : ℂ), (Real.cosh β : ℂ)]

/-- `det(R(β) − I) = 2 − 2 cosh β`, using `cosh² − sinh² = 1`. -/
theorem boost_sub_one_det (β : ℝ) :
    (boostMatrix β - 1).det = (2 : ℂ) - 2 * (Real.cosh β : ℂ) := by
  have hid : (Real.cosh β : ℂ) ^ 2 - (Real.sinh β : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Real.cosh_sq_sub_sinh_sq, Complex.ofReal_one]
  simp only [Matrix.det_fin_two, boostMatrix, Matrix.one_fin_two, Matrix.sub_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val']
  linear_combination hid

/-- **SO(1,1) holonomy rigidity on ℂ²**: for `β ≠ 0`, the only fixed vector of the
boost is `0`. -/
theorem boost_rigidity (β : ℝ) (hβ : β ≠ 0) (v : Fin 2 → ℂ)
    (hv : boostMatrix β *ᵥ v = v) : v = 0 := by
  have hdet : (boostMatrix β - 1).det ≠ 0 := by
    rw [boost_sub_one_det]
    have : (1 : ℝ) < Real.cosh β := cosh_gt_one_of_ne_zero β hβ
    intro h
    have hre : (2 : ℝ) - 2 * Real.cosh β = 0 := by
      have := congrArg Complex.re h
      simpa using this
    linarith
  have hker : (boostMatrix β - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hker

/-- The SO(2) rotation `R(α) = [[cos α, −sin α],[sin α, cos α]]` on `ℂ²`. -/
noncomputable def rotationMatrix (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos α : ℂ), (-Real.sin α : ℂ); (Real.sin α : ℂ), (Real.cos α : ℂ)]

/-- `det(R(α) − I) = 2 − 2 cos α`, using `cos² + sin² = 1`. -/
theorem rotation_sub_one_det (α : ℝ) :
    (rotationMatrix α - 1).det = (2 : ℂ) - 2 * (Real.cos α : ℂ) := by
  have hid : (Real.cos α : ℂ) ^ 2 + (Real.sin α : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  simp only [Matrix.det_fin_two, rotationMatrix, Matrix.one_fin_two, Matrix.sub_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val']
  linear_combination hid

/-- **SO(2) holonomy rigidity on ℂ²**: if `cos α ≠ 1` (i.e. `α` is not a multiple of
`2π`), the only fixed vector of the rotation is `0`. -/
theorem rotation_rigidity (α : ℝ) (hα : Real.cos α ≠ 1) (v : Fin 2 → ℂ)
    (hv : rotationMatrix α *ᵥ v = v) : v = 0 := by
  have hdet : (rotationMatrix α - 1).det ≠ 0 := by
    rw [rotation_sub_one_det]
    intro h
    have hre : (2 : ℝ) - 2 * Real.cos α = 0 := by
      have := congrArg Complex.re h; simpa using this
    exact hα (by linarith)
  have hker : (rotationMatrix α - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hker

end MacadayPhysicsLean.HolonomyRigidity
