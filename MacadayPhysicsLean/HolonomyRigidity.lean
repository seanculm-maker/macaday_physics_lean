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
import Mathlib.Tactic

namespace MacadayPhysicsLean.HolonomyRigidity

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

end MacadayPhysicsLean.HolonomyRigidity
