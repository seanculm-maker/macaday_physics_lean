/-
**The neutral-prior bridge** — Paper R Stage 0 (`RelativeEntropy.lean` header).

  `D(ρ‖I/d) = log d − S(ρ)`

Setting the prior to the maximally mixed state `I/d` recovers Paper W's von
Neumann entropy: relative entropy against the neutral prior is `log d` minus the
entropy.  This is the cheapest confirmation that the Umegaki definition is the
right one — the whole neutral-prior VCT is the `σ = I/d` specialisation.

The operator logarithm of the scalar state is scalar: `log(I/d) = (log 1/d)·I`,
via `cfc_algebraMap` (the functional calculus of `algebraMap ℝ _ (1/d)` is
`algebraMap ℝ _ (log 1/d)`).  Then `Tr(ρ log(I/d)) = (log 1/d) Tr ρ = log 1/d`.
-/

import MacadayPhysicsLean.RelativeEntropy
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Real
open scoped ComplexOrder

variable {n : ℕ}

namespace DensityOp

/-- The **maximally mixed state** `I/d` on a `d = n`-dimensional space. -/
noncomputable def maximallyMixed (n : ℕ) [NeZero n] : DensityOp n where
  M := (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
  posSemidef := Matrix.PosSemidef.one.smul (by positivity)
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast,
      inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne n))]

/-- `I/d` is `algebraMap ℝ _ (1/d)`, so its operator logarithm is scalar:
`log(I/d) = (log 1/d) • I`. -/
theorem logM_maximallyMixed (n : ℕ) [NeZero n] :
    (maximallyMixed n).logM
      = ((Real.log ((n : ℝ)⁻¹) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have halg : (maximallyMixed n).M = algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) ((n : ℝ)⁻¹) := by
    show (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = _
    rw [Complex.coe_smul]
    exact (Algebra.algebraMap_eq_smul_one _).symm
  rw [logM, ← (maximallyMixed n).isHermitian.cfc_eq Real.log, halg, cfc_algebraMap,
    Algebra.algebraMap_eq_smul_one]
  exact (Complex.coe_smul _ _).symm

/-- **The neutral-prior bridge.** `D(ρ‖I/d) = log d − S(ρ)`. -/
theorem relEntropy_maximallyMixed [NeZero n] (ρ : DensityOp n) :
    relativeEntropy ρ (maximallyMixed n) = Real.log n - vonNeumannEntropy ρ := by
  have hcross : (ρ.M * (((Real.log ((n : ℝ)⁻¹) : ℝ) : ℂ)
        • (1 : Matrix (Fin n) (Fin n) ℂ))).trace.re = Real.log ((n : ℝ)⁻¹) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, ρ.trace_one, smul_eq_mul,
      mul_one, Complex.ofReal_re]
  rw [relativeEntropy, trace_mul_logM_self, logM_maximallyMixed, hcross, Real.log_inv]
  ring

end DensityOp

end MacadayPhysicsLean
