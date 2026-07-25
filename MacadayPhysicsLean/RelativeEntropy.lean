/-
Quantum (Umegaki) relative entropy — Stage 0 infrastructure for Paper R
(the Relative VCT).

  `D(ρ‖σ) = Tr(ρ log ρ) − Tr(ρ log σ)`

Paper R needs an operator logarithm, which Paper W never did (von Neumann
entropy is a function of eigenvalues only, with no logarithm of an operator).
We supply `log` through Mathlib's continuous functional calculus for Hermitian
matrices (`Matrix.IsHermitian.cfc`), which realizes `f(A)` as
`U · diagonal (f ∘ eigenvalues) · U⋆`.

This is **Stage 0 (route a, CFC)** of `paperR_lean_verification_spec.md`: the
definition, the fundamental spectral-trace identity everything rests on, and
the neutral-prior bridge `D(ρ‖I/d) = log d − S(ρ)` that makes Paper W's
von Neumann entropy a corollary — the cheapest confirmation the definition is
the right one.

Nonnegativity (Klein's inequality) and the pinching Pythagorean identity are in
the companion Stage-0/Stage-1 files; they build on `traceLog` and the fundamental
lemma proved here.
-/

import MacadayPhysicsLean.DensityOp
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Real Finset Unitary
open scoped ComplexOrder

variable {n : ℕ}

namespace DensityOp

/-- The operator logarithm of a density operator, via the continuous functional
calculus: `log ρ = U · diagonal (log ∘ eigenvalues) · U⋆`.  For a faithful
(positive-definite) `ρ` this is the genuine matrix logarithm; for a general
density operator the zero eigenvalues are sent to `log 0 = 0` by Mathlib's
junk-value convention, which is exactly the `0 log 0 = 0` convention of entropy. -/
noncomputable def logM (ρ : DensityOp n) : Matrix (Fin n) (Fin n) ℂ :=
  ρ.isHermitian.cfc Real.log

/-- **Umegaki relative entropy** `D(ρ‖σ) = Tr(ρ log ρ) − Tr(ρ log σ)`.

The traces are real (each is `Tr` of a product of Hermitian-derived matrices);
we take real parts so the value lives in `ℝ`. -/
noncomputable def relativeEntropy (ρ σ : DensityOp n) : ℝ :=
  (ρ.M * ρ.logM).trace.re - (ρ.M * σ.logM).trace.re

/-! ### The fundamental spectral-trace identity

`Tr(ρ · f(ρ)) = Σᵢ λᵢ · f(λᵢ)`, because `ρ` and `f(ρ)` are simultaneously
diagonalized by the same eigenvector unitary. This is the workhorse: every
"self" trace term reduces to an eigenvalue sum through it. -/

/-- `Tr(ρ · cfc f ρ) = Σᵢ (λᵢ : ℂ) · f(λᵢ)`. -/
theorem trace_mul_cfc_self (ρ : DensityOp n) (f : ℝ → ℝ) :
    (ρ.M * ρ.isHermitian.cfc f).trace
      = ∑ i, ((ρ.eigenvalues i : ℂ) * (f (ρ.eigenvalues i) : ℂ)) := by
  -- ρ.M and cfc f ρ are `conjStarAlgAut U D₁`, `conjStarAlgAut U D₂` with the
  -- SAME eigenvector unitary U, so their product is `conjStarAlgAut U (D₁ D₂)`.
  have hprod : ρ.M * ρ.isHermitian.cfc f
      = conjStarAlgAut ℂ _ ρ.isHermitian.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues)
            * diagonal (RCLike.ofReal ∘ f ∘ ρ.isHermitian.eigenvalues)) := by
    rw [map_mul]
    congr 1
    exact ρ.isHermitian.spectral_theorem
  rw [hprod, conjStarAlgAut_apply, diagonal_mul_diagonal,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, DensityOp.eigenvalues]
  rfl

/-- `Tr(ρ · log ρ) = Σᵢ λᵢ log λᵢ = −S(ρ)` (real part). -/
theorem trace_mul_logM_self (ρ : DensityOp n) :
    (ρ.M * ρ.logM).trace.re = -vonNeumannEntropy ρ := by
  rw [logM, trace_mul_cfc_self, vonNeumannEntropy, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← Finset.sum_neg_distrib]
  congr 1; ext i
  simp only [Real.negMulLog]; ring

end DensityOp

end MacadayPhysicsLean
