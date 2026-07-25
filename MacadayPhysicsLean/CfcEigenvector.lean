/-
The keystone lemma for Paper R's remaining hard pieces:

  `A *ᵥ v = t • v  ⟹  (f A) *ᵥ v = f t • v`   for Hermitian `A`

i.e. the continuous functional calculus acts on eigenvectors by acting on the
eigenvalue. True because `f(A) = Σ_μ f(μ) Π_μ` and any `t`-eigenvector lies in
`ran Π_t` — degenerate eigenvalues are fine.

This single lemma discharges *both* remaining hard pieces of Paper R:

* the **operator reconstruction** in the equality case of Klein's inequality
  (`σ eᵢ = pᵢ eᵢ ⇒ σ = ρ`), and
* the **direct-sum chain rule**, since block-adapted eigenvectors of the blocks
  are eigenvectors of the block-diagonal matrix, so `f` acts blockwise and
  `log(⊕ q_λ ω_λ)` decomposes into `(log q_λ)·I + log ω_λ` for free.

Working at the eigenvector level avoids building any bespoke
`cfc`-block-decomposition machinery.
-/

import MacadayPhysicsLean.RelativeEntropy
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Unitary

variable {n : ℕ}

/-- **Keystone: the functional calculus acts on eigenvectors by acting on the
eigenvalue.** If `A` is Hermitian and `v` is a `t`-eigenvector of `A`, then `v`
is an `f t`-eigenvector of `f A`. -/
theorem cfc_apply_eigenvector {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) {v : Fin n → ℂ} {t : ℝ} (hv : A *ᵥ v = (t : ℂ) • v) :
    (hA.cfc f) *ᵥ v = ((f t : ℝ) : ℂ) • v := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set Us : Matrix (Fin n) (Fin n) ℂ :=
    ((star hA.eigenvectorUnitary : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hUs
  have hUsU : Us * U = 1 := Unitary.coe_star_mul_self _
  have hUUs : U * Us = 1 := Unitary.coe_mul_star_self _
  -- `Us A U = D`, the diagonalisation, with no rewriting of `A` itself
  have hDeq : Us * A * U = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [conjStarAlgAut_apply] at h
    simpa [hUs, hU, star_star] using h
  set w : Fin n → ℂ := Us *ᵥ v with hw
  -- the coordinate vector `w` is a `t`-eigenvector of the diagonal matrix
  have hDw : (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) *ᵥ w = (t : ℂ) • w := by
    rw [← hDeq, hw, Matrix.mulVec_mulVec]
    have hcollapse : (Us * A * U) * Us = Us * A := by
      rw [Matrix.mul_assoc (Us * A), hUUs, Matrix.mul_one]
    rw [hcollapse, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  -- entrywise: `(λᵢ − t) wᵢ = 0`
  have hentry : ∀ i, ((hA.eigenvalues i : ℝ) : ℂ) * w i = (t : ℂ) * w i := by
    intro i
    have hi := congrFun hDw i
    rw [Matrix.mulVec_diagonal] at hi
    simpa [Function.comp_apply] using hi
  -- hence `f` applied to the diagonal acts as the scalar `f t` on `w`
  have hDfw : (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)) *ᵥ w
      = ((f t : ℝ) : ℂ) • w := by
    funext i
    rw [Matrix.mulVec_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rcases eq_or_ne (w i) 0 with hwi | hwi
    · rw [hwi, mul_zero, mul_zero]
    · have hcast : ((hA.eigenvalues i : ℝ) : ℂ) = ((t : ℝ) : ℂ) :=
        mul_right_cancel₀ hwi (hentry i)
      have hEq : hA.eigenvalues i = t := by exact_mod_cast hcast
      rw [hEq]; rfl
  -- assemble
  have hcfceq : hA.cfc f = U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * Us := by
    rw [hU, hUs, Matrix.IsHermitian.cfc, conjStarAlgAut_apply]
    rfl
  rw [hcfceq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw, hDfw,
    Matrix.mulVec_smul, hw, Matrix.mulVec_mulVec, hUUs, Matrix.one_mulVec]

/-- The generic-`cfc` form of the keystone (bridged by `Matrix.IsHermitian.cfc_eq`). -/
theorem cfc_apply_eigenvector' {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) {v : Fin n → ℂ} {t : ℝ} (hv : A *ᵥ v = (t : ℂ) • v) :
    (cfc f A) *ᵥ v = ((f t : ℝ) : ℂ) • v := by
  rw [hA.cfc_eq]; exact cfc_apply_eigenvector hA f hv

/-- Specialisation to the operator logarithm of a density operator: an
eigenvector of `ρ` with eigenvalue `t` is an eigenvector of `log ρ` with
eigenvalue `log t`. -/
theorem DensityOp.logM_apply_eigenvector (ρ : DensityOp n) {v : Fin n → ℂ} {t : ℝ}
    (hv : ρ.M *ᵥ v = (t : ℂ) • v) :
    ρ.logM *ᵥ v = ((Real.log t : ℝ) : ℂ) • v :=
  cfc_apply_eigenvector ρ.isHermitian Real.log hv

end MacadayPhysicsLean
