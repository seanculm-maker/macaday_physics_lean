/-
Toward the direct-sum chain rule (Paper R §3.1 / paper §6.4 item iii).

The mechanism, per the keystone plan: `JointDiagonalization.adaptedBasis P ρ`
is a **block-adapted orthonormal basis of eigenvectors of the pinched state**
`Δρ` — `adaptedBasis_adapted_mulVec` says each basis vector lies in a single
projector's range, and `adaptedBasis_eigenvector_pinch_mulVec` says it is a
`Δρ`-eigenvector with eigenvalue `mu P ρ s`.

Composing that with the keystone `cfc_apply_eigenvector` gives immediately that
the operator logarithm acts *diagonally* on this basis, with eigenvalue
`log (mu P ρ s)`.  This is the brick the chain rule is built from: since the
basis is block-adapted, `log` of a block-diagonal state splits into a
`log`-of-the-block-weight piece and a within-block piece, with no bespoke
`cfc`-block machinery.
-/

import MacadayPhysicsLean.CfcEigenvector
import MacadayPhysicsLean.JointDiagonalization
import MacadayPhysicsLean.RelEntropyKleinEq
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Pinching JointDiagonalization

variable {n m : ℕ}

/-- **The operator logarithm acts diagonally on the block-adapted basis.**

`log(Δρ) · e_s = log(μ_s) · e_s` for every vector `e_s` of the block-adapted
eigenbasis of the pinched state.  Immediate from the keystone
`cfc_apply_eigenvector` applied to `adaptedBasis_eigenvector_pinch_mulVec`. -/
theorem logM_pinch_apply_adaptedBasis (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    (pinchDensityOp P ρ).logM *ᵥ (⇑(adaptedBasis P ρ s) : Fin n → ℂ)
      = ((Real.log (mu P ρ s) : ℝ) : ℂ) • (⇑(adaptedBasis P ρ s) : Fin n → ℂ) :=
  DensityOp.logM_apply_eigenvector _ (adaptedBasis_eigenvector_pinch_mulVec P ρ s)

/-- The same basis vector is fixed by its own block projector, so the basis is
genuinely block-adapted: the pair
(`logM_pinch_apply_adaptedBasis`, `adaptedBasis_adapted_mulVec`) is exactly the
data the chain rule consumes. -/
theorem adaptedBasis_block_and_log (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    P.proj (k_of P s) *ᵥ (⇑(adaptedBasis P ρ s) : Fin n → ℂ)
        = (⇑(adaptedBasis P ρ s) : Fin n → ℂ)
      ∧ (pinchDensityOp P ρ).logM *ᵥ (⇑(adaptedBasis P ρ s) : Fin n → ℂ)
        = ((Real.log (mu P ρ s) : ℝ) : ℂ) • (⇑(adaptedBasis P ρ s) : Fin n → ℂ) :=
  ⟨adaptedBasis_adapted_mulVec P ρ s, logM_pinch_apply_adaptedBasis P ρ s⟩

/-! ### Block-diagonal states are pinch-fixed

Needed so that `adaptedBasis P ω` is a block-adapted eigenbasis of `ω` *itself*
(not merely of its pinching) whenever `ω` is block diagonal — which is the case
for the reference state of the chain rule and for the equilibrium `ρ*`. -/

/-- A state commuting with every projector is fixed by the pinching map. -/
theorem pinchDensityOp_eq_self_of_commute (P : ProjectorFamily n m)
    (ω : MacadayPhysicsLean.DensityOp n) (hcomm : ∀ k, Commute ω.M (P.proj k)) :
    pinchDensityOp P ω = ω := by
  refine DensityOp.ext ?_
  change P.pinch ω.M = ω.M
  unfold ProjectorFamily.pinch
  have hterm : ∀ k, P.proj k * ω.M * P.proj k = P.proj k * ω.M := by
    intro k
    rw [Matrix.mul_assoc, (hcomm k).eq, ← Matrix.mul_assoc, P.idem]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, P.sum_eq_one,
    Matrix.one_mul]

/-- For a block-diagonal `ω`, the operator logarithm acts diagonally on the
block-adapted basis of `ω` itself, with eigenvalue `log (μ_s)`.

This is the reference-side input to the chain rule: combined with
`adaptedBasis_adapted_mulVec`, it says `log ω` is simultaneously
block-respecting and diagonal in a basis adapted to the blocks. -/
theorem logM_apply_adaptedBasis_of_commute (P : ProjectorFamily n m)
    (ω : MacadayPhysicsLean.DensityOp n) (hcomm : ∀ k, Commute ω.M (P.proj k)) (s : Fin n) :
    ω.logM *ᵥ (⇑(adaptedBasis P ω s) : Fin n → ℂ)
      = ((Real.log (mu P ω s) : ℝ) : ℂ) • (⇑(adaptedBasis P ω s) : Fin n → ℂ) := by
  have h := logM_pinch_apply_adaptedBasis P ω s
  rwa [pinchDensityOp_eq_self_of_commute P ω hcomm] at h

end MacadayPhysicsLean
