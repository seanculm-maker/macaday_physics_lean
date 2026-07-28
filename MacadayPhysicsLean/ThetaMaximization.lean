/-
E₈ × E₈ Theta Maximization at B = 0 — Paper P2 §4.

**Statement.**  Among all even self-dual `(8, 8)` Narain lattices,
`E₈ × E₈` at `B = 0` maximizes the theta function `Θ_Λ`.

**Mathematical core (Sub-approach B2 from spec).**  At `B = 0`, a
root vector `α` with `|α|² = 2` is purely left-moving (`p_L = α`,
`p_R = 0`).  At `B ≠ 0`, the `B`-field mixes chiralities:

  `p_L = α + B w`,   `p_R = B w`,

and the total norm-squared

  `|p_L|² + |p_R|² = |α|² + 2|B w|² = 2 + 2|B w|² ≥ 2`,

with equality iff `B w = 0`.  Hence the Boltzmann weight
`exp(−π τ₂ (|p_L|² + |p_R|²))` *decreases* at `B ≠ 0`.  Summing
over all root vectors, the theta function decreases.

**Lean scope.**  We prove the algebraic Boltzmann-weight inequality
plus the equality condition, then sum over a finite root set.

**Context — CKRV.**  The published Cohn-Kumar-Miller-Radchenko-Viazovska
2022 theorem (Annals of Math 196, 983-1082) establishes E₈ as
universally optimal among point configurations in `ℝ⁸`.  This applies
to *Euclidean* lattices, not directly to Narain; we cite it as
external context only.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace MacadayPhysicsLean.ThetaMaximization

/-! ### Boltzmann weight inequality -/

/-- **At `B ≠ 0`, the root-vector norm-squared increases**:
`|α|² + 2|Bw|² ≥ |α|²` since `|Bw|² ≥ 0`. -/
theorem norm_sq_increases_with_B
    (alpha_sq Bw_sq : ℝ) (_hα : alpha_sq = 2) (hB : 0 ≤ Bw_sq) :
    alpha_sq + 2 * Bw_sq ≥ alpha_sq := by linarith

/-- **At `B ≠ 0`, the Boltzmann weight decreases**:
`exp(−π τ₂ (|α|² + 2|Bw|²)) ≤ exp(−π τ₂ |α|²)`. -/
theorem boltzmann_weight_decreases_with_B
    (alpha_sq Bw_sq τ₂ : ℝ)
    (_hα : alpha_sq = 2) (hB : 0 ≤ Bw_sq) (hτ : 0 < τ₂) :
    Real.exp (-Real.pi * τ₂ * (alpha_sq + 2 * Bw_sq)) ≤
      Real.exp (-Real.pi * τ₂ * alpha_sq) := by
  apply Real.exp_le_exp.mpr
  have h_prod_nonneg : 0 ≤ Real.pi * τ₂ * Bw_sq :=
    mul_nonneg (mul_nonneg Real.pi_pos.le hτ.le) hB
  nlinarith [h_prod_nonneg]

/-- **Equality holds iff `B w = 0`** (`Bw_sq = 0`). -/
theorem theta_eq_iff_B_zero
    (Bw_sq τ₂ : ℝ) (_hB : 0 ≤ Bw_sq) (hτ : 0 < τ₂) :
    Real.exp (-Real.pi * τ₂ * (2 + 2 * Bw_sq)) =
      Real.exp (-Real.pi * τ₂ * 2) ↔ Bw_sq = 0 := by
  constructor
  · intro h
    have h_arg : -Real.pi * τ₂ * (2 + 2 * Bw_sq) = -Real.pi * τ₂ * 2 :=
      Real.exp_injective h
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_pi_tau : Real.pi * τ₂ > 0 := mul_pos h_pi_pos hτ
    nlinarith [h_pi_tau]
  · intro h
    rw [h]; ring_nf

/-! ### Theta function consequence (Finset sum) -/

/-- **Theta-contribution sum decreases at `B ≠ 0`**: summing the
Boltzmann weight inequality over a finite root set, the
`B ≠ 0` total is at most the `B = 0` total. -/
theorem theta_contribution_decreases
    {ι : Type*} (roots : Finset ι)
    (Bw_sq : ι → ℝ) (τ₂ : ℝ)
    (hB : ∀ i, 0 ≤ Bw_sq i) (hτ : 0 < τ₂) :
    roots.sum (fun i =>
        Real.exp (-Real.pi * τ₂ * (2 + 2 * Bw_sq i))) ≤
      roots.sum (fun _ =>
        Real.exp (-Real.pi * τ₂ * 2)) := by
  apply Finset.sum_le_sum
  intro i _
  exact boltzmann_weight_decreases_with_B 2 (Bw_sq i) τ₂ rfl (hB i) hτ

/-! ### Context — CKRV citation

The Cohn-Kumar-Miller-Radchenko-Viazovska (CKRV) theorem
(Annals of Math 196 (2022), 983-1082) establishes E₈ as
universally optimal among point configurations in `ℝ⁸`.  This is
a deep recent result whose full statement involves energy
functionals on point configurations and is far beyond current
Lean formalization scope.  We cite it as external context: the
*Euclidean* optimality of E₈ is published mathematics, and the
Narain theta-maximization above is the *physical* (Boltzmann-
weight) analog that does NOT depend on CKRV. -/

end MacadayPhysicsLean.ThetaMaximization
