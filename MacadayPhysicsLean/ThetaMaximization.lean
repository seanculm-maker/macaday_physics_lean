/-
Narain Boltzmann-weight monotonicity in a norm-sum model — Paper Z.

**What this file proves.**  An elementary Boltzmann-weight monotonicity in a
CHIRALITY-MIXING NORM-SUM MODEL.  Writing the total norm-squared of a root
vector as `2 + 2σ` with `σ ≥ 0` the chirality-mixing excess, the Boltzmann
weight `exp(−π τ₂ (2 + 2σ))` is maximised at `σ = 0` and strictly decreases
for `σ > 0`; summed over a finite root set, the theta contribution is
maximised at `σ = 0`.  The norm-sum model comes from writing
`|p_L|² + |p_R|² = |α|² + 2|B w|²` with `p_L = α + B w`, `p_R = B w`.

**What this file does NOT prove.**  The norm-sum model above OMITS the linear
cross term of the actual Narain quadratic form `(w + B n)ᵀ G⁻¹ (w + B n)`; the
file does not formalize the `B`-dependence of that true quadratic form.  In
particular the genuine global statement — `Θ(y; G, B) ≤ Θ(y; G, 0)` for all
`B`, with equality iff `B` is integral — is proved in Paper Z by Poisson
summation and is NOT formalized here (this is why a naive pair ratio such as
`e^(−π y c) · cosh(π y d) > 1` does not contradict anything below).  The finite
inequality step of that Poisson argument is captured by `sum_mul_cos_le_sum`
below; the Poisson summation identity itself is out of scope.

**Context — CKRV.**  The published Cohn-Kumar-Miller-Radchenko-Viazovska
2022 theorem (Annals of Math 196, 983-1082) establishes E₈ as
universally optimal among point configurations in `ℝ⁸`.  This applies
to *Euclidean* lattices, not directly to Narain; we cite it as
external context only.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

/-! ### The finite inequality step of the paper's Poisson argument

Paper Z's genuine `B`-maximum (§9.5) is proved by Poisson summation; the single
inequality step of that argument is the elementary cosine bound below.  The
Poisson summation identity itself is not formalized (out of scope). -/

/-- **Cosine-weighted sum bound.**  For nonnegative weights `a i` and arbitrary
phases `θ i`, `∑ a i · cos (θ i) ≤ ∑ a i`, since `cos ≤ 1`.  This is the
inequality step of the Poisson-summation form of the theta bound. -/
theorem sum_mul_cos_le_sum
    {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    s.sum (fun i => a i * Real.cos (θ i)) ≤ s.sum a := by
  apply Finset.sum_le_sum
  intro i hi
  calc a i * Real.cos (θ i)
      ≤ a i * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ i)) (ha i hi)
    _ = a i := mul_one _

/-- **Equality case.**  The cosine bound is tight iff `cos (θ i) = 1` for every
`i` carrying positive weight `a i > 0`. -/
theorem sum_mul_cos_eq_sum_iff
    {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    s.sum (fun i => a i * Real.cos (θ i)) = s.sum a ↔
      ∀ i ∈ s, 0 < a i → Real.cos (θ i) = 1 := by
  have hle : ∀ i ∈ s, a i * Real.cos (θ i) ≤ a i := by
    intro i hi
    calc a i * Real.cos (θ i)
        ≤ a i * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ i)) (ha i hi)
      _ = a i := mul_one _
  rw [Finset.sum_eq_sum_iff_of_le hle]
  constructor
  · intro h i hi hpos
    have hi_eq : a i * Real.cos (θ i) = a i * 1 := by rw [mul_one]; exact h i hi
    exact mul_left_cancel₀ (ne_of_gt hpos) hi_eq
  · intro h i hi
    rcases eq_or_lt_of_le (ha i hi) with hzero | hpos
    · rw [← hzero]; ring
    · rw [h i hi hpos, mul_one]

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
