/-
Narain Theorem, Step A: `T`-invariance of the lattice theta function
forces an even lattice (T-duality invariance forces evenness).

**Mathematical statement.**  If the lattice partition function
`Θ_Λ(τ) = Σ_{p ∈ Λ} q^{|p|²/2}` (with `q = e^{2πiτ}`) is invariant
under `T : τ → τ + 1`, then `|p|² ∈ 2ℤ` for every lattice vector
`p ∈ Λ`.

**Proof.**  Under `T : τ → τ + 1`, the theta function gets multiplied
by `e^{iπ|p|²}` for each lattice term.  Invariance therefore demands
`e^{iπ|p|²} = 1` for every `p ∈ Λ`, which holds iff `|p|² ∈ 2ℤ`.

**Lean formalization.**  The core mathematical content is the
*purely-numerical* equivalence

  `Complex.exp (π · i · k) = 1 ↔ Even k`

for `k : ℤ`.  We prove this clean kernel via `Complex.exp_eq_one_iff`
(Mathlib's "`exp z = 1 ↔ z = 2πin` for some integer `n`").

The physics consequence: every Narain lattice that gives a modular-
invariant partition function is *even*.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace MacadayPhysicsLean.NarainEven

open Complex

/-! ### The numerical kernel: `exp(iπk) = 1 ↔ Even k` -/

/-- **The kernel of Narain Step A.**

`Complex.exp (π · I · k) = 1 ↔ Even k` for `k : ℤ`.  Proof: by
`Complex.exp_eq_one_iff`, `exp z = 1 ↔ z = n · (2πi)` for some
`n : ℤ`.  Specialized to `z = πi · k`, we get `πi · k = n · 2πi`,
i.e. `k = 2n`, i.e. `k` is even. -/
theorem exp_pi_mul_I_int_eq_one_iff (k : ℤ) :
    Complex.exp ((Real.pi : ℂ) * I * k) = 1 ↔ Even k := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    -- hn : (π : ℂ) * I * k = n * (2 * π * I)
    have hπI : (Real.pi : ℂ) * I ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
    have hk2n : (k : ℂ) = 2 * n := by
      have h2 : (Real.pi : ℂ) * I * k = (Real.pi : ℂ) * I * (2 * n) := by
        rw [hn]; ring
      exact mul_left_cancel₀ hπI h2
    have hkℤ : k = 2 * n := by exact_mod_cast hk2n
    exact ⟨n, by omega⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hj]; push_cast; ring

/-! ### Narain Step A (abstract) -/

/-- **Narain Step A — abstract.**

Given a lattice with integer-valued norm-squared function `nsq : Λ → ℤ`,
if `e^{iπ · nsq(p)} = 1` for every `p ∈ Λ` (the `T`-invariance
condition extracted from theta-function invariance), then `Λ` is
*even*: `nsq(p) ∈ 2ℤ` for all `p`.

This is the algebraic Step A of the Narain modular-invariance
theorem, abstracted away from the differential-geometric setup of
theta functions. -/
theorem nsq_even_of_T_invariance
    {Λ : Type*} (nsq : Λ → ℤ)
    (h_T_inv : ∀ p, Complex.exp ((Real.pi : ℂ) * I * (nsq p)) = 1)
    (p : Λ) : Even (nsq p) :=
  (exp_pi_mul_I_int_eq_one_iff (nsq p)).mp (h_T_inv p)

/-! ### Oscillator counting (Paper O §3.1-3.2)

4 βγ pairs at `c = 2` each combine to total central charge `c = 8`.
The partition-function denominator is `|η(τ)|^{−16} = |η(τ)|^{−2c}`,
matching the Narain denominator for `c/2 = 8/2 = 4` complex
(= 8 real) compact bosons. -/

/-- **Central charge sum**: 4 βγ pairs × 2 each = 8. -/
theorem central_charge_sum : 4 * 2 = 8 := by norm_num

/-- **Narain denominator exponent**: `2c = 16` at `c = 8`. -/
theorem narain_denominator_exponent : 2 * (8 : ℕ) = 16 := by norm_num

end MacadayPhysicsLean.NarainEven
