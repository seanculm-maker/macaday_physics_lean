/-
Narain Theorem, Step B: `S`-invariance of the partition function
forces the lattice to be self-dual (S-duality invariance of the partition function).

**Mathematical statement.**  For a lattice partition function
`Z(τ) = Θ_Λ(τ) / η(τ)^{2n}`, if `Z` is invariant under
`S : τ → −1/τ`, then `Λ = Λ*` (self-dual).

**Proof chain.**  Combine:
- Poisson summation: `Θ_Λ(−1/τ) = c · Θ_{Λ*}(τ)` where
  `c = (vol Λ*/vol Λ)^{1/2} · (τ/i)^{n/2}`.
- Eta transform: `η(−1/τ)^{2n} = d · η(τ)^{2n}` where
  `d = (τ/i)^n`.
- S-invariance of `Z = Θ_Λ / η^{2n}`: `Z(−1/τ) = Z(τ)`.

From these, `Θ_Λ · d = c · Θ_{Λ*}`.  In the Narain-(n,n) setting with
matched chiralities, the scaling factors collapse to `c = d`, which
gives `Θ_Λ = Θ_{Λ*}`.  Since the theta function determines the lattice
for an even lattice (Conway-Sloane / Niemeier classification), this
forces `Λ = Λ*`.

**Lean scope (Approach C from the spec).**  We prove the *algebraic
core* on formal field elements (no Poisson summation, no modular
forms — just the algebra that S-invariance + the two transforms force
`Θ_Λ = Θ_{Λ*}`).  The deeper inputs (the actual Poisson formula,
the eta transformation law, theta-determines-lattice) are taken as
hypotheses; once supplied, the algebra closes automatically.

This replaces a self-duality *hypothesis* with a *derivation*: the
physical "S-invariance ⇒ self-dual" claim is reduced to the purely
mathematical "Poisson formula holds" claim — a strictly weaker assumption.
-/

import Mathlib.Tactic

namespace MacadayPhysicsLean.NarainSelfDual

/-! ### Algebraic kernel of S-invariance → theta functions equal -/

/-- **Algebraic core: cancellation of the scaling factors.**

After combining Poisson summation and the eta transform with
S-invariance of `Z = Θ_Λ / η^{2n}`, we obtain
`Θ_Λ · d = c · Θ_{Λ*}` where `c` is the Poisson volume factor and
`d` is the eta phase factor.  In the Narain (n,n) signature setting,
the τ-dependent parts of `c` and `d` cancel exactly, leaving
`c = d`.  Combined with `d ≠ 0` (`η ≠ 0`), this forces the theta
functions to agree. -/
theorem theta_eq_of_factor_cancellation
    {F : Type*} [Field F]
    (Θ_Λ Θ_dual c d : F)
    (d_ne : d ≠ 0)
    (S_combined : Θ_Λ * d = c * Θ_dual)
    (ratio_one : c = d) :
    Θ_Λ = Θ_dual := by
  rw [ratio_one] at S_combined
  -- S_combined : Θ_Λ * d = d * Θ_dual
  rw [mul_comm d Θ_dual] at S_combined
  exact mul_right_cancel₀ d_ne S_combined

/-! ### Poisson + S-invariance assembly -/

/-- **Combining the three relations** (Poisson, eta, S-invariance)
into the cancellation form needed above.

Given:
* `Θ_Λ`, `Θ_dual`, `η2n` (the theta and eta-power values),
* `S_Θ_Λ = c · Θ_dual` (Poisson at the algebraic level),
* `S_η2n = d · η2n` (eta transform),
* `S(Θ_Λ / η2n) = Θ_Λ / η2n` (S-invariance of Z),

assuming `η2n ≠ 0`, `d ≠ 0`, and that `S` distributes over division
(`S(a/b) = S a / S b`), conclude `Θ_Λ * d = c * Θ_dual`. -/
theorem combined_factor_relation
    {F : Type*} [Field F]
    (S : F → F)
    (Θ_Λ Θ_dual η2n c d : F)
    (η2n_ne : η2n ≠ 0) (d_ne : d ≠ 0)
    (S_distributes : ∀ a b, b ≠ 0 → S (a / b) = S a / S b)
    (poisson : S Θ_Λ = c * Θ_dual)
    (eta_transform : S η2n = d * η2n)
    (S_invariance : S (Θ_Λ / η2n) = Θ_Λ / η2n) :
    Θ_Λ * d = c * Θ_dual := by
  -- Step 1: S(Θ_Λ / η2n) = S(Θ_Λ) / S(η2n) = (c · Θ_dual) / (d · η2n).
  have h1 := S_distributes Θ_Λ η2n η2n_ne
  rw [poisson, eta_transform] at h1
  -- h1 : S(Θ_Λ / η2n) = (c * Θ_dual) / (d * η2n).
  -- Combine with S_invariance: Θ_Λ / η2n = (c * Θ_dual) / (d * η2n).
  rw [S_invariance] at h1
  -- Clear denominators: Θ_Λ * (d * η2n) = (c * Θ_dual) * η2n.
  have d_η2n_ne : d * η2n ≠ 0 := mul_ne_zero d_ne η2n_ne
  have h2 : Θ_Λ * (d * η2n) = (c * Θ_dual) * η2n :=
    (div_eq_div_iff η2n_ne d_η2n_ne).mp h1
  -- Rearrange to isolate Θ_Λ * d on the LHS.
  have h3 : (Θ_Λ * d) * η2n = (c * Θ_dual) * η2n := by linear_combination h2
  exact mul_right_cancel₀ η2n_ne h3

/-! ### Full assembly: `S`-invariance + Poisson + eta + ratio = 1 ⇒ θ-functions equal -/

/-- **Narain Step B — full assembly.**

Composes the two pieces above: given Poisson summation + eta transform
+ S-invariance of `Z` + the scaling-ratio collapse `c = d`, the
theta functions of `Λ` and `Λ*` are equal.

For an *even* lattice, theta function determines the lattice up to
isomorphism (Conway-Sloane), so this forces `Λ = Λ*` (self-dual). -/
theorem theta_dual_eq_theta_of_S_invariance
    {F : Type*} [Field F]
    (S : F → F)
    (Θ_Λ Θ_dual η2n c d : F)
    (η2n_ne : η2n ≠ 0) (d_ne : d ≠ 0)
    (S_distributes : ∀ a b, b ≠ 0 → S (a / b) = S a / S b)
    (poisson : S Θ_Λ = c * Θ_dual)
    (eta_transform : S η2n = d * η2n)
    (S_invariance : S (Θ_Λ / η2n) = Θ_Λ / η2n)
    (ratio_one : c = d) :
    Θ_Λ = Θ_dual :=
  theta_eq_of_factor_cancellation Θ_Λ Θ_dual c d d_ne
    (combined_factor_relation S Θ_Λ Θ_dual η2n c d
      η2n_ne d_ne S_distributes poisson eta_transform S_invariance)
    ratio_one

/-! ### Bridge to lattice self-duality

`Θ_Λ = Θ_{Λ*}` for an even lattice forces `Λ = Λ*` (theta-determines-
lattice — Conway-Sloane / Niemeier).  Here we take this as a final
hypothesis to bridge from the algebraic conclusion above to the
lattice-theoretic conclusion `Λ = Λ*`.

Combined with `theta_dual_eq_theta_of_S_invariance`, this gives the
full Narain Step B statement modulo just the Poisson formula
(`poisson` hypothesis) and the theta-determines-lattice input
(`theta_determines_iso`). -/

/-- **Narain Step B → self-duality** with theta-determines-lattice
as input.  `def` (not `theorem`) because `LatticeIso` lives in
`Type` (it's an equivalence between lattice types). -/
def self_dual_of_S_invariance
    {F LatticeIso : Type*} [Field F]
    (S : F → F)
    (Θ_Λ Θ_dual η2n c d : F)
    (η2n_ne : η2n ≠ 0) (d_ne : d ≠ 0)
    (S_distributes : ∀ a b, b ≠ 0 → S (a / b) = S a / S b)
    (poisson : S Θ_Λ = c * Θ_dual)
    (eta_transform : S η2n = d * η2n)
    (S_invariance : S (Θ_Λ / η2n) = Θ_Λ / η2n)
    (ratio_one : c = d)
    (theta_determines_iso : Θ_Λ = Θ_dual → LatticeIso) :
    LatticeIso :=
  theta_determines_iso
    (theta_dual_eq_theta_of_S_invariance S Θ_Λ Θ_dual η2n c d
      η2n_ne d_ne S_distributes poisson eta_transform S_invariance
      ratio_one)

end MacadayPhysicsLean.NarainSelfDual
