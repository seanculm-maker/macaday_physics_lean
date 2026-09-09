/-
Moncrief letter (Paper M) — Theorem A.4 (fixed-area slice) formalisation.

Extends `MoncriefA2`.  Theorem A.4 states that the unit-area rescaling of the
four-parameter flat ISO(2,1) family carries exactly the canonical symplectic
form, with an explicit nonlinear momentum map `(β, λ) ↦ (P₁, P₂)`.  Everything
below is pure field algebra (no analysis, no manifolds): the paper's sentence
"verified by exact symbolic computation" refers to a CAS check of these same
identities, which this file replaces by kernel-checked proofs.

Setup.  Over a field `K` of characteristic ≠ 2, with `s² τ₂ = 1` (so `s` plays
`√(1/τ₂)` and no square roots are needed):

* `ê₁ = (0, s, 0)`, `ê₂ = (0, sτ₁, sτ₂)`   (so(2,1) index `a = 0,1,2`)
* `ω̂₁ = β(ê₂ − λê₁) = (0, βs(τ₁−λ), βsτ₂)`, `ω̂₂ = λ ω̂₁`
* `q₁ = βs(τ₁−λ)`, `q₂ = βsτ₂`   (the nonzero components of `ω̂₁`)
* `P₁ = β(τ₁−λ)/τ₂`, `P₂ = β(τ₂² − (τ₁−λ)²)/(2τ₂²)`   (the A.4 momenta)

Contents:
* `A4_flatness_lorentz`, `A4_torsion_free` — componentwise, for the cross
  product with an *arbitrary* signature `η : Fin 3 → K` (covers so(3) and every
  sign convention for so(2,1)); `A4_flat_general` — the same via the
  convention-free alternating-bilinear argument of `MoncriefA2.family_flat`.
* `A4_unit_area` — the induced-metric determinant squares to 1.
* `q2_ne_zero_iff` — `q₂ ≠ 0 ↔ β ≠ 0`; `lam_eq` — `λ = τ₁ − τ₂ q₁/q₂` as an identity.
* `A4_potential_collapse_dtau2` — the `dτ₂`-coefficient collapse.
* `A4_delta_s_coefficient` — the `δs`-coefficient collapse.
* `A4_momentum_P1`, `A4_momentum_P2`, `A4_momentum_identities` — `s q₁ = P₁`
  and `s(q₂² − q₁²)/(2q₂) = P₂`; `A4_P1_of_A2`, `A4_P2_of_A2` — the Theorem A.2
  relations `P₁ = p₁/τ₂`, `P₂ = (p₂² − p₁²)/(2τ₂p₂)`.
* `A4_jacobian`, `A4_jacobian_det` — the fibre Jacobian of `(β,λ) ↦ (P₁,P₂)` is
  `β((τ₁−λ)² + τ₂²)/(2τ₂³)`; `A4_jacobian_ne_zero` over `ℝ`.
* `A4_fiber_quadratic`, `A4_fiber_root_exists`, `A4_fiber_coverage`,
  `A4_fiber_coverage_real` — coverage: every `(p, q) ≠ (0, 0)` is hit by the
  momentum map at some `β ≠ 0`, via the quadratic `β² − 2qβ − p² = 0`.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MacadayPhysicsLean.MoncriefA2

namespace MacadayPhysicsLean.MoncriefA4

open MacadayPhysicsLean.MoncriefA2

variable {K : Type*} [Field K]

/-! ### Preliminaries on the relation `s² τ₂ = 1` -/

/-- `s ≠ 0` follows from `s² τ₂ = 1`. -/
theorem s_ne_zero {s τ₂ : K} (hs : s ^ 2 * τ₂ = 1) : s ≠ 0 := by
  rintro rfl; simp at hs

/-- `τ₂ ≠ 0` follows from `s² τ₂ = 1` (so the spec's `hτ₂` is redundant). -/
theorem tau2_ne_zero {s τ₂ : K} (hs : s ^ 2 * τ₂ = 1) : τ₂ ≠ 0 := by
  rintro rfl; simp at hs

/-- `τ₂ = 1/s²` — used to eliminate `τ₂` in the rational identities below. -/
theorem tau2_eq {s τ₂ : K} (hs : s ^ 2 * τ₂ = 1) : τ₂ = 1 / s ^ 2 := by
  have hs0 : s ≠ 0 := s_ne_zero hs
  field_simp
  linear_combination hs

/-! ### The hatted (unit-area) family -/

/-- `ê₁ = (0, s, 0)`. -/
def e1 (s : K) : Fin 3 → K := ![0, s, 0]

/-- `ê₂ = (0, sτ₁, sτ₂)`. -/
def e2 (s τ₁ τ₂ : K) : Fin 3 → K := ![0, s * τ₁, s * τ₂]

/-- `ω̂₁ = β(ê₂ − λê₁)`. -/
def w1 (s τ₁ τ₂ β lam : K) : Fin 3 → K := β • (e2 s τ₁ τ₂ - lam • e1 s)

/-- `ω̂₂ = λ ω̂₁`. -/
def w2 (s τ₁ τ₂ β lam : K) : Fin 3 → K := lam • w1 s τ₁ τ₂ β lam

/-- The components of `ω̂₁` are `(0, βs(τ₁−λ), βsτ₂)`, as in the paper. -/
theorem w1_components (s τ₁ τ₂ β lam : K) :
    w1 s τ₁ τ₂ β lam = ![0, β * s * (τ₁ - lam), β * s * τ₂] := by
  ext i
  fin_cases i <;> simp [w1, e1, e2] <;> ring

/-- The cross product with an arbitrary signature `η` (`η = 1` is so(3); any
Lorentzian sign placement is so(2,1)). It is bilinear and alternating for every
`η`, which is all the flatness / torsion-free argument uses. -/
def cross (η : Fin 3 → K) (u v : Fin 3 → K) : Fin 3 → K :=
  ![η 0 * (u 1 * v 2 - u 2 * v 1),
    η 1 * (u 2 * v 0 - u 0 * v 2),
    η 2 * (u 0 * v 1 - u 1 * v 0)]

/-- `cross η` is alternating. -/
theorem cross_self (η u : Fin 3 → K) : cross η u u = 0 := by
  ext i
  fin_cases i <;> simp [cross, -mul_eq_zero] <;> ring

set_option linter.unnecessarySeqFocus false in
/-- **Flatness** (Theorem A.4(i)): `ω̂₁ × ω̂₂ = 0` componentwise, for every
signature `η`. -/
theorem A4_flatness_lorentz (η : Fin 3 → K) (s τ₁ τ₂ β lam : K) :
    cross η (w1 s τ₁ τ₂ β lam) (w2 s τ₁ τ₂ β lam) = 0 := by
  ext i
  fin_cases i <;> simp [cross, w1, w2, e1, e2, -mul_eq_zero] <;> ring

set_option linter.unnecessarySeqFocus false in
/-- **Torsion-free** (Theorem A.4(i)): `ω̂₁ × ê₂ − ω̂₂ × ê₁ = 0` componentwise,
for every signature `η`. -/
theorem A4_torsion_free (η : Fin 3 → K) (s τ₁ τ₂ β lam : K) :
    cross η (w1 s τ₁ τ₂ β lam) (e2 s τ₁ τ₂) - cross η (w2 s τ₁ τ₂ β lam) (e1 s) = 0 := by
  ext i
  fin_cases i <;> simp [cross, w1, w2, e1, e2, -mul_eq_zero] <;> ring

/-- The convention-free form: flatness and torsion-free of the hatted family for
**any** alternating bilinear `B`, by direct reuse of `MoncriefA2.family_flat`. -/
theorem A4_flat_general {N : Type*} [AddCommGroup N] [Module K N]
    (B : (Fin 3 → K) →ₗ[K] (Fin 3 → K) →ₗ[K] N) (halt : ∀ v, B v v = 0)
    (s τ₁ τ₂ β lam : K) :
    B (w1 s τ₁ τ₂ β lam) (w2 s τ₁ τ₂ β lam) = 0 ∧
      B (w1 s τ₁ τ₂ β lam) (e2 s τ₁ τ₂) = B (w2 s τ₁ τ₂ β lam) (e1 s) := by
  simp only [w2, w1]
  exact family_flat B halt (e1 s) (e2 s τ₁ τ₂) β lam

/-- **Unit area** (Theorem A.4(ii)): the determinant of the induced metric is
`(ê₁ ∧ ê₂)² = (s · sτ₂)² = (s²τ₂)² = 1`. -/
theorem A4_unit_area (s τ₁ τ₂ : K) (hs : s ^ 2 * τ₂ = 1) :
    (e1 s 1 * e2 s τ₁ τ₂ 2 - e1 s 2 * e2 s τ₁ τ₂ 1) ^ 2 = 1 := by
  have h : e1 s 1 * e2 s τ₁ τ₂ 2 - e1 s 2 * e2 s τ₁ τ₂ 1 = s ^ 2 * τ₂ := by
    simp [e1, e2]
    ring
  rw [h, hs, one_pow]

/-! ### The momentum map -/

/-- `q₁ = βs(τ₁−λ)`, the `a = 1` component of `ω̂₁`. -/
def q1 (s τ₁ β lam : K) : K := β * s * (τ₁ - lam)

/-- `q₂ = βsτ₂`, the `a = 2` component of `ω̂₁`. -/
def q2 (s τ₂ β : K) : K := β * s * τ₂

/-- `P₁ = β(τ₁−λ)/τ₂`. -/
def P1 (τ₁ τ₂ β lam : K) : K := β * (τ₁ - lam) / τ₂

/-- `P₂ = β(τ₂² − (τ₁−λ)²)/(2τ₂²)`. -/
def P2 (τ₁ τ₂ β lam : K) : K := β * (τ₂ ^ 2 - (τ₁ - lam) ^ 2) / (2 * τ₂ ^ 2)

/-- Theorem A.2's `p₁ = β(τ₁−λ)`. -/
def p1 (τ₁ β lam : K) : K := β * (τ₁ - lam)

/-- Theorem A.2's `p₂ = βτ₂`. -/
def p2 (τ₂ β : K) : K := β * τ₂

/-- `q₂ ≠ 0 ↔ β ≠ 0` under `s²τ₂ = 1`. -/
theorem q2_ne_zero_iff (s τ₂ β : K) (hs : s ^ 2 * τ₂ = 1) :
    q2 s τ₂ β ≠ 0 ↔ β ≠ 0 := by
  simp [q2, s_ne_zero hs, tau2_ne_zero hs]

/-- `λ = τ₁ − τ₂ q₁/q₂` as an identity (given `β ≠ 0`). -/
theorem lam_eq (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1) (hβ : β ≠ 0) :
    lam = τ₁ - τ₂ * q1 s τ₁ β lam / q2 s τ₂ β := by
  have hs0 := s_ne_zero hs
  have hτ := tau2_ne_zero hs
  simp only [q1, q2]
  field_simp
  ring

/-- **`δs`-coefficient collapse** (Theorem A.4(ii)):
`q₁τ₁ + q₂τ₂ − λq₁ = τ₂(q₁² + q₂²)/q₂`, an identity in `(τ₁, τ₂, β, λ, s)`. -/
theorem A4_delta_s_coefficient (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1) (hβ : β ≠ 0) :
    q1 s τ₁ β lam * τ₁ + q2 s τ₂ β * τ₂ - lam * q1 s τ₁ β lam
      = τ₂ * (q1 s τ₁ β lam ^ 2 + q2 s τ₂ β ^ 2) / q2 s τ₂ β := by
  have hs0 := s_ne_zero hs
  have hτ := tau2_ne_zero hs
  simp only [q1, q2]
  field_simp
  ring

/-- **Momentum identity 1** (Theorem A.4(ii)): `s q₁ = P₁`. -/
theorem A4_momentum_P1 (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1) :
    s * q1 s τ₁ β lam = P1 τ₁ τ₂ β lam := by
  have hs0 := s_ne_zero hs
  obtain rfl := tau2_eq hs
  simp only [q1, P1]
  field_simp

/-- **Theorem A.2 relation** `P₁ = p₁/τ₂` (definitional). -/
theorem A4_P1_of_A2 (τ₁ τ₂ β lam : K) : P1 τ₁ τ₂ β lam = p1 τ₁ β lam / τ₂ := rfl

/-- **Quadratic-root identity**: `b = q + r` with `r² = q² + p²` solves
`τ₂² b² − 2τ₂² q b − (pτ₂)² = 0`.  (Any commutative ring.) -/
theorem A4_fiber_quadratic (p q r τ₂ : K) (hr : r ^ 2 = q ^ 2 + p ^ 2) :
    τ₂ ^ 2 * (q + r) ^ 2 - 2 * τ₂ ^ 2 * q * (q + r) - (p * τ₂) ^ 2 = 0 := by
  linear_combination τ₂ ^ 2 * hr

section CharNeTwo

variable [NeZero (2 : K)]

/-- **Potential collapse, `dτ₂` coefficient** (Theorem A.4(ii), the heart).
A pure rational identity in `(q₁, q₂, s, τ₂)` with `q₂ ≠ 0`, `τ₂ ≠ 0`:
`s q₂ − (τ₂(q₁² + q₂²)/q₂)(s/(2τ₂)) = s(q₂² − q₁²)/(2q₂)`. -/
theorem A4_potential_collapse_dtau2 (q₁ q₂ s τ₂ : K) (hq₂ : q₂ ≠ 0) (hτ : τ₂ ≠ 0) :
    s * q₂ - (τ₂ * (q₁ ^ 2 + q₂ ^ 2) / q₂) * (s / (2 * τ₂))
      = s * (q₂ ^ 2 - q₁ ^ 2) / (2 * q₂) := by
  field_simp
  ring

/-- The same, instantiated on the family's `q₁, q₂` (with `β ≠ 0`). -/
theorem A4_potential_collapse_dtau2' (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1)
    (hβ : β ≠ 0) :
    s * q2 s τ₂ β
        - (τ₂ * (q1 s τ₁ β lam ^ 2 + q2 s τ₂ β ^ 2) / q2 s τ₂ β) * (s / (2 * τ₂))
      = s * (q2 s τ₂ β ^ 2 - q1 s τ₁ β lam ^ 2) / (2 * q2 s τ₂ β) :=
  A4_potential_collapse_dtau2 _ _ _ _ ((q2_ne_zero_iff s τ₂ β hs).mpr hβ) (tau2_ne_zero hs)

/-- **Momentum identity 2** (Theorem A.4(ii)): `s(q₂² − q₁²)/(2q₂) = P₂`. -/
theorem A4_momentum_P2 (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1) (hβ : β ≠ 0) :
    s * (q2 s τ₂ β ^ 2 - q1 s τ₁ β lam ^ 2) / (2 * q2 s τ₂ β) = P2 τ₁ τ₂ β lam := by
  have hs0 := s_ne_zero hs
  obtain rfl := tau2_eq hs
  simp only [q1, q2, P2]
  field_simp

/-- **Momentum identities** (Theorem A.4(ii)), packaged: `s q₁ = P₁` and
`s(q₂² − q₁²)/(2q₂) = P₂`. -/
theorem A4_momentum_identities (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1) (hβ : β ≠ 0) :
    s * q1 s τ₁ β lam = P1 τ₁ τ₂ β lam ∧
      s * (q2 s τ₂ β ^ 2 - q1 s τ₁ β lam ^ 2) / (2 * q2 s τ₂ β) = P2 τ₁ τ₂ β lam :=
  ⟨A4_momentum_P1 s τ₁ τ₂ β lam hs, A4_momentum_P2 s τ₁ τ₂ β lam hs hβ⟩

/-- **Theorem A.2 relation** `P₂ = (p₂² − p₁²)/(2τ₂p₂)`. -/
theorem A4_P2_of_A2 (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) (hβ : β ≠ 0) :
    P2 τ₁ τ₂ β lam = (p2 τ₂ β ^ 2 - p1 τ₁ β lam ^ 2) / (2 * τ₂ * p2 τ₂ β) := by
  simp only [P2, p1, p2]
  field_simp

/-! ### The fibre Jacobian

The partial derivatives of the rational functions `P₁, P₂` in `(β, λ)` at fixed
`τ`, written out by hand; the lemma checks the resulting algebraic identity. -/

/-- `∂P₁/∂β = (τ₁−λ)/τ₂`. -/
def dP1_dβ (τ₁ τ₂ lam : K) : K := (τ₁ - lam) / τ₂

/-- `∂P₁/∂λ = −β/τ₂`. -/
def dP1_dlam (τ₂ β : K) : K := -β / τ₂

/-- `∂P₂/∂β = (τ₂² − (τ₁−λ)²)/(2τ₂²)`. -/
def dP2_dβ (τ₁ τ₂ lam : K) : K := (τ₂ ^ 2 - (τ₁ - lam) ^ 2) / (2 * τ₂ ^ 2)

/-- `∂P₂/∂λ = β(τ₁−λ)/τ₂²`. -/
def dP2_dlam (τ₁ τ₂ β lam : K) : K := β * (τ₁ - lam) / τ₂ ^ 2

/-- **Fibre Jacobian** (Theorem A.4(iii)):
`(∂P₁/∂β)(∂P₂/∂λ) − (∂P₁/∂λ)(∂P₂/∂β) = β((τ₁−λ)² + τ₂²)/(2τ₂³)`. -/
theorem A4_jacobian (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) :
    dP1_dβ τ₁ τ₂ lam * dP2_dlam τ₁ τ₂ β lam - dP1_dlam τ₂ β * dP2_dβ τ₁ τ₂ lam
      = β * ((τ₁ - lam) ^ 2 + τ₂ ^ 2) / (2 * τ₂ ^ 3) := by
  simp only [dP1_dβ, dP1_dlam, dP2_dβ, dP2_dlam]
  field_simp
  ring

/-- The same as a `2 × 2` determinant, in the style of `MoncriefA2.family_jacobian_det`. -/
theorem A4_jacobian_det (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) :
    (Matrix.of ![![dP1_dβ τ₁ τ₂ lam, dP1_dlam τ₂ β],
                 ![dP2_dβ τ₁ τ₂ lam, dP2_dlam τ₁ τ₂ β lam]] : Matrix (Fin 2) (Fin 2) K).det
      = β * ((τ₁ - lam) ^ 2 + τ₂ ^ 2) / (2 * τ₂ ^ 3) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact A4_jacobian τ₁ τ₂ β lam hτ

/-! ### Fibre coverage

Solving `(P₁, P₂) = (p, q)` for `β` at fixed `τ` gives the quadratic
`β² − 2qβ − p² = 0`, whose roots are `q ± √(q² + p²)`.  We work with any `r`
satisfying `r² = q² + p²` (over `ℝ`, `r = √(q² + p²)`). -/

/-- **A nonzero root exists** whenever `(p, q) ≠ (0, 0)`: one of `q ± r` is
nonzero, and both solve `b² − 2qb − p² = 0`. -/
theorem A4_fiber_root_exists (p q r : K) (hr : r ^ 2 = q ^ 2 + p ^ 2)
    (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ b ^ 2 - 2 * q * b - p ^ 2 = 0 := by
  by_cases h : q + r = 0
  · refine ⟨q - r, ?_, by linear_combination hr⟩
    intro h'
    have h2q : 2 * q = 0 := by linear_combination h + h'
    have hq : q = 0 := (mul_eq_zero.mp h2q).resolve_left two_ne_zero
    have hr0 : r = 0 := by linear_combination h - hq
    have hp2 : p ^ 2 = 0 := by
      rw [hq, hr0] at hr
      linear_combination -hr
    rcases hpq with hp | hq'
    · exact hp (pow_eq_zero_iff two_ne_zero |>.mp hp2)
    · exact hq' hq
  · exact ⟨q + r, h, by linear_combination hr⟩

/-- **Fibre coverage** (Theorem A.4(iii)): for `(p, q) ≠ (0, 0)` and any `r` with
`r² = q² + p²`, there are `β ≠ 0` and `λ` with `(P₁, P₂)(τ, β, λ) = (p, q)`. -/
theorem A4_fiber_coverage (τ₁ τ₂ p q r : K) (hτ : τ₂ ≠ 0)
    (hr : r ^ 2 = q ^ 2 + p ^ 2) (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ β : K, β ≠ 0 ∧ ∃ lam : K, P1 τ₁ τ₂ β lam = p ∧ P2 τ₁ τ₂ β lam = q := by
  obtain ⟨b, hb, hquad⟩ := A4_fiber_root_exists p q r hr hpq
  refine ⟨b, hb, τ₁ - p * τ₂ / b, ?_, ?_⟩
  · simp only [P1]
    field_simp
    ring
  · simp only [P2]
    have hsub : τ₁ - (τ₁ - p * τ₂ / b) = p * τ₂ / b := by ring
    rw [hsub]
    field_simp
    linear_combination hquad

end CharNeTwo

/-! ### Real specialisations -/

/-- Over `ℝ` the Jacobian is nonzero for `β ≠ 0`, `τ₂ ≠ 0`. -/
theorem A4_jacobian_ne_zero (τ₁ τ₂ β lam : ℝ) (hτ : τ₂ ≠ 0) (hβ : β ≠ 0) :
    dP1_dβ τ₁ τ₂ lam * dP2_dlam τ₁ τ₂ β lam - dP1_dlam τ₂ β * dP2_dβ τ₁ τ₂ lam ≠ 0 := by
  rw [A4_jacobian τ₁ τ₂ β lam hτ]
  have hpos : (τ₁ - lam) ^ 2 + τ₂ ^ 2 ≠ 0 := by positivity
  have h3 : 2 * τ₂ ^ 3 ≠ 0 := by positivity
  exact div_ne_zero (mul_ne_zero hβ hpos) h3

/-- **Fibre coverage over `ℝ`** with `r = √(q² + p²)`: every `(p, q) ≠ (0, 0)`
is hit by the momentum map at some `β ≠ 0`. -/
theorem A4_fiber_coverage_real (τ₁ τ₂ p q : ℝ) (hτ : τ₂ ≠ 0) (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ β : ℝ, β ≠ 0 ∧ ∃ lam : ℝ, P1 τ₁ τ₂ β lam = p ∧ P2 τ₁ τ₂ β lam = q :=
  A4_fiber_coverage τ₁ τ₂ p q (Real.sqrt (q ^ 2 + p ^ 2)) hτ
    (Real.sq_sqrt (by positivity)) hpq

end MacadayPhysicsLean.MoncriefA4
