/-
Statistics Inheritance Theorem — companion results from Paper C.

Two results live here:

* `no_cnumber_eigenvalues` — if `ψ ∘ ψ = 0` on a ℂ-module, every
  eigenvalue of `ψ` is zero.  Physically: a Grassmann-odd operator
  has no c-number eigenvalues, so no classical configuration of the
  fermionic sector exists.

* `fks_cocycle_is_sign` — the Frenkel–Kac–Segal cocycle
  `ε(α,β) = (-1)^{Σ_{i<j} α_i β_j}` lives in `{+1, -1}` for any
  integer exponent.  Trivial; included so the WZW-level statement
  `k = 1` from Paper C has its arithmetic piece machine-checked.
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

namespace MacadayPhysicsLean.SIT

open LinearMap
open scoped ComplexOrder

/-! ### The Statistics Inheritance Theorem proper

The SIT states: if a bilinear bracket (commutator or anticommutator)
vanishes on all bulk field pairs, it vanishes on all corner data
(linear combinations of bulk fields restricted to the screen).

This is algebraically trivial — the content is the IDENTIFICATION
of corner data with linear images of bulk fields, not the algebra.
The non-trivial consequence is `no_cnumber_eigenvalues` below. -/

/-- **Statistics Inheritance Theorem (Paper C, Theorem 1):**
A bilinear form that vanishes on all inputs continues to vanish
when inputs are replaced by images under any linear map.

Physically: if bulk fields anticommute (`{φ₁, φ₂} = 0` for all
spacelike-separated field pairs), then the corner data obtained
by linear restriction to a codimension-2 surface also anticommute.
Grassmann parity is inherited, not postulated.

The proof is one line — the theorem is a TAUTOLOGY of bilinearity.
This triviality is the physical point: the classical/quantum
boundary requires no new input beyond the algebraic structure
of the bulk fields. -/
theorem statistics_inheritance
    {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V]
    {W : Type*} [AddCommGroup W] [Module R W]
    (B : V →ₗ[R] V →ₗ[R] W)
    (h_zero : ∀ v w, B v w = 0)
    (T : V →ₗ[R] V) :
    ∀ v w, B (T v) (T w) = 0 :=
  fun v w => h_zero (T v) (T w)

/-- If a ℂ-linear endomorphism `ψ` is nilpotent (`ψ ∘ ψ = 0`),
then every eigenvalue of `ψ` is zero. -/
theorem no_cnumber_eigenvalues
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : V →ₗ[ℂ] V)
    (h_nilpotent : ψ ∘ₗ ψ = 0)
    (c : ℂ) (v : V) (hv : v ≠ 0)
    (h_eigen : ψ v = c • v) :
    c = 0 := by
  -- (ψ ∘ₗ ψ) v = 0
  have h1 : ψ (ψ v) = 0 := by
    have := congrArg (fun f : V →ₗ[ℂ] V => f v) h_nilpotent
    simpa using this
  -- ψ (ψ v) = c² • v
  have h2 : ψ (ψ v) = (c * c) • v := by
    rw [h_eigen, map_smul, h_eigen, smul_smul]
  -- Combine: (c * c) • v = 0
  have h3 : (c * c) • v = 0 := by
    rw [← h2]; exact h1
  -- v ≠ 0 ⇒ c * c = 0
  have h4 : c * c = 0 := by
    rcases smul_eq_zero.mp h3 with hcc | hv0
    · exact hcc
    · exact absurd hv0 hv
  -- ℂ is an integral domain
  exact mul_self_eq_zero.mp h4

/-- FKS cocycle takes values in `{+1, -1}`: for every integer `n`,
`(-1)^n` is either `1` or `-1`.  Physical content: on an even
self-dual lattice the Frenkel–Kac–Segal cocycle is a sign, which
forces the WZW level to be exactly `k = 1`. -/
theorem fks_cocycle_is_sign (n : ℕ) :
    (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  rcases Nat.even_or_odd n with he | ho
  · left;  exact he.neg_one_pow
  · right; exact ho.neg_one_pow

/-! ### Bilinear parity (Paper C Appendix F)

Contrast with `no_cnumber_eigenvalues`: a positive-semidefinite
operator (modeling `ψ† ψ`) CAN have nonzero eigenvalues.  Its
eigenvalues are nonneg reals, not forced to zero.

Physically: if `ψ` is Grassmann-odd, then `ψ† ψ` is Grassmann-even
(bosonic).  Number operators `n = B† B` are classicalizable, even
though `B = εψψψ` itself is not. -/

/-- **PSD operators have non-negative real eigenvalues** — direct
re-export of Mathlib's `PosSemidef.eigenvalues_nonneg`.  The point
is to make explicit the contrast with `no_cnumber_eigenvalues`:
PSD eigenvalues are *not forced* to be zero. -/
theorem psd_eigenvalues_nonneg_real
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin n) :
    0 ≤ hA.1.eigenvalues i :=
  hA.eigenvalues_nonneg i

end MacadayPhysicsLean.SIT
