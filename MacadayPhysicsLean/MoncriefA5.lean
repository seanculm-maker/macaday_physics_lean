/-
Moncrief letter (Paper M) — Theorem A.5 (ADM matching) formalisation.

Extends `MoncriefA2` / `MoncriefA4`.  Theorem A.5 derives the identification of
the Lorentz-deformation parameters with canonical momenta from the ADM data
induced by the unit-area family of Theorem A.4.  Everything here is field algebra
(no analysis, no manifolds); the manuscript's "verified by exact symbolic
computation" refers to a CAS check of these same identities.

**Conventions (stated once, used throughout).**
* Coframe `ê^i_B` is a `2×2` matrix with row `i` = internal index, column `B` =
  coordinate index.  We use the **unit-area `s`-convention** of `MoncriefA4`:
  `ê = s • [[1, τ₁], [0, τ₂]]` with `s² τ₂ = 1`, so `det ê = 1` exactly and the
  columns of `ê` are A.4's `e1 = (s, 0)` and `e2 = (sτ₁, sτ₂)`.
* `ε = [[0, 1], [-1, 0]]`, `w = (1, λ)`, `v̂ = ê (−λ, 1)ᵀ`, `ω̂^i_A = β w_A v̂^i`.
* `q̂_AB = (êᵀ ê)_AB = [[1/τ₂, τ₁/τ₂], [τ₁/τ₂, (τ₁²+τ₂²)/τ₂]]` (rational in `τ`;
  `det q̂ = 1`), and `K_AB = β w_A w_B`.
* `P₁, P₂` are `MoncriefA4.P1`, `MoncriefA4.P2`; `dz² = (dσ¹ + τ dσ²)²` has real
  and imaginary parts `dz2R = [[1, τ₁], [τ₁, τ₁²−τ₂²]]`, `dz2I = [[0, τ₂], [τ₂, 2τ₁τ₂]]`.
* Symplectic coefficients live in the `(dτ₁, dτ₂, dβ, dλ)` basis indexed by
  `Fin 4`, using `MoncriefA2.wedge`.  The partial derivatives of the rational
  functions `π^{AB}`, `q̂_AB`, `P₁`, `P₂` are written out by hand as literal
  vectors (`dpi11`, …, `dP1`, `dP2`; the `β, λ` components of `dP1, dP2` are the
  A.4 Jacobian entries `dP1_dβ`, …), exactly as in A.4's Jacobian lemma; the
  lemmas check the resulting algebraic identities.

Contents:
* `A5_eps_conj` — `Mᵀ ε M = (det M) ε` for every `2×2` `M` (any commutative ring);
  `A5_ehat_eps` — the unit-area case `êᵀ ε ê = ε`.
* `A5_K_derivation_general` — `Σ_{ij} ε_ij ω^j_A E^i_B = (det E) β w_A (ε u)_B` for
  any coframe `E` and `ω^i_A = β w_A (E u)^i`; `A5_K_derivation` — for `ê`, with
  `u = (−λ, 1)`: `K_AB = β w_A w_B`.
* `A5_rank_one_constraint` — `(tr_q K)² = K_AB K^AB` for `K = β w wᵀ` and any
  invertible symmetric `q` (the Hamiltonian-constraint algebra).
* `A5_qhat_eq_coframe`, `A5_qhat_det`, `A5_qhat_inv`, `A5_trace_K` — the induced metric.
* `A5_c_extraction` — `K̃ = P₂ • dz2R − P₁ • dz2I`, i.e. `c = P₂ + i P₁`.
* `A5_pi_closed_form` — the closed form of `π^{AB} = (q̂⁻¹ K̃ q̂⁻¹)^{AB}`.
* `A5_symplectic_match` — `Σ_{A,B} dπ^{AB} ∧ dq̂_AB = −2 (dP₁ ∧ dτ₁ + dP₂ ∧ dτ₂)`
  (full double sum over ordered pairs `(A, B)`, so the off-diagonal term counts twice).
* `A5_trace_decoupling` — `det q̂ = 1` and `d(det q̂) = 0` identically.
* `A44_boost_pair`, `A44_ds_consistent`, `A44_coframe_form` — the §4.4 slice facts.

Not formalised (out of scope, geometric rather than algebraic): flatness `R(q̂) = 0`
of the constant torus metric, and the `1/16πG` normalisation prose.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MacadayPhysicsLean.MoncriefA2
import MacadayPhysicsLean.MoncriefA4

namespace MacadayPhysicsLean.MoncriefA5

open MacadayPhysicsLean.MoncriefA2 MacadayPhysicsLean.MoncriefA4
open Matrix

/-! ### 1. The ε-conjugation identity -/

/-- `ε = [[0, 1], [-1, 0]]`. -/
def eps (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 1], ![-1, 0]]

/-- **ε-conjugation** (Theorem A.5, preliminary): `Mᵀ ε M = (det M) • ε` for every
`2×2` matrix over a commutative ring. -/
theorem A5_eps_conj {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    Mᵀ * eps R * M = M.det • eps R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

variable {K : Type*} [Field K]

/-! ### 2. The unit-area coframe and the ε-dual extrinsic curvature -/

/-- The unit-area coframe `ê = s • [[1, τ₁], [0, τ₂]]` (row = internal `i`, column =
coordinate `B`); its columns are `MoncriefA4.e1`, `MoncriefA4.e2`. -/
def ehat (s τ₁ τ₂ : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![s, s * τ₁], ![0, s * τ₂]]

/-- The columns of `ê` are A.4's `ê₁ = (s, 0)` and `ê₂ = (sτ₁, sτ₂)`. -/
theorem ehat_columns (s τ₁ τ₂ : K) :
    ehat s τ₁ τ₂ 0 0 = e1 s 1 ∧ ehat s τ₁ τ₂ 1 0 = e1 s 2 ∧
      ehat s τ₁ τ₂ 0 1 = e2 s τ₁ τ₂ 1 ∧ ehat s τ₁ τ₂ 1 1 = e2 s τ₁ τ₂ 2 := by
  simp [ehat, e1, e2]

theorem ehat_det (s τ₁ τ₂ : K) : (ehat s τ₁ τ₂).det = s ^ 2 * τ₂ := by
  rw [Matrix.det_fin_two]
  simp [ehat]
  ring

/-- `det ê = 1` on the unit-area slice. -/
theorem ehat_det_one (s τ₁ τ₂ : K) (hs : s ^ 2 * τ₂ = 1) : (ehat s τ₁ τ₂).det = 1 := by
  rw [ehat_det, hs]

/-- `êᵀ ε ê = ε` — the "well defined since `det ê = 1`" clause of Theorem A.5. -/
theorem A5_ehat_eps (s τ₁ τ₂ : K) (hs : s ^ 2 * τ₂ = 1) :
    (ehat s τ₁ τ₂)ᵀ * eps K * ehat s τ₁ τ₂ = eps K := by
  rw [A5_eps_conj, ehat_det_one s τ₁ τ₂ hs, one_smul]

/-- `w = (1, λ)`. -/
def wvec (lam : K) : Fin 2 → K := ![1, lam]

/-- `u = (−λ, 1)`, so that `v = E u = e₂ − λ e₁`. -/
def uvec (lam : K) : Fin 2 → K := ![-lam, 1]

/-- The ε-dual contraction `Σ_{i,j} ε_ij ω^j_A E^i_B` with `ω^i_A = β w_A (E u)^i`,
for an arbitrary coframe `E` and vectors `w, u`. -/
def epsContraction (E : Matrix (Fin 2) (Fin 2) K) (β : K) (w u : Fin 2 → K) (A B : Fin 2) : K :=
  ∑ i, ∑ j, eps K i j * (β * w A * (E.mulVec u) j) * E i B

/-- **ε-dual contraction, general coframe** (the convention-fixing step of A.5):
`Σ_{ij} ε_ij ω^j_A E^i_B = (det E) β w_A (ε u)_B`.  This is `A5_eps_conj` read
componentwise: `(ε E u) · E_B = (Eᵀ ε E u)_B = det E · (ε u)_B`. -/
theorem A5_K_derivation_general (E : Matrix (Fin 2) (Fin 2) K) (β : K) (w u : Fin 2 → K)
    (A B : Fin 2) :
    epsContraction E β w u A B = E.det * β * w A * ((eps K).mulVec u) B := by
  simp only [epsContraction]
  fin_cases B <;>
    simp [eps, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- `ε u = w` for `u = (−λ, 1)`, `w = (1, λ)`. -/
theorem eps_mulVec_uvec (lam : K) : (eps K).mulVec (uvec lam) = wvec lam := by
  ext i
  fin_cases i <;> simp [eps, uvec, wvec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The induced extrinsic curvature** (Theorem A.5): on the unit-area family,
`K_AB := ε^{ij} ω̂^j_A ê^i_B = β w_A w_B` with `w = (1, λ)`. -/
theorem A5_K_derivation (s τ₁ τ₂ β lam : K) (hs : s ^ 2 * τ₂ = 1) (A B : Fin 2) :
    epsContraction (ehat s τ₁ τ₂) β (wvec lam) (uvec lam) A B = β * wvec lam A * wvec lam B := by
  rw [A5_K_derivation_general, ehat_det_one s τ₁ τ₂ hs, eps_mulVec_uvec]
  ring

/-! ### 3. The rank-one Hamiltonian-constraint identity -/

/-- A symmetric `2×2` matrix `[[q11, q12], [q12, q22]]`. -/
def qsym (q11 q12 q22 : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![q11, q12], ![q12, q22]]

/-- Its explicit inverse (for `q11 q22 − q12² ≠ 0`). -/
def qsymInv (q11 q12 q22 : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![q22 / (q11 * q22 - q12 ^ 2), -q12 / (q11 * q22 - q12 ^ 2)],
              ![-q12 / (q11 * q22 - q12 ^ 2), q11 / (q11 * q22 - q12 ^ 2)]]

theorem qsym_mul_qsymInv (q11 q12 q22 : K) (hdet : q11 * q22 - q12 ^ 2 ≠ 0) :
    qsym q11 q12 q22 * qsymInv q11 q12 q22 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qsym, qsymInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- `tr_q K = q^{AB} K_AB` (given the inverse metric `qi`). -/
def trq (qi Kmat : Matrix (Fin 2) (Fin 2) K) : K := ∑ A, ∑ B, qi A B * Kmat A B

/-- `K^{AB} = (q⁻¹ K q⁻¹)^{AB}`. -/
def raise (qi Kmat : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K := qi * Kmat * qi

/-- `K_AB K^{AB}`. -/
def contract (Kmat Kup : Matrix (Fin 2) (Fin 2) K) : K := ∑ A, ∑ B, Kmat A B * Kup A B

/-- The rank-one symmetric matrix `β w wᵀ`. -/
def rankOne (β w1 w2 : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![β * w1 * w1, β * w1 * w2], ![β * w2 * w1, β * w2 * w2]]

/-- **Rank-one constraint** (Theorem A.5(i)): for `K = β w wᵀ` and any symmetric `q`
with the explicit inverse `qsymInv`, `(tr_q K)² = K_AB K^AB`.  (The identity holds
as an identity of rational expressions in the entries of `q⁻¹`, so no invertibility
hypothesis is even needed.) -/
theorem A5_rank_one_constraint (q11 q12 q22 β w1 w2 : K) :
    (trq (qsymInv q11 q12 q22) (rankOne β w1 w2)) ^ 2
      = contract (rankOne β w1 w2) (raise (qsymInv q11 q12 q22) (rankOne β w1 w2)) := by
  simp only [trq, contract, raise, qsymInv, rankOne, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

/-! ### 4. The induced metric and the traceless part -/

/-- `q̂ = êᵀ ê = [[1/τ₂, τ₁/τ₂], [τ₁/τ₂, (τ₁²+τ₂²)/τ₂]]` (rational in `τ`). -/
def qhat (τ₁ τ₂ : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![1 / τ₂, τ₁ / τ₂], ![τ₁ / τ₂, (τ₁ ^ 2 + τ₂ ^ 2) / τ₂]]

/-- `q̂⁻¹ = [[(τ₁²+τ₂²)/τ₂, −τ₁/τ₂], [−τ₁/τ₂, 1/τ₂]]`. -/
def qhatInv (τ₁ τ₂ : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![(τ₁ ^ 2 + τ₂ ^ 2) / τ₂, -τ₁ / τ₂], ![-τ₁ / τ₂, 1 / τ₂]]

/-- `q̂` is the metric induced by the unit-area coframe: `q̂ = êᵀ ê` (uses `s²τ₂ = 1`). -/
theorem A5_qhat_eq_coframe (s τ₁ τ₂ : K) (hs : s ^ 2 * τ₂ = 1) :
    qhat τ₁ τ₂ = (ehat s τ₁ τ₂)ᵀ * ehat s τ₁ τ₂ := by
  have hs0 := s_ne_zero hs
  obtain rfl := tau2_eq hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qhat, ehat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- `det q̂ = 1`. -/
theorem A5_qhat_det (τ₁ τ₂ : K) (hτ : τ₂ ≠ 0) : (qhat τ₁ τ₂).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [qhat]
  field_simp
  ring

theorem A5_qhat_inv (τ₁ τ₂ : K) (hτ : τ₂ ≠ 0) : qhat τ₁ τ₂ * qhatInv τ₁ τ₂ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qhat, qhatInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- `K = β w wᵀ` with `w = (1, λ)`. -/
def Kmat (β lam : K) : Matrix (Fin 2) (Fin 2) K := rankOne β 1 lam

/-- `tr_q̂ K = β((τ₁−λ)² + τ₂²)/τ₂`. -/
theorem A5_trace_K (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) :
    trq (qhatInv τ₁ τ₂) (Kmat β lam) = β * ((τ₁ - lam) ^ 2 + τ₂ ^ 2) / τ₂ := by
  simp only [trq, qhatInv, Kmat, rankOne, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

section CharNeTwo

variable [NeZero (2 : K)]

/-- The traceless part `K̃ = K − (tr_q̂ K / 2) q̂`. -/
def Ktilde (τ₁ τ₂ β lam : K) : Matrix (Fin 2) (Fin 2) K :=
  Kmat β lam - (trq (qhatInv τ₁ τ₂) (Kmat β lam) / 2) • qhat τ₁ τ₂

/-- `Re (dz²)` for `dz = dσ¹ + τ dσ²`. -/
def dz2R (τ₁ τ₂ : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![1, τ₁], ![τ₁, τ₁ ^ 2 - τ₂ ^ 2]]

/-- `Im (dz²)` for `dz = dσ¹ + τ dσ²`. -/
def dz2I (τ₁ τ₂ : K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![0, τ₂], ![τ₂, 2 * τ₁ * τ₂]]

/-- **Coefficient extraction** (Theorem A.5(ii)): `K̃ = P₂ • Re(dz²) − P₁ • Im(dz²)`,
i.e. `K̃ = Re(c dz²)` with `c = P₂ + i P₁` — exactly the momenta of Theorem A.4.
All three components are checked (the `11`, `12` components determine `(P₂, P₁)`,
the `22` component is the consistency check). -/
theorem A5_c_extraction (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) :
    Ktilde τ₁ τ₂ β lam = P2 τ₁ τ₂ β lam • dz2R τ₁ τ₂ - P1 τ₁ τ₂ β lam • dz2I τ₁ τ₂ := by
  rw [Ktilde, A5_trace_K τ₁ τ₂ β lam hτ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kmat, rankOne, qhat, dz2R, dz2I, P1, P2] <;> field_simp <;> ring

/-! ### 5. The ADM momentum and the symplectic match -/

/-- `π^{AB} = (q̂⁻¹ K̃ q̂⁻¹)^{AB}` (with `√q̂ = 1` on the unit-area slice). -/
def piADM (τ₁ τ₂ β lam : K) : Matrix (Fin 2) (Fin 2) K :=
  qhatInv τ₁ τ₂ * Ktilde τ₁ τ₂ β lam * qhatInv τ₁ τ₂

/-- Closed form of `π^{11}`. -/
def pi11 (τ₁ τ₂ β lam : K) : K :=
  β * (lam * τ₁ - lam * τ₂ - τ₁ ^ 2 - τ₂ ^ 2) * (lam * τ₁ + lam * τ₂ - τ₁ ^ 2 - τ₂ ^ 2)
    / (2 * τ₂ ^ 2)

/-- Closed form of `π^{12} = π^{21}`. -/
def pi12 (τ₁ τ₂ β lam : K) : K :=
  -β * (lam ^ 2 * τ₁ - 2 * lam * τ₁ ^ 2 - 2 * lam * τ₂ ^ 2 + τ₁ ^ 3 + τ₁ * τ₂ ^ 2)
    / (2 * τ₂ ^ 2)

/-- Closed form of `π^{22}`. -/
def pi22 (τ₁ τ₂ β lam : K) : K :=
  β * (lam - τ₁ - τ₂) * (lam - τ₁ + τ₂) / (2 * τ₂ ^ 2)

/-- The ADM momentum on the family, in closed form. -/
theorem A5_pi_closed_form (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) :
    piADM τ₁ τ₂ β lam
      = Matrix.of ![![pi11 τ₁ τ₂ β lam, pi12 τ₁ τ₂ β lam],
                    ![pi12 τ₁ τ₂ β lam, pi22 τ₁ τ₂ β lam]] := by
  rw [piADM, A5_c_extraction τ₁ τ₂ β lam hτ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qhatInv, dz2R, dz2I, P1, P2, pi11, pi12, pi22, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-! Hand-differentiated partials in the `(τ₁, τ₂, β, λ)` basis. -/

/-- `dπ^{11}`. -/
def dpi11 (τ₁ τ₂ β lam : K) : Fin 4 → K :=
  ![β * (lam - 2 * τ₁) * (lam * τ₁ - τ₁ ^ 2 - τ₂ ^ 2) / τ₂ ^ 2,
    -β * (lam * τ₁ - τ₁ ^ 2 - τ₂ ^ 2) * (lam * τ₁ - τ₁ ^ 2 + τ₂ ^ 2) / τ₂ ^ 3,
    (lam * τ₁ - lam * τ₂ - τ₁ ^ 2 - τ₂ ^ 2) * (lam * τ₁ + lam * τ₂ - τ₁ ^ 2 - τ₂ ^ 2)
      / (2 * τ₂ ^ 2),
    β * (lam * τ₁ ^ 2 - lam * τ₂ ^ 2 - τ₁ ^ 3 - τ₁ * τ₂ ^ 2) / τ₂ ^ 2]

/-- `dπ^{12}`. -/
def dpi12 (τ₁ τ₂ β lam : K) : Fin 4 → K :=
  ![-β * (lam ^ 2 - 4 * lam * τ₁ + 3 * τ₁ ^ 2 + τ₂ ^ 2) / (2 * τ₂ ^ 2),
    β * τ₁ * (lam - τ₁) ^ 2 / τ₂ ^ 3,
    -(lam ^ 2 * τ₁ - 2 * lam * τ₁ ^ 2 - 2 * lam * τ₂ ^ 2 + τ₁ ^ 3 + τ₁ * τ₂ ^ 2) / (2 * τ₂ ^ 2),
    -β * (lam * τ₁ - τ₁ ^ 2 - τ₂ ^ 2) / τ₂ ^ 2]

/-- `dπ^{22}`. -/
def dpi22 (τ₁ τ₂ β lam : K) : Fin 4 → K :=
  ![-β * (lam - τ₁) / τ₂ ^ 2,
    -β * (lam - τ₁) ^ 2 / τ₂ ^ 3,
    (lam - τ₁ - τ₂) * (lam - τ₁ + τ₂) / (2 * τ₂ ^ 2),
    β * (lam - τ₁) / τ₂ ^ 2]

/-- `dq̂_11`. -/
def dq11 (τ₂ : K) : Fin 4 → K := ![0, -1 / τ₂ ^ 2, 0, 0]

/-- `dq̂_12`. -/
def dq12 (τ₁ τ₂ : K) : Fin 4 → K := ![1 / τ₂, -τ₁ / τ₂ ^ 2, 0, 0]

/-- `dq̂_22`. -/
def dq22 (τ₁ τ₂ : K) : Fin 4 → K := ![2 * τ₁ / τ₂, -(τ₁ - τ₂) * (τ₁ + τ₂) / τ₂ ^ 2, 0, 0]

/-- `dP₁` (its `β, λ` components are the A.4 Jacobian entries). -/
def dP1 (τ₁ τ₂ β lam : K) : Fin 4 → K :=
  ![β / τ₂, β * (lam - τ₁) / τ₂ ^ 2, dP1_dβ τ₁ τ₂ lam, dP1_dlam τ₂ β]

/-- `dP₂` (its `β, λ` components are the A.4 Jacobian entries). -/
def dP2 (τ₁ τ₂ β lam : K) : Fin 4 → K :=
  ![β * (lam - τ₁) / τ₂ ^ 2, β * (lam - τ₁) ^ 2 / τ₂ ^ 3, dP2_dβ τ₁ τ₂ lam,
    dP2_dlam τ₁ τ₂ β lam]

/-- `dτ₁`. -/
def dτ1 : Fin 4 → K := ![1, 0, 0, 0]

/-- `dτ₂`. -/
def dτ2 : Fin 4 → K := ![0, 1, 0, 0]

set_option linter.unnecessarySeqFocus false in
/-- **Symplectic match** (Theorem A.5(iii)): on the four-parameter family,
`Σ_{A,B} dπ^{AB} ∧ dq̂_AB = −2 (dP₁ ∧ dτ₁ + dP₂ ∧ dτ₂)`, as `4×4` antisymmetric
coefficient matrices in the `(dτ₁, dτ₂, dβ, dλ)` basis.  The sum runs over all four
ordered pairs `(A, B)`, so the symmetric off-diagonal term appears twice.
(With the ADM prefactor `1/16πG` this is the `(1/8πG) ω_can` of the manuscript, up
to the overall sign fixed by the orientation of the normal.) -/
theorem A5_symplectic_match (τ₁ τ₂ β lam : K) (hτ : τ₂ ≠ 0) :
    wedge (dpi11 τ₁ τ₂ β lam) (dq11 τ₂)
      + (2 : K) • wedge (dpi12 τ₁ τ₂ β lam) (dq12 τ₁ τ₂)
      + wedge (dpi22 τ₁ τ₂ β lam) (dq22 τ₁ τ₂)
    = (-2 : K) • (wedge (dP1 τ₁ τ₂ β lam) dτ1 + wedge (dP2 τ₁ τ₂ β lam) dτ2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [wedge, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      dpi11, dpi12, dpi22, dq11, dq12, dq22, dP1, dP2, dτ1, dτ2,
      dP1_dβ, dP1_dlam, dP2_dβ, dP2_dlam, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val] <;>
    field_simp <;> ring

end CharNeTwo

/-! ### 6. Trace decoupling -/

/-- The 1-form `d(det q̂) = q̂₂₂ dq̂₁₁ + q̂₁₁ dq̂₂₂ − 2 q̂₁₂ dq̂₁₂` (product rule on the
literal partials). -/
def ddet_qhat (τ₁ τ₂ : K) : Fin 4 → K :=
  fun μ => (τ₁ ^ 2 + τ₂ ^ 2) / τ₂ * dq11 τ₂ μ + 1 / τ₂ * dq22 τ₁ τ₂ μ
    - 2 * (τ₁ / τ₂) * dq12 τ₁ τ₂ μ

set_option linter.unnecessarySeqFocus false in
/-- **Trace decoupling** (Theorem A.5(iii), load-bearing clause): `det q̂ = 1` and
`d(det q̂) = 0` along all four coordinates, so `δq̂` is automatically trace-free and
the trace sector of the momentum cannot contribute. -/
theorem A5_trace_decoupling (τ₁ τ₂ : K) (hτ : τ₂ ≠ 0) :
    (qhat τ₁ τ₂).det = 1 ∧ ddet_qhat τ₁ τ₂ = 0 := by
  refine ⟨A5_qhat_det τ₁ τ₂ hτ, ?_⟩
  ext μ
  fin_cases μ <;> simp [ddet_qhat, dq11, dq12, dq22] <;> field_simp <;> ring

/-! ### §4.4 slice facts (bonus) -/

/-- The Lorentzian pairing with `η = diag(−1, 1)`. -/
def lpair (a b : Fin 2 → K) : K := -(a 0 * b 0) + a 1 * b 1

/-- **Area–boost pair** (§4.4): with `n = (ch, sh)`, `s = (sh, ch)`, `ch² − sh² = 1`,
`Ẽ = sq • s`, and two formal variations `(dsq₁, dφ₁)`, `(dsq₂, dφ₂)` (so
`dn_k = dφ_k s`, `dẼ_k = dsq_k s + sq dφ_k n`), the antisymmetrised pairing
`⟨dẼ₁, dn₂⟩ − ⟨dẼ₂, dn₁⟩` equals `dsq₁ dφ₂ − dsq₂ dφ₁`. -/
theorem A44_boost_pair (ch sh sq dsq1 dsq2 dφ1 dφ2 : K) (hch : ch ^ 2 - sh ^ 2 = 1) :
    lpair (dsq1 • ![sh, ch] + (sq * dφ1) • ![ch, sh]) (dφ2 • ![sh, ch])
      - lpair (dsq2 • ![sh, ch] + (sq * dφ2) • ![ch, sh]) (dφ1 • ![sh, ch])
      = dsq1 * dφ2 - dsq2 * dφ1 := by
  simp only [lpair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (dsq1 * dφ2 - dsq2 * dφ1) * hch

/-- The implicit derivative `∂s/∂τ₂ = −s/(2τ₂)` is the value consistent with
differentiating the constraint `s² τ₂ = 1`: `2 s (∂s/∂τ₂) τ₂ + s² = 0`. -/
theorem A44_ds_consistent (s τ₂ : K) [NeZero (2 : K)] (hτ : τ₂ ≠ 0) :
    2 * s * (-s / (2 * τ₂)) * τ₂ + s ^ 2 = 0 := by
  field_simp
  ring

/-- **Coframe 2-form** (§4.4): for the unit-area coframe `ê₁ = (s, 0)`,
`ê₂ = (sτ₁, sτ₂)` with `ds = −s/(2τ₂) dτ₂`, the `dτ₁ ∧ dτ₂` coefficient of
`2 Σ_a dê^a_1 ∧ dê^a_2` is `1/τ₂²`.  The `(dτ₁, dτ₂)` coefficient vectors are
`dê¹₁ = (0, −s/(2τ₂))`, `dê²₁ = (0, 0)`, `dê¹₂ = (s, −sτ₁/(2τ₂))`, `dê²₂ = (0, s/2)`. -/
theorem A44_coframe_form (s τ₁ τ₂ : K) [NeZero (2 : K)] (hs : s ^ 2 * τ₂ = 1) :
    2 * ((0 * (-s * τ₁ / (2 * τ₂)) - (-s / (2 * τ₂)) * s)
          + (0 * (s / 2) - 0 * 0)) = 1 / τ₂ ^ 2 := by
  have hs0 := s_ne_zero hs
  obtain rfl := tau2_eq hs
  field_simp
  ring

end MacadayPhysicsLean.MoncriefA5
