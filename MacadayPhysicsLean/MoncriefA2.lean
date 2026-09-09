/-
Moncrief letter (Paper M) — Theorem A.2 insurance formalisation.

A machine check of the headline algebra of Theorem A.2, public since the Paper M
staging of July 2026 (tag v1.0).  The Theorem A.4 (fixed-area slice) extension
lives in `MoncriefA4`, which imports this file.

Contents (spec Part 3):
* 3a(i)  `family_flat` — flatness + torsion-free of the four-parameter family,
  stated for an *arbitrary alternating bilinear map* (the letter's proof uses
  only bilinearity + the alternating property).
* 3a(ii) `symplectic_2form_identity` — the Chern–Simons symplectic-coefficient
  2-form identity, as antisymmetric-matrix equality over any commutative ring.
* 3a(iii) `family_jacobian_det` — the `(β,λ) ↦ (p₁,p₂)` Jacobian is `p₂`.
* 3b `real_proportional_of_im_zero` — g = 1 Ricci real-proportionality.
* 3d `york_jacobian_det` — the York-map Jacobian is `-1/(4τ₂)`.
* 3e `S_chart_im`, `TS_chart_im` — SL(2,ℤ) chart-coverage identities.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace MacadayPhysicsLean.MoncriefA2

/-! ### 3a(i) — Flatness of the four-parameter family

The letter's family: `ω₁ = β(e₂ − λe₁)`, `ω₂ = λω₁`.  Flatness and torsion-free
are `B ω₁ ω₂ = 0` and `B ω₁ e₂ = B ω₂ e₁` for the so(2,1) cross product `B`.
The proof uses only that `B` is bilinear and alternating (`B v v = 0`), so we
prove it at that generality — convention-independent. -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- An alternating bilinear map is skew: `B x y = - B y x`. -/
theorem alt_skew (B : M →ₗ[R] M →ₗ[R] N) (halt : ∀ v, B v v = 0) (x y : M) :
    B x y = - B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [halt x, halt y] at h
  -- h : 0 + B x y + (B y x + 0) = 0
  linear_combination (norm := module) h

/-- **Flatness + torsion-free of the four-parameter family** (Theorem A.2(i)).

For any alternating bilinear `B`, with `ω₁ = β • (e₂ − λ • e₁)` and `ω₂ = λ • ω₁`:
`B ω₁ ω₂ = 0` (flatness) and `B ω₁ e₂ = B ω₂ e₁` (torsion-free). -/
theorem family_flat (B : M →ₗ[R] M →ₗ[R] N) (halt : ∀ v, B v v = 0)
    (e₁ e₂ : M) (β lam : R) :
    B (β • (e₂ - lam • e₁)) (lam • (β • (e₂ - lam • e₁))) = 0 ∧
      B (β • (e₂ - lam • e₁)) e₂ = B (lam • (β • (e₂ - lam • e₁))) e₁ := by
  set w : M := e₂ - lam • e₁ with hw
  refine ⟨?_, ?_⟩
  · -- flatness: everything collapses to `B w w = 0`
    simp only [map_smul, LinearMap.smul_apply, halt w, smul_zero]
  · -- torsion-free: expand `w`, use `halt` on `e₁,e₂` and the skew relation
    have hwe₂ : B w e₂ = - lam • B e₁ e₂ := by
      rw [hw, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, halt e₂,
        zero_sub, neg_smul]
    have hwe₁ : B w e₁ = - B e₁ e₂ := by
      rw [hw, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, halt e₁,
        smul_zero, sub_zero, alt_skew B halt e₂ e₁, alt_skew B halt e₁ e₂, neg_neg]
    simp only [map_smul, LinearMap.smul_apply, hwe₂, hwe₁]
    module

/-! ### 3a(ii) — The symplectic-coefficient 2-form identity

Coordinate basis `(dτ₁, dτ₂, dβ, dλ)` indexed by `Fin 4` (0,1,2,3).  A 1-form is a
`Fin 4 → R` coefficient vector; the wedge of two 1-forms `u ∧ v` is the
antisymmetric matrix `uᵢvⱼ − uⱼvᵢ`.  With `p₁ = β(τ₁ − λ)`, `p₂ = βτ₂`:
`dp₁ = β dτ₁ + (τ₁−λ) dβ − β dλ`, `dp₂ = β dτ₂ + τ₂ dβ`. -/

/-- The wedge of two 1-forms as an antisymmetric `4×4` matrix. -/
def wedge (u v : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of (fun i j => u i * v j - u j * v i)

/-- **The Chern–Simons symplectic-coefficient identity** (Theorem A.2(ii)):
`dp₁ ∧ dτ₁ + dp₂ ∧ dτ₂ = (τ₁−λ) dβ∧dτ₁ − β dλ∧dτ₁ + τ₂ dβ∧dτ₂`, for all
`τ₁, τ₂, β, λ` in any commutative ring. -/
theorem symplectic_2form_identity (τ₁ τ₂ β lam : R) :
    wedge (fun i => (![β, 0, τ₁ - lam, -β] : Fin 4 → R) i) (![1, 0, 0, 0])
      + wedge (![0, β, τ₂, 0]) (![0, 1, 0, 0])
    = (τ₁ - lam) • wedge (![0, 0, 1, 0]) (![1, 0, 0, 0])
      - β • wedge (![0, 0, 0, 1]) (![1, 0, 0, 0])
      + τ₂ • wedge (![0, 0, 1, 0]) (![0, 1, 0, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedge, Matrix.add_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### 3a(iii) — Local symplectomorphism on `p₂ ≠ 0` -/

/-- **The family Jacobian is `p₂`** (Theorem A.2(iii)): at fixed `τ`, the map
`(β, λ) ↦ (p₁, p₂)` has Jacobian determinant `βτ₂ = p₂`. -/
theorem family_jacobian_det (τ₁ τ₂ β : R) :
    (Matrix.of ![![τ₁ - 0, -β], ![τ₂, 0]] : Matrix (Fin 2) (Fin 2) R).det = β * τ₂ := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ### 3b — g = 1 Ricci real-proportionality

On the torus, quadratic differentials are constants, so §4.2 reduces to a
statement about two complex numbers.  If `Im(conj c₀ · c₁) = 0` and `c₀ ≠ 0`,
they are real-proportional. -/

/-- **Real proportionality** (torus case, spec 3b). -/
theorem real_proportional_of_im_zero (c₀ c₁ : ℂ) (h0 : c₀ ≠ 0)
    (him : (starRingEnd ℂ c₀ * c₁).im = 0) :
    ∃ lam : ℝ, c₁ = (lam : ℂ) * c₀ := by
  refine ⟨(starRingEnd ℂ c₀ * c₁).re / Complex.normSq c₀, ?_⟩
  have hnorm : (Complex.normSq c₀ : ℂ) ≠ 0 := by
    simpa using (Complex.normSq_pos.mpr h0).ne'
  -- `conj c₀ * c₁` is real, equal to its real part
  have hreal : starRingEnd ℂ c₀ * c₁ = ((starRingEnd ℂ c₀ * c₁).re : ℂ) := by
    simp [Complex.ext_iff, him]
  have hkey : c₀ * (starRingEnd ℂ c₀ * c₁) = (Complex.normSq c₀ : ℂ) * c₁ := by
    rw [← mul_assoc, Complex.mul_conj]
  rw [hreal] at hkey
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hnorm]
  linear_combination -hkey

/-! ### 3d — York-map Jacobian -/

/-- **The York-map Jacobian is `-1/(4τ₂)`** (spec 3d), hence nonzero for `τ₂ > 0`.
The map `(h₁,h₂) ↦ (Re f, Im f)` with `f = h₁/2 − i(h₂−h₁τ₁)/(2τ₂)` sends
`(h₁,h₂) ↦ (h₁/2, (h₁τ₁−h₂)/(2τ₂))`. -/
theorem york_jacobian_det (τ₁ τ₂ : ℝ) (hτ : τ₂ ≠ 0) :
    (Matrix.of ![![(1:ℝ)/2, 0], ![τ₁/(2*τ₂), -1/(2*τ₂)]] :
      Matrix (Fin 2) (Fin 2) ℝ).det = -1/(4*τ₂) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-! ### 3e — SL(2,ℤ) chart coverage

Under `τ' = (aτ+b)/(cτ+d)`, `p' = (cτ+d)² p`.  Two coverage claims (with
`p = p₁ + i p₂`, `τ = τ₁ + i τ₂`), verified as complex-algebra identities. -/

/-- **S-chart** (`τ → −1/τ`, so `c=1,d=0`, `p' = τ² p`): if `p₂ = 0` and `τ₁ ≠ 0`,
then `Im(p') = 2 τ₁ τ₂ p₁ ≠ 0`. -/
theorem S_chart_im (p₁ τ₁ τ₂ : ℝ) :
    (((τ₁ : ℂ) + τ₂ * Complex.I) ^ 2 * (p₁ + (0 : ℝ) * Complex.I)).im
      = 2 * τ₁ * τ₂ * p₁ := by
  rw [pow_two]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **TS-chart** (`τ → −1/(τ+1)`, so `c=1,d=1`, `p' = (τ+1)² p`): if `p₂ = 0` and
`τ₁ = 0`, then `Im(p') = 2 τ₂ p₁ ≠ 0`. -/
theorem TS_chart_im (p₁ τ₂ : ℝ) :
    ((((0 : ℝ) : ℂ) + τ₂ * Complex.I + 1) ^ 2 * (p₁ + (0 : ℝ) * Complex.I)).im
      = 2 * τ₂ * p₁ := by
  rw [pow_two]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.one_im, Complex.one_re, Complex.I_im, Complex.I_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

end MacadayPhysicsLean.MoncriefA2
