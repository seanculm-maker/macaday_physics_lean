/-
Klein's inequality — Stage 0 nonnegativity of quantum relative entropy
(Paper R `relEntropy_nonneg`).

  `D(ρ‖σ) ≥ 0`   for faithful σ

This is the linchpin: it turns `coherence_le_total_defect` (§4.3) unconditional
and is a prerequisite for the Stage-2 minimiser. The proof reuses the repo's
existing doubly-stochastic machinery.

Route: writing `ρ = Σᵢ pᵢ|eᵢ⟩⟨eᵢ|`, `σ = Σⱼ qⱼ|fⱼ⟩⟨fⱼ|` (both faithful, so
`qⱼ > 0`), the mixed trace becomes

  `Tr(ρ log σ) = Σᵢ pᵢ Σⱼ Mᵢⱼ log qⱼ`,   `Mᵢⱼ = |⟨eᵢ|fⱼ⟩|²`

with `M` doubly stochastic (rows/columns of a unitary). Concavity of `log`
(Jensen) gives `Σⱼ Mᵢⱼ log qⱼ ≤ log rᵢ` with `rᵢ = Σⱼ Mᵢⱼ qⱼ`, `Σᵢ rᵢ = 1`,
whence `D(ρ‖σ) ≥ Σᵢ pᵢ log(pᵢ/rᵢ) = D_KL(p‖r) ≥ 0` by `log x ≤ x − 1`.
-/

import MacadayPhysicsLean.RelativeEntropy
import MacadayPhysicsLean.RelEntropyPinching
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Real Finset Unitary
open scoped ComplexOrder

variable {n : ℕ}

namespace DensityOp

/-- The unitary bridging the two eigenbases: `W = Up⋆ · Uq` (as a genuine
unitary matrix), whose squared moduli `|Wᵢⱼ|²` form the classical mixing
(doubly-stochastic) matrix. -/
noncomputable def crossW (ρ σ : DensityOp n) : Matrix (Fin n) (Fin n) ℂ :=
  ((star ρ.isHermitian.eigenvectorUnitary * σ.isHermitian.eigenvectorUnitary :
    unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)

/-- Trace of a `D₁ · W · D₂ · W⋆` sandwich, entrywise:
`Tr = Σᵢ Σⱼ (d₁ᵢ)(d₂ⱼ)|Wᵢⱼ|²`. -/
theorem trace_diagonal_mul_conj (d1 d2 : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    (diagonal d1 * W * diagonal d2 * Wᴴ).trace
      = ∑ i, ∑ j, d1 i * d2 j * (W i j * star (W i j)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Trace is invariant under unitary conjugation `X ↦ U X U⋆`. -/
theorem trace_conjStarAlgAut (V : unitary (Matrix (Fin n) (Fin n) ℂ))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (conjStarAlgAut ℂ _ V X).trace = X.trace := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul]

/-- **Cross-trace identity** (the crux of Klein's inequality).

`Tr(ρ · f(σ)) = Σᵢ Σⱼ λᵢ(ρ) · f(λⱼ(σ)) · |Wᵢⱼ|²`, where `W = crossW ρ σ` is the
unitary connecting the two eigenbases. Proved by conjugating into ρ's
eigenbasis (trace-invariant), diagonalizing ρ there, and expanding the
sandwiched `f(σ)`. -/
theorem trace_mul_cfc_cross (ρ σ : DensityOp n) (f : ℝ → ℝ) :
    (ρ.M * σ.isHermitian.cfc f).trace
      = ∑ i, ∑ j, (ρ.eigenvalues i : ℂ) * (f (σ.eigenvalues j) : ℂ)
          * (crossW ρ σ i j * star (crossW ρ σ i j)) := by
  set Up := ρ.isHermitian.eigenvectorUnitary with hUp
  set Uq := σ.isHermitian.eigenvectorUnitary with hUq
  -- conjugate the whole product into ρ's eigenbasis
  rw [← trace_conjStarAlgAut (star Up) (ρ.M * σ.isHermitian.cfc f), map_mul]
  -- conjStarAlgAut (star Up) ρ.M = diagonal (ρ's eigenvalues)
  rw [ρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  -- σ.cfc f = conjStarAlgAut Uq (diagonal f∘q); compose the two conjugations
  change (diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues)
      * conjStarAlgAut ℂ _ (star Up)
          (conjStarAlgAut ℂ _ Uq
            (diagonal (RCLike.ofReal ∘ f ∘ σ.isHermitian.eigenvalues)))).trace = _
  rw [← conjStarAlgAut_mul_apply, conjStarAlgAut_apply, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.star_eq_conjTranspose, trace_diagonal_mul_conj]
  simp only [Function.comp_apply, DensityOp.eigenvalues, DensityOp.crossW, hUp, hUq]
  rfl

/-! ### The classical mixing matrix `Mᵢⱼ = |Wᵢⱼ|²` is doubly stochastic -/

/-- `z · z⋆ = |z|²` as a complex number. -/
theorem mul_star_eq_normSq (z : ℂ) : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [← starRingEnd_apply, Complex.mul_conj]

/-- The doubly-stochastic mixing matrix of squared overlaps. -/
noncomputable def mixing (ρ σ : DensityOp n) (i j : Fin n) : ℝ :=
  Complex.normSq (crossW ρ σ i j)

theorem mixing_nonneg (ρ σ : DensityOp n) (i j : Fin n) : 0 ≤ mixing ρ σ i j :=
  Complex.normSq_nonneg _

theorem crossW_mul_conjTranspose (ρ σ : DensityOp n) :
    crossW ρ σ * (crossW ρ σ)ᴴ = 1 := by
  rw [crossW, ← Matrix.star_eq_conjTranspose]
  exact mem_unitaryGroup_iff.mp (Subtype.property _)

theorem crossW_conjTranspose_mul (ρ σ : DensityOp n) :
    (crossW ρ σ)ᴴ * crossW ρ σ = 1 := by
  rw [crossW, ← Matrix.star_eq_conjTranspose]
  exact Matrix.UnitaryGroup.star_mul_self _

/-- Row sums of the mixing matrix are 1 (each row of a unitary has norm 1). -/
theorem mixing_row_sum (ρ σ : DensityOp n) (i : Fin n) : ∑ j, mixing ρ σ i j = 1 := by
  have h := congrArg (fun A => A i i) (crossW_mul_conjTranspose ρ σ)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have hc : (∑ j, (mixing ρ σ i j : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mixing, ← mul_star_eq_normSq]
  exact_mod_cast hc

/-- Column sums of the mixing matrix are 1. -/
theorem mixing_col_sum (ρ σ : DensityOp n) (j : Fin n) : ∑ i, mixing ρ σ i j = 1 := by
  have h := congrArg (fun A => A j j) (crossW_conjTranspose_mul ρ σ)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have hc : (∑ i, (mixing ρ σ i j : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mixing, ← mul_star_eq_normSq, mul_comm]
  exact_mod_cast hc

/-! ### Classical Klein inequality (pure real analysis) -/

/-- The classical core of Klein's inequality: for probability vectors `p, q`
(`q` strictly positive) and a doubly-stochastic kernel `M`,

  `Σᵢ Σⱼ pᵢ log(qⱼ) Mᵢⱼ ≤ Σᵢ pᵢ log pᵢ`.

Jensen (log concave) with `rᵢ = Σⱼ Mᵢⱼ qⱼ` (a probability vector), then
`log x ≤ x − 1` gives the residual `D_KL(p‖r) ≥ 0`. -/
theorem klein_classical (p q : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ j, 0 < q j) (hqsum : ∑ j, q j = 1)
    (hM : ∀ i j, 0 ≤ M i j) (hMrow : ∀ i, ∑ j, M i j = 1) (hMcol : ∀ j, ∑ i, M i j = 1) :
    (∑ i, ∑ j, p i * Real.log (q j) * M i j) ≤ ∑ i, p i * Real.log (p i) := by
  set r : Fin n → ℝ := fun i => ∑ j, M i j * q j with hr
  have hr_pos : ∀ i, 0 < r i := by
    intro i
    obtain ⟨j0, hj0⟩ : ∃ j, 0 < M i j := by
      by_contra hc; simp only [not_exists, not_lt] at hc
      have hz : ∑ j, M i j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (hc j) (hM i j))
      rw [hMrow i] at hz; exact one_ne_zero hz
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hM i j) (hq j).le)
      ⟨j0, Finset.mem_univ _, mul_pos hj0 (hq j0)⟩
  have hr_sum : ∑ i, r i = 1 := by
    simp only [hr]; rw [Finset.sum_comm]
    calc ∑ j, ∑ i, M i j * q j = ∑ j, (∑ i, M i j) * q j := by
            refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.sum_mul]
      _ = ∑ j, q j := by refine Finset.sum_congr rfl (fun j _ => ?_); rw [hMcol j, one_mul]
      _ = 1 := hqsum
  have hjensen : ∀ i, ∑ j, M i j * Real.log (q j) ≤ Real.log (r i) := by
    intro i
    have hcc := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := Finset.univ) (fun j _ => hM i j) (hMrow i) (fun j (_ : j ∈ Finset.univ) => hq j)
    simp only [smul_eq_mul] at hcc
    exact hcc
  calc ∑ i, ∑ j, p i * Real.log (q j) * M i j
      = ∑ i, p i * (∑ j, M i j * Real.log (q j)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ ∑ i, p i * Real.log (r i) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left (hjensen i) (hp i)
    _ ≤ ∑ i, p i * Real.log (p i) := by
        have key : ∀ i, p i * Real.log (r i) - p i * Real.log (p i) ≤ r i - p i := by
          intro i
          rcases eq_or_lt_of_le (hp i) with hpi | hpi
          · simp only [← hpi, zero_mul, sub_zero]; exact (hr_pos i).le
          · have hlog : Real.log (r i) - Real.log (p i) = Real.log (r i / p i) :=
              (Real.log_div (hr_pos i).ne' hpi.ne').symm
            have hb : Real.log (r i / p i) ≤ r i / p i - 1 :=
              Real.log_le_sub_one_of_pos (div_pos (hr_pos i) hpi)
            have hmul : p i * (Real.log (r i) - Real.log (p i)) ≤ p i * (r i / p i - 1) := by
              rw [hlog]; exact mul_le_mul_of_nonneg_left hb hpi.le
            rw [mul_sub, mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one] at hmul
            linarith [hmul]
        have hsum : ∑ i, (p i * Real.log (r i) - p i * Real.log (p i)) ≤ ∑ i, (r i - p i) :=
          Finset.sum_le_sum (fun i _ => key i)
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hr_sum, hpsum, sub_self] at hsum
        linarith [hsum]

/-! ### Klein's inequality: nonnegativity of quantum relative entropy -/

/-- **Klein's inequality** (Paper R Stage 0 `relEntropy_nonneg`).
For a faithful (positive-definite) prior `σ`, `D(ρ‖σ) ≥ 0`. -/
theorem relEntropy_nonneg (ρ σ : DensityOp n) (hσ : σ.M.PosDef) :
    0 ≤ relativeEntropy ρ σ := by
  have hq : ∀ j, 0 < σ.eigenvalues j := fun j => hσ.eigenvalues_pos j
  have hself : (ρ.M * ρ.logM).trace.re
      = ∑ i, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
    rw [logM, trace_mul_cfc_self, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Complex.mul_re]
  have hcross : (ρ.M * σ.logM).trace.re
      = ∑ i, ∑ j, ρ.eigenvalues i * Real.log (σ.eigenvalues j) * mixing ρ σ i j := by
    rw [logM, trace_mul_cfc_cross, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_star_eq_normSq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
      mixing]
  rw [relativeEntropy, hself, hcross]
  have hpsum : ∑ i, ρ.eigenvalues i = 1 := by
    have ht := congrArg Complex.re ρ.isHermitian.trace_eq_sum_eigenvalues
    rw [ρ.trace_one] at ht
    simp only [Complex.one_re, Complex.re_sum, DensityOp.eigenvalues] at ht ⊢
    simpa using ht.symm
  have hqsum : ∑ j, σ.eigenvalues j = 1 := by
    have ht := congrArg Complex.re σ.isHermitian.trace_eq_sum_eigenvalues
    rw [σ.trace_one] at ht
    simp only [Complex.one_re, Complex.re_sum, DensityOp.eigenvalues] at ht ⊢
    simpa using ht.symm
  have hcl := klein_classical ρ.eigenvalues σ.eigenvalues (mixing ρ σ)
    (fun i => ρ.eigenvalues_nonneg i) hpsum hq hqsum
    (fun i j => mixing_nonneg ρ σ i j) (fun i => mixing_row_sum ρ σ i)
    (fun j => mixing_col_sum ρ σ j)
  linarith [hcl]

end DensityOp

/-- **`coherence_le_total_defect`, now UNCONDITIONAL** (Paper R §4.3).

With Klein's inequality proved, the coherence bound `D(ρ‖Δρ) ≤ D(ρ‖ρ*)` holds
outright for any faithful, block-diagonal equilibrium `ρ*` — no hypothesis on the
relative entropy is assumed. This is the inequality Papers D, S1, S2, G, LA, MP,
GB consume via `‖ρ − Δρ‖₁ ≤ √(2δ)` (quantum Pinsker, cited). -/
theorem coherence_le_total_defect_unconditional
    {n m : ℕ} (P : Pinching.ProjectorFamily n m) (ρ ρ_star : DensityOp n)
    (hcomm : ∀ k, Commute ρ_star.M (P.proj k)) (hpos : ρ_star.M.PosDef) :
    DensityOp.relativeEntropy ρ (Pinching.pinchDensityOp P ρ)
      ≤ DensityOp.relativeEntropy ρ ρ_star := by
  have hpyth := pinching_pythagorean P ρ ρ_star hcomm
  have hnn := DensityOp.relEntropy_nonneg (Pinching.pinchDensityOp P ρ) ρ_star hpos
  linarith

end MacadayPhysicsLean
