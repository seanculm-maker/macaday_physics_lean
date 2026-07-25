/-
Equality case of Klein's inequality — `D(ρ‖σ) = 0 ⟺ ρ = σ`
(Paper R Stage-0 `relEntropy_eq_zero_iff`; the forward direction is
Stage-2 load-bearing: the minimiser's conditional-preservation is exactly
`Σ_λ p_λ D(τ_λ‖σ_λ) = 0 ⇒ τ_λ = σ_λ`).

This reuses the machinery already verified in `RelEntropyKlein`:

* equality in `log x ≤ x − 1` (`Real.log_lt_sub_one_of_pos`, strict off `x = 1`)
  forces the classical `D_KL(p‖r) = 0`, hence `p = r = M q` and — since the
  prior is faithful — `p` is strictly positive;
* the equality case of Jensen for the strictly concave `log`
  (`StrictConcaveOn.eq_of_map_sum_eq`) forces `qⱼ` constant on each positive
  row-support `{j : Mᵢⱼ > 0}`, with common value `pᵢ`.

Both halves are proved here: the **classical extraction**
(`klein_classical_eq_zero`) and the **operator reconstruction**
(`relEntropy_eq_zero`).  The reconstruction does not chase eigenvectors: the
classical extraction gives `Wᵢⱼ qⱼ = pᵢ Wᵢⱼ` for *all* `i, j`, so conjugating
`σ` into `ρ`'s eigenbasis collapses `W D_q W⋆` to `pᵢ · (W W⋆) = D_p` in one
step, which is `ρ` in the same basis; injectivity of the conjugation finishes.
Since every `pᵢ > 0`, no PSD-plus-trace argument is needed.
-/

import MacadayPhysicsLean.RelEntropyKlein
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Real Finset Unitary
open scoped ComplexOrder

variable {n : ℕ}

namespace DensityOp

/-- **Classical extraction from the equality case.**

Under the doubly-stochastic hypotheses of `klein_classical`, if the defining
inequality is in fact an equality (`D = 0`), then every prior weight is
strictly positive, and `qⱼ = pᵢ` whenever `Mᵢⱼ > 0`. -/
theorem klein_classical_eq_zero (p q : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ j, 0 < q j) (hqsum : ∑ j, q j = 1)
    (hM : ∀ i j, 0 ≤ M i j) (hMrow : ∀ i, ∑ j, M i j = 1) (hMcol : ∀ j, ∑ i, M i j = 1)
    (hD : (∑ i, ∑ j, p i * Real.log (q j) * M i j) = ∑ i, p i * Real.log (p i)) :
    (∀ i, 0 < p i) ∧ (∀ i j, 0 < M i j → q j = p i) := by
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
  -- Jensen slack Sᵢ = log rᵢ − Σⱼ Mᵢⱼ log qⱼ ≥ 0
  have hjensen : ∀ i, ∑ j, M i j * Real.log (q j) ≤ Real.log (r i) := by
    intro i
    have hcc := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := Finset.univ) (fun j _ => hM i j) (hMrow i) (fun j (_ : j ∈ Finset.univ) => hq j)
    simp only [smul_eq_mul] at hcc; exact hcc
  -- KL term Aᵢ = pᵢ log pᵢ − pᵢ log rᵢ, with pᵢ log(pᵢ/rᵢ) ≥ pᵢ − rᵢ
  have hkl_term : ∀ i, p i - r i ≤ p i * Real.log (p i) - p i * Real.log (r i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · simp only [← hpi, zero_mul, sub_zero]; linarith [(hr_pos i).le]
    · have hb : Real.log (r i / p i) ≤ r i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hr_pos i) hpi)
      have hlog : Real.log (r i) - Real.log (p i) = Real.log (r i / p i) :=
        (Real.log_div (hr_pos i).ne' hpi.ne').symm
      have : p i * (Real.log (r i) - Real.log (p i)) ≤ r i - p i := by
        rw [hlog]
        calc p i * Real.log (r i / p i) ≤ p i * (r i / p i - 1) :=
              mul_le_mul_of_nonneg_left hb hpi.le
          _ = r i - p i := by rw [mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one]
      linarith [this]
  -- reindex the D-defining double sum into `∑ᵢ pᵢ (∑ⱼ Mᵢⱼ log qⱼ)`
  have hDrw : (∑ i, p i * (∑ j, M i j * Real.log (q j))) = ∑ i, p i * Real.log (p i) := by
    rw [← hD]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
  -- Total slack Σᵢ [pᵢ Sᵢ + (Aᵢ − (pᵢ − rᵢ))] = 0, each summand ≥ 0
  have hslack_nonneg : ∀ i, 0 ≤ p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)) := by
    intro i; exact mul_nonneg (hp i) (by linarith [hjensen i])
  have hAterm_nonneg : ∀ i, 0 ≤ (p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i) := by
    intro i; linarith [hkl_term i]
  have htotal : (∑ i, (p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
      + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i)))) = 0 := by
    have hcong : (∑ i, (p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
        + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i))))
        = ∑ i, (p i * Real.log (p i) - p i * (∑ j, M i j * Real.log (q j)) - (p i - r i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [hcong, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hDrw, hpsum, hr_sum]; ring
  -- each summand is 0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
      + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i)) :=
    fun i _ => add_nonneg (hslack_nonneg i) (hAterm_nonneg i)
  have hzero : ∀ i, p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
      + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i)) = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htotal i (Finset.mem_univ i)
  -- ⇒ pᵢ > 0 (else the KL term is rᵢ > 0) and rᵢ = pᵢ
  have hp_pos : ∀ i, 0 < p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · exfalso
      have h0 := hzero i
      rw [← hpi] at h0
      simp only [zero_mul, sub_zero, zero_sub, neg_neg] at h0
      -- h0 : 0 + (0 - (0 - r i)) = 0  ⇒  r i = 0, contradicting r i > 0
      have : r i = 0 := by linarith [h0]
      exact absurd this (hr_pos i).ne'
    · exact hpi
  have hr_eq_p : ∀ i, r i = p i := by
    intro i
    have h0 := hzero i
    have hs := hslack_nonneg i
    have hA := hAterm_nonneg i
    -- both nonneg summands are individually 0
    have hAz : (p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i) = 0 := by linarith
    -- for pᵢ > 0, equality in log forces rᵢ = pᵢ
    by_contra hne
    have hpi := hp_pos i
    have hstrict : Real.log (r i / p i) < r i / p i - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos (hr_pos i) hpi) (by
        rw [ne_eq, div_eq_one_iff_eq hpi.ne']; exact hne)
    have hlog : Real.log (r i) - Real.log (p i) = Real.log (r i / p i) :=
      (Real.log_div (hr_pos i).ne' hpi.ne').symm
    have : p i * (Real.log (r i) - Real.log (p i)) < r i - p i := by
      rw [hlog]
      calc p i * Real.log (r i / p i) < p i * (r i / p i - 1) :=
            mul_lt_mul_of_pos_left hstrict hpi
        _ = r i - p i := by rw [mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one]
    linarith [hAz]
  -- Jensen equality ⇒ q constant on positive row-support, value = rᵢ = pᵢ
  refine ⟨hp_pos, fun i j hMij => ?_⟩
  have hSz : p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)) = 0 := by
    have h0 := hzero i; have hA := hAterm_nonneg i; have hs := hslack_nonneg i; linarith
  have hSeq : Real.log (r i) = ∑ j, M i j * Real.log (q j) := by
    have := (mul_eq_zero.mp hSz).resolve_left (hp_pos i).ne'
    linarith [this]
  -- restrict to the support S = {j : 0 < M i j}; there weights are positive
  set S : Finset (Fin n) := Finset.univ.filter (fun j => 0 < M i j) with hS
  have hout : ∀ k, k ∉ S → M i k = 0 := by
    intro k hk
    exact le_antisymm (not_lt.mp (fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)))
      (hM i k)
  have hSrow : ∑ j ∈ S, M i j = 1 := by
    rw [← hMrow i]
    exact Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hk => hout k hk)
  have hSsum_q : ∑ j ∈ S, M i j * q j = r i := by
    rw [hr]
    exact Finset.sum_subset (Finset.filter_subset _ _)
      (fun k _ hk => by rw [hout k hk, zero_mul])
  have hSsum_logq : ∑ j ∈ S, M i j * Real.log (q j) = ∑ j, M i j * Real.log (q j) :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hk => by rw [hout k hk, zero_mul])
  have hjS : Real.log (∑ j ∈ S, M i j • q j) = ∑ j ∈ S, M i j • Real.log (q j) := by
    simp only [smul_eq_mul, hSsum_q, hSsum_logq]; exact hSeq
  -- Jensen equality on S with positive weights ⇒ q constant on S
  have hconst := strictConcaveOn_log_Ioi.eq_of_map_sum_eq (t := S) (w := M i) (p := q)
    (fun k hk => (Finset.mem_filter.mp hk).2) hSrow (fun k _ => hq k) (le_of_eq hjS)
  have hjS_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hMij⟩
  -- rᵢ = qⱼ (all q on S equal qⱼ)
  have hri_qj : r i = q j := by
    rw [← hSsum_q]
    calc ∑ k ∈ S, M i k * q k = ∑ k ∈ S, M i k * q j := by
          refine Finset.sum_congr rfl (fun k hk => ?_); rw [hconst hk hjS_mem]
      _ = (∑ k ∈ S, M i k) * q j := by rw [Finset.sum_mul]
      _ = q j := by rw [hSrow, one_mul]
  rw [← hri_qj]; exact hr_eq_p i

/-! ### Relative entropy in classical form -/

/-- `D(ρ‖σ)` in eigenvalue + mixing-matrix form (the two halves already used
inside `relEntropy_nonneg`, exposed for the equality case). -/
theorem relativeEntropy_eq_classical (ρ σ : DensityOp n) :
    relativeEntropy ρ σ = (∑ i, ρ.eigenvalues i * Real.log (ρ.eigenvalues i))
      - ∑ i, ∑ j, ρ.eigenvalues i * Real.log (σ.eigenvalues j) * mixing ρ σ i j := by
  have hself : (ρ.M * ρ.logM).trace.re
      = ∑ i, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
    rw [logM, trace_mul_cfc_self, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_); simp [Complex.mul_re]
  have hcross : (ρ.M * σ.logM).trace.re
      = ∑ i, ∑ j, ρ.eigenvalues i * Real.log (σ.eigenvalues j) * mixing ρ σ i j := by
    rw [logM, trace_mul_cfc_cross, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_star_eq_normSq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
      mixing]
  rw [relativeEntropy, hself, hcross]

/-! ### Operator reconstruction: `D(ρ‖σ) = 0 ⇒ ρ = σ` -/

/-- **Equality case of Klein's inequality, forward direction.**

For a faithful prior `σ`, vanishing relative entropy forces `ρ = σ`.

Reconstruction route: the classical extraction gives `qⱼ = pᵢ` whenever
`Wᵢⱼ ≠ 0`, i.e. `Wᵢⱼ qⱼ = pᵢ Wᵢⱼ` for *all* `i, j`. Conjugating `σ` into `ρ`'s
eigenbasis therefore collapses `W D_q W⋆` to `pᵢ · (W W⋆) = D_p`, which is
exactly `ρ` conjugated into the same basis; injectivity of the conjugation
finishes. (All `pᵢ > 0`, so no PSD-plus-trace argument is needed.) -/
theorem relEntropy_eq_zero (ρ σ : DensityOp n) (hσ : σ.M.PosDef)
    (hD : relativeEntropy ρ σ = 0) : ρ.M = σ.M := by
  have hq : ∀ j, 0 < σ.eigenvalues j := fun j => hσ.eigenvalues_pos j
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
  -- classical extraction
  have hclass : (∑ i, ∑ j, ρ.eigenvalues i * Real.log (σ.eigenvalues j) * mixing ρ σ i j)
      = ∑ i, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
    have := relativeEntropy_eq_classical ρ σ
    rw [hD] at this; linarith [this]
  obtain ⟨hp_pos, hqp⟩ := klein_classical_eq_zero ρ.eigenvalues σ.eigenvalues (mixing ρ σ)
    (fun i => ρ.eigenvalues_nonneg i) hpsum hq hqsum
    (fun i j => mixing_nonneg ρ σ i j) (fun i => mixing_row_sum ρ σ i)
    (fun j => mixing_col_sum ρ σ j) hclass
  -- the multiplicative form `Wᵢⱼ qⱼ = pᵢ Wᵢⱼ`
  have hWq : ∀ i j, crossW ρ σ i j * (RCLike.ofReal (σ.isHermitian.eigenvalues j) : ℂ)
      = (RCLike.ofReal (ρ.isHermitian.eigenvalues i) : ℂ) * crossW ρ σ i j := by
    intro i j
    rcases eq_or_ne (crossW ρ σ i j) 0 with h0 | h0
    · rw [h0, zero_mul, mul_zero]
    · have hmix : 0 < mixing ρ σ i j := by
        rw [mixing]; exact Complex.normSq_pos.mpr h0
      rw [show σ.isHermitian.eigenvalues j = ρ.isHermitian.eigenvalues i from hqp i j hmix]
      ring
  -- conjugating σ into ρ's eigenbasis collapses to D_p
  have hWDW : crossW ρ σ * diagonal (RCLike.ofReal ∘ σ.isHermitian.eigenvalues)
      * (crossW ρ σ)ᴴ = diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues) := by
    funext i k
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply]
    have hstep : ∀ j, crossW ρ σ i j * (RCLike.ofReal (σ.isHermitian.eigenvalues j) : ℂ)
        * star (crossW ρ σ k j)
        = (RCLike.ofReal (ρ.isHermitian.eigenvalues i) : ℂ)
          * (crossW ρ σ i j * star (crossW ρ σ k j)) := by
      intro j; rw [hWq i j]; ring
    have hWW : ∑ j, crossW ρ σ i j * star (crossW ρ σ k j)
        = (1 : Matrix (Fin n) (Fin n) ℂ) i k := by
      conv_rhs => rw [← crossW_mul_conjTranspose ρ σ]
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hsum : (∑ j, crossW ρ σ i j * (RCLike.ofReal (σ.isHermitian.eigenvalues j) : ℂ)
        * star (crossW ρ σ k j))
        = (RCLike.ofReal (ρ.isHermitian.eigenvalues i) : ℂ)
          * ∑ j, (crossW ρ σ i j * star (crossW ρ σ k j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => hstep j)
    rw [hsum, hWW, Matrix.one_apply]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik]
  -- both conjugations agree, and conjugation is injective
  have hσconj : conjStarAlgAut ℂ _ (star ρ.isHermitian.eigenvectorUnitary) σ.M
      = diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues) := by
    have h1 : conjStarAlgAut ℂ _ (star ρ.isHermitian.eigenvectorUnitary) σ.M
        = conjStarAlgAut ℂ _
            (star ρ.isHermitian.eigenvectorUnitary * σ.isHermitian.eigenvectorUnitary)
            (diagonal (RCLike.ofReal ∘ σ.isHermitian.eigenvalues)) := by
      rw [conjStarAlgAut_mul_apply]
      exact congrArg _ σ.isHermitian.spectral_theorem
    rw [h1, conjStarAlgAut_apply, ← hWDW]
    rfl
  have hρconj : conjStarAlgAut ℂ _ (star ρ.isHermitian.eigenvectorUnitary) ρ.M
      = diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues) :=
    ρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  exact (conjStarAlgAut ℂ _ (star ρ.isHermitian.eigenvectorUnitary)).injective
    (hρconj.trans hσconj.symm)

/-- Density operators are determined by their matrices (the other fields are
propositions). -/
theorem ext {ρ σ : DensityOp n} (h : ρ.M = σ.M) : ρ = σ := by
  cases ρ; cases σ; simp_all

/-- `D(ρ‖ρ) = 0`. -/
@[simp] theorem relEntropy_self (ρ : DensityOp n) : relativeEntropy ρ ρ = 0 :=
  sub_self _

/-- **`relEntropy_eq_zero_iff`** (Paper R Stage 0). For a faithful prior,
relative entropy vanishes exactly on the prior itself. -/
theorem relEntropy_eq_zero_iff (ρ σ : DensityOp n) (hσ : σ.M.PosDef) :
    relativeEntropy ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h; exact ext (relEntropy_eq_zero ρ σ hσ h)
  · rintro rfl; exact relEntropy_self ρ

end DensityOp

/-- **Equality condition for the §4.3 coherence bound.**

`D(ρ‖Δρ) = D(ρ‖ρ*)` exactly when the pinched state *is* the equilibrium.
Immediate from the pinching Pythagorean plus the equality case of Klein: the
gap between the two sides is precisely `D(Δρ‖ρ*)`. This sharpens
`coherence_le_total_defect_unconditional` from an inequality to an inequality
with a characterised equality case. -/
theorem coherence_eq_total_defect_iff {m : ℕ} (P : Pinching.ProjectorFamily n m)
    (ρ ρ_star : DensityOp n) (hcomm : ∀ k, Commute ρ_star.M (P.proj k))
    (hpos : ρ_star.M.PosDef) :
    DensityOp.relativeEntropy ρ (Pinching.pinchDensityOp P ρ)
      = DensityOp.relativeEntropy ρ ρ_star
    ↔ Pinching.pinchDensityOp P ρ = ρ_star := by
  have hpyth := pinching_pythagorean P ρ ρ_star hcomm
  rw [← DensityOp.relEntropy_eq_zero_iff (Pinching.pinchDensityOp P ρ) ρ_star hpos]
  constructor
  · intro h; linarith [hpyth, h]
  · intro h; linarith [hpyth, h]

end MacadayPhysicsLean
