/-
**Support-relative equality case of Klein's inequality** — the Stage-2 keystone
for Paper R's minimiser (Theorem 2, §4.1).

  `supp ρ ⊆ supp σ`,  `D(ρ‖σ) = 0`  ⟹  `ρ = σ`

The landed `relEntropy_eq_zero` assumes `σ` is faithful on the *whole* space
(`σ.M.PosDef`).  The minimiser needs the equality case where `σ` is faithful only
on its own support — the coherence term (`σ := Δρ`, not full-rank) and the block
terms (`σ_λ` faithful only on `H_λ`) both fall outside the full-space theorem.

The proof reuses the *operator reconstruction* of `relEntropy_eq_zero` verbatim —
it consumes only `hqp : 0 < mixing ρ σ i j ⟹ σ_j = ρ_i`, never `ρ_i > 0`.  What
must be redone is the *classical extraction* of `hqp`: with zero prior weights the
junk value `log 0 = 0` breaks the Jensen/Gibbs structure, so the whole argument is
run over the positive support `T = {j : q_j > 0}`.  The support hypothesis
(`p_i > 0 ∧ q_j = 0 ⟹ M_ij = 0`) confines every occupied row's mixing mass to
`T`, which is exactly what makes the row weights sum to `1` there.
-/

import MacadayPhysicsLean.RelEntropyKleinEq
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Real Finset Unitary
open scoped ComplexOrder

variable {n : ℕ}

namespace DensityOp

/-- **Support-relative classical extraction.**

Doubly-stochastic `M`, distributions `p, q` (with `q` possibly having zeros), and
the support condition `hsupp : 0 < p i → q j = 0 → M i j = 0`.  If the classical
`D`-defect vanishes (junk `log 0 = 0` convention), then `q_j = p_i` whenever
`M_ij > 0` — for *every* `i, j`, including the zero-weight rows. -/
theorem klein_classical_eq_zero_of_support (p q : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ j, 0 ≤ q j) (hqsum : ∑ j, q j = 1)
    (hM : ∀ i j, 0 ≤ M i j) (hMrow : ∀ i, ∑ j, M i j = 1) (hMcol : ∀ j, ∑ i, M i j = 1)
    (hsupp : ∀ i j, 0 < p i → q j = 0 → M i j = 0)
    (hD : (∑ i, ∑ j, p i * Real.log (q j) * M i j) = ∑ i, p i * Real.log (p i)) :
    ∀ i j, 0 < M i j → q j = p i := by
  classical
  -- the row-average `r_i = Σ_j M_ij q_j`
  set r : Fin n → ℝ := fun i => ∑ j, M i j * q j with hr
  have hr_nonneg : ∀ i, 0 ≤ r i := fun i =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hq j))
  have hr_sum : ∑ i, r i = 1 := by
    simp only [hr]; rw [Finset.sum_comm]
    calc ∑ j, ∑ i, M i j * q j = ∑ j, (∑ i, M i j) * q j := by
            refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.sum_mul]
      _ = ∑ j, q j := by refine Finset.sum_congr rfl (fun j _ => ?_); rw [hMcol j, one_mul]
      _ = 1 := hqsum
  -- on an OCCUPIED row the mixing mass sits on the positive support `T`
  have hrow_supp : ∀ i, 0 < p i → ∀ j, q j = 0 → M i j = 0 := fun i hpi j hqj =>
    hsupp i j hpi hqj
  -- hence `r_i > 0` for occupied rows (row sums to 1 over positive-q columns)
  have hr_pos_of_p : ∀ i, 0 < p i → 0 < r i := by
    intro i hpi
    -- some column `j` with `M_ij > 0` must have `q_j > 0`
    obtain ⟨j0, _, hj0⟩ : ∃ j ∈ (Finset.univ : Finset (Fin n)), 0 < M i j ∧ 0 < q j := by
      by_contra hc
      simp only [not_exists, not_and, Finset.mem_univ, forall_true_left] at hc
      -- every column is either M_ij = 0 or q_j = 0; but M_ij = 0 when q_j = 0 too
      have hz : ∀ j, M i j * q j = 0 := by
        intro j
        rcases eq_or_lt_of_le (hM i j) with hMj | hMj
        · rw [← hMj, zero_mul]
        · rcases eq_or_lt_of_le (hq j) with hqj | hqj
          · rw [← hqj, mul_zero]
          · exact absurd hqj (hc j hMj)
      have : ∑ j, M i j = 0 := by
        -- if every M_ij q_j = 0 with q_j possibly 0, use support to kill M_ij on q_j=0
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rcases eq_or_lt_of_le (hq j) with hqj | hqj
        · exact hrow_supp i hpi j hqj.symm
        · have := hz j; rw [mul_eq_zero] at this
          exact this.resolve_right (ne_of_gt hqj)
      rw [hMrow i] at this; exact one_ne_zero this
    obtain ⟨hMj0, hqj0⟩ := hj0
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hM i j) (hq j))
      ⟨j0, Finset.mem_univ _, mul_pos hMj0 hqj0⟩
  -- Gibbs: `Σ_i p_i log(p_i / r_i) ≥ 0`, run only over occupied rows
  -- KL term Aᵢ = pᵢ log pᵢ − pᵢ log rᵢ ≥ pᵢ − rᵢ
  have hkl_term : ∀ i, p i - r i ≤ p i * Real.log (p i) - p i * Real.log (r i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · simp only [← hpi, zero_mul, sub_zero]; linarith [hr_nonneg i]
    · have hrp := hr_pos_of_p i hpi
      have hb : Real.log (r i / p i) ≤ r i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hrp hpi)
      have hlog : Real.log (r i) - Real.log (p i) = Real.log (r i / p i) :=
        (Real.log_div hrp.ne' hpi.ne').symm
      have : p i * (Real.log (r i) - Real.log (p i)) ≤ r i - p i := by
        rw [hlog]
        calc p i * Real.log (r i / p i) ≤ p i * (r i / p i - 1) :=
              mul_le_mul_of_nonneg_left hb hpi.le
          _ = r i - p i := by rw [mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one]
      linarith [this]
  -- Jensen slack on the occupied rows: `Σ_j M_ij log q_j ≤ log r_i`
  -- (only the positive-`q` columns contribute; on an occupied row they sum to 1)
  have hjensen : ∀ i, 0 < p i → ∑ j, M i j * Real.log (q j) ≤ Real.log (r i) := by
    intro i hpi
    set T : Finset (Fin n) := Finset.univ.filter (fun j => 0 < q j) with hT
    have hknotT : ∀ k, k ∉ T → q k = 0 := by
      intro k hk
      by_contra h
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, lt_of_le_of_ne (hq k) (Ne.symm h)⟩)
    have hTsum_row : ∑ j ∈ T, M i j = 1 := by
      rw [← hMrow i]
      exact Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => hrow_supp i hpi k (hknotT k hk))
    have hTsum_r : ∑ j ∈ T, M i j * q j = r i :=
      Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => by rw [hknotT k hk, mul_zero])
    have hTsum_logr : ∑ j ∈ T, M i j * Real.log (q j) = ∑ j, M i j * Real.log (q j) :=
      Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => by rw [hrow_supp i hpi k (hknotT k hk), zero_mul])
    rw [← hTsum_logr, ← hTsum_r]
    have hcc := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := T) (fun k _ => hM i k) hTsum_row
      (fun k hk => (Finset.mem_filter.mp hk).2)
    simp only [smul_eq_mul] at hcc
    exact hcc
  -- reindex D-defining sum
  have hDrw : (∑ i, p i * (∑ j, M i j * Real.log (q j))) = ∑ i, p i * Real.log (p i) := by
    rw [← hD]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
  -- total slack decomposition, each summand ≥ 0
  have hslack_nonneg : ∀ i, 0 ≤ p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · rw [← hpi, zero_mul]
    · exact mul_nonneg hpi.le (by linarith [hjensen i hpi])
  have hAterm_nonneg : ∀ i, 0 ≤ (p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i) :=
    fun i => by linarith [hkl_term i]
  have htotal : (∑ i, (p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
      + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i)))) = 0 := by
    have hcong : (∑ i, (p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
        + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i))))
        = ∑ i, (p i * Real.log (p i) - p i * (∑ j, M i j * Real.log (q j)) - (p i - r i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [hcong, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hDrw, hpsum, hr_sum]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
      + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i)) :=
    fun i _ => add_nonneg (hslack_nonneg i) (hAterm_nonneg i)
  have hzero : ∀ i, p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j))
      + ((p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i)) = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htotal i (Finset.mem_univ i)
  -- `r_i = p_i` for every `i` (Gibbs equality)
  have hr_eq_p : ∀ i, r i = p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · -- zero-weight row: slack terms force r_i = p_i = 0
      have h0 := hzero i
      rw [← hpi] at h0
      simp only [zero_mul, sub_zero, zero_sub, neg_neg] at h0
      have hri0 : r i = 0 := by linarith [hslack_nonneg i, h0]
      rw [hri0, ← hpi]
    · -- occupied row: strict log forces equality
      have h0 := hzero i
      have hAz : (p i * Real.log (p i) - p i * Real.log (r i)) - (p i - r i) = 0 := by
        linarith [hslack_nonneg i, hAterm_nonneg i, h0]
      by_contra hne
      have hrp := hr_pos_of_p i hpi
      have hstrict : Real.log (r i / p i) < r i / p i - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos hrp hpi) (by
          rw [ne_eq, div_eq_one_iff_eq hpi.ne']; exact hne)
      have hlog : Real.log (r i) - Real.log (p i) = Real.log (r i / p i) :=
        (Real.log_div hrp.ne' hpi.ne').symm
      have : p i * (Real.log (r i) - Real.log (p i)) < r i - p i := by
        rw [hlog]
        calc p i * Real.log (r i / p i) < p i * (r i / p i - 1) :=
              mul_lt_mul_of_pos_left hstrict hpi
          _ = r i - p i := by rw [mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one]
      linarith [hAz]
  -- now extract `q_j = p_i` on `M_ij > 0`
  intro i j hMij
  rcases eq_or_lt_of_le (hp i) with hpi | hpi
  · -- zero-weight row: r_i = 0 kills positive-q columns, so q_j = 0 = p_i
    have hri0 : r i = 0 := by rw [hr_eq_p i, ← hpi]
    have hsum0 : ∑ k, M i k * q k = 0 := by simpa only [hr] using hri0
    have hjterm : M i j * q j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hM i k) (hq k))).mp
        hsum0 j (Finset.mem_univ j)
    rw [mul_eq_zero] at hjterm
    rw [(hjterm.resolve_left (ne_of_gt hMij)), ← hpi]
  · -- occupied row: Jensen equality gives q constant on the positive row-support
    have hSz : p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)) = 0 := by
      have hA := hAterm_nonneg i; have hs := hslack_nonneg i; linarith [hzero i]
    have hSeq : Real.log (r i) = ∑ j, M i j * Real.log (q j) :=
      by have := (mul_eq_zero.mp hSz).resolve_left hpi.ne'; linarith [this]
    -- restrict to the row-support inside `T`
    set S : Finset (Fin n) := Finset.univ.filter (fun k => 0 < M i k) with hS
    have hqj_pos : 0 < q j := by
      rcases eq_or_lt_of_le (hq j) with h | h
      · exact absurd (hrow_supp i hpi j h.symm) (ne_of_gt hMij)
      · exact h
    have hSpos : ∀ k ∈ S, 0 < q k := by
      intro k hk
      have hMk := (Finset.mem_filter.mp hk).2
      rcases eq_or_lt_of_le (hq k) with h | h
      · exact absurd (hrow_supp i hpi k h.symm) (ne_of_gt hMk)
      · exact h
    have hout : ∀ k, k ∉ S → M i k = 0 := fun k hk =>
      le_antisymm (not_lt.mp (fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩))) (hM i k)
    have hSrow : ∑ k ∈ S, M i k = 1 := by
      rw [← hMrow i]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hk => hout k hk)
    have hSsum_q : ∑ k ∈ S, M i k * q k = r i := by
      rw [hr]
      exact Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => by rw [hout k hk, zero_mul])
    have hSsum_logq : ∑ k ∈ S, M i k * Real.log (q k) = ∑ k, M i k * Real.log (q k) :=
      Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hk => by rw [hout k hk, zero_mul])
    have hjS : Real.log (∑ k ∈ S, M i k • q k) = ∑ k ∈ S, M i k • Real.log (q k) := by
      simp only [smul_eq_mul, hSsum_q, hSsum_logq]; exact hSeq
    have hconst := strictConcaveOn_log_Ioi.eq_of_map_sum_eq (t := S) (w := M i) (p := q)
      (fun k hk => (Finset.mem_filter.mp hk).2) hSrow hSpos (le_of_eq hjS)
    have hjS_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hMij⟩
    have hri_qj : r i = q j := by
      rw [← hSsum_q]
      calc ∑ k ∈ S, M i k * q k = ∑ k ∈ S, M i k * q j := by
            refine Finset.sum_congr rfl (fun k hk => ?_); rw [hconst hk hjS_mem]
        _ = (∑ k ∈ S, M i k) * q j := by rw [Finset.sum_mul]
        _ = q j := by rw [hSrow, one_mul]
    rw [← hri_qj]; exact hr_eq_p i

/-- **Support-relative Klein inequality (nonnegativity).**

Same hypotheses as the extraction minus `D = 0`: the classical `D`-defect is
nonnegative even when `σ` has zeros, provided `supp ρ ⊆ supp σ` (the support
condition confines each occupied row to the positive-`q` columns). -/
theorem klein_classical_le_of_support (p q : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hq : ∀ j, 0 ≤ q j) (hqsum : ∑ j, q j = 1)
    (hM : ∀ i j, 0 ≤ M i j) (hMrow : ∀ i, ∑ j, M i j = 1) (hMcol : ∀ j, ∑ i, M i j = 1)
    (hsupp : ∀ i j, 0 < p i → q j = 0 → M i j = 0) :
    (∑ i, ∑ j, p i * Real.log (q j) * M i j) ≤ ∑ i, p i * Real.log (p i) := by
  classical
  set r : Fin n → ℝ := fun i => ∑ j, M i j * q j with hr
  have hr_nonneg : ∀ i, 0 ≤ r i := fun i =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hq j))
  have hr_sum : ∑ i, r i = 1 := by
    simp only [hr]; rw [Finset.sum_comm]
    calc ∑ j, ∑ i, M i j * q j = ∑ j, (∑ i, M i j) * q j := by
            refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.sum_mul]
      _ = ∑ j, q j := by refine Finset.sum_congr rfl (fun j _ => ?_); rw [hMcol j, one_mul]
      _ = 1 := hqsum
  have hrow_supp : ∀ i, 0 < p i → ∀ j, q j = 0 → M i j = 0 := fun i hpi j hqj =>
    hsupp i j hpi hqj
  have hr_pos_of_p : ∀ i, 0 < p i → 0 < r i := by
    intro i hpi
    obtain ⟨j0, _, hMj0, hqj0⟩ : ∃ j ∈ (Finset.univ : Finset (Fin n)), 0 < M i j ∧ 0 < q j := by
      by_contra hc
      simp only [not_exists, not_and, Finset.mem_univ, forall_true_left] at hc
      have : ∑ j, M i j = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rcases eq_or_lt_of_le (hq j) with hqj | hqj
        · exact hrow_supp i hpi j hqj.symm
        · exact le_antisymm (not_lt.mp (fun h => hc j h hqj)) (hM i j)
      rw [hMrow i] at this; exact one_ne_zero this
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hM i j) (hq j))
      ⟨j0, Finset.mem_univ _, mul_pos hMj0 hqj0⟩
  have hjensen : ∀ i, 0 < p i → ∑ j, M i j * Real.log (q j) ≤ Real.log (r i) := by
    intro i hpi
    set T : Finset (Fin n) := Finset.univ.filter (fun j => 0 < q j) with hT
    have hknotT : ∀ k, k ∉ T → q k = 0 := fun k hk => by
      by_contra h
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, lt_of_le_of_ne (hq k) (Ne.symm h)⟩)
    have hTsum_row : ∑ j ∈ T, M i j = 1 := by
      rw [← hMrow i]
      exact Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => hrow_supp i hpi k (hknotT k hk))
    have hTsum_r : ∑ j ∈ T, M i j * q j = r i :=
      Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => by rw [hknotT k hk, mul_zero])
    have hTsum_logr : ∑ j ∈ T, M i j * Real.log (q j) = ∑ j, M i j * Real.log (q j) :=
      Finset.sum_subset (Finset.filter_subset _ _)
        (fun k _ hk => by rw [hrow_supp i hpi k (hknotT k hk), zero_mul])
    rw [← hTsum_logr, ← hTsum_r]
    have hcc := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := T) (fun k _ => hM i k) hTsum_row (fun k hk => (Finset.mem_filter.mp hk).2)
    simp only [smul_eq_mul] at hcc
    exact hcc
  have hkl_term : ∀ i, p i - r i ≤ p i * Real.log (p i) - p i * Real.log (r i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · simp only [← hpi, zero_mul, sub_zero]; linarith [hr_nonneg i]
    · have hrp := hr_pos_of_p i hpi
      have hb : Real.log (r i / p i) ≤ r i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hrp hpi)
      have hlog : Real.log (r i) - Real.log (p i) = Real.log (r i / p i) :=
        (Real.log_div hrp.ne' hpi.ne').symm
      have : p i * (Real.log (r i) - Real.log (p i)) ≤ r i - p i := by
        rw [hlog]
        calc p i * Real.log (r i / p i) ≤ p i * (r i / p i - 1) :=
              mul_le_mul_of_nonneg_left hb hpi.le
          _ = r i - p i := by rw [mul_sub, mul_div_cancel₀ _ hpi.ne', mul_one]
      linarith [this]
  have hslack : ∀ i, 0 ≤ p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with hpi | hpi
    · rw [← hpi, zero_mul]
    · exact mul_nonneg hpi.le (by linarith [hjensen i hpi])
  -- assemble: D = Σ slack + Σ KL-term, both nonneg
  have hDeq : (∑ i, p i * Real.log (p i)) - (∑ i, ∑ j, p i * Real.log (q j) * M i j)
      = (∑ i, p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)))
        + (∑ i, (p i * Real.log (p i) - p i * Real.log (r i))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hpull : (∑ j, p i * Real.log (q j) * M i j) = p i * ∑ j, M i j * Real.log (q j) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    rw [hpull]; ring
  have hKL : 0 ≤ ∑ i, (p i * Real.log (p i) - p i * Real.log (r i)) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hkl_term i)
    rw [Finset.sum_sub_distrib, hpsum, hr_sum, sub_self] at this
    linarith [this]
  have hslacksum : 0 ≤ ∑ i, p i * (Real.log (r i) - ∑ j, M i j * Real.log (q j)) :=
    Finset.sum_nonneg (fun i _ => hslack i)
  linarith [hDeq, hKL, hslacksum]

/-- **Support-relative nonnegativity of relative entropy.** For `supp ρ ⊆ supp σ`
(spectral/mixing form), `0 ≤ D(ρ‖σ)` even when `σ` is not faithful. -/
theorem relEntropy_nonneg_of_support (ρ σ : DensityOp n)
    (hsupp : ∀ i j, 0 < ρ.eigenvalues i → σ.eigenvalues j = 0 → mixing ρ σ i j = 0) :
    0 ≤ relativeEntropy ρ σ := by
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
  have hle := klein_classical_le_of_support ρ.eigenvalues σ.eigenvalues (mixing ρ σ)
    (fun i => ρ.eigenvalues_nonneg i) hpsum (fun j => σ.eigenvalues_nonneg j) hqsum
    (fun i j => mixing_nonneg ρ σ i j) (fun i => mixing_row_sum ρ σ i)
    (fun j => mixing_col_sum ρ σ j) hsupp
  rw [relativeEntropy_eq_classical]
  linarith [hle]

/-- **Support-relative equality case of Klein's inequality.**

If `σ` is faithful only on its own support and `supp ρ ⊆ supp σ` — expressed in
spectral form as `hsupp` — then `D(ρ‖σ) = 0` still forces `ρ = σ`.  The support
condition is exactly what makes the reconstruction go through with a non-faithful
`σ`: the classical extraction (`klein_classical_eq_zero_of_support`) yields
`q_j = p_i` on every mixing overlap, and the operator reconstruction is identical
to the full-space case (it never used `p_i > 0`). -/
theorem relEntropy_eq_zero_of_support (ρ σ : DensityOp n)
    (hsupp : ∀ i j, 0 < ρ.eigenvalues i → σ.eigenvalues j = 0 → mixing ρ σ i j = 0)
    (hD : relativeEntropy ρ σ = 0) : ρ.M = σ.M := by
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
  have hclass : (∑ i, ∑ j, ρ.eigenvalues i * Real.log (σ.eigenvalues j) * mixing ρ σ i j)
      = ∑ i, ρ.eigenvalues i * Real.log (ρ.eigenvalues i) := by
    have := relativeEntropy_eq_classical ρ σ
    rw [hD] at this; linarith [this]
  have hqp := klein_classical_eq_zero_of_support ρ.eigenvalues σ.eigenvalues (mixing ρ σ)
    (fun i => ρ.eigenvalues_nonneg i) hpsum (fun j => σ.eigenvalues_nonneg j) hqsum
    (fun i j => mixing_nonneg ρ σ i j) (fun i => mixing_row_sum ρ σ i)
    (fun j => mixing_col_sum ρ σ j) hsupp hclass
  -- the multiplicative form `Wᵢⱼ qⱼ = pᵢ Wᵢⱼ` (identical to the full-space case)
  have hWq : ∀ i j, crossW ρ σ i j * (RCLike.ofReal (σ.isHermitian.eigenvalues j) : ℂ)
      = (RCLike.ofReal (ρ.isHermitian.eigenvalues i) : ℂ) * crossW ρ σ i j := by
    intro i j
    rcases eq_or_ne (crossW ρ σ i j) 0 with h0 | h0
    · rw [h0, zero_mul, mul_zero]
    · have hmix : 0 < mixing ρ σ i j := by
        rw [mixing]; exact Complex.normSq_pos.mpr h0
      rw [show σ.isHermitian.eigenvalues j = ρ.isHermitian.eigenvalues i from hqp i j hmix]
      ring
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

/-! ### Operator-support bridge: kernel inclusion ⟹ mixing support

The equality/nonneg theorems consume the mixing-form support condition.  The
usable *operator* hypothesis is kernel inclusion `ker σ.M ⊆ ker ρ.M` (equivalently
`supp ρ ⊆ supp σ`).  The bridge is one PSD move: a zero-eigenvector `f_j` of `σ`
(`σ f_j = 0`) is killed by `ρ` too, and conjugating `ρ f_j = 0` into `ρ`'s
eigenbasis gives `p_i · W_ij = 0`, hence `M_ij = |W_ij|² = 0` wherever `p_i > 0`. -/

/-- **The support bridge.** Kernel inclusion `ker σ.M ⊆ ker ρ.M` yields the
mixing-form support condition consumed by the support-relative theorems. -/
theorem mixing_eq_zero_of_ker_inclusion (ρ σ : DensityOp n)
    (hker : ∀ v : Fin n → ℂ, σ.M *ᵥ v = 0 → ρ.M *ᵥ v = 0)
    (i j : Fin n) (hpi : 0 < ρ.eigenvalues i) (hqj : σ.eigenvalues j = 0) :
    mixing ρ σ i j = 0 := by
  set Uρ : Matrix (Fin n) (Fin n) ℂ :=
    (ρ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUρ
  set Uρs : Matrix (Fin n) (Fin n) ℂ :=
    ((star ρ.isHermitian.eigenvectorUnitary : unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) with hUρs
  set Uσ : Matrix (Fin n) (Fin n) ℂ :=
    (σ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUσ
  set Uσs : Matrix (Fin n) (Fin n) ℂ :=
    ((star σ.isHermitian.eigenvectorUnitary : unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) with hUσs
  have hUρUs : Uρ * Uρs = 1 := Unitary.coe_mul_star_self _
  have hUσUs : Uσ * Uσs = 1 := Unitary.coe_mul_star_self _
  set Dρ : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues) with hDρdef
  set Dσ : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (RCLike.ofReal ∘ σ.isHermitian.eigenvalues) with hDσdef
  have hDρ : Uρs * ρ.M * Uρ = Dρ := by
    have h := ρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [conjStarAlgAut_apply] at h
    simpa [hUρs, hUρ, hDρdef, star_star] using h
  have hDσ : Uσs * σ.M * Uσ = Dσ := by
    have h := σ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [conjStarAlgAut_apply] at h
    simpa [hUσs, hUσ, hDσdef, star_star] using h
  -- `f` = j-th eigenvector of σ, eigenvalue 0
  set f : Fin n → ℂ := Uσ *ᵥ Pi.single j 1 with hf
  have hσMUσ : σ.M * Uσ = Uσ * Dσ := by
    calc σ.M * Uσ = Uσ * (Uσs * σ.M * Uσ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUσUs, Matrix.one_mul]
      _ = _ := by rw [hDσ]
  have hDσej : Dσ *ᵥ (Pi.single j 1 : Fin n → ℂ) = 0 := by
    funext k
    rw [hDσdef, Matrix.mulVec_diagonal]
    by_cases hk : k = j
    · simp [hk, Function.comp_apply, show σ.isHermitian.eigenvalues j = 0 from hqj]
    · simp [Pi.single_eq_of_ne hk]
  have hσf : σ.M *ᵥ f = 0 := by
    rw [hf, Matrix.mulVec_mulVec, hσMUσ, ← Matrix.mulVec_mulVec, hDσej, Matrix.mulVec_zero]
  have hρf : ρ.M *ᵥ f = 0 := hker f hσf
  -- `crossW = Uρs * Uσ`, and `Dρ * crossW = Uρs * ρ.M * Uσ`
  have hcrossW : crossW ρ σ = Uρs * Uσ := by
    rw [crossW, UnitaryGroup.mul_apply]
  have hUρρ : Uρs * ρ.M = Dρ * Uρs := by
    calc Uρs * ρ.M = (Uρs * ρ.M * Uρ) * Uρs := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hUρUs, Matrix.mul_one]
      _ = _ := by rw [hDρ]
  have hDρcross : Dρ * crossW ρ σ = Uρs * ρ.M * Uσ := by
    rw [hcrossW, ← Matrix.mul_assoc, ← hUρρ, Matrix.mul_assoc]
  have hcol : (Dρ * crossW ρ σ) *ᵥ (Pi.single j 1 : Fin n → ℂ) = 0 := by
    rw [hDρcross, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hf, hρf,
      Matrix.mulVec_zero]
  -- entry `i`: `p_i · W_ij = 0`
  have hentry : (RCLike.ofReal (ρ.isHermitian.eigenvalues i) : ℂ) * crossW ρ σ i j = 0 := by
    have hi := congrFun hcol i
    have hij : ((Dρ * crossW ρ σ) *ᵥ (Pi.single j 1 : Fin n → ℂ)) i
        = (Dρ * crossW ρ σ) i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hij, Matrix.mul_apply, Finset.sum_eq_single i] at hi
    · rw [hDρdef, Matrix.diagonal_apply_eq, Function.comp_apply] at hi
      simpa using hi
    · intro k _ hki; rw [hDρdef, Matrix.diagonal_apply_ne _ (Ne.symm hki), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hpne : (RCLike.ofReal (ρ.isHermitian.eigenvalues i) : ℂ) ≠ 0 := by
    rw [ne_eq, RCLike.ofReal_eq_zero]; exact ne_of_gt hpi
  have hWij : crossW ρ σ i j = 0 := (mul_eq_zero.mp hentry).resolve_left hpne
  rw [mixing, hWij, map_zero]

end DensityOp

/-! ### §6.4 item (i) — Lemma 2 (support lemma) as kernel inclusion

`supp ρ ⊆ supp Δρ` for the pinching `Δρ = Σ_λ Π_λ ρ Π_λ`: if `Δρ v = 0` then
`ρ v = 0`.  The proof is the PSD move `⟨v, Δρ v⟩ = Σ_λ ⟨Π_λ v, ρ (Π_λ v)⟩`, every
summand nonnegative, so each `ρ (Π_λ v) = 0`, whence `ρ v = Σ_λ ρ (Π_λ v) = 0`. -/

open Pinching in
/-- **Lemma 2 (§6.4 item i).** `ker (Δρ) ⊆ ker ρ`. -/
theorem pinch_ker_inclusion {m : ℕ} (P : ProjectorFamily n m) (ρ : DensityOp n)
    {v : Fin n → ℂ} (hv : (pinchDensityOp P ρ).M *ᵥ v = 0) : ρ.M *ᵥ v = 0 := by
  -- each block kills `Π_λ v`
  have hblock : ∀ k, ρ.M *ᵥ (P.proj k *ᵥ v) = 0 := by
    intro k
    -- the block quadratic forms are complex-nonneg and sum to `⟨v, Δρ v⟩ = 0`
    have hterm_nonneg : ∀ l, (0 : ℂ) ≤ star v ⬝ᵥ (P.proj l * ρ.M * P.proj l) *ᵥ v :=
      fun l => (posSemidef_pinch_term P ρ.posSemidef l).dotProduct_mulVec_nonneg v
    have hpinchM : (pinchDensityOp P ρ).M = ∑ l, P.proj l * ρ.M * P.proj l := rfl
    have hexpand : star v ⬝ᵥ (pinchDensityOp P ρ).M *ᵥ v
        = ∑ l, star v ⬝ᵥ (P.proj l * ρ.M * P.proj l) *ᵥ v := by
      rw [hpinchM, Matrix.sum_mulVec, dotProduct_sum]
    have hsum : (∑ l, star v ⬝ᵥ (P.proj l * ρ.M * P.proj l) *ᵥ v) = 0 := by
      rw [← hexpand, hv, dotProduct_zero]
    have hzero : star v ⬝ᵥ (P.proj k * ρ.M * P.proj k) *ᵥ v = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hterm_nonneg l)).mp hsum k (Finset.mem_univ k)
    -- `⟨v, Π_k ρ Π_k v⟩ = ⟨Π_k v, ρ (Π_k v)⟩`, so `ρ (Π_k v) = 0`
    have hcyc : star (P.proj k *ᵥ v) ⬝ᵥ ρ.M *ᵥ (P.proj k *ᵥ v)
        = star v ⬝ᵥ (P.proj k * ρ.M * P.proj k) *ᵥ v := by
      rw [Matrix.star_mulVec, (P.isHermitian k).eq, Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
        ← Matrix.dotProduct_mulVec]
    exact (PosSemidef.dotProduct_mulVec_zero_iff ρ.posSemidef (P.proj k *ᵥ v)).mp
      (hcyc.trans hzero)
  -- `ρ v = ρ (Σ_k Π_k v) = Σ_k ρ (Π_k v) = 0`
  have hsum1 : (∑ k, P.proj k) *ᵥ v = v := by rw [P.sum_eq_one, Matrix.one_mulVec]
  calc ρ.M *ᵥ v = ρ.M *ᵥ ((∑ k, P.proj k) *ᵥ v) := by rw [hsum1]
    _ = ρ.M *ᵥ (∑ k, P.proj k *ᵥ v) := by rw [Matrix.sum_mulVec]
    _ = ∑ k, ρ.M *ᵥ (P.proj k *ᵥ v) := by rw [Matrix.mulVec_sum]
    _ = 0 := by rw [Finset.sum_congr rfl (fun k _ => hblock k), Finset.sum_const_zero]

end MacadayPhysicsLean
