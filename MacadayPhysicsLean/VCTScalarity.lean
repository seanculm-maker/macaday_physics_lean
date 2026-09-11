/-
**VCT scalarity — Paper W §2.3, end-to-end matrix form.**

The existing Paper-W modules stop at *entropy equality* at the pinched maximizer
(`VCT.vct_lemma_3_quantum : S(Δρ*) = S(ρ*)`).  This module closes the remaining
glue and states the theorem Paper W actually claims, as a **matrix equality**:

  every entropy maximizer under commuting constraints is the scalar state
  `ρ* = Σ_k (p_k / r_k) Π_k`,  `p_k = Tr(Π_k ρ*)`,  `r_k = Tr Π_k = rank Π_k`.

Consequently `Δρ* = ρ*` (block diagonal), and on every block of positive weight the
normalised block state is the maximally mixed state `Π_k / r_k`.  Zero-weight blocks
are not quantified over — they carry no state.

**Route (B of the spec): uniform-prior specialisation of the Relative Classicality
Theorem.**  With the prior `σ_u = I/n` (`DensityOp.maximallyMixed`):

* `σ_u` is positive definite, block diagonal, with sector weights `r_k / n > 0` and
  conditional blocks `Π_k / r_k` (`uniformBlockDecomp`);
* `Δρ*` carries the block decomposition with weights `p_k` and blocks
  `Π_k ρ* Π_k / p_k` (or an arbitrary block state where `p_k = 0`; `pinchBlockDecomp`);
* the reset state `R_{σ_u}(ρ*) = Σ_k p_k (Π_k / r_k)` **is** the scalar state;
* `D(ρ‖σ_u) = log n − S(ρ)` (`relEntropy_maximallyMixed`), so
  `MinimizerR.relEntropy_ge_blockKL` gives `S(ρ*) ≤ log n − D_KL(p‖r/n) = S(scalar)`,
  while feasibility of the scalar state (`hC_eig` is load-bearing here) and
  maximality give `S(scalar) ≤ S(ρ*)`;
* equality then feeds `MinimizerR.relEntropy_eq_blockKL_iff_reset`, whose
  conclusion is the matrix equality `ρ* = R_{σ_u}(ρ*)`.

**Hypotheses of the main theorem.**  `P` is any projector family with every
projector nonzero (`hrank`); the constraints `C j` satisfy the joint-eigenprojector
relation `C j * Π_k = eigval j k • Π_k`; `ρ*` is feasible and maximises the von
Neumann entropy among feasible states.  No Hermiticity of the `C j` is needed.

Nothing in the existing modules is modified; this file is purely additive.
-/

import MacadayPhysicsLean.MinimizerR
import MacadayPhysicsLean.NeutralBridge
import MacadayPhysicsLean.VCT
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace MacadayPhysicsLean.VCTScalarity

open Matrix Pinching DensityOp
open scoped ComplexOrder

variable {n m : ℕ}

/-! ### Projectors: positivity and rank -/

/-- Every projector of a `ProjectorFamily` is positive semidefinite (`Π = Πᴴ Π`). -/
theorem proj_posSemidef (P : ProjectorFamily n m) (k : Fin m) : (P.proj k).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (P.proj k)
  rwa [(P.isHermitian k).eq, P.idem k] at h

/-- The rank of `Π_k`, read off as the (real) trace `Tr Π_k`. -/
noncomputable def blockRank (P : ProjectorFamily n m) (k : Fin m) : ℝ := (P.proj k).trace.re

/-- `Tr Π_k = r_k` as a complex identity — the trace of a PSD matrix is real. -/
theorem trace_proj (P : ProjectorFamily n m) (k : Fin m) :
    (P.proj k).trace = ((blockRank P k : ℝ) : ℂ) := by
  have h : star (P.proj k).trace = (P.proj k).trace := by
    rw [← Matrix.trace_conjTranspose, (P.isHermitian k).eq]
  have him : (P.proj k).trace.im = 0 := Complex.conj_eq_iff_im.mp h
  rw [Complex.ext_iff]
  exact ⟨by rw [Complex.ofReal_re]; rfl, by rw [Complex.ofReal_im, him]⟩

theorem blockRank_nonneg (P : ProjectorFamily n m) (k : Fin m) : 0 ≤ blockRank P k := by
  have h := (proj_posSemidef P k).trace_nonneg
  rw [trace_proj] at h
  exact Complex.zero_le_real.mp h

/-- A zero-rank projector is the zero matrix (PSD with zero trace). -/
theorem proj_eq_zero_of_blockRank_eq_zero (P : ProjectorFamily n m) (k : Fin m)
    (h : blockRank P k = 0) : P.proj k = 0 := by
  rw [← (proj_posSemidef P k).trace_eq_zero_iff, trace_proj, h]
  simp

/-- A nonzero projector has positive rank. -/
theorem blockRank_pos (P : ProjectorFamily n m) (k : Fin m) (h : P.proj k ≠ 0) :
    0 < blockRank P k := by
  rcases (blockRank_nonneg P k).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (proj_eq_zero_of_blockRank_eq_zero P k heq.symm) h

/-! ### Sector weights `p_k = Tr(Π_k ρ)` -/

/-- `Tr(Π_k ρ) = p_k` as a complex identity. -/
theorem trace_proj_mul (P : ProjectorFamily n m) (ρ : DensityOp n) (k : Fin m) :
    (P.proj k * ρ.M).trace = ((sectorWeight P ρ k : ℝ) : ℂ) := by
  rw [← trace_pinch_term, trace_pinch_block]

theorem sectorWeight_nonneg (P : ProjectorFamily n m) (ρ : DensityOp n) (k : Fin m) :
    0 ≤ sectorWeight P ρ k := by
  have h := (posSemidef_pinch_term P ρ.posSemidef k).trace_nonneg
  rw [trace_pinch_block] at h
  exact Complex.zero_le_real.mp h

/-- The sector weights sum to `1`. -/
theorem sectorWeight_sum (P : ProjectorFamily n m) (ρ : DensityOp n) :
    ∑ k, sectorWeight P ρ k = 1 := by
  have h : ∑ k, (P.proj k * ρ.M).trace = 1 := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, P.sum_eq_one, Matrix.one_mul, ρ.trace_one]
  simp_rw [trace_proj_mul] at h
  exact_mod_cast h

/-- An unoccupied block carries no state: `p_k = 0 → Π_k ρ Π_k = 0`. -/
theorem pinch_term_eq_zero_of_sectorWeight_eq_zero (P : ProjectorFamily n m) (ρ : DensityOp n)
    (k : Fin m) (h : sectorWeight P ρ k = 0) : P.proj k * ρ.M * P.proj k = 0 := by
  rw [← (posSemidef_pinch_term P ρ.posSemidef k).trace_eq_zero_iff, trace_pinch_block, h]
  simp

theorem sectorWeight_eq_zero_of_proj_eq_zero (P : ProjectorFamily n m) (ρ : DensityOp n)
    (k : Fin m) (h : P.proj k = 0) : sectorWeight P ρ k = 0 := by
  simp [sectorWeight, h]

/-- A density operator forces `n ≠ 0` (the trace over `Fin 0` vanishes). -/
theorem _root_.MacadayPhysicsLean.DensityOp.n_ne_zero (ρ : DensityOp n) : n ≠ 0 := by
  rintro rfl
  have h := ρ.trace_one
  simp [Matrix.trace] at h

/-! ### The scalar state `Σ_k (p_k / r_k) Π_k` -/

/-- The **scalar state** of `ρ` relative to `P`: `Σ_k (p_k / r_k) Π_k` with
`p_k = Tr(Π_k ρ)` and `r_k = Tr Π_k`.  It is a density operator with no side
hypothesis (a zero-rank block is the zero matrix and then also has zero weight). -/
noncomputable def scalarState (P : ProjectorFamily n m) (ρ : DensityOp n) : DensityOp n where
  M := ∑ k, ((sectorWeight P ρ k / blockRank P k : ℝ) : ℂ) • P.proj k
  posSemidef := Matrix.posSemidef_sum _ (fun k _ => (proj_posSemidef P k).smul
    (Complex.zero_le_real.mpr (div_nonneg (sectorWeight_nonneg P ρ k) (blockRank_nonneg P k))))
  trace_one := by
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, trace_proj, smul_eq_mul]
    rw [← Complex.ofReal_one, ← sectorWeight_sum P ρ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Complex.ofReal_mul]
    congr 1
    rcases eq_or_ne (blockRank P k) 0 with hr | hr
    · rw [hr, div_zero, zero_mul,
        sectorWeight_eq_zero_of_proj_eq_zero P ρ k (proj_eq_zero_of_blockRank_eq_zero P k hr)]
    · exact div_mul_cancel₀ _ hr

theorem scalarState_M (P : ProjectorFamily n m) (ρ : DensityOp n) :
    (scalarState P ρ).M = ∑ k, ((sectorWeight P ρ k / blockRank P k : ℝ) : ℂ) • P.proj k := rfl

/-- The scalar state commutes with every projector. -/
theorem scalarState_commute (P : ProjectorFamily n m) (ρ : DensityOp n) (k : Fin m) :
    Commute (scalarState P ρ).M (P.proj k) := by
  change (∑ j, ((sectorWeight P ρ j / blockRank P j : ℝ) : ℂ) • P.proj j) * P.proj k
    = P.proj k * ∑ j, ((sectorWeight P ρ j / blockRank P j : ℝ) : ℂ) • P.proj j
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  by_cases hjk : j = k
  · subst hjk; rfl
  · rw [P.ortho j k hjk, P.ortho k j (Ne.symm hjk)]

/-- The scalar state is block diagonal: it is fixed by the pinching map. -/
theorem pinch_scalarState (P : ProjectorFamily n m) (ρ : DensityOp n) :
    pinchDensityOp P (scalarState P ρ) = scalarState P ρ :=
  pinchDensityOp_eq_self_of_commute P _ (scalarState_commute P ρ)

/-- The `k`-th block of the scalar state is `(p_k / r_k) Π_k`. -/
theorem proj_mul_scalarState_mul_proj (P : ProjectorFamily n m) (ρ : DensityOp n) (k : Fin m) :
    P.proj k * (scalarState P ρ).M * P.proj k
      = ((sectorWeight P ρ k / blockRank P k : ℝ) : ℂ) • P.proj k := by
  rw [scalarState_M, Matrix.mul_sum, Finset.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_smul, Matrix.smul_mul, P.idem, P.idem]
  · intro j _ hjk
    rw [Matrix.mul_smul, Matrix.smul_mul, P.ortho k j (Ne.symm hjk), Matrix.zero_mul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### Feasibility of the scalar state (where `hC_eig` is load-bearing) -/

/-- For a constraint `C` with `C Π_k = e_k Π_k`, `Tr(ρ C) = Σ_k p_k e_k` for **every**
state `ρ` — the constraint value only sees the sector weights. -/
theorem trace_mul_C_eq (P : ProjectorFamily n m) (ρ : DensityOp n)
    (C : Matrix (Fin n) (Fin n) ℂ) (e : Fin m → ℂ)
    (hC : ∀ k, C * P.proj k = e k • P.proj k) :
    (ρ.M * C).trace = ∑ k, ((sectorWeight P ρ k : ℝ) : ℂ) * e k := by
  have hsplit : ρ.M * C = ∑ k, e k • (ρ.M * P.proj k) := by
    calc ρ.M * C = ρ.M * C * 1 := (Matrix.mul_one _).symm
      _ = ρ.M * C * ∑ k, P.proj k := by rw [P.sum_eq_one]
      _ = ∑ k, e k • (ρ.M * P.proj k) := by
          rw [Matrix.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Matrix.mul_assoc, hC k, Matrix.mul_smul]
  rw [hsplit, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_mul_comm, trace_proj_mul, smul_eq_mul, mul_comm]

/-- The scalar state has the same constraint values: `Tr(scalar · C) = Σ_k p_k e_k`. -/
theorem trace_scalarState_mul_C (P : ProjectorFamily n m) (ρ : DensityOp n)
    (C : Matrix (Fin n) (Fin n) ℂ) (e : Fin m → ℂ)
    (hC : ∀ k, C * P.proj k = e k • P.proj k) :
    ((scalarState P ρ).M * C).trace = ∑ k, ((sectorWeight P ρ k : ℝ) : ℂ) * e k := by
  rw [scalarState_M, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm, hC k, Matrix.trace_smul,
    trace_proj, smul_eq_mul, smul_eq_mul]
  rcases eq_or_ne (blockRank P k) 0 with hr | hr
  · rw [hr, div_zero,
      sectorWeight_eq_zero_of_proj_eq_zero P ρ k (proj_eq_zero_of_blockRank_eq_zero P k hr)]
    simp
  · have hr' : ((blockRank P k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
    rw [Complex.ofReal_div]
    field_simp

/-- **Feasibility transfers to the scalar state.** -/
theorem scalarState_feasible (P : ProjectorFamily n m) (ρ : DensityOp n)
    {K : ℕ} (C : Fin K → Matrix (Fin n) (Fin n) ℂ) (eigval : Fin K → Fin m → ℂ)
    (hC_eig : ∀ j k, C j * P.proj k = eigval j k • P.proj k)
    (c : Fin K → ℂ) (h_feas : ∀ j, (ρ.M * C j).trace = c j) :
    ∀ j, ((scalarState P ρ).M * C j).trace = c j := by
  intro j
  rw [trace_scalarState_mul_C P ρ (C j) (eigval j) (hC_eig j), ← h_feas j,
    trace_mul_C_eq P ρ (C j) (eigval j) (hC_eig j)]

/-! ### The two block decompositions of Route B -/

/-- The maximally mixed block state `Π_k / r_k` (needs `Π_k ≠ 0`). -/
noncomputable def uniformBlockState (P : ProjectorFamily n m) (k : Fin m) (hk : P.proj k ≠ 0) :
    DensityOp n where
  M := (((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k
  posSemidef := (proj_posSemidef P k).smul (by simpa using inv_nonneg.mpr (blockRank_nonneg P k))
  trace_one := by
    rw [Matrix.trace_smul, trace_proj, smul_eq_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (ne_of_gt (blockRank_pos P k hk)), Complex.ofReal_one]

/-- The normalised block `Π_k ρ Π_k / p_k` of an occupied sector. -/
noncomputable def sectorStateAt (P : ProjectorFamily n m) (ρ : DensityOp n) (k : Fin m)
    (hk : 0 < sectorWeight P ρ k) : DensityOp n where
  M := ((sectorWeight P ρ k : ℝ) : ℂ)⁻¹ • (P.proj k * ρ.M * P.proj k)
  posSemidef := by
    apply (posSemidef_pinch_term P ρ.posSemidef k).smul
    rw [← Complex.ofReal_inv]
    simpa using le_of_lt (inv_pos.mpr hk)
  trace_one := by
    rw [Matrix.trace_smul, trace_pinch_block, smul_eq_mul, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hk), Complex.ofReal_one]

/-- The block decomposition of `Δρ`: weights `p_k`, blocks `Π_k ρ Π_k / p_k` on occupied
sectors and the uniform block state on unoccupied ones (where `Π_k ρ Π_k = 0`). -/
noncomputable def pinchBlockDecomp (P : ProjectorFamily n m) (ρ : DensityOp n)
    (hrank : ∀ k, P.proj k ≠ 0) : BlockDecomp P (pinchDensityOp P ρ) where
  w := sectorWeight P ρ
  st := fun k => if hk : 0 < sectorWeight P ρ k then sectorStateAt P ρ k hk
    else uniformBlockState P k (hrank k)
  w_nonneg := sectorWeight_nonneg P ρ
  supported := fun k => by
    by_cases hk : 0 < sectorWeight P ρ k
    · rw [dif_pos hk]
      change P.proj k * (((sectorWeight P ρ k : ℝ) : ℂ)⁻¹ • (P.proj k * ρ.M * P.proj k))
        = ((sectorWeight P ρ k : ℝ) : ℂ)⁻¹ • (P.proj k * ρ.M * P.proj k)
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.idem]
    · rw [dif_neg hk]
      change P.proj k * ((((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k)
        = (((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k
      rw [Matrix.mul_smul, P.idem]
  sum_eq := by
    change P.pinch ρ.M = _
    unfold ProjectorFamily.pinch
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : 0 < sectorWeight P ρ k
    · rw [dif_pos hk]
      change P.proj k * ρ.M * P.proj k
        = ((sectorWeight P ρ k : ℝ) : ℂ)
            • (((sectorWeight P ρ k : ℝ) : ℂ)⁻¹ • (P.proj k * ρ.M * P.proj k))
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hk), one_smul]
    · rw [dif_neg hk]
      have h0 : sectorWeight P ρ k = 0 :=
        le_antisymm (not_lt.mp hk) (sectorWeight_nonneg P ρ k)
      rw [pinch_term_eq_zero_of_sectorWeight_eq_zero P ρ k h0, h0]
      simp

/-- The block decomposition of the maximally mixed state `I/n`: weights `r_k / n`,
blocks `Π_k / r_k`. -/
noncomputable def uniformBlockDecomp (P : ProjectorFamily n m) (hrank : ∀ k, P.proj k ≠ 0)
    [NeZero n] : BlockDecomp P (maximallyMixed n) where
  w := fun k => blockRank P k / n
  st := fun k => uniformBlockState P k (hrank k)
  w_nonneg := fun k => div_nonneg (blockRank_nonneg P k) (Nat.cast_nonneg n)
  supported := fun k => by
    change P.proj k * ((((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k)
      = (((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k
    rw [Matrix.mul_smul, P.idem]
  sum_eq := by
    change (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      = ∑ k, ((blockRank P k / n : ℝ) : ℂ) • ((((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k)
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hterm : ∀ k, ((blockRank P k / n : ℝ) : ℂ) • ((((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k)
        = (((n : ℝ)⁻¹ : ℝ) : ℂ) • P.proj k := by
      intro k
      have hr : blockRank P k ≠ 0 := ne_of_gt (blockRank_pos P k (hrank k))
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      field_simp
    simp_rw [hterm]
    rw [← Finset.smul_sum, P.sum_eq_one]

theorem uniformBlockDecomp_w_pos (P : ProjectorFamily n m) (hrank : ∀ k, P.proj k ≠ 0)
    [NeZero n] (k : Fin m) : 0 < (uniformBlockDecomp P hrank).w k :=
  div_pos (blockRank_pos P k (hrank k)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n)))

/-- `I/n` is positive definite. -/
theorem maximallyMixed_posDef (n : ℕ) [NeZero n] : (maximallyMixed n).M.PosDef := by
  have h : (maximallyMixed n).M = Matrix.diagonal (fun _ : Fin n => (((n : ℝ)⁻¹ : ℝ) : ℂ)) := by
    change (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = _
    rw [Matrix.smul_one_eq_diagonal]
  rw [h]
  exact Matrix.PosDef.diagonal (fun _ => Complex.zero_lt_real.mpr
    (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n)))))

/-- **The reset state against the uniform prior is the scalar state.** -/
theorem resetState_eq_scalarState (P : ProjectorFamily n m) (ρ : DensityOp n)
    (hrank : ∀ k, P.proj k ≠ 0) [NeZero n] :
    resetState (pinchBlockDecomp P ρ hrank) (uniformBlockDecomp P hrank) = scalarState P ρ := by
  refine DensityOp.ext ?_
  change ∑ k, ((sectorWeight P ρ k : ℝ) : ℂ) • ((((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k)
    = ∑ k, ((sectorWeight P ρ k / blockRank P k : ℝ) : ℂ) • P.proj k
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul, ← Complex.ofReal_mul, div_eq_mul_inv]

/-- The classical divergence against the uniform sector weights:
`D_KL(p ‖ r/n) = log n − (H(p) + Σ_k p_k log r_k)`. -/
theorem blockKL_uniform (P : ProjectorFamily n m) (ρ : DensityOp n)
    (hrank : ∀ k, P.proj k ≠ 0) [NeZero n] :
    blockKL (sectorWeight P ρ) (fun k => blockRank P k / n)
      = Real.log n - (∑ k, Real.negMulLog (sectorWeight P ρ k)
          + ∑ k, sectorWeight P ρ k * Real.log (blockRank P k)) := by
  unfold blockKL
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hterm : ∀ k, sectorWeight P ρ k * Real.log (sectorWeight P ρ k / (blockRank P k / n))
      = sectorWeight P ρ k * Real.log n
        - (Real.negMulLog (sectorWeight P ρ k)
            + sectorWeight P ρ k * Real.log (blockRank P k)) := by
    intro k
    have hr : 0 < blockRank P k := blockRank_pos P k (hrank k)
    rcases (sectorWeight_nonneg P ρ k).lt_or_eq with hw | hw
    · rw [Real.log_div (ne_of_gt hw) (ne_of_gt (div_pos hr hn)),
        Real.log_div (ne_of_gt hr) (ne_of_gt hn)]
      simp only [Real.negMulLog]
      ring
    · rw [← hw]
      simp [Real.negMulLog]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib, ← Finset.sum_mul,
    sectorWeight_sum, one_mul, Finset.sum_add_distrib]

/-! ### The main theorem -/

/-- **VCT scalarity — matrix form.**

Let `P` be a projector family with nonzero projectors, `C j` constraints admitting
`P` as joint eigenprojectors (`C j * Π_k = eigval j k • Π_k`), and `ρ*` a feasible
state maximising the von Neumann entropy among feasible states.  Then

  `ρ* = scalarState P ρ* = Σ_k (Tr(Π_k ρ*) / Tr Π_k) • Π_k`

— `ρ*` is block diagonal **and** scalar on every block. -/
theorem vct_scalarity (P : ProjectorFamily n m) (hrank : ∀ k, P.proj k ≠ 0)
    {K : ℕ} (C : Fin K → Matrix (Fin n) (Fin n) ℂ) (eigval : Fin K → Fin m → ℂ)
    (hC_eig : ∀ j k, C j * P.proj k = eigval j k • P.proj k)
    (c : Fin K → ℂ) (ρ_star : DensityOp n)
    (h_feas : ∀ j, (ρ_star.M * C j).trace = c j)
    (h_max : ∀ σ : DensityOp n, (∀ j, (σ.M * C j).trace = c j) →
      vonNeumannEntropy σ ≤ vonNeumannEntropy ρ_star) :
    ρ_star = scalarState P ρ_star := by
  haveI : NeZero n := ⟨ρ_star.n_ne_zero⟩
  set A := pinchBlockDecomp P ρ_star hrank with hA
  set S := uniformBlockDecomp P hrank with hS
  have hq : ∀ k, 0 < S.w k := uniformBlockDecomp_w_pos P hrank
  have hpos : (maximallyMixed n).M.PosDef := maximallyMixed_posDef n
  have hreset : resetState A S = scalarState P ρ_star :=
    resetState_eq_scalarState P ρ_star hrank
  -- maximality: `S(scalar) ≤ S(ρ*)` (the scalar state is feasible)
  have h1 : vonNeumannEntropy (scalarState P ρ_star) ≤ vonNeumannEntropy ρ_star :=
    h_max _ (scalarState_feasible P ρ_star C eigval hC_eig c h_feas)
  -- the classical bound is `log n − S(scalar)`
  have h2 : blockKL A.w S.w = Real.log n - vonNeumannEntropy (scalarState P ρ_star) := by
    rw [← relEntropy_resetState_eq_blockKL A S hq hpos, hreset, relEntropy_maximallyMixed]
  -- Theorem 2 inequality: `blockKL ≤ D(ρ*‖I/n) = log n − S(ρ*)`
  have h3 : blockKL A.w S.w ≤ Real.log n - vonNeumannEntropy ρ_star := by
    rw [← relEntropy_maximallyMixed]
    exact relEntropy_ge_blockKL A S hq hpos
  -- hence equality, and the characterisation gives the matrix statement
  have h4 : relativeEntropy ρ_star (maximallyMixed n) = blockKL A.w S.w := by
    rw [relEntropy_maximallyMixed]
    linarith
  exact ((relEntropy_eq_blockKL_iff_reset A S hq hpos).mp h4).trans hreset

/-! ### Readable corollaries -/

/-- **Block diagonality**: `Δρ* = ρ*`. -/
theorem vct_scalarity_pinch_fixed (P : ProjectorFamily n m) (hrank : ∀ k, P.proj k ≠ 0)
    {K : ℕ} (C : Fin K → Matrix (Fin n) (Fin n) ℂ) (eigval : Fin K → Fin m → ℂ)
    (hC_eig : ∀ j k, C j * P.proj k = eigval j k • P.proj k)
    (c : Fin K → ℂ) (ρ_star : DensityOp n)
    (h_feas : ∀ j, (ρ_star.M * C j).trace = c j)
    (h_max : ∀ σ : DensityOp n, (∀ j, (σ.M * C j).trace = c j) →
      vonNeumannEntropy σ ≤ vonNeumannEntropy ρ_star) :
    pinchDensityOp P ρ_star = ρ_star := by
  have h := vct_scalarity P hrank C eigval hC_eig c ρ_star h_feas h_max
  calc pinchDensityOp P ρ_star = pinchDensityOp P (scalarState P ρ_star) := congrArg _ h
    _ = scalarState P ρ_star := pinch_scalarState P ρ_star
    _ = ρ_star := h.symm

/-- **Block scalarity**: on every block of positive weight, the normalised block state
`Π_k ρ* Π_k / p_k` is the maximally mixed state `Π_k / r_k`.  Zero-weight blocks are
not quantified over. -/
theorem vct_scalarity_block (P : ProjectorFamily n m) (hrank : ∀ k, P.proj k ≠ 0)
    {K : ℕ} (C : Fin K → Matrix (Fin n) (Fin n) ℂ) (eigval : Fin K → Fin m → ℂ)
    (hC_eig : ∀ j k, C j * P.proj k = eigval j k • P.proj k)
    (c : Fin K → ℂ) (ρ_star : DensityOp n)
    (h_feas : ∀ j, (ρ_star.M * C j).trace = c j)
    (h_max : ∀ σ : DensityOp n, (∀ j, (σ.M * C j).trace = c j) →
      vonNeumannEntropy σ ≤ vonNeumannEntropy ρ_star)
    (k : Fin m) (hk : 0 < sectorWeight P ρ_star k) :
    ((sectorWeight P ρ_star k : ℝ) : ℂ)⁻¹ • (P.proj k * ρ_star.M * P.proj k)
      = (((blockRank P k)⁻¹ : ℝ) : ℂ) • P.proj k := by
  have h := vct_scalarity P hrank C eigval hC_eig c ρ_star h_feas h_max
  have hblock : P.proj k * ρ_star.M * P.proj k
      = ((sectorWeight P ρ_star k / blockRank P k : ℝ) : ℂ) • P.proj k := by
    conv_lhs => rw [h]
    exact proj_mul_scalarState_mul_proj P ρ_star k
  rw [hblock, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 2
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk), one_mul]

/-- The entropy of the scalar state is `H(p) + Σ_k p_k log r_k` — the value Paper W's
Step 2 assigns to the block-depolarised maximizer. -/
theorem entropy_scalarState (P : ProjectorFamily n m) (ρ : DensityOp n)
    (hrank : ∀ k, P.proj k ≠ 0) :
    vonNeumannEntropy (scalarState P ρ)
      = ∑ k, Real.negMulLog (sectorWeight P ρ k)
        + ∑ k, sectorWeight P ρ k * Real.log (blockRank P k) := by
  haveI : NeZero n := ⟨ρ.n_ne_zero⟩
  have h := relEntropy_resetState_eq_blockKL (pinchBlockDecomp P ρ hrank)
    (uniformBlockDecomp P hrank) (uniformBlockDecomp_w_pos P hrank) (maximallyMixed_posDef n)
  rw [resetState_eq_scalarState, relEntropy_maximallyMixed] at h
  have hKL := blockKL_uniform P ρ hrank
  change blockKL (sectorWeight P ρ) (fun k => blockRank P k / n) = _ at hKL
  change _ = blockKL (sectorWeight P ρ) (fun k => blockRank P k / n) at h
  linarith

end MacadayPhysicsLean.VCTScalarity
