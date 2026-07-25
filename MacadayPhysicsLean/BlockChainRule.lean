/-
**The direct-sum chain rule** — Paper R, Proposition 2 (§3.4); the refinement
that turns the two-term pinching Pythagorean identity into the three-defect
decomposition of Theorem 4 (§7.1).

  `D(⊕ p_λ τ_λ ‖ ⊕ q_λ ω_λ) = D_KL(p‖q) + Σ_λ p_λ D(τ_λ‖ω_λ)`

**Scope, inherited from the paper.** Proposition 2 hypothesises `q_λ > 0` and
`ω_λ` faithful on `H_λ` — the *reference* side is blockwise faithful — while the
`p`-side is free (`p_λ ≥ 0`, `τ_λ` arbitrary), blocks with `p_λ = 0` contributing
zero by the `0 log 0 = 0` convention.  Given a block decomposition, that pair of
hypotheses is exactly `ω.M.PosDef`, which is how it is stated here.

**Machinery.** Everything reduces to two facts about the block-adapted basis
`JointDiagonalization.adaptedBasis`, both consequences of the keystone
`cfc_apply_eigenvector`:

* a block-diagonal state is pinch-fixed, so `adaptedBasis P ω` diagonalises `ω`
  itself (not merely `Δω`), and hence also `log ω`, every projector `Π_λ`, and
  every block state — one common eigenbasis for all of it;
* the functional calculus of an operator supported in `ran Π` is again supported
  there, whenever `f 0 = 0` (`cfc_supported`), which is what confines
  `log ω_λ` to its own block.
-/

import MacadayPhysicsLean.ChainRule
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Pinching JointDiagonalization
open scoped ComplexOrder

variable {n m : ℕ}

/-! ### A trace identity for operators sharing an eigenbasis

If the columns of a unitary `U` are eigenvectors of both `A` and `B`, then
`Tr(A B)` is the sum of the products of the eigenvalues.  This is the workhorse
below: `adaptedBasis P η` simultaneously diagonalises `η`, `log η`, every
projector, and every block state, so every trace in the chain rule collapses to
an eigenvalue sum through this lemma. -/

/-- If every column of `U` is an `A`-eigenvector with eigenvalue `a s`, then
`A U = U · diag a`. -/
theorem mul_eq_mul_diagonal_of_col_eigen {U : Matrix (Fin n) (Fin n) ℂ}
    {A : Matrix (Fin n) (Fin n) ℂ} {a : Fin n → ℂ}
    (hA : ∀ s, A *ᵥ Matrix.col U s = a s • Matrix.col U s) :
    A * U = U * Matrix.diagonal a := by
  ext i s
  have h := congrFun (hA s) i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, Matrix.col, dotProduct,
    Matrix.transpose_apply] at h
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  ring

/-- **Common-eigenbasis trace identity.** If the columns of the unitary `U` are
eigenvectors of `A` with eigenvalues `a` and of `B` with eigenvalues `b`, then
`Tr(A B) = Σ_s a s * b s`. -/
theorem trace_mul_of_col_eigen {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    {A B : Matrix (Fin n) (Fin n) ℂ} {a b : Fin n → ℂ}
    (hA : ∀ s, A *ᵥ Matrix.col U s = a s • Matrix.col U s)
    (hB : ∀ s, B *ᵥ Matrix.col U s = b s • Matrix.col U s) :
    (A * B).trace = ∑ s, a s * b s := by
  have hAB : ∀ s, (A * B) *ᵥ Matrix.col U s = (a s * b s) • Matrix.col U s := by
    intro s
    rw [← Matrix.mulVec_mulVec, hB s, Matrix.mulVec_smul, hA s, smul_smul,
      mul_comm]
  have hkey := mul_eq_mul_diagonal_of_col_eigen hAB
  have hstar : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  calc (A * B).trace
      = ((A * B) * (U * star U)).trace := by rw [hstar, Matrix.mul_one]
    _ = (((A * B) * U) * star U).trace := by rw [Matrix.mul_assoc (A * B) U (star U)]
    _ = ((U * Matrix.diagonal (fun s => a s * b s)) * star U).trace := by rw [hkey]
    _ = (Matrix.diagonal (fun s => a s * b s) * (star U * U)).trace := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ∑ s, a s * b s := by
          rw [Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mul_one,
            Matrix.trace_diagonal]

/-! ### The functional calculus preserves support

For `f 0 = 0`, `f(A)` lives in the same block as `A`.  This is what keeps
`log ω_λ` confined to `H_λ`, so that the cross terms of the chain rule vanish. -/

/-- If `A Q = 0` for an idempotent `Q`, then `f(A) Q = 0` whenever `f 0 = 0`:
the range of `Q` is killed by `A`, hence consists of `0`-eigenvectors, on which
`f(A)` acts as `f 0 = 0`. -/
theorem cfc_mul_eq_zero_of_mul_eq_zero {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) {f : ℝ → ℝ} (hf0 : f 0 = 0)
    (hQ : Q * Q = Q) (hAQ : A * Q = 0) :
    hA.cfc f * Q = 0 := by
  ext i j
  -- the `j`-th column of `Q` is fixed by `Q`, hence annihilated by `A`
  have hQcol : A *ᵥ Matrix.col Q j = ((0 : ℝ) : ℂ) • Matrix.col Q j := by
    have h : (A * Q) *ᵥ Matrix.col Q j = 0 := by rw [hAQ, Matrix.zero_mulVec]
    rw [← Matrix.mulVec_mulVec] at h
    have hfix : Q *ᵥ Matrix.col Q j = Matrix.col Q j := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply]
      simpa [Matrix.mul_apply] using congrFun (congrFun hQ i) j
    rw [hfix] at h
    rw [Complex.ofReal_zero, zero_smul]
    exact h
  have hcfc := cfc_apply_eigenvector hA f hQcol
  rw [hf0] at hcfc
  have hij := congrFun hcfc i
  simpa [Matrix.col, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply] using hij

/-- **The functional calculus preserves block support.** If `A` is Hermitian and
supported in the range of the Hermitian idempotent `Π` (i.e. `Π A = A`), and
`f 0 = 0`, then `f(A)` is supported there too, on both sides. -/
theorem cfc_supported {A Q : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hQh : Q.IsHermitian) (hQi : Q * Q = Q) (hsupp : Q * A = A)
    {f : ℝ → ℝ} (hf0 : f 0 = 0) :
    hA.cfc f * Q = hA.cfc f ∧ Q * hA.cfc f = hA.cfc f := by
  -- the complementary projector
  have hcompl_idem : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hQi]
    abel
  -- `A` is annihilated by the complementary projector, on both sides
  have hAQ : A * Q = A := by
    have h := congrArg Matrix.conjTranspose hsupp
    rwa [Matrix.conjTranspose_mul, hA.eq, hQh.eq] at h
  have hAcompl : A * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hAQ, sub_self]
  have hzero := cfc_mul_eq_zero_of_mul_eq_zero hA hf0 hcompl_idem hAcompl
  have hright : hA.cfc f * Q = hA.cfc f := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hzero
    exact (sub_eq_zero.mp hzero).symm
  refine ⟨hright, ?_⟩
  -- the left version: `A` commutes with `Q`, hence so does `f(A)`
  have hcomm : Commute A Q := by
    change A * Q = Q * A
    rw [hAQ, hsupp]
  have hcomm' : Commute (hA.cfc f) Q := by
    rw [← hA.cfc_eq f]
    exact hcomm.cfc_real f
  rw [← hcomm'.eq, hright]

/-! ### Block decompositions

`η = ⊕_λ w_λ · st_λ` with each `st_λ` a state supported in block `λ`.  The paper
writes this as a direct sum over sectors; here the blocks stay embedded in the
ambient space, so no sub-space `DensityOp` ever has to be constructed. -/

/-- A **block decomposition** of `η` relative to the projector family `P`:
`η = ⊕_λ w_λ · st_λ`, each `st_λ` a state supported in `ran Π_λ`. -/
structure BlockDecomp (P : ProjectorFamily n m) (η : DensityOp n) where
  /-- The sector weights `p_λ` (or `q_λ` on the reference side). -/
  w : Fin m → ℝ
  /-- The normalised sector states `τ_λ` (or `ω_λ`), embedded in the full space. -/
  st : Fin m → DensityOp n
  /-- Weights are nonnegative. -/
  w_nonneg : ∀ k, 0 ≤ w k
  /-- Each sector state is supported in its own block. -/
  supported : ∀ k, P.proj k * (st k).M = (st k).M
  /-- The decomposition reproduces `η`. -/
  sum_eq : η.M = ∑ k, (w k : ℂ) • (st k).M

namespace BlockDecomp

variable {P : ProjectorFamily n m} {η : DensityOp n}

/-- Support on the right as well, by Hermitian symmetry. -/
theorem supported_right (B : BlockDecomp P η) (k : Fin m) :
    (B.st k).M * P.proj k = (B.st k).M := by
  have h := congrArg Matrix.conjTranspose (B.supported k)
  rwa [Matrix.conjTranspose_mul, (B.st k).isHermitian.eq, (P.isHermitian k).eq] at h

/-- A projector annihilates the states of the other blocks. -/
theorem proj_mul_st_eq_zero (B : BlockDecomp P η) {k j : Fin m} (hkj : k ≠ j) :
    P.proj k * (B.st j).M = 0 := by
  rw [← B.supported j, ← Matrix.mul_assoc, P.ortho k j hkj, Matrix.zero_mul]

theorem st_mul_proj_eq_zero (B : BlockDecomp P η) {k j : Fin m} (hkj : k ≠ j) :
    (B.st j).M * P.proj k = 0 := by
  rw [← B.supported_right j, Matrix.mul_assoc, P.ortho j k (Ne.symm hkj),
    Matrix.mul_zero]

/-- **`Π_λ η = w_λ · st_λ`** — the projector reads off exactly one block. -/
theorem proj_mul (B : BlockDecomp P η) (k : Fin m) :
    P.proj k * η.M = (B.w k : ℂ) • (B.st k).M := by
  rw [B.sum_eq, Matrix.mul_sum]
  rw [Finset.sum_eq_single k]
  · rw [Matrix.mul_smul, B.supported k]
  · intro j _ hjk
    rw [Matrix.mul_smul, B.proj_mul_st_eq_zero (Ne.symm hjk), smul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `η Π_λ = w_λ · st_λ` as well. -/
theorem mul_proj (B : BlockDecomp P η) (k : Fin m) :
    η.M * P.proj k = (B.w k : ℂ) • (B.st k).M := by
  rw [B.sum_eq, Finset.sum_mul]
  rw [Finset.sum_eq_single k]
  · rw [Matrix.smul_mul, B.supported_right k]
  · intro j _ hjk
    rw [Matrix.smul_mul, B.st_mul_proj_eq_zero (Ne.symm hjk), smul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- A block-decomposed state commutes with every projector — i.e. it satisfies
the paper's compatibility hypothesis H2 and is block diagonal. -/
theorem commute (B : BlockDecomp P η) (k : Fin m) : Commute η.M (P.proj k) := by
  change η.M * P.proj k = P.proj k * η.M
  rw [B.mul_proj, B.proj_mul]

/-- Hence a block-decomposed state is fixed by the pinching map. -/
theorem pinch_eq (B : BlockDecomp P η) : pinchDensityOp P η = η :=
  pinchDensityOp_eq_self_of_commute P η B.commute

/-- The sector weights sum to `1`. -/
theorem w_sum (B : BlockDecomp P η) : ∑ k, B.w k = 1 := by
  have ht := η.trace_one
  rw [B.sum_eq, Matrix.trace_sum] at ht
  simp only [Matrix.trace_smul, smul_eq_mul, DensityOp.trace_one, mul_one] at ht
  exact_mod_cast ht

end BlockDecomp

/-! ### The canonical block decomposition of a compatible state

Paper R states Theorem 1 from the compatibility hypothesis `[σ, C_k] = 0`, and
*derives* the sector decomposition `σ = ⊕_λ s_λ σ_λ` with `s_λ = Tr(Π_λ σ)` and
`σ_λ = Π_λ σ Π_λ / s_λ`.  This section supplies that derivation as a
`BlockDecomp`, so the paper-shaped Theorem 1 is one `chain_rule` application away
— the compatibility hypothesis is the input, the decomposition is the output,
exactly matching the paper's logical shape rather than assuming the decomposition
as data.

The only extra input is `0 < s_λ` for every sector — the paper's occupied-sector
condition — which is also precisely `chain_rule`'s reference-weight hypothesis.
Zero-weight sectors carry no state to normalise, so the construction genuinely
needs it; for a faithful `σ` it holds in every sector with `Π_λ ≠ 0`. -/

/-- The canonical sector weight `s_λ = Tr(Π_λ σ)` (real, since `Π_λ σ Π_λ` is
positive semidefinite). -/
noncomputable def sectorWeight (P : ProjectorFamily n m) (σ : DensityOp n)
    (k : Fin m) : ℝ := (P.proj k * σ.M).trace.re

/-- `Tr(Π_λ σ Π_λ) = s_λ` as a complex identity — the block trace is the real
sector weight. -/
theorem trace_pinch_block (P : ProjectorFamily n m) (σ : DensityOp n) (k : Fin m) :
    (P.proj k * σ.M * P.proj k).trace = ((sectorWeight P σ k : ℝ) : ℂ) := by
  have hpsd := posSemidef_pinch_term P σ.posSemidef k
  have h : star (P.proj k * σ.M * P.proj k).trace = (P.proj k * σ.M * P.proj k).trace := by
    rw [← Matrix.trace_conjTranspose, hpsd.isHermitian.eq]
  have him : (P.proj k * σ.M * P.proj k).trace.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : (P.proj k * σ.M * P.proj k).trace.re = sectorWeight P σ k :=
    congrArg Complex.re (trace_pinch_term P σ.M k)
  rw [Complex.ext_iff]
  exact ⟨by rw [Complex.ofReal_re, hre], by rw [Complex.ofReal_im, him]⟩

/-- The canonical sector state `σ_λ = Π_λ σ Π_λ / s_λ`, for occupied sectors. -/
noncomputable def sectorState (P : ProjectorFamily n m) (σ : DensityOp n)
    (hs : ∀ k, 0 < sectorWeight P σ k) (k : Fin m) : DensityOp n where
  M := ((sectorWeight P σ k : ℝ) : ℂ)⁻¹ • (P.proj k * σ.M * P.proj k)
  posSemidef := by
    apply (posSemidef_pinch_term P σ.posSemidef k).smul
    rw [← Complex.ofReal_inv]
    exact Mathlib.Meta.Positivity.ofReal_nonneg (le_of_lt (inv_pos.mpr (hs k)))
  trace_one := by
    rw [Matrix.trace_smul, trace_pinch_block, smul_eq_mul, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (hs k)), Complex.ofReal_one]

/-- **The canonical block decomposition of a compatible state.**

If `σ` commutes with every constraint projector (`[σ, Π_λ] = 0`, the paper's H2)
and every sector is occupied (`0 < s_λ`), then `σ = ⊕_λ s_λ σ_λ` with
`s_λ = Tr(Π_λ σ)` and `σ_λ = Π_λ σ Π_λ / s_λ`. -/
noncomputable def blockDecomp_of_compat (P : ProjectorFamily n m) (σ : DensityOp n)
    (hcomm : ∀ k, Commute σ.M (P.proj k)) (hs : ∀ k, 0 < sectorWeight P σ k) :
    BlockDecomp P σ where
  w := sectorWeight P σ
  st := sectorState P σ hs
  w_nonneg := fun k => le_of_lt (hs k)
  supported := fun k => by
    show P.proj k * (((sectorWeight P σ k : ℝ) : ℂ)⁻¹ • (P.proj k * σ.M * P.proj k))
      = ((sectorWeight P σ k : ℝ) : ℂ)⁻¹ • (P.proj k * σ.M * P.proj k)
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.idem]
  sum_eq := by
    have hpinch : P.pinch σ.M = σ.M := congrArg DensityOp.M
      (pinchDensityOp_eq_self_of_commute P σ hcomm)
    rw [← hpinch, ProjectorFamily.pinch]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show P.proj k * σ.M * P.proj k
      = (sectorWeight P σ k : ℂ) • (((sectorWeight P σ k : ℝ) : ℂ)⁻¹
          • (P.proj k * σ.M * P.proj k))
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt (hs k)), one_smul]

/-! ### Positivity of the adapted eigenvalues of a faithful state -/

/-- For a block-diagonal **faithful** state, every adapted eigenvalue is
positive.  (`adaptedBasis P ω` diagonalises `ω` itself here, because `ω` is
pinch-fixed, so its `mu` are genuine eigenvalues of `ω`.) -/
theorem mu_pos_of_posDef {P : ProjectorFamily n m} {ω : DensityOp n}
    (B : BlockDecomp P ω) (hpos : ω.M.PosDef) (s : Fin n) : 0 < mu P ω s := by
  have hmem : mu P ω s ∈ Multiset.map (mu P ω) (Finset.univ : Finset (Fin n)).val :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ s)
  rw [multiset_mu_eq_eigenvalues P ω, B.pinch_eq] at hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  rw [← hi]
  exact hpos.eigenvalues_pos i

/-! ### Matrices are determined by their action on the adapted basis -/

/-- Two matrices agreeing on the block-adapted basis are equal. -/
theorem eq_of_mulVec_adaptedBasis {P : ProjectorFamily n m} {ρ : DensityOp n}
    {M N : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ s, M *ᵥ (⇑(adaptedBasis P ρ s) : Fin n → ℂ)
            = N *ᵥ (⇑(adaptedBasis P ρ s) : Fin n → ℂ)) : M = N := by
  set U : Matrix (Fin n) (Fin n) ℂ := (adaptedUnitary P ρ : Matrix (Fin n) (Fin n) ℂ)
    with hU
  have hcol : ∀ s, M *ᵥ Matrix.col U s = N *ᵥ Matrix.col U s := h
  have hMU : M * U = N * U := by
    ext i s
    have hi := congrFun (hcol s) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col,
      Matrix.transpose_apply] using hi
  have hstar : U * star U = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (adaptedUnitary P ρ).2
  calc M = M * (U * star U) := by rw [hstar, Matrix.mul_one]
    _ = (M * U) * star U := by rw [Matrix.mul_assoc]
    _ = (N * U) * star U := by rw [hMU]
    _ = N * (U * star U) := by rw [Matrix.mul_assoc]
    _ = N := by rw [hstar, Matrix.mul_one]

/-! ### The reference-side block logarithm

Proposition 2's opening step — "on an occupied block,
`log(q_λ ω_λ) = (log q_λ) I_λ + log ω_λ`" — as a single operator identity on the
whole space:

  `log(⊕_λ q_λ ω_λ) = Σ_λ (log q_λ) Π_λ + Σ_λ log ω_λ`.

The hypotheses `hq : ∀ λ, 0 < q_λ` and `hpos : ω.M.PosDef` are exactly the
paper's `q_λ > 0` and "`ω_λ` faithful on `H_λ`": given the block decomposition
and `q_λ > 0`, faithfulness of every block is equivalent to faithfulness of `ω`
on the whole space. -/

/-- Each block state is diagonal in the adapted basis of `ω`, with eigenvalue
`μ_s / q_λ` on its own block and `0` elsewhere. -/
theorem st_mulVec_adaptedBasis {P : ProjectorFamily n m} {ω : DensityOp n}
    (B : BlockDecomp P ω) {k : Fin m} (hq : 0 < B.w k) (s : Fin n) :
    (B.st k).M *ᵥ (⇑(adaptedBasis P ω s) : Fin n → ℂ)
      = (((if k = k_of P s then mu P ω s / B.w k else 0) : ℝ) : ℂ)
          • (⇑(adaptedBasis P ω s) : Fin n → ℂ) := by
  set e : Fin n → ℂ := (⇑(adaptedBasis P ω s) : Fin n → ℂ) with he
  have hω : ω.M *ᵥ e = ((mu P ω s : ℝ) : ℂ) • e := by
    have h := adaptedBasis_eigenvector_pinch_mulVec P ω s
    rwa [B.pinch_eq] at h
  -- `q_λ • (ω_λ v) = Π_λ (ω v) = μ_s • (Π_λ v)`
  have hkey : ((B.w k : ℝ) : ℂ) • ((B.st k).M *ᵥ e)
      = ((mu P ω s : ℝ) : ℂ) • (P.proj k *ᵥ e) := by
    rw [← Matrix.smul_mulVec, ← B.proj_mul, ← Matrix.mulVec_mulVec, hω,
      Matrix.mulVec_smul]
  have hwne : ((B.w k : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hq
  have hcancel : (B.st k).M *ᵥ e
      = (((B.w k : ℝ) : ℂ))⁻¹ • (((B.w k : ℝ) : ℂ) • ((B.st k).M *ᵥ e)) :=
    (inv_smul_smul₀ hwne _).symm
  by_cases hk : k = k_of P s
  · subst hk
    rw [if_pos rfl, hcancel, hkey, adaptedBasis_adapted_mulVec P ω s, smul_smul]
    congr 1
    push_cast
    ring
  · rw [proj_apply_zero_of_adapted P e (k_of P s)
      (adaptedBasis_adapted_mulVec P ω s) k hk, smul_zero] at hkey
    rw [if_neg hk, hcancel, hkey, smul_zero]
    simp

/-- **The reference-side operator identity.** -/
theorem logM_of_blockDecomp {P : ProjectorFamily n m} {ω : DensityOp n}
    (B : BlockDecomp P ω) (hq : ∀ k, 0 < B.w k) (hpos : ω.M.PosDef) :
    ω.logM = (∑ k, ((Real.log (B.w k) : ℝ) : ℂ) • P.proj k) + ∑ k, (B.st k).logM := by
  refine eq_of_mulVec_adaptedBasis (P := P) (ρ := ω) (fun s => ?_)
  set e : Fin n → ℂ := (⇑(adaptedBasis P ω s) : Fin n → ℂ) with he
  set k₀ : Fin m := k_of P s with hk₀
  have hmu : 0 < mu P ω s := mu_pos_of_posDef B hpos s
  -- left-hand side
  have hL : ω.logM *ᵥ e = ((Real.log (mu P ω s) : ℝ) : ℂ) • e :=
    logM_apply_adaptedBasis_of_commute P ω B.commute s
  -- the projector sum picks out block `k₀`
  have hP : (∑ k, ((Real.log (B.w k) : ℝ) : ℂ) • P.proj k) *ᵥ e
      = ((Real.log (B.w k₀) : ℝ) : ℂ) • e := by
    rw [Matrix.sum_mulVec]
    rw [Finset.sum_eq_single k₀]
    · rw [Matrix.smul_mulVec, adaptedBasis_adapted_mulVec P ω s]
    · intro j _ hj
      rw [Matrix.smul_mulVec,
        proj_apply_zero_of_adapted P e k₀ (adaptedBasis_adapted_mulVec P ω s) j hj,
        smul_zero]
    · intro h; exact absurd (Finset.mem_univ k₀) h
  -- the block-log sum picks out block `k₀` too, with value `log (μ_s / q_k₀)`
  have hS : (∑ k, (B.st k).logM) *ᵥ e
      = ((Real.log (mu P ω s / B.w k₀) : ℝ) : ℂ) • e := by
    rw [Matrix.sum_mulVec]
    rw [Finset.sum_eq_single k₀]
    · have := DensityOp.logM_apply_eigenvector (B.st k₀)
        (st_mulVec_adaptedBasis B (hq k₀) s)
      rwa [if_pos rfl] at this
    · intro j _ hj
      have := DensityOp.logM_apply_eigenvector (B.st j)
        (st_mulVec_adaptedBasis B (hq j) s)
      rw [if_neg hj, Real.log_zero] at this
      simpa using this
    · intro h; exact absurd (Finset.mem_univ k₀) h
  rw [hL, Matrix.add_mulVec, hP, hS, ← add_smul]
  congr 1
  rw [Real.log_div (ne_of_gt hmu) (ne_of_gt (hq k₀))]
  push_cast
  ring


/-! ### Trace bookkeeping in the adapted basis

Every trace appearing in the chain rule is a trace of a product of two operators
that are *simultaneously* diagonal in `adaptedBasis P η`: the state itself, its
logarithm, each projector, each of its own block states, and — via
`logM_of_blockDecomp` — the reference logarithm.  So each collapses to an
eigenvalue sum through `trace_mul_of_col_eigen`. -/

/-- Real-valued form of the common-eigenbasis trace identity, specialised to the
block-adapted basis. -/
theorem trace_mul_of_adapted_re {P : ProjectorFamily n m} {rho : DensityOp n}
    {A B : Matrix (Fin n) (Fin n) ℂ} {a b : Fin n → ℝ}
    (hA : ∀ s, A *ᵥ (⇑(adaptedBasis P rho s) : Fin n → ℂ)
            = ((a s : ℝ) : ℂ) • (⇑(adaptedBasis P rho s) : Fin n → ℂ))
    (hB : ∀ s, B *ᵥ (⇑(adaptedBasis P rho s) : Fin n → ℂ)
            = ((b s : ℝ) : ℂ) • (⇑(adaptedBasis P rho s) : Fin n → ℂ)) :
    (A * B).trace.re = ∑ s, a s * b s := by
  rw [trace_mul_of_col_eigen (adaptedUnitary P rho).2 hA hB]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- Each projector is diagonal in the adapted basis, with eigenvalue `1` on its
own block and `0` elsewhere. -/
theorem proj_mulVec_adaptedBasis (P : ProjectorFamily n m) (rho : DensityOp n)
    (k : Fin m) (s : Fin n) :
    P.proj k *ᵥ (⇑(adaptedBasis P rho s) : Fin n → ℂ)
      = (((if k = k_of P s then 1 else 0) : ℝ) : ℂ)
          • (⇑(adaptedBasis P rho s) : Fin n → ℂ) := by
  by_cases hk : k = k_of P s
  · subst hk
    rw [if_pos rfl]
    simpa using adaptedBasis_adapted_mulVec P rho s
  · rw [if_neg hk]
    simpa using proj_apply_zero_of_adapted P _ (k_of P s)
      (adaptedBasis_adapted_mulVec P rho s) k hk

namespace BlockDecomp

variable {P : ProjectorFamily n m} {η : DensityOp n}

/-- A block-diagonal state is diagonal in its own adapted basis. -/
theorem self_mulVec_adaptedBasis (A : BlockDecomp P η) (s : Fin n) :
    η.M *ᵥ (⇑(adaptedBasis P η s) : Fin n → ℂ)
      = ((mu P η s : ℝ) : ℂ) • (⇑(adaptedBasis P η s) : Fin n → ℂ) := by
  have h := adaptedBasis_eigenvector_pinch_mulVec P η s
  rwa [A.pinch_eq] at h

/-- The adapted eigenvalues of a state are nonnegative. -/
theorem mu_nonneg (A : BlockDecomp P η) (s : Fin n) : 0 ≤ mu P η s := by
  have hmem : mu P η s ∈ Multiset.map (mu P η) (Finset.univ : Finset (Fin n)).val :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ s)
  rw [multiset_mu_eq_eigenvalues P η, A.pinch_eq] at hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  rw [← hi]
  exact η.posSemidef.eigenvalues_nonneg i

/-- **Sector weights are eigenvalue sums**: `p_λ = Σ_{s ∈ λ} μ_s`. -/
theorem w_eq_sum_mu (A : BlockDecomp P η) (k : Fin m) :
    A.w k = ∑ s, (if k = k_of P s then mu P η s else 0) := by
  have h : (P.proj k * η.M).trace.re
      = ∑ s, (if k = k_of P s then (1 : ℝ) else 0) * mu P η s :=
    trace_mul_of_adapted_re (proj_mulVec_adaptedBasis P η k) (A.self_mulVec_adaptedBasis)
  rw [A.proj_mul k, Matrix.trace_smul, (A.st k).trace_one, smul_eq_mul, mul_one,
    Complex.ofReal_re] at h
  rw [h]
  exact Finset.sum_congr rfl (fun s _ => by split <;> simp)

/-- If a sector is unoccupied, every adapted eigenvalue in it vanishes. -/
theorem mu_eq_zero_of_w_eq_zero (A : BlockDecomp P η) {k : Fin m} (hk : A.w k = 0)
    {s : Fin n} (hs : k = k_of P s) : mu P η s = 0 := by
  have hsum := (A.w_eq_sum_mu k).symm.trans hk
  have hnn : ∀ t ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (if k = k_of P t then mu P η t else 0) := by
    intro t _; split
    · exact A.mu_nonneg t
    · exact le_refl 0
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum s (Finset.mem_univ s)
  rwa [if_pos hs] at this

/-- **The self term, blockwise**: `Tr(η log η)` restricted to sector `λ` is
`p_λ log p_λ + p_λ Tr(τ_λ log τ_λ)`. -/
theorem block_selfterm (A : BlockDecomp P η) (k : Fin m) :
    A.w k * Real.log (A.w k) + A.w k * ((A.st k).M * (A.st k).logM).trace.re
      = ∑ s, (if k = k_of P s then mu P η s * Real.log (mu P η s) else 0) := by
  rcases eq_or_lt_of_le (A.w_nonneg k) with hw | hw
  · -- unoccupied sector: both sides vanish
    rw [← hw]
    simp only [Real.log_zero, zero_mul, mul_zero, add_zero]
    refine (Finset.sum_eq_zero (fun s _ => ?_)).symm
    by_cases hs : k = k_of P s
    · rw [if_pos hs, A.mu_eq_zero_of_w_eq_zero hw.symm hs, zero_mul]
    · rw [if_neg hs]
  · -- occupied sector: `Tr(τ_λ log τ_λ)` is an eigenvalue sum over that block
    set t : Fin n → ℝ := fun s => if k = k_of P s then mu P η s / A.w k else 0 with ht
    have hst : ∀ s, (A.st k).M *ᵥ (⇑(adaptedBasis P η s) : Fin n → ℂ)
        = ((t s : ℝ) : ℂ) • (⇑(adaptedBasis P η s) : Fin n → ℂ) :=
      fun s => st_mulVec_adaptedBasis A hw s
    have hlog : ∀ s, (A.st k).logM *ᵥ (⇑(adaptedBasis P η s) : Fin n → ℂ)
        = ((Real.log (t s) : ℝ) : ℂ) • (⇑(adaptedBasis P η s) : Fin n → ℂ) :=
      fun s => DensityOp.logM_apply_eigenvector _ (hst s)
    rw [trace_mul_of_adapted_re hst hlog, Finset.mul_sum]
    -- rewrite each block term and telescope the `log p_λ` contributions
    have hterm : ∀ s, A.w k * (t s * Real.log (t s))
        = (if k = k_of P s then mu P η s * Real.log (mu P η s) else 0)
          - (if k = k_of P s then mu P η s else 0) * Real.log (A.w k) := by
      intro s
      by_cases hs : k = k_of P s
      · rw [if_pos hs, if_pos hs, ht]
        simp only [if_pos hs]
        rcases eq_or_lt_of_le (A.mu_nonneg s) with hmu | hmu
        · rw [← hmu]; simp
        · rw [Real.log_div (ne_of_gt hmu) (ne_of_gt hw)]
          field_simp
      · rw [if_neg hs, if_neg hs, ht]
        simp only [if_neg hs, Real.log_zero, mul_zero, zero_mul, sub_zero]
    rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← A.w_eq_sum_mu k]
    ring



/-! ### The chain rule -/

/-- **The self term**: `Tr(η log η) = Σ_λ [p_λ log p_λ + p_λ Tr(τ_λ log τ_λ)]`. -/
theorem trace_mul_logM_self_block (A : BlockDecomp P η) :
    (η.M * η.logM).trace.re
      = ∑ k, (A.w k * Real.log (A.w k)
              + A.w k * ((A.st k).M * (A.st k).logM).trace.re) := by
  have hL : (η.M * η.logM).trace.re = ∑ s, mu P η s * Real.log (mu P η s) :=
    trace_mul_of_adapted_re A.self_mulVec_adaptedBasis
      (logM_apply_adaptedBasis_of_commute P η A.commute)
  rw [hL, Finset.sum_congr rfl (fun k _ => A.block_selfterm k), Finset.sum_comm]
  exact (Finset.sum_congr rfl (fun s _ => by simp)).symm

/-- **The cross term**: `Tr(η log ω) = Σ_λ [p_λ log q_λ + p_λ Tr(τ_λ log ω_λ)]`,
for a blockwise-faithful reference `ω`. -/
theorem trace_mul_logM_cross_block {ω : DensityOp n}
    (A : BlockDecomp P η) (Bo : BlockDecomp P ω)
    (hq : ∀ k, 0 < Bo.w k) (hpos : ω.M.PosDef) :
    (η.M * ω.logM).trace.re
      = ∑ k, (A.w k * Real.log (Bo.w k)
              + A.w k * ((A.st k).M * (Bo.st k).logM).trace.re) := by
  rw [logM_of_blockDecomp Bo hq hpos, Matrix.mul_add, Matrix.trace_add,
    Complex.add_re, Finset.sum_add_distrib]
  congr 1
  · -- the `Σ_λ (log q_λ) Π_λ` part reads off the sector weights
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.mul_smul, Matrix.trace_smul, A.mul_proj k, Matrix.trace_smul,
      (A.st k).trace_one]
    simp [mul_comm]
  · -- the `Σ_λ log ω_λ` part is confined to its own block by `cfc_supported`
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hsupp : P.proj k * (Bo.st k).logM = (Bo.st k).logM :=
      (cfc_supported (Bo.st k).isHermitian (P.isHermitian k) (P.idem k)
        (Bo.supported k) Real.log_zero).2
    calc (η.M * (Bo.st k).logM).trace.re
        = ((η.M * P.proj k) * (Bo.st k).logM).trace.re := by
            rw [Matrix.mul_assoc, hsupp]
      _ = ((((A.w k : ℝ) : ℂ) • (A.st k).M) * (Bo.st k).logM).trace.re := by
            rw [A.mul_proj]
      _ = A.w k * ((A.st k).M * (Bo.st k).logM).trace.re := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
              Complex.re_ofReal_mul]

end BlockDecomp

/-- Classical Kullback–Leibler divergence of two sector-weight vectors,
`D_KL(p‖q) = Σ_λ p_λ log (p_λ / q_λ)`, with the `0 log 0 = 0` convention. -/
noncomputable def blockKL (p q : Fin m → ℝ) : ℝ := ∑ k, p k * Real.log (p k / q k)

/-- **Proposition 2 — the direct-sum chain rule.**

For `η = ⊕_λ p_λ τ_λ` and `ω = ⊕_λ q_λ ω_λ` with `q_λ > 0` and each `ω_λ`
faithful on its block (jointly: `ω` faithful),

  `D(η‖ω) = D_KL(p‖q) + Σ_λ p_λ D(τ_λ‖ω_λ)`.

The `p`-side is unconstrained — sectors with `p_λ = 0` contribute zero on both
sides by the `0 log 0 = 0` convention, exactly as the paper scopes it. -/
theorem chain_rule {P : ProjectorFamily n m} {η ω : DensityOp n}
    (A : BlockDecomp P η) (Bo : BlockDecomp P ω)
    (hq : ∀ k, 0 < Bo.w k) (hpos : ω.M.PosDef) :
    DensityOp.relativeEntropy η ω
      = blockKL A.w Bo.w
        + ∑ k, A.w k * DensityOp.relativeEntropy (A.st k) (Bo.st k) := by
  rw [DensityOp.relativeEntropy, A.trace_mul_logM_self_block,
    A.trace_mul_logM_cross_block Bo hq hpos, blockKL, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [DensityOp.relativeEntropy]
  rcases eq_or_lt_of_le (A.w_nonneg k) with hw | hw
  · rw [← hw]; simp
  · rw [Real.log_div (ne_of_gt hw) (ne_of_gt (hq k))]; ring

/-! ### The matching-weights chain rule (channel-form middle term)

The channel form of Theorems 1 and 4 needs `D(Δρ‖R_σ(ρ)) = Σ_λ p_λ D(τ_λ‖σ_λ)`,
where `Δρ = ⊕_λ p_λ τ_λ` and `R_σ(ρ) = ⊕_λ p_λ σ_λ` carry the **same** weights.
`chain_rule` doesn't apply directly: `R_σ(ρ)` need not be faithful (its weights
can vanish, and it is not full-space `PosDef`).  But when the weights match, the
`D_KL(p‖p)` term is zero and the identity survives — provided the reference is
faithful on each *occupied* block, which is exactly what a faithful prior/
equilibrium supplies.  Unoccupied blocks vanish on both sides by the
`0 log 0 = 0` convention.

The hypothesis is stated as `homega : ∀ s, k_of P s = k → 0 < mu P ω s` — the
`ω`-eigenvalues in an occupied sector are positive — which is precisely
blockwise faithfulness, and is `mu_pos_of_posDef` in the full-space case. -/

/-- **Local log-split on an occupied block.** For a block `k` with `Bo.w k > 0`
whose `ω`-eigenvalues are positive, the operator logarithm restricted to that
block splits as `(log q_λ) Π_λ + log ω_λ`.  Unlike `logM_of_blockDecomp`, this
needs positivity only on the single block `k`, so other blocks may be
unoccupied. -/
theorem logM_local_split {P : ProjectorFamily n m} {ω : DensityOp n}
    (Bo : BlockDecomp P ω) {k : Fin m} (hk : 0 < Bo.w k)
    (homega : ∀ s, k_of P s = k → 0 < mu P ω s) :
    P.proj k * ω.logM * P.proj k
      = ((Real.log (Bo.w k) : ℝ) : ℂ) • P.proj k + (Bo.st k).logM := by
  refine eq_of_mulVec_adaptedBasis (P := P) (ρ := ω) (fun s => ?_)
  have hωlog := logM_apply_adaptedBasis_of_commute P ω Bo.commute s
  have hstlog := DensityOp.logM_apply_eigenvector (Bo.st k) (st_mulVec_adaptedBasis Bo hk s)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
  by_cases hk' : k = k_of P s
  · subst hk'
    have hμ : 0 < mu P ω s := homega s rfl
    rw [proj_mulVec_adaptedBasis P ω (k_of P s) s]
    simp only [↓reduceIte, Complex.ofReal_one, one_smul]
    rw [hωlog, Matrix.mulVec_smul, proj_mulVec_adaptedBasis P ω (k_of P s) s]
    simp only [↓reduceIte, Complex.ofReal_one, one_smul]
    rw [hstlog]
    simp only [↓reduceIte]
    rw [← add_smul]
    congr 1
    rw [← Complex.ofReal_add]
    congr 1
    rw [Real.log_div (ne_of_gt hμ) (ne_of_gt hk)]; ring
  · rw [proj_mulVec_adaptedBasis P ω k s]
    simp only [if_neg hk', Complex.ofReal_zero, zero_smul, Matrix.mulVec_zero, smul_zero]
    rw [hstlog]
    simp [if_neg hk', Real.log_zero]

/-- **The self-term as a block sum with matching structure.** -/
theorem BlockDecomp.trace_mul_logM_cross_matched {P : ProjectorFamily n m}
    {η ω : DensityOp n} (A : BlockDecomp P η) (Bo : BlockDecomp P ω)
    (hmatch : ∀ k, A.w k = Bo.w k)
    (homega : ∀ s, 0 < A.w (k_of P s) → 0 < mu P ω s) :
    (η.M * ω.logM).trace.re
      = ∑ k, (A.w k * Real.log (Bo.w k)
              + A.w k * ((A.st k).M * (Bo.st k).logM).trace.re) := by
  -- Tr(η log ω) = Σ_k Tr((Π_k η) log ω) = Σ_k A.w k · Tr(st_k · log ω)
  have hsplit : (η.M * ω.logM).trace = ∑ k, (P.proj k * η.M * ω.logM).trace := by
    rw [← Matrix.trace_sum]
    congr 1
    rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, Matrix.one_mul]
  rw [hsplit, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases eq_or_lt_of_le (A.w_nonneg k) with hw | hw
  · -- unoccupied block: η's block is 0, both sides vanish
    rw [A.proj_mul k, ← hw]
    simp
  · -- occupied block: use the local split
    have hk : 0 < Bo.w k := hmatch k ▸ hw
    have homega' : ∀ s, k_of P s = k → 0 < mu P ω s := fun s hs =>
      homega s (by rw [hs]; exact hw)
    have hloc := logM_local_split Bo hk homega'
    have hstsupp : (A.st k).M * P.proj k = (A.st k).M := A.supported_right k
    -- Tr(Π_k η · logω) = A.w k · Tr(st_k · (Π_k logω Π_k))  (trace cyclicity)
    have htr : ((A.st k).M * (P.proj k * ω.logM * P.proj k)).trace
        = ((A.st k).M * ω.logM).trace := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hstsupp, Matrix.trace_mul_cycle,
        A.supported k]
    have hstep : (P.proj k * η.M * ω.logM).trace
        = (A.w k : ℂ) * ((A.st k).M * (P.proj k * ω.logM * P.proj k)).trace := by
      rw [htr, A.proj_mul k, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have hone : ((A.st k).M * P.proj k).trace = 1 := by rw [hstsupp, (A.st k).trace_one]
    rw [hstep, hloc, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, hone, mul_one]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring

/-- **The matching-weights chain rule** (channel-form middle term).

`D(⊕ p_λ τ_λ ‖ ⊕ p_λ ω_λ) = Σ_λ p_λ D(τ_λ‖ω_λ)` when the two states carry the
same sector weights and `ω` is faithful on every occupied block.  The `D_KL`
term is zero because the weights match. -/
theorem chain_rule_matched {P : ProjectorFamily n m} {η ω : DensityOp n}
    (A : BlockDecomp P η) (Bo : BlockDecomp P ω)
    (hmatch : ∀ k, A.w k = Bo.w k)
    (homega : ∀ s, 0 < A.w (k_of P s) → 0 < mu P ω s) :
    DensityOp.relativeEntropy η ω
      = ∑ k, A.w k * DensityOp.relativeEntropy (A.st k) (Bo.st k) := by
  rw [DensityOp.relativeEntropy, A.trace_mul_logM_self_block,
    A.trace_mul_logM_cross_matched Bo hmatch homega, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [DensityOp.relativeEntropy, hmatch k]
  ring

end MacadayPhysicsLean
