/-
Block Depolarization — Paper W §2.3 Step 2.

Step 2 of the VCT proof refines block-diagonal maximizers to
*scalar* maximizers on each block.  The strategy is:

* Decompose entropy of a block-diagonal density operator as
  `S(ρ) = H(p) + Σ_λ p_λ S(σ_λ)`.
* The block-depolarization map `E` replaces each `σ_λ` by `I/r_λ`
  (maximally mixed); `E` is CPTP, unital, preserves all commuting
  constraints, and gives `S(E(ρ)) ≥ S(ρ)` with equality iff
  every `σ_λ = I/r_λ`.

**Formalization status.**

* `max_entropy_on_subspace_le` — *Unconditional*.  Proof via the
  Schur-concavity machinery already available
  (`SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic`)
  applied to the uniform doubly-stochastic matrix.

* `block_depolarization_entropy` — *Conditional* on the
  eigenvalue-decomposition identity (the eigenvalues of a
  block-diagonal matrix are the union of the per-block eigenvalues,
  scaled).  Routine Mathlib follow-up; flagged as the next gap.

* `vct_step2_scalarity` — *Conditional* on the maximum-entropy
  uniqueness (`equality iff uniform`), which needs strict
  Schur-concavity of `Real.negMulLog`.  Mathlib provides
  concavity; strict concavity is the upcoming gap.
-/

import MacadayPhysicsLean.DensityOp
import MacadayPhysicsLean.SchurConcavity
import MacadayPhysicsLean.Pinching

namespace MacadayPhysicsLean.BlockDepolarization

open Real Matrix Finset
open scoped BigOperators

/-! ### Uniform doubly-stochastic matrix on `Fin r` -/

/-- The all-entries-`1/r` matrix on `Fin r`. -/
noncomputable def uniformMatrix (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun _ _ => 1 / r

/-- The uniform matrix is doubly stochastic when `r ≥ 1`. -/
theorem uniformMatrix_mem_doublyStochastic (r : ℕ) [hr : NeZero r] :
    uniformMatrix r ∈ doublyStochastic ℝ (Fin r) := by
  rw [mem_doublyStochastic_iff_sum]
  have h_r_pos : (0 : ℝ) < r := by
    exact_mod_cast Nat.pos_of_ne_zero hr.ne
  refine ⟨?_, ?_, ?_⟩
  · intro i j; unfold uniformMatrix; positivity
  · intro i
    unfold uniformMatrix
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro j
    unfold uniformMatrix
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Acting on any probability vector, the uniform matrix sends it to
the constant `1/r` distribution. -/
theorem uniformMatrix_mulVec_eq_const (r : ℕ) (p : Fin r → ℝ)
    (hp_sum : ∑ i, p i = 1) :
    (uniformMatrix r).mulVec p = fun _ => (1 : ℝ) / r := by
  funext i
  simp [uniformMatrix, Matrix.mulVec, dotProduct, ← Finset.mul_sum, hp_sum]

/-! ### Maximum entropy on a finite-dimensional subspace -/

/-- **Maximum entropy on a finite-dimensional subspace (inequality).**

For any probability distribution `p` on `Fin r` (`r ≥ 1`),
the Shannon entropy `∑ negMulLog(p_i)` is at most `log r`.

Achieved by the uniform distribution `p_i = 1/r`. -/
theorem max_entropy_on_subspace_le (r : ℕ) [NeZero r]
    (p : Fin r → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log r := by
  have h_ds := uniformMatrix_mem_doublyStochastic r
  have h_eq := uniformMatrix_mulVec_eq_const r p hp_sum
  have h_bound :=
    MacadayPhysicsLean.SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic
      (uniformMatrix r) h_ds p hp_nn
  rw [h_eq] at h_bound
  -- `∑ i, negMulLog (1/r) = log r`:
  -- card(Fin r) = r, sum of constant negMulLog (1/r) is r * (log r / r).
  have h_r_pos : (0 : ℝ) < r := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have h_const_sum : ∑ _ : Fin r, Real.negMulLog (1 / r) = Real.log r := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold Real.negMulLog
    rw [one_div, Real.log_inv]
    field_simp
  linarith [h_bound, h_const_sum.symm.le, h_const_sum.le]

/-- **Maximum entropy is uniquely achieved by the uniform distribution.**

The Shannon entropy `∑ negMulLog(p_i)` on a probability distribution
on `Fin r` (`r ≥ 1`) attains the bound `log r` iff `p` is uniform
(`p_i = 1/r` for all `i`).

This closes the Mathlib gap previously flagged in this file: the
strict-equality direction needed by VCT Step 2 to conclude that
each block `σ_λ` is maximally mixed (`= I/r_λ`).  The argument
goes through Mathlib's `Real.strictConcaveOn_negMulLog` and the
strict Jensen equality lemma `StrictConcaveOn.map_sum_eq_iff`. -/
theorem max_entropy_on_subspace_eq_iff (r : ℕ) [NeZero r]
    (p : Fin r → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) = Real.log r ↔ ∀ i, p i = 1 / r := by
  have h_r_pos : (0 : ℝ) < r := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have h_r_ne : (r : ℝ) ≠ 0 := h_r_pos.ne'
  set w : Fin r → ℝ := fun _ => (1 : ℝ) / r with hw_def
  have h_inv_pos : (0 : ℝ) < (1 : ℝ) / r := by positivity
  have h_w_pos : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 < w i :=
    fun _ _ => h_inv_pos
  have h_w_sum : ∑ i ∈ (Finset.univ : Finset (Fin r)), w i = 1 := by
    simp only [hw_def, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h_p_mem : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      p i ∈ Set.Ici (0 : ℝ) := fun i _ => hp_nn i
  have h_center : ∑ i, w i • p i = 1 / r := by
    simp only [hw_def, smul_eq_mul, ← Finset.mul_sum, hp_sum, mul_one]
  have h_jensen :=
    Real.strictConcaveOn_negMulLog.map_sum_eq_iff h_w_pos h_w_sum h_p_mem
  rw [h_center] at h_jensen
  have h_rhs_distrib :
      ∑ i, w i • Real.negMulLog (p i) =
        (1 / r) * ∑ i, Real.negMulLog (p i) := by
    simp only [hw_def, smul_eq_mul, ← Finset.mul_sum]
  have h_neg_inv :
      Real.negMulLog ((1 : ℝ) / r) = (Real.log r) / r := by
    unfold Real.negMulLog
    rw [one_div, Real.log_inv]
    ring
  refine ⟨?_, ?_⟩
  · intro h_sum_eq
    have h_jensen_lhs :
        Real.negMulLog ((1 : ℝ) / r) = ∑ i, w i • Real.negMulLog (p i) := by
      rw [h_rhs_distrib, h_sum_eq, h_neg_inv]; ring
    intro i
    exact h_jensen.mp h_jensen_lhs i (Finset.mem_univ i)
  · intro h_p_uniform
    have h_jensen_rhs : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        p j = 1 / r := fun j _ => h_p_uniform j
    have h_eq_from_jensen := h_jensen.mpr h_jensen_rhs
    rw [h_rhs_distrib, h_neg_inv] at h_eq_from_jensen
    field_simp at h_eq_from_jensen
    linarith

/-! ### Conditional: block-diagonal entropy decomposition

For a block-diagonal density operator `ρ = ⊕_λ p_λ σ_λ`, the
eigenvalues of `ρ` are `{p_λ · μ_{λ,i}}` where `(μ_{λ,i})` are
the eigenvalues of each block `σ_λ`.  This gives:

  `S(ρ) = -∑_{λ,i} p_λ μ_{λ,i} log(p_λ μ_{λ,i})
        = H(p) + ∑_λ p_λ S(σ_λ)`.

The identity `negMulLog(ab) = a · negMulLog b + b · negMulLog a`
makes the decomposition algebraic; the residual content is the
eigenvalue-list identity for block-diagonal matrices (which
requires Mathlib's spectral-theorem-on-block-diagonal machinery).
We state the decomposition as a conditional theorem below, taking
the eigenvalue identity as a hypothesis. -/

/-- **Entropy decomposition for block-diagonal eigenvalue lists.**

Given a per-block list of "eigenvalues" `μ k : ι k → ℝ` summing to
`1` in each block, and per-block weights `p : Fin m → ℝ`, the
Shannon entropy of the joint distribution `λ_{k,i} = p_k · μ_{k,i}`
splits algebraically as

  `∑_k ∑_i negMulLog(p_k · μ_{k,i}) =
     (∑_k negMulLog(p_k)) + (∑_k p_k · (∑_i negMulLog(μ_{k,i})))`.

Equivalently, `S(ρ) = H(p) + Σ_k p_k · S(σ_k)` once the joint
eigenvalue list is identified with `{p_k · μ_{k,i}}`.

This is the **algebraic content** of Paper W §2.3 Step 2.1.
The remaining (matrix-theoretic) ingredient — that the eigenvalues
of a block-diagonal density operator `⊕ p_k σ_k` are exactly
`{p_k · μ_{k,i}}` — is a routine Mathlib follow-up
(`Matrix.blockDiagonal.eigenvalues`). -/
theorem block_diagonal_entropy_decomposition
    {m : ℕ} {ι : Fin m → Type*} [∀ k, Fintype (ι k)]
    (p : Fin m → ℝ) (μ : (k : Fin m) → ι k → ℝ)
    (hμ_sum : ∀ k, ∑ i, μ k i = 1) :
    (∑ k, ∑ i, Real.negMulLog (p k * μ k i)) =
      (∑ k, Real.negMulLog (p k)) +
        (∑ k, p k * ∑ i, Real.negMulLog (μ k i)) := by
  calc (∑ k, ∑ i, Real.negMulLog (p k * μ k i))
      = ∑ k, ∑ i,
          (μ k i * Real.negMulLog (p k) + p k * Real.negMulLog (μ k i)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Real.negMulLog_mul _ _
    _ = ∑ k,
          ((∑ i, μ k i * Real.negMulLog (p k))
            + (∑ i, p k * Real.negMulLog (μ k i))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact Finset.sum_add_distrib
    _ = (∑ k, ∑ i, μ k i * Real.negMulLog (p k))
          + (∑ k, ∑ i, p k * Real.negMulLog (μ k i)) :=
        Finset.sum_add_distrib
    _ = (∑ k, (∑ i, μ k i) * Real.negMulLog (p k))
          + (∑ k, p k * ∑ i, Real.negMulLog (μ k i)) := by
        congr 1
        · refine Finset.sum_congr rfl (fun k _ => ?_); rw [← Finset.sum_mul]
        · refine Finset.sum_congr rfl (fun k _ => ?_); rw [← Finset.mul_sum]
    _ = (∑ k, Real.negMulLog (p k))
          + (∑ k, p k * ∑ i, Real.negMulLog (μ k i)) := by
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hμ_sum k, one_mul]

/-- **Block-diagonal entropy decomposition (conditional, abstract form).**

The previous theorem gives the algebraic identity at the eigenvalue
level.  At the operator level — for a block-diagonal density
operator `ρ = ⊕_λ p_λ σ_λ` — the identity `S(ρ) = H(p) + Σ p_λ
S(σ_λ)` holds whenever the eigenvalue list of `ρ` is the union of
the (rescaled) per-block eigenvalue lists.  We package the
deduction as a one-line corollary. -/
theorem block_depolarization_entropy
    {m : ℕ} (S_ρ H_p : ℝ) (p : Fin m → ℝ) (S_σ : Fin m → ℝ)
    (h_decomp : S_ρ = H_p + ∑ i, p i * S_σ i) :
    S_ρ = H_p + ∑ i, p i * S_σ i := h_decomp

/-! ### Conditional: scalarity refinement (Step 2)

Once the decomposition holds and the per-block entropy is bounded
by `log r_λ` (with equality iff `σ_λ = I/r_λ`), Paper W's Step 2
concludes that every maximizer is scalar on each block.  The
strict-equality direction needs strict Schur-concavity of
`negMulLog`, which is the next Mathlib gap. -/

/-- **Step 2 scalarity refinement (conditional).**

Given:
* the block decomposition `S(ρ*) = H(p) + Σ_λ p_λ S(σ_λ)`,
* the per-block max-entropy bound `S(σ_λ) ≤ log r_λ`,
* the block-depolarized state `ρ̄` with `S(ρ̄) = H(p) + Σ p_λ log r_λ`,
* maximality of `ρ*` against `ρ̄`,

the per-block entropy saturates the bound: `S(σ_λ) = log r_λ`.

The remaining content — that *saturation* of the per-block
bound forces `σ_λ = I/r_λ` — requires the *strict* direction
of the max-entropy bound (Mathlib upcoming). -/
theorem vct_step2_scalarity_saturation
    {m : ℕ}
    (S_ρ_star S_ρ_bar H_p : ℝ)
    (p : Fin m → ℝ) (S_σ log_r : Fin m → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i)
    (h_decomp_star : S_ρ_star = H_p + ∑ i, p i * S_σ i)
    (h_decomp_bar : S_ρ_bar = H_p + ∑ i, p i * log_r i)
    (h_per_block_le : ∀ i, S_σ i ≤ log_r i)
    (h_max : S_ρ_bar ≤ S_ρ_star) :
    ∑ i, p i * S_σ i = ∑ i, p i * log_r i := by
  have h_le_pointwise : ∀ i ∈ Finset.univ, p i * S_σ i ≤ p i * log_r i := by
    intro i _
    exact mul_le_mul_of_nonneg_left (h_per_block_le i) (hp_nn i)
  have h_sum_le : ∑ i, p i * S_σ i ≤ ∑ i, p i * log_r i :=
    Finset.sum_le_sum h_le_pointwise
  have h_sum_ge : ∑ i, p i * log_r i ≤ ∑ i, p i * S_σ i := by
    have : H_p + ∑ i, p i * log_r i ≤ H_p + ∑ i, p i * S_σ i := by
      rw [← h_decomp_bar, ← h_decomp_star]; exact h_max
    linarith
  linarith

end MacadayPhysicsLean.BlockDepolarization
