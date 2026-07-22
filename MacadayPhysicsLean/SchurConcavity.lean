/-
Schur-concavity from doubly stochastic matrices (foundation for VCT Lemma 3).

Hardy–Littlewood–Polya: if `f` is concave and `M` is doubly stochastic,
then for any vector `y`,
  `∑ᵢ f((M y)ᵢ) ≥ ∑ⱼ f(yⱼ)`.

Specialized to Shannon entropy `H(p) = ∑ⱼ negMulLog(pⱼ)` (since
`negMulLog x = -x log x` is concave on `[0, ∞)`), this gives:

  `H(M p) ≥ H(p)` for `M` doubly stochastic, `p ≥ 0`.

This is the **Schur-concavity half** of VCT Lemma 3.  The remaining
piece — "the eigenvalues of `Δ(ρ)` are obtained from those of `ρ`
by a doubly stochastic matrix" — is the quantum-mechanical content
(Hardy–Littlewood–Polya is the analysis side).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

namespace MacadayPhysicsLean.SchurConcavity

open Finset Matrix Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Hardy–Littlewood–Polya (one direction).**

If `M : Matrix n n ℝ` is doubly stochastic and `f : ℝ → ℝ` is
concave on a convex set containing the range of `y`, then summing
`f` over `M y` is at least summing `f` over `y`.

Physical reading: applying a doubly stochastic averaging cannot
decrease the sum of any concave functional.  This is the Schur-
concavity of `∑ f`. -/
theorem sum_le_sum_mulVec_of_doublyStochastic
    (M : Matrix n n ℝ) (hM : M ∈ doublyStochastic ℝ n)
    {s : Set ℝ}
    (y : n → ℝ) (hy : ∀ j, y j ∈ s)
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) :
    ∑ j, f (y j) ≤ ∑ i, f ((M.mulVec y) i) := by
  -- For each `i`: by Jensen on the convex combination
  --   `(M y) i = ∑ j, M i j • y j`     with weights `M i j` summing to 1,
  -- we have   `∑ j, M i j • f (y j) ≤ f ((M y) i)`.
  have per_row : ∀ i, ∑ j, M i j • f (y j) ≤ f ((M.mulVec y) i) := by
    intro i
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ M i j :=
      fun j _ => nonneg_of_mem_doublyStochastic hM
    have h_sum_one : ∑ j ∈ (Finset.univ : Finset n), M i j = 1 :=
      sum_row_of_mem_doublyStochastic hM i
    have h_mem : ∀ j ∈ (Finset.univ : Finset n), y j ∈ s := fun j _ => hy j
    have h_jensen :
        ∑ j ∈ (Finset.univ : Finset n), M i j • f (y j)
          ≤ f (∑ j ∈ (Finset.univ : Finset n), M i j • y j) :=
      ConcaveOn.le_map_sum hf h_nonneg h_sum_one h_mem
    -- Identify `∑ j, M i j • y j` with `(M.mulVec y) i`.
    have h_id : (M.mulVec y) i = ∑ j, M i j • y j := by
      simp [Matrix.mulVec, dotProduct]
    rw [h_id]
    exact h_jensen
  -- Sum over `i`:   ∑ⱼ f(y j) = ∑ⱼ (∑ᵢ M i j) f(y j) = ∑ᵢ ∑ⱼ M i j • f(y j) ≤ ∑ᵢ f((M y) i).
  calc ∑ j, f (y j)
      = ∑ j, (∑ i, M i j) • f (y j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [sum_col_of_mem_doublyStochastic hM j, one_smul]
    _ = ∑ j, ∑ i, M i j • f (y j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_smul]
    _ = ∑ i, ∑ j, M i j • f (y j) := Finset.sum_comm
    _ ≤ ∑ i, f ((M.mulVec y) i) := Finset.sum_le_sum (fun i _ => per_row i)

/-- **Shannon-entropy specialization.**

If `M` is doubly stochastic and `p : n → ℝ` is nonneg, then the
"Shannon-entropy" `∑ⱼ negMulLog(pⱼ)` is non-decreased by applying
`M` to `p`:
  `∑ⱼ negMulLog(pⱼ) ≤ ∑ᵢ negMulLog((M p)ᵢ)`.

This is the Schur-concavity content of VCT Lemma 3 — what remains
is the eigenvalue-majorization claim that pinching realizes this
`M`. -/
theorem shannon_entropy_le_mulVec_of_doublyStochastic
    (M : Matrix n n ℝ) (hM : M ∈ doublyStochastic ℝ n)
    (p : n → ℝ) (hp : ∀ j, 0 ≤ p j) :
    ∑ j, negMulLog (p j) ≤ ∑ i, negMulLog ((M.mulVec p) i) :=
  sum_le_sum_mulVec_of_doublyStochastic
    M hM p (fun j => hp j) concaveOn_negMulLog

end MacadayPhysicsLean.SchurConcavity
