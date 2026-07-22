/-
Doubly stochastic matrix from a pair of orthonormal bases (VCT Lemma 3b half).

The classical setup for VCT Lemma 3b:

Given two orthonormal bases `e, f : ι → E` of a finite-dimensional
complex inner-product space `E`, define

  `M i j := ‖⟨e i, f j⟩‖²`.

Then `M` is **doubly stochastic** — all entries are non-negative,
each row sums to `‖e i‖² = 1`, and each column sums to `‖f j‖² = 1`.
These are direct corollaries of Parseval's identity:
`sum_sq_norm_inner_right` and `sum_sq_norm_inner_left` in Mathlib.

This is the *orthonormality* half of VCT Lemma 3b.  The remaining
*quantum* half is the eigenvalue equation
`λ(Δρ) = M · λ(ρ)` for adapted ONBs `e` of `Δρ` and `f` of `ρ`,
which requires the spectral theorem for commuting Hermitians plus
the observation that `Πₖ |eᵢ⟩ = |eᵢ⟩` when `eᵢ ∈ range Πₖ`.
-/

import MacadayPhysicsLean.DensityOp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Tactic

namespace MacadayPhysicsLean.OrthonormalBridge

open Matrix Real Finset
open scoped InnerProductSpace ComplexConjugate

variable {ι 𝕜 E : Type*}

/-- The transition matrix between two orthonormal families, with entries
`M i j = ‖⟨e i, f j⟩‖²`.  When `e` and `f` are orthonormal bases of the
same finite-dim inner product space, this matrix is doubly stochastic
(see `transitionMatrix_doublyStochastic`). -/
noncomputable def transitionMatrix
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e f : ι → E) : Matrix ι ι ℝ :=
  fun i j => ‖inner 𝕜 (e i) (f j)‖ ^ 2

/-! ### Doubly stochasticity from orthonormality -/

/-- Entries of the transition matrix are non-negative
(trivially: norms-squared are nonneg). -/
theorem transitionMatrix_nonneg
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e f : ι → E) (i j : ι) :
    0 ≤ transitionMatrix (𝕜 := 𝕜) e f i j := by
  unfold transitionMatrix
  positivity

/-- Row sums of the transition matrix equal `‖e i‖²`.  When `e` is an ONB,
each row sums to 1. -/
theorem transitionMatrix_row_sum
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E) (f : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ∑ j, transitionMatrix (𝕜 := 𝕜) e (fun k => f k) i j = ‖e i‖ ^ 2 := by
  unfold transitionMatrix
  exact f.sum_sq_norm_inner_left (e i)

/-- Column sums of the transition matrix equal `‖f j‖²`.  When `f` is an ONB,
each column sums to 1. -/
theorem transitionMatrix_col_sum
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : OrthonormalBasis ι 𝕜 E) (f : ι → E) (j : ι) :
    ∑ i, transitionMatrix (𝕜 := 𝕜) (fun k => e k) f i j = ‖f j‖ ^ 2 := by
  unfold transitionMatrix
  exact e.sum_sq_norm_inner_right (f j)

/-- **Transition matrix between two ONBs is doubly stochastic.**

Direct corollary of Parseval's identity for both rows and columns,
plus non-negativity of squared norms. -/
theorem transitionMatrix_doublyStochastic
    [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e f : OrthonormalBasis ι 𝕜 E) :
    transitionMatrix (𝕜 := 𝕜) (fun k => e k) (fun k => f k) ∈
      doublyStochastic ℝ ι := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · -- entrywise non-negativity
    intro i j
    exact transitionMatrix_nonneg (𝕜 := 𝕜) _ _ i j
  · -- row sums = 1
    intro i
    rw [transitionMatrix_row_sum (𝕜 := 𝕜) _ f i, e.orthonormal.1 i, one_pow]
  · -- column sums = 1
    intro j
    rw [transitionMatrix_col_sum (𝕜 := 𝕜) e _ j, f.orthonormal.1 j, one_pow]

end MacadayPhysicsLean.OrthonormalBridge
