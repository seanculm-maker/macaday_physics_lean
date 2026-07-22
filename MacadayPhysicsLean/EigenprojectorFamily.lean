/-
Eigenprojector ProjectorFamily — Mathlib gap (3).

This file closes the third Mathlib gap previously flagged by the
VCT Corollary: the construction of a `Pinching.ProjectorFamily`
from a Hermitian matrix's eigenbasis.

**Layout.**

1. `rank1Proj` — the outer-product matrix `|v⟩⟨v|` via `vecMulVec`.
2. Hermiticity, idempotence, orthogonality of rank-1 projectors.
3. Resolution of identity: `Σ_k |e_k⟩⟨e_k| = 𝟙` when `{e_k}` is ONB.
4. Commutativity with the matrix `A` from the eigenvalue equation.
5. `projectorFamilyOfOrthonormal` — assembles 1-4 into a
   `Pinching.ProjectorFamily n n`.

**What's left (Mathlib bridge).** Translating
`Matrix.IsHermitian.eigenvectorBasis` into a `Fin n → Fin n → ℂ`
in this orthonormality form is mechanical
(`OrthonormalBasis.toMatrix`, `mulVec_eigenvectorBasis`,
`star_mulVec`).  We provide the abstract construction here so
papers can cite the corollary directly; the bridge can land
as a one-screen follow-up.
-/

import MacadayPhysicsLean.Pinching
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace MacadayPhysicsLean.EigenprojectorFamily

open Matrix

variable {n : ℕ}

/-! ### Rank-1 outer-product projector `|v⟩⟨v|` -/

/-- **Rank-1 projector `|v⟩⟨v|` as a matrix** — the outer product
`vᵢ · star vⱼ`. -/
noncomputable def rank1Proj (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec v (star v)

@[simp] theorem rank1Proj_apply (v : Fin n → ℂ) (i j : Fin n) :
    rank1Proj v i j = v i * star (v j) := rfl

/-- **Hermitian**: `|v⟩⟨v|ᴴ = |v⟩⟨v|`. -/
theorem rank1Proj_isHermitian (v : Fin n → ℂ) :
    (rank1Proj v).IsHermitian := by
  change (rank1Proj v)ᴴ = rank1Proj v
  unfold rank1Proj
  rw [Matrix.conjTranspose_vecMulVec, star_star]

/-- **Idempotent under unit norm**: if `⟨v, v⟩ = 1`, then
`|v⟩⟨v| · |v⟩⟨v| = |v⟩⟨v|`. -/
theorem rank1Proj_idem (v : Fin n → ℂ) (h_norm : star v ⬝ᵥ v = 1) :
    rank1Proj v * rank1Proj v = rank1Proj v := by
  unfold rank1Proj
  rw [Matrix.vecMulVec_mul_vecMulVec, h_norm, one_smul]

/-- **Orthogonal**: `|v⟩⟨v| · |w⟩⟨w| = 0` when `⟨v, w⟩ = 0`. -/
theorem rank1Proj_ortho (v w : Fin n → ℂ) (h_ortho : star v ⬝ᵥ w = 0) :
    rank1Proj v * rank1Proj w = 0 := by
  unfold rank1Proj
  rw [Matrix.vecMulVec_mul_vecMulVec, h_ortho, zero_smul, Matrix.vecMulVec_zero]

/-! ### Resolution of identity (`Σ_k |e_k⟩⟨e_k| = 𝟙`) -/

/-- **Resolution of identity** for an orthonormal family:
if `v : Fin n → (Fin n → ℂ)` satisfies `⟨vⱼ, vₖ⟩ = δⱼₖ`, then
`Σ_k rank1Proj (vₖ) = 𝟙`.

Proof: let `U` be the matrix whose `k`-th column is `vₖ`.
Then `Uᴴ * U = 𝟙` by orthonormality (entry `(j, k)` is `⟨vⱼ, vₖ⟩`),
hence `U * Uᴴ = 𝟙` by `mul_eq_one_comm` on the finite-dimensional
square matrix ring `Matrix (Fin n) (Fin n) ℂ`.  The `(i, j)` entry
of `U * Uᴴ` is `Σ_k (vₖ)ᵢ · star((vₖ)ⱼ)`, which is exactly the
entry of `Σ_k rank1Proj (vₖ)`. -/
theorem rank1Proj_sum_eq_one (v : Fin n → Fin n → ℂ)
    (h_orth : ∀ j k : Fin n, star (v j) ⬝ᵥ v k = if j = k then 1 else 0) :
    ∑ k, rank1Proj (v k) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  -- Column-matrix `U` from the family.
  set U : Matrix (Fin n) (Fin n) ℂ := fun i k => v k i with hU_def
  -- Express the sum as `U * Uᴴ`.
  have h_sum_eq_UUH :
      ∑ k, rank1Proj (v k) = U * Uᴴ := by
    ext i j
    simp [rank1Proj, Matrix.vecMulVec_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Matrix.sum_apply, hU_def]
  rw [h_sum_eq_UUH]
  -- Show Uᴴ * U = 𝟙.
  have h_UH_U : Uᴴ * U = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_def,
               Matrix.one_apply]
    have h := h_orth j k
    -- (Uᴴ * U) j k = Σ_i star((v j) i) * (v k) i = (star (v j)) ⬝ᵥ (v k)
    have h_id : ∑ i, star (v j i) * v k i = star (v j) ⬝ᵥ v k := by
      rfl
    rw [h_id, h]
  -- Conclude via mul_eq_one_comm.
  exact mul_eq_one_comm.mpr h_UH_U

/-! ### Commutativity with the matrix from the eigenvalue equation -/

/-- **Commutativity with a Hermitian matrix from the eigenvalue
equation.**  If `A` is Hermitian and `A *ᵥ v = λ • v` for some real
`λ`, then `A · |v⟩⟨v| = |v⟩⟨v| · A`. -/
theorem rank1Proj_commute_of_eigenvector
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (v : Fin n → ℂ) (lam : ℝ) (h_eigen : A *ᵥ v = (lam : ℂ) • v) :
    A * rank1Proj v = rank1Proj v * A := by
  -- A * |v⟩⟨v| = |Av⟩⟨v| = (λ • |v⟩)⟨v| = λ • |v⟩⟨v|
  have h_left : A * rank1Proj v = (lam : ℂ) • rank1Proj v := by
    unfold rank1Proj
    rw [Matrix.mul_vecMulVec, h_eigen, Matrix.smul_vecMulVec]
  -- |v⟩⟨v| * A = |v⟩⟨vA⟩.
  -- star (A *ᵥ v) = star v ᵥ* Aᴴ = star v ᵥ* A (Hermitian)
  -- star (A *ᵥ v) = star (λ • v) = star λ • star v = λ • star v (λ real)
  have h_star_eigen : star (A *ᵥ v) = (lam : ℂ) • star v := by
    rw [h_eigen, star_smul]
    congr 1
    simp [Complex.conj_ofReal]
  have h_starv_A : star v ᵥ* A = (lam : ℂ) • star v := by
    have h1 := Matrix.star_mulVec A v
    rw [show Aᴴ = A from hA] at h1
    rw [← h1, h_star_eigen]
  have h_right : rank1Proj v * A = (lam : ℂ) • rank1Proj v := by
    unfold rank1Proj
    rw [Matrix.vecMulVec_mul, h_starv_A, Matrix.vecMulVec_smul]
  rw [h_left, h_right]

/-! ### Assembling the ProjectorFamily -/

/-- **From an orthonormal family of vectors, construct a
`ProjectorFamily`.**  The rank-1 outer projectors `|vₖ⟩⟨vₖ|`
together form a `Pinching.ProjectorFamily n n`. -/
noncomputable def projectorFamilyOfOrthonormal
    (v : Fin n → Fin n → ℂ)
    (h_orth : ∀ j k : Fin n, star (v j) ⬝ᵥ v k = if j = k then 1 else 0) :
    MacadayPhysicsLean.Pinching.ProjectorFamily n n where
  proj k := rank1Proj (v k)
  isHermitian k := rank1Proj_isHermitian (v k)
  idem k := by
    have h_norm : star (v k) ⬝ᵥ v k = 1 := by
      have h := h_orth k k
      simp only [if_true] at h
      exact h
    exact rank1Proj_idem (v k) h_norm
  ortho j k hjk := by
    have h_ortho_pair : star (v j) ⬝ᵥ v k = 0 := by
      have := h_orth j k
      rw [if_neg hjk] at this
      exact this
    exact rank1Proj_ortho (v j) (v k) h_ortho_pair
  sum_eq_one := rank1Proj_sum_eq_one v h_orth

end MacadayPhysicsLean.EigenprojectorFamily
