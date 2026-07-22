/-
Density operators and the eigenvalue bridge to Schur concavity.

A **density operator** on `ℂⁿ` is a positive-semidefinite Hermitian
matrix with trace 1.  Its eigenvalues `λ : Fin n → ℝ` are
nonnegative real numbers summing to 1 (a probability distribution).

The **von Neumann entropy** of `ρ` is the Shannon entropy of its
eigenvalue distribution:

  `S(ρ) := ∑ᵢ negMulLog(λᵢ) = -∑ᵢ λᵢ log λᵢ.`

This file proves the *eigenvalue bridge* for VCT Lemma 3: if a
CPTP map `Δ` sends the eigenvalues of `ρ` through a doubly-
stochastic matrix `M` (`λ(Δρ) = M · λ(ρ)`), then `S(Δρ) ≥ S(ρ)` —
proved here, by composition with
`SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic`.

What remains for the full discharge of VCT Lemma 3 (called Lemma 3b
in `VCT.lean`) is the quantum-mechanical step: *constructing* such
a doubly-stochastic `M` from the pinching map.  Concretely,
`M_{ij} = |⟨e_i | f_j⟩|²` where `{e_i}` is the joint Π-eigenbasis
and `{f_j}` is the ρ-eigenbasis; orthonormality of both bases makes
`M` doubly stochastic.  That construction touches the spectral
theorem for commuting Hermitians.
-/

import MacadayPhysicsLean.SchurConcavity
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Real Finset
open scoped ComplexOrder

/-- A density operator on `ℂⁿ`: positive-semidefinite Hermitian
matrix with trace 1. -/
structure DensityOp (n : ℕ) where
  /-- Underlying matrix. -/
  M : Matrix (Fin n) (Fin n) ℂ
  /-- Positive-semidefiniteness (subsumes Hermitian). -/
  posSemidef : M.PosSemidef
  /-- Trace 1 normalization. -/
  trace_one : M.trace = 1

namespace DensityOp

variable {n : ℕ}

/-- A density operator is Hermitian (corollary of PosSemidef). -/
theorem isHermitian (ρ : DensityOp n) : ρ.M.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- Eigenvalues of a density operator (real-valued, by Hermitian). -/
noncomputable def eigenvalues (ρ : DensityOp n) : Fin n → ℝ :=
  ρ.isHermitian.eigenvalues

/-- Eigenvalues of a density operator are non-negative. -/
theorem eigenvalues_nonneg (ρ : DensityOp n) (i : Fin n) :
    0 ≤ eigenvalues ρ i :=
  Matrix.PosSemidef.eigenvalues_nonneg ρ.posSemidef i

/-- **Von Neumann entropy.**  `S(ρ) = -∑ᵢ λᵢ log λᵢ`,
where `{λᵢ}` are the eigenvalues of `ρ`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOp n) : ℝ :=
  ∑ i, Real.negMulLog (eigenvalues ρ i)

/-! ### Eigenvalue-bridge theorem (VCT Lemma 3, modulo Lemma 3b)

If a transformation `Δ : DensityOp n → DensityOp n` realizes a
doubly-stochastic map on eigenvalues — i.e. there exists
`M ∈ doublyStochastic ℝ (Fin n)` with
`eigenvalues (Δ ρ) = M · eigenvalues ρ` — then von Neumann entropy
is non-decreased.

This is the concrete-quantum-statement version of VCT Lemma 3,
discharged via the already-proved `SchurConcavity` Hardy–Littlewood–
Polya inequality.  Constructing such an `M` from pinching is the
remaining quantum step (Lemma 3b). -/
theorem entropy_nondecreasing_of_doublyStochastic
    (ρ ρ' : DensityOp n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n))
    (h_eig : eigenvalues ρ' = M.mulVec (eigenvalues ρ)) :
    vonNeumannEntropy ρ ≤ vonNeumannEntropy ρ' := by
  unfold vonNeumannEntropy
  rw [h_eig]
  exact MacadayPhysicsLean.SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic
    M hM (eigenvalues ρ) (fun j => eigenvalues_nonneg ρ j)

end DensityOp

end MacadayPhysicsLean
