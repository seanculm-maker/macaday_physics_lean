/-
VCT Corollary — Paper W §3.

For a single Hermitian observable `A` with mean `⟨A⟩ = m` and
second-moment `⟨A²⟩ = v` constraints, the maximum-entropy
state can be taken diagonal in the eigenbasis of `A`.

**Mathematical content.**

1. **Trivial commutativity** — `A · A² = A³ = A² · A`.
   The constraints `Tr(ρ A) = m`, `Tr(ρ A²) = v` are therefore
   expectations of commuting Hermitian operators `{A, A²}`.

2. **Abstract corollary** — by the unconditional VCT Lemma 3
   (`vct_lemma_3_quantum`), pinching by the joint spectral
   projectors of `{A, A²}` preserves entropy at the maximizer.

3. **Diagonal in the nondegenerate case** — when the eigenvalues
   of `A` are distinct, the joint spectral projectors of `{A, A²}`
   coincide with the eigenprojectors of `A`, all of rank `1`,
   so the pinched state is diagonal in the eigenbasis of `A`.

The trivial commutativity and the abstract corollary structure
are formalized here.  The concrete construction of the
eigenprojector `ProjectorFamily` for a nondegenerate Hermitian
matrix is a routine Mathlib exercise (rank-`1` outer products of
`Matrix.IsHermitian.eigenvectorBasis`) and is taken as an
input to the corollary statement.
-/

import MacadayPhysicsLean.VCT

namespace MacadayPhysicsLean.VCTCorollary

/-! ### Trivial commutativity `[A, A²] = 0` -/

/-- **`A` and `A²` commute** — pure associativity.

The point is that the corollary's two constraints `Tr(ρ A) = m`
and `Tr(ρ A²) = v` are expectations of commuting Hermitian
observables, so VCT applies. -/
theorem A_A2_commute {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A * (A * A) = (A * A) * A := by
  rw [← Matrix.mul_assoc]

/-! ### The abstract corollary -/

/-- **VCT Corollary for mean–variance constraints.**

Given a projector family `P` for which both `A` and `A²` commute
with every projector (the joint spectral projectors of `{A, A²}`,
which in the nondegenerate case are the eigenprojectors of `A`),
the pinched maximizer of the entropy under the constraints
`Tr(ρ A) = m`, `Tr(ρ A²) = v` has the same entropy as the
original maximizer.

In the nondegenerate case `P` consists of rank-`1` projectors,
so `pinchDensityOp P ρ_star` is diagonal in the eigenbasis
of `A`. -/
theorem vct_corollary_diagonal
    {n m : ℕ} (P : MacadayPhysicsLean.Pinching.ProjectorFamily n m)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (h_A_comm : ∀ k, P.proj k * A = A * P.proj k)
    (h_A2_comm : ∀ k, P.proj k * (A * A) = (A * A) * P.proj k)
    (m_val v_val : ℂ)
    (ρ_star : MacadayPhysicsLean.DensityOp n)
    (h_feas : (ρ_star.M * A).trace = m_val ∧
              (ρ_star.M * (A * A)).trace = v_val)
    (h_max : ∀ σ : MacadayPhysicsLean.DensityOp n,
              (σ.M * A).trace = m_val →
              (σ.M * (A * A)).trace = v_val →
              MacadayPhysicsLean.DensityOp.vonNeumannEntropy σ
                ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ_star) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy
        (MacadayPhysicsLean.Pinching.pinchDensityOp P ρ_star)
      = MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ_star := by
  -- Feasibility predicate bundling the two trace constraints.
  let feasible : MacadayPhysicsLean.DensityOp n → Prop := fun ρ =>
    (ρ.M * A).trace = m_val ∧ (ρ.M * (A * A)).trace = v_val
  -- Pinching preserves both trace constraints (Lemma 2 twice).
  have h_preserve : ∀ ρ : MacadayPhysicsLean.DensityOp n,
      feasible ρ → feasible (MacadayPhysicsLean.Pinching.pinchDensityOp P ρ) := by
    intro ρ ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · -- Tr((Δρ).M · A) = Tr(P.pinch ρ.M · A) = Tr(ρ.M · A) = m_val
      change (MacadayPhysicsLean.Pinching.ProjectorFamily.pinch P ρ.M * A).trace = m_val
      rw [MacadayPhysicsLean.Pinching.pinch_preserves_trace_mul P ρ.M A h_A_comm]
      exact h1
    · -- Tr((Δρ).M · A²) = Tr(ρ.M · A²) = v_val
      change (MacadayPhysicsLean.Pinching.ProjectorFamily.pinch P ρ.M * (A * A)).trace = v_val
      rw [MacadayPhysicsLean.Pinching.pinch_preserves_trace_mul P ρ.M (A * A) h_A2_comm]
      exact h2
  -- Re-cast h_max as a predicate over `feasible`.
  have h_max' : ∀ σ : MacadayPhysicsLean.DensityOp n, feasible σ →
      MacadayPhysicsLean.DensityOp.vonNeumannEntropy σ
        ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ_star :=
    fun σ ⟨hs1, hs2⟩ => h_max σ hs1 hs2
  -- Apply the unconditional concrete VCT theorem.
  exact MacadayPhysicsLean.VCT.vct_lemma_3_quantum P feasible h_preserve ρ_star h_feas h_max'

/-! ### Symmetric form of `A_A2_commute` -/

/-- **Polynomial-in-`A` commutativity**: any matrix polynomial in
`A` commutes with `A`.  Stated here as the special case
`A · (c₁ A + c₂ A²) = (c₁ A + c₂ A²) · A`. -/
theorem A_poly_commute {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c1 c2 : ℂ) :
    A * (c1 • A + c2 • (A * A)) = (c1 • A + c2 • (A * A)) * A := by
  rw [Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul,
      A_A2_commute A]

end MacadayPhysicsLean.VCTCorollary
