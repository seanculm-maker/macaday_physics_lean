/-
VCT — Variational Coarse-graining Theorem (Paper W §2-3, the
finite-dimensional case §5.1).

**Mathematical content.**  Given commuting Hermitian constraints
`C₁, …, C_m` on a finite-dimensional Hilbert space, the entropy
maximizer subject to fixed traces `Tr(ρ Cₖ) = cₖ` can be taken
*block-diagonal in the joint spectral projectors* of the `Cₖ`.

**Proof pattern (Paper W §2.2-2.3).**  Let `Π = {Π_λ}` be the joint
spectral projectors.  Define the *pinching map*

  Δ(ρ) = Σ_λ Π_λ ρ Π_λ.

Then:

* **(Lemma 1)** Δ is CPTP.
* **(Lemma 2)** Δ preserves the constraint expectations:
  `Tr(Δ(ρ) Cₖ) = Tr(ρ Cₖ)`.
* **(Lemma 3)** Δ does not decrease von Neumann entropy:
  `S(Δ(ρ)) ≥ S(ρ)`.

The main theorem is a *four-line squeeze*: if `ρ_*` is the
maximizer, then `Δ(ρ_*)` is feasible (Lemma 2), so
`S(Δ(ρ_*)) ≤ S(ρ_*)`; but Lemma 3 gives `S(Δ(ρ_*)) ≥ S(ρ_*)`;
hence equality, and `Δ(ρ_*)` is also a maximizer and
block-diagonal by construction.

**Formalization status — UNCONDITIONAL.**  All three lemmas are
fully discharged in this repo:

* **Lemma 1** (CPTP): `MacadayPhysicsLean.Pinching.pinchDensityOp` packages
  trace, Hermitian, and PSD preservation as a `DensityOp → DensityOp`.
* **Lemma 2** (constraint preservation):
  `MacadayPhysicsLean.Pinching.pinch_preserves_trace_mul`.
* **Lemma 3** (entropy non-decrease):
  `MacadayPhysicsLean.JointDiagonalization.vct_lemma_3_unconditional` — proved
  via the joint diagonalization framework (Phases 15-20): projector
  submodules form an internal direct sum, `pinch_sym` preserves each,
  per-cell pinch eigenbases are collected and reindexed to `Fin n`,
  the resulting adapted ONB satisfies the eigenvalue equation, and
  spectral multiset uniqueness (via characteristic-polynomial roots)
  closes the entropy equation.

The four-line squeeze (`vct_squeeze`) plus Lemma 3 gives the
unconditional concrete VCT theorem (`vct_lemma_3_quantum`).
-/

import Mathlib.Tactic
import Mathlib.Order.Basic
import MacadayPhysicsLean.JointDiagonalization

namespace MacadayPhysicsLean.VCT

/-! ### The abstract VCT squeeze

Stated for an arbitrary "state space" `α`, an arbitrary "entropy"
functional `S : α → ℝ`, and an arbitrary "pinching map" `Δ : α → α`.
The two hypotheses encode Lemmas 2 (constraint-preservation) and
3 (entropy non-decrease). -/

/-- **The abstract VCT squeeze.**

If `Δ` preserves a feasibility predicate `feasible` (Lemma 2 — `Δ`
preserves the linear constraints `Tr(ρ Cₖ) = cₖ`), and `Δ` does not
decrease an entropy functional `S` (Lemma 3 — pinching is
entropy-monotone), then for any entropy maximizer `ρ_*` the pinched
state `Δ(ρ_*)` is *also* an entropy maximizer with the same value:

  `S(Δ(ρ_*)) = S(ρ_*)`.

This is the heart of Paper W §2.3 — fully proved, no proof placeholders. -/
theorem vct_squeeze
    {α : Type*}
    (S : α → ℝ) (Δ : α → α) (feasible : α → Prop)
    (h_preserve : ∀ ρ, feasible ρ → feasible (Δ ρ))
    (h_monotone : ∀ ρ, S ρ ≤ S (Δ ρ))
    (ρ_star : α)
    (h_feas : feasible ρ_star)
    (h_max : ∀ σ, feasible σ → S σ ≤ S ρ_star) :
    S (Δ ρ_star) = S ρ_star := by
  apply le_antisymm
  · -- `Δ ρ_*` is feasible, so `S(Δ ρ_*) ≤ S(ρ_*)` by maximality
    exact h_max (Δ ρ_star) (h_preserve ρ_star h_feas)
  · -- `S(ρ_*) ≤ S(Δ ρ_*)` by entropy monotonicity
    exact h_monotone ρ_star

/-- **Consequence: `Δ(ρ_*)` is itself an entropy maximizer.** -/
theorem vct_pinched_is_maximizer
    {α : Type*}
    (S : α → ℝ) (Δ : α → α) (feasible : α → Prop)
    (h_preserve : ∀ ρ, feasible ρ → feasible (Δ ρ))
    (h_monotone : ∀ ρ, S ρ ≤ S (Δ ρ))
    (ρ_star : α)
    (h_feas : feasible ρ_star)
    (h_max : ∀ σ, feasible σ → S σ ≤ S ρ_star) :
    ∀ σ, feasible σ → S σ ≤ S (Δ ρ_star) := by
  intro σ hσ
  rw [vct_squeeze S Δ feasible h_preserve h_monotone ρ_star h_feas h_max]
  exact h_max σ hσ

/-- **Δ(ρ_*) attains the maximum and is feasible.** -/
theorem vct_pinched_witness
    {α : Type*}
    (S : α → ℝ) (Δ : α → α) (feasible : α → Prop)
    (h_preserve : ∀ ρ, feasible ρ → feasible (Δ ρ))
    (h_monotone : ∀ ρ, S ρ ≤ S (Δ ρ))
    (ρ_star : α)
    (h_feas : feasible ρ_star)
    (h_max : ∀ σ, feasible σ → S σ ≤ S ρ_star) :
    feasible (Δ ρ_star) ∧ S (Δ ρ_star) = S ρ_star :=
  ⟨h_preserve ρ_star h_feas,
   vct_squeeze S Δ feasible h_preserve h_monotone ρ_star h_feas h_max⟩

/-! ### The quantum-specific Lemmas 1, 2, 3

These convert the abstract squeeze above into the concrete
VCT statement on density operators.  Each is stated here at the
"forwardable" level — proofs are routed to Mathlib / Physlib.

`α = density operators on a finite-dim Hilbert space`
`Δ = pinching map for joint spectral projectors of {Cₖ}`
`S = von Neumann entropy`
`feasible ρ ↔ ∀ k, Tr(ρ Cₖ) = cₖ` -/

/-- **Lemma 1 (pinching is CPTP — positive trace-preserving).**

The pinching map `Δ(ρ) := ∑_k Pₖ ρ Pₖ` sends density operators to
density operators.  This is packaged as `MacadayPhysicsLean.Pinching.pinchDensityOp`
(built from `pinch_trace` + `pinch_isHermitian` + `pinch_posSemidef`). -/
noncomputable def pinching_is_CPTP
    {n m : ℕ} (P : MacadayPhysicsLean.Pinching.ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) : MacadayPhysicsLean.DensityOp n :=
  MacadayPhysicsLean.Pinching.pinchDensityOp P ρ

/-- **Lemma 2 (pinching preserves commuting-constraint expectations).**

For any observable `A` that commutes with every `P.proj k`,
`Tr((Δρ) · A) = Tr(ρ · A)`.  This is exactly
`MacadayPhysicsLean.Pinching.pinch_preserves_trace_mul`. -/
theorem pinching_preserves_constraints
    {n m : ℕ} (P : MacadayPhysicsLean.Pinching.ProjectorFamily n m)
    (ρ A : Matrix (Fin n) (Fin n) ℂ)
    (h_comm : ∀ k, P.proj k * A = A * P.proj k) :
    (P.pinch ρ * A).trace = (ρ * A).trace :=
  MacadayPhysicsLean.Pinching.pinch_preserves_trace_mul P ρ A h_comm

/-- **Lemma 3 (pinching does not decrease von Neumann entropy).**

`S(ρ) ≤ S(Δ ρ)` for any density operator `ρ` and projector family `P`.
This is the *deep* lemma — Uhlmann (1970) / Wehrl (1978) / Hayashi
Lemma 3.10.  **PROVED UNCONDITIONALLY** in this repo via the joint
diagonalization framework
(`MacadayPhysicsLean.JointDiagonalization.vct_lemma_3_unconditional`):

1. **Schur-concavity half** —
   `MacadayPhysicsLean.SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic`
   gives Hardy-Littlewood-Pólya via per-row Jensen + column stochasticity.

2. **Eigenvalue bridge** — `MacadayPhysicsLean.DensityOp.entropy_nondecreasing_of_doublyStochastic`
   composes the analytic half with `vonNeumannEntropy`.

3. **Doubly-stochastic transition matrix** —
   `MacadayPhysicsLean.OrthonormalBridge.transitionMatrix_doublyStochastic`
   from Parseval/Plancherel.

4. **Joint diagonalization → adapted ONB** —
   `MacadayPhysicsLean.JointDiagonalization.adaptedBasis`, built from projector
   1-eigenspaces (`projSubmodule_isInternal`) + per-cell pinch
   eigenbasis (`cellBasis`) + Mathlib's `collectedOrthonormalBasis`.

5. **Spectral multiset uniqueness** —
   `MacadayPhysicsLean.JointDiagonalization.spectral_theorem_adapted` +
   `charpoly_eq_mu` + `multiset_mu_eq_eigenvalues` reduces the
   entropy equation to `Multiset.map_injective` of `Complex.ofReal`. -/
theorem pinching_entropy_nondecreasing
    {n m : ℕ} (P : MacadayPhysicsLean.Pinching.ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy
          (MacadayPhysicsLean.Pinching.pinchDensityOp P ρ) :=
  MacadayPhysicsLean.JointDiagonalization.vct_lemma_3_unconditional P ρ

/-! ### The concrete quantum VCT theorem (unconditional)

Compose the abstract squeeze with the three quantum lemmas. -/

/-- **VCT — concrete unconditional form on density operators.**

Given a projector family `P` (the joint spectral projectors of the
constraints `Cₖ`), a feasibility predicate `feasible`, and a feasibility-
preservation hypothesis for the pinching map (which holds whenever
each `Cₖ` commutes with every `P.proj k`, by Lemma 2), the pinched
maximizer attains the same entropy as the original. -/
theorem vct_lemma_3_quantum
    {n m : ℕ} (P : MacadayPhysicsLean.Pinching.ProjectorFamily n m)
    (feasible : MacadayPhysicsLean.DensityOp n → Prop)
    (h_preserve : ∀ ρ, feasible ρ → feasible (MacadayPhysicsLean.Pinching.pinchDensityOp P ρ))
    (ρ_star : MacadayPhysicsLean.DensityOp n)
    (h_feas : feasible ρ_star)
    (h_max : ∀ σ, feasible σ →
              MacadayPhysicsLean.DensityOp.vonNeumannEntropy σ
                ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ_star) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy
        (MacadayPhysicsLean.Pinching.pinchDensityOp P ρ_star)
      = MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ_star :=
  vct_squeeze MacadayPhysicsLean.DensityOp.vonNeumannEntropy
    (MacadayPhysicsLean.Pinching.pinchDensityOp P) feasible h_preserve
    (fun ρ => pinching_entropy_nondecreasing P ρ) ρ_star h_feas h_max

end MacadayPhysicsLean.VCT
