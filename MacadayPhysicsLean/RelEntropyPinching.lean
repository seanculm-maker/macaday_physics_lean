/-
Pinching Pythagorean identity — Stage 1.2 of Paper R (the load-bearing lemma).

  `D(ρ‖σ) = D(ρ‖Δρ) + D(Δρ‖σ)`   whenever σ is block-diagonal w.r.t. {Π_λ}

This is the exact conditional-expectation Pythagorean identity of
Lindblad / Hiai–Ohya–Tsukada, specialized to the pinching channel `Δ`. It is
the identity every downstream defect decomposition is assembled from, and it
needs *no* Klein inequality — only that the operator logarithm of a
block-diagonal state commutes with the projectors, which reduces to
`pinch_preserves_trace_mul` (already proved in `Pinching.lean`).

The compatibility hypothesis (Paper R H2, `[σ, C_k] = 0`) enters here in exactly
the form the identity uses: `σ` commutes with every joint spectral projector
`Π_λ`, i.e. `σ` lies in the image of the pinching map. We state that directly
as `∀ k, Commute σ.M (P.proj k)`.
-/

import MacadayPhysicsLean.RelativeEntropy
import MacadayPhysicsLean.Pinching
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Pinching

variable {n m : ℕ}

namespace DensityOp

/-- If `ρ` commutes with `X`, then so does `log ρ` (functions of an operator
commute with everything the operator commutes with). -/
theorem logM_commute (ρ : DensityOp n) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : Commute ρ.M X) : Commute ρ.logM X := by
  have hlog : ρ.logM = cfc Real.log ρ.M := by
    rw [logM]; exact (ρ.isHermitian.cfc_eq Real.log).symm
  rw [hlog]
  exact h.cfc_real Real.log

end DensityOp

/-- **Pinching Pythagorean identity** (Paper R Proposition 1, §3.2).

For a state `σ` block-diagonal with respect to the projector family `P`
(`σ` commutes with every projector), the Umegaki relative entropy splits
exactly across the pinching channel:

  `D(ρ‖σ) = D(ρ‖Δρ) + D(Δρ‖σ)`.

Standard (Lindblad / Hiai–Ohya–Tsukada); proved self-containedly here. -/
theorem pinching_pythagorean (P : ProjectorFamily n m) (ρ σ : DensityOp n)
    (hσ_comm : ∀ k, Commute σ.M (P.proj k)) :
    DensityOp.relativeEntropy ρ σ
      = DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
        + DensityOp.relativeEntropy (pinchDensityOp P ρ) σ := by
  set Δρ := pinchDensityOp P ρ with hΔ
  have hΔM : Δρ.M = P.pinch ρ.M := rfl
  -- `log σ` and `log Δρ` commute with every projector
  have hcσ : ∀ k, P.proj k * σ.logM = σ.logM * P.proj k := fun k =>
    ((σ.logM_commute (P.proj k) (hσ_comm k)).symm).eq
  have hcΔ : ∀ k, P.proj k * Δρ.logM = Δρ.logM * P.proj k := fun k => by
    have hcomm : Commute Δρ.M (P.proj k) := hΔM ▸ pinch_commutes P ρ.M k
    exact ((Δρ.logM_commute (P.proj k) hcomm).symm).eq
  -- pinching leaves the two mixed traces invariant
  have hA : (ρ.M * σ.logM).trace = (Δρ.M * σ.logM).trace := by
    rw [hΔM]; exact (pinch_preserves_trace_mul P ρ.M σ.logM hcσ).symm
  have hB : (ρ.M * Δρ.logM).trace = (Δρ.M * Δρ.logM).trace := by
    rw [hΔM]; exact (pinch_preserves_trace_mul P ρ.M Δρ.logM hcΔ).symm
  simp only [DensityOp.relativeEntropy]
  rw [hA, hB]
  ring

/-- **The coherence bound the downstream programme consumes** (Paper R §4.3).

`D(ρ‖Δρ) ≤ D(ρ‖ρ*)`: the block-coherence defect never exceeds the total
divergence from the equilibrium `ρ*`. Combined with quantum Pinsker (cited, not
proved here — Paper R Stage 3 is out of scope) this gives the near-saturation
bound `‖ρ − Δρ‖₁ ≤ √(2δ)` that Papers D, S1, S2, G, LA, MP, GB all cite.

Immediate from the pinching Pythagorean once `ρ*` is block-diagonal: the missing
term `D(Δρ‖ρ*)` is a quantum relative entropy, hence nonnegative by Klein's
inequality. That nonnegativity is Paper R's Stage-0 `relEntropy_nonneg`; here it
is taken as the explicit hypothesis `h_nonneg`, flagged as the one external
input in the Paper W conditional-theorem style. -/
theorem coherence_le_total_defect (P : ProjectorFamily n m) (ρ ρ_star : DensityOp n)
    (hρstar_comm : ∀ k, Commute ρ_star.M (P.proj k))
    (h_nonneg : 0 ≤ DensityOp.relativeEntropy (pinchDensityOp P ρ) ρ_star) :
    DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
      ≤ DensityOp.relativeEntropy ρ ρ_star := by
  have hpyth := pinching_pythagorean P ρ ρ_star hρstar_comm
  linarith

end MacadayPhysicsLean
