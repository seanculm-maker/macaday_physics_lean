/-
**The equilibrium-defect decomposition** — Paper R, Theorem 4 (§7.1).

  `D(ρ‖ρ*) = D(ρ‖Δρ) + Σ_λ p_λ D(τ_λ‖σ_λ) + D_KL(p‖p*)`

Three defects, each measuring a different way an arbitrary state can differ from
the inferred equilibrium: the **coherence** it carries across sectors, the
**within-sector** discrepancy from the reference blocks, and the
**sector-weight** discrepancy from the equilibrium weights.

The proof is pure assembly: the pinching Pythagorean identity (§3.2) splits off
the coherence defect, and the direct-sum chain rule (Proposition 2, §3.4)
refines what remains.

**Hypotheses.** The paper states Theorem 4 as an identity in the *extended*
nonnegative reals, with the caveat that if `p_λ > 0` in a sector where
`p*_λ = 0` then both `D(ρ‖ρ*)` and `D_KL(p‖p*)` are `+∞`.  The real-valued
formalisation here scopes that away by hypothesising `p*_λ > 0` and `ρ*`
faithful — which, in the intended application, is exactly what the paper's
Lemma 3 (active-support positivity, §7.3) supplies on the active space, feasible
states being supported there.  Lemma 3 itself is out of scope for this pass.

Following the paper, the block decompositions are *given*, not constructed:
Theorem 4 opens "for any state `ρ`, write `Δρ = ⊕_λ p_λ τ_λ`".
-/

import MacadayPhysicsLean.BlockChainRule
import MacadayPhysicsLean.RelEntropyPinching
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Pinching JointDiagonalization
open scoped ComplexOrder

variable {n m : ℕ}

/-- **Theorem 4 — the equilibrium-defect decomposition.**

For any state `ρ`, with `Δρ = ⊕_λ p_λ τ_λ` and the equilibrium
`ρ* = ⊕_λ p*_λ σ_λ` blockwise faithful,

  `D(ρ‖ρ*) = D(ρ‖Δρ) + Σ_λ p_λ D(τ_λ‖σ_λ) + D_KL(p‖p*)`

— coherence defect, within-sector defect, sector-weight defect. -/
theorem three_defect {P : ProjectorFamily n m} {ρ ρstar : DensityOp n}
    (A : BlockDecomp P (pinchDensityOp P ρ)) (S : BlockDecomp P ρstar)
    (hq : ∀ k, 0 < S.w k) (hpos : ρstar.M.PosDef) :
    DensityOp.relativeEntropy ρ ρstar
      = DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
        + (∑ k, A.w k * DensityOp.relativeEntropy (A.st k) (S.st k))
        + blockKL A.w S.w := by
  rw [pinching_pythagorean P ρ ρstar S.commute, chain_rule A S hq hpos]
  ring

/-- **Theorem 1 — the prior-relative defect decomposition** (§3).

For every state `ρ`, with `Δρ = ⊕_λ p_λ τ_λ` and the compatible prior
`σ = ⊕_λ s_λ σ_λ` (faithful, per the paper's §2 standing convention),

  `D(ρ‖σ) = D(ρ‖Δρ) + Σ_λ p_λ D(τ_λ‖σ_λ) + D_KL(p‖s)`.

This is the *same* identity as `three_defect` — that theorem is stated for an
arbitrary block-decomposed reference, so Theorem 1 (reference = the prior `σ`)
and Theorem 4 (reference = the minimizer `ρ*`) are two instantiations of it.
Both are recorded because §6.4 names them separately. -/
theorem prior_relative_decomposition {P : ProjectorFamily n m} {ρ σ : DensityOp n}
    (A : BlockDecomp P (pinchDensityOp P ρ)) (S : BlockDecomp P σ)
    (hs : ∀ k, 0 < S.w k) (hpos : σ.M.PosDef) :
    DensityOp.relativeEntropy ρ σ
      = DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
        + (∑ k, A.w k * DensityOp.relativeEntropy (A.st k) (S.st k))
        + blockKL A.w S.w :=
  three_defect A S hs hpos

/-- **Theorem 1 in the paper's own hypothesis shape.**

Rather than taking the sector decomposition of the prior `σ` as data, this takes
the paper's actual hypotheses — `σ` compatible (`[σ, Π_λ] = 0`), faithful, every
sector occupied (`0 < s_λ`) — and *derives* the decomposition via
`blockDecomp_of_compat`, so the sector weights are `s_λ = Tr(Π_λ σ)` and the
sector states are `σ_λ = Π_λ σ Π_λ / s_λ`, exactly as in §3. -/
theorem prior_relative_decomposition_compat {P : ProjectorFamily n m}
    {ρ σ : DensityOp n} (A : BlockDecomp P (pinchDensityOp P ρ))
    (hcomm : ∀ k, Commute σ.M (P.proj k)) (hpos : σ.M.PosDef)
    (hs : ∀ k, 0 < sectorWeight P σ k) :
    DensityOp.relativeEntropy ρ σ
      = DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
        + (∑ k, A.w k * DensityOp.relativeEntropy (A.st k)
            ((blockDecomp_of_compat P σ hcomm hs).st k))
        + blockKL A.w (sectorWeight P σ) :=
  three_defect A (blockDecomp_of_compat P σ hcomm hs) hs hpos

/-! ### The reset channel

`R_σ(ρ) = ⊕_λ p_λ σ_λ` — the state that keeps `ρ`'s sector weights but replaces
each sector's internal state by the reference block.  It is the intermediate
point of Theorem 4's channel form; the third defect is exactly the relative
entropy from it to the equilibrium. -/

/-- `R_σ(ρ) = ⊕_λ p_λ σ_λ`, built from `Δρ`'s sector weights and `ρ*`'s blocks. -/
noncomputable def resetState {P : ProjectorFamily n m} {η ρstar : DensityOp n}
    (A : BlockDecomp P η) (S : BlockDecomp P ρstar) : DensityOp n where
  M := ∑ k, (A.w k : ℂ) • (S.st k).M
  posSemidef := by
    refine Matrix.posSemidef_sum _ (fun k _ => ?_)
    exact (S.st k).posSemidef.smul (by simpa using A.w_nonneg k)
  trace_one := by
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, DensityOp.trace_one, smul_eq_mul, mul_one]
    rw [← Complex.ofReal_sum, A.w_sum, Complex.ofReal_one]

/-- The reset state carries the obvious block decomposition: `ρ`'s weights with
`ρ*`'s blocks. -/
def resetBlockDecomp {P : ProjectorFamily n m} {η ρstar : DensityOp n}
    (A : BlockDecomp P η) (S : BlockDecomp P ρstar) :
    BlockDecomp P (resetState A S) where
  w := A.w
  st := S.st
  w_nonneg := A.w_nonneg
  supported := S.supported
  sum_eq := rfl

/-- **The third defect is the sector-weight divergence**:
`D(R_σ(ρ)‖ρ*) = D_KL(p‖p*)`.  The within-sector terms cancel exactly, because
the reset state already carries `ρ*`'s blocks. -/
theorem relEntropy_resetState_eq_blockKL {P : ProjectorFamily n m}
    {η ρstar : DensityOp n} (A : BlockDecomp P η) (S : BlockDecomp P ρstar)
    (hq : ∀ k, 0 < S.w k) (hpos : ρstar.M.PosDef) :
    DensityOp.relativeEntropy (resetState A S) ρstar = blockKL A.w S.w := by
  rw [chain_rule (resetBlockDecomp A S) S hq hpos]
  have : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      (resetBlockDecomp A S).w k
        * DensityOp.relativeEntropy ((resetBlockDecomp A S).st k) (S.st k) = 0 := by
    intro k _
    rw [show (resetBlockDecomp A S).st k = S.st k from rfl,
      DensityOp.relEntropy_self, mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero, add_zero]
  rfl

/-- **Theorem 4, channel form** (§7.1, second boxed identity).

`D(ρ‖ρ*) = D(ρ‖Δρ) + D(Δρ‖R_σ(ρ)) + D(R_σ(ρ)‖ρ*)`

— the same three defects as `three_defect`, expressed through the reset channel
`R_σ`.  The middle term is the matching-weights chain rule (`Δρ` and `R_σ(ρ)`
carry the *same* sector weights); the third is `relEntropy_resetState_eq_blockKL`.

`hfaith` is the reference's blockwise faithfulness — `R_σ(ρ)` has positive
eigenvalues on every occupied sector — which is exactly what a faithful
equilibrium `ρ*` supplies; it is the hypothesis of the matching-weights chain
rule, load-bearing because the `0 log 0 = 0` convention would otherwise break the
per-block log split. -/
theorem three_defect_channel {P : ProjectorFamily n m} {ρ ρstar : DensityOp n}
    (A : BlockDecomp P (pinchDensityOp P ρ)) (S : BlockDecomp P ρstar)
    (hq : ∀ k, 0 < S.w k) (hpos : ρstar.M.PosDef)
    (hfaith : ∀ s, 0 < A.w (k_of P s) → 0 < mu P (resetState A S) s) :
    DensityOp.relativeEntropy ρ ρstar
      = DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
        + DensityOp.relativeEntropy (pinchDensityOp P ρ) (resetState A S)
        + DensityOp.relativeEntropy (resetState A S) ρstar := by
  rw [three_defect A S hq hpos,
    chain_rule_matched A (resetBlockDecomp A S) (fun _ => rfl) hfaith,
    relEntropy_resetState_eq_blockKL A S hq hpos]
  rfl

end MacadayPhysicsLean
