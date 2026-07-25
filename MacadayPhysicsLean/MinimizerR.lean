/-
**The Relative Classicality Theorem** — Paper R, Theorem 2 (§4.1–4.2).

For a faithful compatible prior `σ` and any feasible `ρ`,

  `D(ρ‖σ) ≥ D_KL(p‖s)`,  with equality iff  `ρ = R_σ(ρ) = ⊕_λ p_λ σ_λ`.

This is the quantum content of Theorem 2: among all states with a given sector
weight vector `p`, the reset state `⊕_λ p_λ σ_λ` is the *unique* minimiser of
`D(·‖σ)`, and its value is the classical projection `D_KL(p‖s)`.  Existence and
uniqueness of the classical minimiser `p*` over the constraint polytope `P_c` is
classical convex analysis and is *scoped out* (as both specs sanction, mirroring
Paper W's `h_max`-as-hypothesis convention): the theorem characterises the form
of any minimiser, which is the load-bearing claim.

The proof is the paper's §4.2 argument: `three_defect` splits `D(ρ‖σ)` into the
coherence defect, the within-sector defect, and `D_KL(p‖s)`; the first two are
nonnegative (support-relative Klein) and vanish exactly when `ρ = Δρ` and each
`τ_λ = σ_λ` (support-relative equality case), which together say `ρ = R_σ(ρ)`.
-/

import MacadayPhysicsLean.RelEntropySupport
import MacadayPhysicsLean.ThreeDefect
import Mathlib.Tactic

namespace MacadayPhysicsLean

open Matrix Pinching JointDiagonalization DensityOp
open scoped ComplexOrder

variable {n m : ℕ}

/-! ### Block faithfulness of the equilibrium (shared with the channel form's `hfaith`)

For a faithful `ρ*` decomposed as `⊕_λ p*_λ σ_λ`, each `σ_λ` is faithful on its
block: `σ_λ v = 0 ⟹ Π_λ v = 0`.  Because `Π_λ ρ* Π_λ = p*_λ σ_λ`, this is the
`PosDef` quadratic form `⟨Π_λ v, ρ* Π_λ v⟩ = 0 ⟹ Π_λ v = 0`. -/

/-- The block `Π_λ ρ* Π_λ` equals `p*_λ σ_λ`. -/
theorem proj_mul_proj_eq {P : ProjectorFamily n m} {ρstar : DensityOp n}
    (S : BlockDecomp P ρstar) (k : Fin m) :
    P.proj k * ρstar.M * P.proj k = (S.w k : ℂ) • (S.st k).M := by
  rw [S.proj_mul k, Matrix.smul_mul, S.supported_right k]

/-- **Block faithfulness.** For a faithful `ρ*`, `σ_λ v = 0 ⟹ Π_λ v = 0`. -/
theorem blockState_ker {P : ProjectorFamily n m} {ρstar : DensityOp n}
    (S : BlockDecomp P ρstar) (hpos : ρstar.M.PosDef) (k : Fin m)
    {v : Fin n → ℂ} (hv : (S.st k).M *ᵥ v = 0) : P.proj k *ᵥ v = 0 := by
  have hz : (P.proj k * ρstar.M * P.proj k) *ᵥ v = 0 := by
    rw [proj_mul_proj_eq S k, Matrix.smul_mulVec, hv, smul_zero]
  have hqf : star (P.proj k *ᵥ v) ⬝ᵥ ρstar.M *ᵥ (P.proj k *ᵥ v) = 0 := by
    have hcyc : star (P.proj k *ᵥ v) ⬝ᵥ ρstar.M *ᵥ (P.proj k *ᵥ v)
        = star v ⬝ᵥ (P.proj k * ρstar.M * P.proj k) *ᵥ v := by
      rw [Matrix.star_mulVec, (P.isHermitian k).eq, Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
        ← Matrix.dotProduct_mulVec]
    rw [hcyc, hz, dotProduct_zero]
  by_contra hne
  have hpos' := hpos.re_dotProduct_pos hne
  rw [hqf] at hpos'
  simp at hpos'

/-- **Block kernel inclusion.** For a `Π_λ`-supported state `τ_λ` and the faithful
block `σ_λ`, `ker σ_λ ⊆ ker τ_λ`: `σ_λ v = 0 ⟹ τ_λ v = 0`.  The support
condition consumed by `mixing_eq_zero_of_ker_inclusion`. -/
theorem blockState_ker_inclusion {P : ProjectorFamily n m} {η ρstar : DensityOp n}
    (A : BlockDecomp P η) (S : BlockDecomp P ρstar) (hpos : ρstar.M.PosDef) (k : Fin m)
    {v : Fin n → ℂ} (hv : (S.st k).M *ᵥ v = 0) : (A.st k).M *ᵥ v = 0 := by
  have hProj : P.proj k *ᵥ v = 0 := blockState_ker S hpos k hv
  have key : (A.st k).M *ᵥ (P.proj k *ᵥ v) = (A.st k).M *ᵥ v := by
    rw [Matrix.mulVec_mulVec, A.supported_right k]
  rw [← key, hProj, Matrix.mulVec_zero]

/-! ### The two defect terms are nonnegative and vanish exactly at the reset -/

/-- The coherence defect is nonnegative (`supp ρ ⊆ supp Δρ`). -/
theorem coherence_nonneg (P : ProjectorFamily n m) (ρ : DensityOp n) :
    0 ≤ relativeEntropy ρ (pinchDensityOp P ρ) :=
  relEntropy_nonneg_of_support ρ (pinchDensityOp P ρ)
    (fun i j hi hj => mixing_eq_zero_of_ker_inclusion ρ (pinchDensityOp P ρ)
      (fun _v hv => pinch_ker_inclusion P ρ hv) i j hi hj)

/-- Each within-sector defect is nonnegative (`supp τ_λ ⊆ supp σ_λ`, faithful `ρ*`). -/
theorem blockDefect_nonneg {P : ProjectorFamily n m} {η ρstar : DensityOp n}
    (A : BlockDecomp P η) (S : BlockDecomp P ρstar) (hpos : ρstar.M.PosDef) (k : Fin m) :
    0 ≤ relativeEntropy (A.st k) (S.st k) :=
  relEntropy_nonneg_of_support (A.st k) (S.st k)
    (fun i j hi hj => mixing_eq_zero_of_ker_inclusion (A.st k) (S.st k)
      (fun _v hv => blockState_ker_inclusion A S hpos k hv) i j hi hj)

/-- **Theorem 2, inequality (`inf D = inf D_KL`).** For any feasible `ρ`,
`D_KL(p‖s) ≤ D(ρ‖σ)` — the quantum minimum is bounded below by the classical
Kullback–Leibler projection, and is attained at the reset state. -/
theorem relEntropy_ge_blockKL {P : ProjectorFamily n m} {ρ σ : DensityOp n}
    (A : BlockDecomp P (pinchDensityOp P ρ)) (S : BlockDecomp P σ)
    (hq : ∀ k, 0 < S.w k) (hpos : σ.M.PosDef) :
    blockKL A.w S.w ≤ relativeEntropy ρ σ := by
  rw [three_defect A S hq hpos]
  have hsum : 0 ≤ ∑ k, A.w k * relativeEntropy (A.st k) (S.st k) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (A.w_nonneg k) (blockDefect_nonneg A S hpos k))
  linarith [coherence_nonneg P ρ]

/-- **Theorem 2, characterisation.** A feasible `ρ` attains the classical bound
`D(ρ‖σ) = D_KL(p‖s)` **iff** it is the reset state `R_σ(ρ) = ⊕_λ p_λ σ_λ`.  This
is the load-bearing form of the Relative Classicality Theorem: any minimiser has
no cross-sector coherence and reproduces the conditional prior in each occupied
sector. -/
theorem relEntropy_eq_blockKL_iff_reset {P : ProjectorFamily n m} {ρ σ : DensityOp n}
    (A : BlockDecomp P (pinchDensityOp P ρ)) (S : BlockDecomp P σ)
    (hq : ∀ k, 0 < S.w k) (hpos : σ.M.PosDef) :
    relativeEntropy ρ σ = blockKL A.w S.w ↔ ρ = resetState A S := by
  constructor
  · intro hmin
    -- both nonnegative defects vanish
    have hdefects : relativeEntropy ρ (pinchDensityOp P ρ)
        + ∑ k, A.w k * relativeEntropy (A.st k) (S.st k) = 0 := by
      have h3 := three_defect A S hq hpos
      rw [hmin] at h3; linarith [h3]
    have hsum_nn : 0 ≤ ∑ k, A.w k * relativeEntropy (A.st k) (S.st k) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (A.w_nonneg k) (blockDefect_nonneg A S hpos k))
    have hcoh0 : relativeEntropy ρ (pinchDensityOp P ρ) = 0 := by
      linarith [coherence_nonneg P ρ]
    have hsum0 : ∑ k, A.w k * relativeEntropy (A.st k) (S.st k) = 0 := by
      linarith [coherence_nonneg P ρ]
    -- ρ = Δρ (no coherence)
    have hρΔ : ρ.M = (pinchDensityOp P ρ).M :=
      relEntropy_eq_zero_of_support ρ (pinchDensityOp P ρ)
        (fun i j hi hj => mixing_eq_zero_of_ker_inclusion ρ (pinchDensityOp P ρ)
          (fun _v hv => pinch_ker_inclusion P ρ hv) i j hi hj) hcoh0
    -- each occupied block: τ_λ = σ_λ
    have hblockeq : ∀ k, 0 < A.w k → (A.st k).M = (S.st k).M := by
      intro k hk
      have hterm0 : A.w k * relativeEntropy (A.st k) (S.st k) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun l _ => mul_nonneg (A.w_nonneg l) (blockDefect_nonneg A S hpos l))).mp
          hsum0 k (Finset.mem_univ k)
      have hD0 : relativeEntropy (A.st k) (S.st k) = 0 :=
        (mul_eq_zero.mp hterm0).resolve_left (ne_of_gt hk)
      exact relEntropy_eq_zero_of_support (A.st k) (S.st k)
        (fun i j hi hj => mixing_eq_zero_of_ker_inclusion (A.st k) (S.st k)
          (fun _v hv => blockState_ker_inclusion A S hpos k hv) i j hi hj) hD0
    -- assemble ρ.M = Δρ.M = Σ p_λ σ_λ = R_σ(ρ)
    refine DensityOp.ext ?_
    rw [hρΔ]
    show (pinchDensityOp P ρ).M = ∑ k, (A.w k : ℂ) • (S.st k).M
    rw [A.sum_eq]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rcases eq_or_lt_of_le (A.w_nonneg k) with hw | hw
    · rw [← hw]; simp
    · rw [hblockeq k hw]
  · intro hr
    conv_lhs => rw [hr]
    exact relEntropy_resetState_eq_blockKL A S hq hpos

/-! ### Discharging the channel form's `hfaith` from `ρ*` PosDef

The reset state `R_σ(ρ) = ⊕_λ p_λ σ_λ` has positive adapted eigenvalues on every
occupied sector — exactly `three_defect_channel`'s `hfaith`.  If `μ_s = 0` on an
occupied sector then `σ_λ e_s = 0`, so block faithfulness (`blockState_ker`) gives
`Π_λ e_s = 0`; but `e_s` is adapted to that sector, so `Π_λ e_s = e_s`, forcing
`e_s = 0`, contradicting orthonormality. -/

/-- **`hfaith` discharged.** The reset state's adapted eigenvalues are positive on
occupied sectors. -/
theorem reset_mu_pos {P : ProjectorFamily n m} {η ρstar : DensityOp n}
    (A : BlockDecomp P η) (S : BlockDecomp P ρstar) (hpos : ρstar.M.PosDef)
    (s : Fin n) (hs : 0 < A.w (k_of P s)) : 0 < mu P (resetState A S) s := by
  rcases eq_or_lt_of_le ((resetBlockDecomp A S).mu_nonneg s) with hmu | hmu
  · exfalso
    -- `σ_λ e_s = (μ_s / p_λ) e_s = 0`
    have hst := st_mulVec_adaptedBasis (resetBlockDecomp A S) (k := k_of P s) hs s
    rw [if_pos rfl, ← hmu] at hst
    simp only [zero_div, Complex.ofReal_zero, zero_smul] at hst
    have hSst : (S.st (k_of P s)).M *ᵥ (⇑(adaptedBasis P (resetState A S) s) : Fin n → ℂ) = 0 := hst
    -- block faithfulness ⇒ `Π_λ e_s = 0`; but `e_s` is adapted, so `Π_λ e_s = e_s`
    have hProj := blockState_ker S hpos (k_of P s) hSst
    have hfix := adaptedBasis_adapted_mulVec P (resetState A S) s
    rw [hProj] at hfix
    apply (adaptedBasis P (resetState A S)).orthonormal.ne_zero s
    ext i
    simpa using (congrFun hfix i).symm
  · exact hmu

/-- **Theorem 4 channel form, unconditional in `hfaith`.** For a feasible `ρ` and a
faithful equilibrium `ρ*`, the reset channel decomposition holds with no side
hypothesis beyond `ρ*` faithful — `hfaith` is supplied by `reset_mu_pos`. -/
theorem three_defect_channel_of_posDef {P : ProjectorFamily n m} {ρ ρstar : DensityOp n}
    (A : BlockDecomp P (pinchDensityOp P ρ)) (S : BlockDecomp P ρstar)
    (hq : ∀ k, 0 < S.w k) (hpos : ρstar.M.PosDef) :
    DensityOp.relativeEntropy ρ ρstar
      = DensityOp.relativeEntropy ρ (pinchDensityOp P ρ)
        + DensityOp.relativeEntropy (pinchDensityOp P ρ) (resetState A S)
        + DensityOp.relativeEntropy (resetState A S) ρstar :=
  three_defect_channel A S hq hpos (fun s hs => reset_mu_pos A S hpos s hs)

end MacadayPhysicsLean
