/-
Holomorphic ⇒ constant on the torus T² = ℂ/Λ, via Liouville
(Papers T3 / T / S2).

**Mathematical statement.**  An entire function `f : ℂ → ℂ` that is
doubly periodic with respect to two ℝ-linearly independent periods
`ω₁, ω₂` is constant.

**Proof.**  The closed fundamental parallelogram
`P = { s·ω₁ + t·ω₂ : s, t ∈ [0,1] }` is the continuous image of the
compact square `[0,1]²`, hence compact, hence `f` is bounded on `P`.
Because `ω₁, ω₂` are an ℝ-basis of `ℂ`, every `z ∈ ℂ` is congruent
mod the lattice `ℤω₁ + ℤω₂` to a point of `P` (subtract the integer
parts of its coordinates), and `f` is invariant under lattice
translation, so `range f = f '' P` is bounded.  Liouville's theorem
then forces `f` constant.

**Role in the programme.**

* **Paper T3 (zero enstrophy).**  The traceless shear is a holomorphic
  quadratic differential (York decomposition + momentum constraint);
  at genus 1 this theorem forces it constant, which with
  `StokesExactForm` gives `K⊥ ≡ 0`.  This *discharges* the harmonicity
  hypothesis that `HarmonicConstant.lean` takes as an input: at genus 1
  one does not need the elliptic estimate at all.
* **Paper T (genus tower).**  The `g = 1` entry `dim H⁰(T², K²) = 1`
  is stated in `GenusTower.lean` conditionally on Riemann–Roch.  For
  the torus, `K_{T²}` is trivial, so a quadratic differential is an
  entire doubly-periodic function times `(dz)²`, and this theorem makes
  the `g = 1` entry **unconditional**.  (`g ≥ 2` stays Riemann–Roch
  conditional — that is expected; this file does *not* modify
  `GenusTower.lean`.)
* **Paper S2 (exclusion route).**  Supplies the constancy input of the
  `B = 0` step.

Unlike the abstract-core files (`StokesExactForm`, `HarmonicConstant`),
this file uses genuine Mathlib analysis — Liouville's theorem
(`Differentiable.apply_eq_apply_of_bounded`) and compactness — so it is
a full-strength verification, no packaged analytic hypotheses.

Conceptual note (worth preserving): harmonicity is an elliptic
*estimate*; holomorphy at genus 1 is an *identity* — `H⁰(T², K²) =
⟨(dz)²⟩` does not bound the variation, it says there is no variation to
bound.
-/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace MacadayPhysicsLean.T2HolomorphicConstant

open Set Bornology

/-! ### Theorem 1 — reduction to the fundamental parallelogram -/

/-- The closed fundamental parallelogram spanned by the periods. -/
def fundamentalParallelogram (ω₁ ω₂ : ℂ) : Set ℂ :=
  {w : ℂ | ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧
    w = s • ω₁ + t • ω₂}

/-- **Every point of `ℂ` differs from a point of the closed fundamental
parallelogram by an integer combination of the periods.**

Route taken: the two independent periods form an ℝ-basis of `ℂ`
(`Fintype.card (Fin 2) = 2 = finrank ℝ ℂ`); writing `z = a·ω₁ + b·ω₂`
in that basis, subtract `⌊a⌋·ω₁ + ⌊b⌋·ω₂` and the fractional parts
land in `[0,1)`. -/
theorem exists_mem_fundamentalParallelogram_sub_int_smul
    (ω₁ ω₂ : ℂ) (h_indep : LinearIndependent ℝ ![ω₁, ω₂]) (z : ℂ) :
    ∃ (m n : ℤ), z - (m • ω₁ + n • ω₂) ∈ fundamentalParallelogram ω₁ ω₂ := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
    simp [Complex.finrank_real_complex]
  set B := basisOfLinearIndependentOfCardEqFinrank h_indep hcard with hB
  have hB0 : B 0 = ω₁ := by simp [hB]
  have hB1 : B 1 = ω₂ := by simp [hB]
  set a := B.repr z 0 with ha
  set b := B.repr z 1 with hb
  have hz : a • ω₁ + b • ω₂ = z := by
    have hsum := B.sum_repr z
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    simpa [ha, hb] using hsum
  refine ⟨⌊a⌋, ⌊b⌋, Int.fract a, Int.fract b,
    ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩,
    ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩, ?_⟩
  have cast1 : (⌊a⌋ : ℤ) • ω₁ = (⌊a⌋ : ℝ) • ω₁ := (Int.cast_smul_eq_zsmul ℝ ⌊a⌋ ω₁).symm
  have cast2 : (⌊b⌋ : ℤ) • ω₂ = (⌊b⌋ : ℝ) • ω₂ := (Int.cast_smul_eq_zsmul ℝ ⌊b⌋ ω₂).symm
  have fa : Int.fract a = a - (⌊a⌋ : ℝ) := (Int.self_sub_floor a).symm
  have fb : Int.fract b = b - (⌊b⌋ : ℝ) := (Int.self_sub_floor b).symm
  rw [← hz, cast1, cast2, fa, fb]
  module

/-! ### Theorem 2 — bounded range -/

/-- **An entire doubly periodic function has bounded range.**

`range f = f '' P` with `P` the (compact) fundamental parallelogram,
using Theorem 1 and invariance of `f` under lattice translation. -/
theorem isBounded_range_of_doubly_periodic
    (f : ℂ → ℂ) (hf : Continuous f)
    (ω₁ ω₂ : ℂ) (h_indep : LinearIndependent ℝ ![ω₁, ω₂])
    (h₁ : ∀ z, f (z + ω₁) = f z) (h₂ : ∀ z, f (z + ω₂) = f z) :
    IsBounded (Set.range f) := by
  -- `h₁`, `h₂` are exactly periodicity; extend to integer multiples of the periods
  have hp1 : Function.Periodic f ω₁ := h₁
  have hp2 : Function.Periodic f ω₂ := h₂
  have per1 : ∀ (m : ℤ) (w : ℂ), f (w + m • ω₁) = f w := fun m => hp1.zsmul m
  have per2 : ∀ (n : ℤ) (w : ℂ), f (w + n • ω₂) = f w := fun n => hp2.zsmul n
  have hlat : ∀ (m n : ℤ) (w : ℂ), f (w + (m • ω₁ + n • ω₂)) = f w := by
    intro m n w
    rw [← add_assoc, per2, per1]
  -- the fundamental parallelogram is the continuous image of the compact square, hence compact
  have hLcont : Continuous (fun p : ℝ × ℝ => p.1 • ω₁ + p.2 • ω₂) := by
    simp only [Complex.real_smul]
    fun_prop
  have hsq : IsCompact ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hP : IsCompact
      ((fun p : ℝ × ℝ => p.1 • ω₁ + p.2 • ω₂) ''
        ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1))) := hsq.image hLcont
  have hfP := (hP.image hf).isBounded
  refine hfP.subset ?_
  rintro y ⟨z, rfl⟩
  obtain ⟨m, n, s, t, hs, ht, hw⟩ :=
    exists_mem_fundamentalParallelogram_sub_int_smul ω₁ ω₂ h_indep z
  refine ⟨z - (m • ω₁ + n • ω₂), ⟨(s, t), ⟨hs, ht⟩, hw.symm⟩, ?_⟩
  have hcancel : z - (m • ω₁ + n • ω₂) + (m • ω₁ + n • ω₂) = z := by abel
  rw [← hlat m n (z - (m • ω₁ + n • ω₂)), hcancel]

/-! ### Theorem 3 — the main result -/

/-- **Holomorphic doubly periodic functions on `ℂ` are constant.**

The genus-1 constancy theorem: Paper T3's kinematic constancy step,
Paper T's unconditional `g = 1` genus-tower entry, Paper S2's
exclusion-route input.  One application of Liouville's theorem to the
bounded range of Theorem 2. -/
theorem const_of_entire_doubly_periodic
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (ω₁ ω₂ : ℂ) (h_indep : LinearIndependent ℝ ![ω₁, ω₂])
    (h₁ : ∀ z, f (z + ω₁) = f z) (h₂ : ∀ z, f (z + ω₂) = f z) :
    ∀ z w, f z = f w :=
  fun z w => hf.apply_eq_apply_of_bounded
    (isBounded_range_of_doubly_periodic f hf.continuous ω₁ ω₂ h_indep h₁ h₂) z w

/-! ### Corollary 4 — the quadratic-differential statement -/

/-- **Every holomorphic quadratic differential on `T² = ℂ/Λ` is a
constant multiple of `(dz)²`.**

Since `K_{T²}` is trivialized by `dz`, a holomorphic quadratic
differential is `f · (dz)²` with `f` entire and `Λ`-periodic; this says
the coefficient `f` is constant, i.e. `dim_ℂ H⁰(T², K²) = 1` realized
concretely. -/
theorem quadratic_differential_coefficient_const
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (ω₁ ω₂ : ℂ) (h_indep : LinearIndependent ℝ ![ω₁, ω₂])
    (h₁ : ∀ z, f (z + ω₁) = f z) (h₂ : ∀ z, f (z + ω₂) = f z) :
    ∃ c : ℂ, ∀ z, f z = c :=
  ⟨f 0, fun z => const_of_entire_doubly_periodic f hf ω₁ ω₂ h_indep h₁ h₂ z 0⟩

end MacadayPhysicsLean.T2HolomorphicConstant
