/-
The pinching map and the composition-form of VCT Lemma 3.

A **projector family** on `ℂⁿ` is a collection of orthogonal
self-adjoint idempotents `proj : K → Mat n` summing to the identity.
The associated **pinching map** is

  Δ(ρ) := ∑_k Pₖ ρ Pₖ.

Two structural facts are proved here:

* **`pinch_trace`** — pinching preserves trace.
  Proof: `Tr(PρP) = Tr(P²ρ) = Tr(Pρ)` by `trace_mul_cycle` and
  idempotence; summing and using `∑P = I` gives `Tr(ρ)`.

* **`vct_lemma_3_composed`** — the *full* assembly of VCT Lemma 3,
  proved by composition from the prior phases:
   `SchurConcavity` (Hardy–Littlewood–Polya for doubly stochastic)
   ∘  `OrthonormalBridge` (transition matrix is doubly stochastic)
   ∘  `DensityOp` (von Neumann entropy as eigenvalue sum).

  The remaining quantum content is packaged into a single
  hypothesis: the eigenvalue equation
  `μ = transitionMatrix e f · λ` for ONBs `e` of `Δρ` and `f` of `ρ`.
  When that's supplied (the natural next file), VCT Lemma 3 is
  a one-line corollary.
-/

import MacadayPhysicsLean.DensityOp
import MacadayPhysicsLean.OrthonormalBridge
import MacadayPhysicsLean.SchurConcavity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace MacadayPhysicsLean.Pinching

open Matrix Finset
open scoped ComplexOrder

/-! ### Projector families and the pinching map -/

variable {n m : ℕ}

/-- A family of orthogonal self-adjoint idempotent matrices summing to `I`. -/
structure ProjectorFamily (n m : ℕ) where
  /-- The underlying matrix-valued family. -/
  proj : Fin m → Matrix (Fin n) (Fin n) ℂ
  /-- Each `proj k` is Hermitian. -/
  isHermitian : ∀ k, (proj k).IsHermitian
  /-- Each `proj k` is idempotent (`proj k * proj k = proj k`). -/
  idem : ∀ k, proj k * proj k = proj k
  /-- Distinct projectors are *orthogonal*: `proj j * proj k = 0` for `j ≠ k`. -/
  ortho : ∀ j k, j ≠ k → proj j * proj k = 0
  /-- The family sums to the identity. -/
  sum_eq_one : ∑ k, proj k = (1 : Matrix (Fin n) (Fin n) ℂ)

/-- The pinching map associated with a projector family:
`Δ(ρ) := ∑_k Pₖ ρ Pₖ`. -/
noncomputable def ProjectorFamily.pinch (P : ProjectorFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ k, P.proj k * ρ * P.proj k

/-! ### Trace preservation (the easy half of Lemma 1) -/

/-- For each `k`: `Tr(Pₖ * ρ * Pₖ) = Tr(Pₖ * ρ)`. -/
theorem trace_pinch_term (P : ProjectorFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (k : Fin m) :
    (P.proj k * ρ * P.proj k).trace = (P.proj k * ρ).trace := by
  -- `Tr(A * ρ * A) = Tr(A * A * ρ) = Tr(A * ρ)`  (idempotence on `A * A`).
  rw [Matrix.trace_mul_cycle, P.idem]

/-- **Pinching preserves trace.** `Tr(Δρ) = Tr(ρ)`. -/
theorem pinch_trace (P : ProjectorFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (P.pinch ρ).trace = ρ.trace := by
  unfold ProjectorFamily.pinch
  rw [Matrix.trace_sum]
  -- After rewriting each term: ∑ Tr(Pₖ ρ) = Tr((∑ Pₖ) * ρ) = Tr(I * ρ) = Tr ρ
  simp_rw [trace_pinch_term]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, P.sum_eq_one, Matrix.one_mul]

/-! ### Hermitian preservation (Lemma 1) -/

/-- Each summand `Pₖ * ρ * Pₖ` is Hermitian when `ρ` and `Pₖ` are. -/
theorem isHermitian_pinch_term (P : ProjectorFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.IsHermitian) (k : Fin m) :
    (P.proj k * ρ * P.proj k).IsHermitian := by
  -- `(P ρ P)ᴴ = Pᴴ ρᴴ Pᴴ = P ρ P` using Hermitian-ness of P and ρ.
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      (P.isHermitian k), hρ, Matrix.mul_assoc]

/-- **Pinching preserves Hermitian-ness** (part of Lemma 1).
Built by induction on the Finset.sum using `IsHermitian.add` and
`isHermitian_zero`. -/
theorem pinch_isHermitian (P : ProjectorFamily n m)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.IsHermitian) :
    (P.pinch ρ).IsHermitian := by
  unfold ProjectorFamily.pinch
  refine Finset.sum_induction _ Matrix.IsHermitian ?_ ?_ ?_
  · intros A B hA hB; exact hA.add hB
  · exact Matrix.isHermitian_zero
  · intro k _
    exact isHermitian_pinch_term P ρ hρ k

/-! ### Positive-semidefiniteness preservation (Lemma 1) -/

/-- Each summand `Pₖ * ρ * Pₖ` is positive-semidefinite when `ρ` is
PSD and `Pₖ` is Hermitian (so `Pₖᴴ = Pₖ`).  Use Mathlib's
`Matrix.PosSemidef.mul_mul_conjTranspose_same` with `B = Pₖ`. -/
theorem posSemidef_pinch_term (P : ProjectorFamily n m)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) (k : Fin m) :
    (P.proj k * ρ * P.proj k).PosSemidef := by
  have h := hρ.mul_mul_conjTranspose_same (B := P.proj k)
  -- `h : (P.proj k * ρ * (P.proj k)ᴴ).PosSemidef`; close by `Pᴴ = P`.
  rwa [P.isHermitian k] at h

/-- **Pinching preserves positive-semidefiniteness** (part of Lemma 1). -/
theorem pinch_posSemidef (P : ProjectorFamily n m)
    {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) :
    (P.pinch ρ).PosSemidef := by
  unfold ProjectorFamily.pinch
  exact Matrix.posSemidef_sum Finset.univ (fun k _ => posSemidef_pinch_term P hρ k)

/-! ### `pinchDensityOp`: pinching as a DensityOp → DensityOp map (Lemma 1 packaged) -/

/-- The pinching map as an endomorphism of density operators.
This is **Lemma 1 of VCT**: pinching is a quantum channel
(CPTP in the operator sense; we record positive-trace-preserving
here, which is what entropy non-decrease needs). -/
noncomputable def pinchDensityOp (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) : MacadayPhysicsLean.DensityOp n where
  M := P.pinch ρ.M
  posSemidef := pinch_posSemidef P ρ.posSemidef
  trace_one := by rw [pinch_trace, ρ.trace_one]

/-! ### Δρ commutes with each projector (needed for joint eigenbasis) -/

/-- **Pinched state commutes with every projector.**

For any `j`: `(Δρ) · Pⱼ = Pⱼ ρ Pⱼ = Pⱼ · (Δρ)`.  Both sides equal
`Pⱼ ρ Pⱼ` because in `∑ₖ Pₖ ρ Pₖ · Pⱼ`, the orthogonality
`Pₖ · Pⱼ = δₖⱼ Pⱼ` kills all terms except `k = j`; symmetric on the
other side. -/
theorem pinch_commutes (P : ProjectorFamily n m)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (j : Fin m) :
    P.pinch ρ * P.proj j = P.proj j * P.pinch ρ := by
  unfold ProjectorFamily.pinch
  rw [Finset.sum_mul, Finset.mul_sum]
  -- LHS sum: only k = j survives.  All other terms vanish by ortho.
  have hlhs_off : ∀ k ∈ (Finset.univ : Finset (Fin m)), k ≠ j →
      (P.proj k * ρ * P.proj k) * P.proj j = 0 := by
    intro k _ hkj
    rw [Matrix.mul_assoc, P.ortho k j hkj, Matrix.mul_zero]
  -- RHS sum: only k = j survives.
  have hrhs_off : ∀ k ∈ (Finset.univ : Finset (Fin m)), k ≠ j →
      P.proj j * (P.proj k * ρ * P.proj k) = 0 := by
    intro k _ hkj
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.ortho j k hkj.symm,
        Matrix.zero_mul, Matrix.zero_mul]
  rw [Finset.sum_eq_single j hlhs_off (fun h => absurd (Finset.mem_univ j) h),
      Finset.sum_eq_single j hrhs_off (fun h => absurd (Finset.mem_univ j) h)]
  -- Both sides simplify to `P.proj j * ρ * P.proj j` via idempotence.
  have h1 : (P.proj j * ρ * P.proj j) * P.proj j = P.proj j * ρ * P.proj j := by
    rw [Matrix.mul_assoc (P.proj j * ρ), P.idem]
  have h2 : P.proj j * (P.proj j * ρ * P.proj j) = P.proj j * ρ * P.proj j := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P.idem]
  rw [h1, h2]

/-! ### Adaptation lemmas: if `v ∈ range(Pₖ)`, then `Δρ · v = Pₖ · ρ · v`. -/

/-- If `v ∈ range(P.proj k)` (i.e. `P.proj k · v = v`), then
`P.proj j · v = 0` for every other `j`.  Proof: `Pⱼ v = Pⱼ Pₖ v = 0 · v`. -/
theorem proj_apply_zero_of_adapted
    (P : ProjectorFamily n m) (v : Fin n → ℂ) (k : Fin m)
    (h : P.proj k *ᵥ v = v) (j : Fin m) (hjk : j ≠ k) :
    P.proj j *ᵥ v = 0 := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, P.ortho j k hjk, Matrix.zero_mulVec]

/-- **Pinching agrees with `ρ` (modulo a final `P.proj k`) on any
adapted vector.**

If `v` is in the range of `P.proj k`, then `(Δρ) · v = P.proj k · ρ · v`
— all the `ℓ ≠ k` summands in `∑ Pₗ ρ Pₗ` annihilate `v`. -/
theorem pinch_mulVec_adapted
    (P : ProjectorFamily n m) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (k : Fin m) (h : P.proj k *ᵥ v = v) :
    (P.pinch ρ) *ᵥ v = P.proj k *ᵥ (ρ *ᵥ v) := by
  unfold ProjectorFamily.pinch
  rw [Matrix.sum_mulVec]
  -- ∑ ℓ, (Pₗ * ρ * Pₗ) *ᵥ v   --- only the ℓ = k term survives.
  rw [Finset.sum_eq_single k]
  · -- The ℓ = k term: `(Pₖ * ρ * Pₖ) v = Pₖ · ρ · (Pₖ v) = Pₖ · ρ · v`.
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h]
  · -- Other ℓ: `(Pₗ * ρ * Pₗ) v = Pₗ · ρ · (Pₗ v) = Pₗ · ρ · 0 = 0`.
    intro ℓ _ hℓk
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        proj_apply_zero_of_adapted P v k h ℓ hℓk, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-- **Quadratic-form version of the adaptation lemma.**

If `v ∈ range(P.proj k)`, then `vᴴ (Δρ) v = vᴴ ρ v` (in the
`star v ⬝ᵥ _ *ᵥ v` sense).  Combine `pinch_mulVec_adapted` with
the adjoint-of-Hermitian identity:
`star v ᵥ* Pₖ = star (Pₖᴴ *ᵥ v) = star (Pₖ *ᵥ v) = star v`. -/
theorem pinch_quadratic_form_adapted
    (P : ProjectorFamily n m) (ρ : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (k : Fin m) (h : P.proj k *ᵥ v = v) :
    star v ⬝ᵥ (P.pinch ρ) *ᵥ v = star v ⬝ᵥ ρ *ᵥ v := by
  -- `Δρ · v = Pₖ · ρ · v`  via Phase-8 adaptation.
  rw [pinch_mulVec_adapted P ρ v k h]
  -- `star v ⬝ᵥ Pₖ *ᵥ (ρ v) = (star v ᵥ* Pₖ) ⬝ᵥ (ρ v)`.
  rw [dotProduct_mulVec]
  congr 1
  -- Show `star v ᵥ* P.proj k = star v`.
  -- Rewrite `P.proj k` via Hermitian-ness as `(P.proj k)ᴴ`, push the star out.
  have hH : P.proj k = (P.proj k)ᴴ := (P.isHermitian k).eq.symm
  conv_lhs => rw [hH]
  rw [← Matrix.star_mulVec, h]

/-! ### Component formula from the spectral theorem -/

/-- **Outer-product component formula for Hermitian matrices.**

`A i k = Σⱼ (fⱼ)ᵢ · λⱼ · star((fⱼ)ₖ)` where `fⱼ = hA.eigenvectorBasis j`
and `λⱼ = hA.eigenvalues j`.

Proof: by `hA.spectral_theorem` we have `A = U · D · star U` with
`U = hA.eigenvectorUnitary` and `D = diagonal(↑ ∘ λ)`.  Then the
`(i, k)` entry is `Σⱼ Uᵢⱼ · λⱼ · star(Uₖⱼ)` (diagonal kills the inner
sum), and `Uᵢⱼ = (fⱼ)ᵢ` by `eigenvectorUnitary_apply`. -/
theorem hermitian_component_outerProduct
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i k : Fin n) :
    A i k = ∑ j, ⇑(hA.eigenvectorBasis j) i *
      (hA.eigenvalues j : ℂ) * star (⇑(hA.eigenvectorBasis j) k) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq,
        Matrix.IsHermitian.eigenvectorUnitary_apply,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply,
        Function.comp_apply]
    rfl
  · intro ℓ _ hℓj
    rw [Matrix.diagonal_apply_ne _ hℓj]
    ring
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-! ### Spectral expansion of the Hermitian quadratic form -/

/-- **The spectral expansion of a Hermitian quadratic form** — stated
as a clean named proposition.

For a Hermitian `A` with Mathlib eigenvalues `λⱼ` and eigenvectors
`fⱼ := hA.eigenvectorBasis j`:

  `vᴴ A v  =  Σⱼ λⱼ · (vᴴ fⱼ) · (fⱼᴴ v)`.

This is a *pure Mathlib lemma* about any Hermitian matrix —
provable from `Matrix.IsHermitian.spectral_theorem`
(`A = conjStarAlgAut U (diagonal (RCLike.ofReal ∘ λ))`) by
unfolding the entries:
  `A i k = Σⱼ λⱼ (fⱼ)ᵢ · star (fⱼ)ₖ`.

Then both sides of the quadratic-form expansion match by `ring`.

We package it as a proposition here so the Lemma 3b-eig assembly
below can compose it without depending on the full proof.  A
follow-up file (`SpectralQuadraticForm.lean` or similar) can
discharge it. -/
def IsSpectralExpansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (hA : A.IsHermitian) (v : Fin n → ℂ),
    star v ⬝ᵥ A *ᵥ v = ∑ j, (hA.eigenvalues j : ℂ) *
      (star v ⬝ᵥ ⇑(hA.eigenvectorBasis j)) *
      (star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ v)

/-- **`IsSpectralExpansion` holds for every Hermitian matrix.**

Proof strategy: substitute `hermitian_component_outerProduct` into
`star v ⬝ᵥ A *ᵥ v`, then for each fixed `j` factor the inner sums.
The inner-`k` factor is `↑λⱼ · (Σₖ star((fⱼ)ₖ) · vₖ)`, the outer-`i`
factor is `Σᵢ star(vᵢ) · (fⱼ)ᵢ`.  Multiplication commutativity in `ℂ`
matches the result with the RHS factored form. -/
theorem isSpectralExpansion_of_hermitian
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : IsSpectralExpansion A := by
  intro hA v
  -- Unfold dotProduct + mulVec on LHS
  change (∑ i, star (v i) * ∑ k, A i k * v k) = _
  -- Substitute the outer-product component formula for A
  simp_rw [hermitian_component_outerProduct hA]
  -- LHS = ∑ i, star (v i) * ∑ k, (∑ j, atom_jik) * v k
  -- Inner: (∑ j, atom_jik) * v k = ∑ j, atom_jik * v k
  simp_rw [Finset.sum_mul]
  -- LHS = ∑ i, star (v i) * ∑ k, ∑ j, atom_jik * v k
  -- Swap inner pair k <-> j under each outer i.  Use Finset.sum_comm
  -- via a `have` so the pattern-matching is unambiguous.
  conv_lhs =>
    rw [show (∑ i, star (v i) * ∑ k : Fin n, ∑ j : Fin n,
              ⇑(hA.eigenvectorBasis j) i * (hA.eigenvalues j : ℂ) *
                star (⇑(hA.eigenvectorBasis j) k) * v k) =
            (∑ i, star (v i) * ∑ j : Fin n, ∑ k : Fin n,
              ⇑(hA.eigenvectorBasis j) i * (hA.eigenvalues j : ℂ) *
                star (⇑(hA.eigenvectorBasis j) k) * v k) from by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]]
  -- LHS = ∑ i, star (v i) * ∑ j, ∑ k, atom_jik * v k
  -- Distribute star (v i) inward: into the j-sum, then into the k-sum
  simp_rw [Finset.mul_sum]
  -- LHS = ∑ i, ∑ j, ∑ k, star (v i) * (atom_jik * v k)
  -- Swap outer i <-> j
  rw [Finset.sum_comm]
  -- LHS = ∑ j, ∑ i, ∑ k, star (v i) * (atom_jik * v k)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Rearrange the per-`j` body:
  --   ∑ i, ∑ k, star (v i) * (((fⱼ)ᵢ * ↑λⱼ * star((fⱼ)ₖ)) * v k)
  -- = ↑λⱼ * (∑ i, star (v i) * (fⱼ)ᵢ) * (∑ k, star ((fⱼ)ₖ) * v k)   by `ring` after factoring.
  -- Group via a single ring rewrite of the atom into the factored form.
  simp_rw [show ∀ i k,
    star (v i) * (⇑(hA.eigenvectorBasis j) i * (hA.eigenvalues j : ℂ) *
        star (⇑(hA.eigenvectorBasis j) k) * v k) =
      (hA.eigenvalues j : ℂ) *
        (star (v i) * ⇑(hA.eigenvectorBasis j) i) *
        (star (⇑(hA.eigenvectorBasis j) k) * v k)
    from fun _ _ => by ring]
  -- Now: ∑ i, ∑ k, ↑λⱼ * (star (v i) * (fⱼ)ᵢ) * (star ((fⱼ)ₖ) * v k)
  -- Factor inner k-sum: ∑ k of `c * X * (star ((fⱼ)ₖ) * v k)` = c * X * ∑ k (...)
  simp_rw [← Finset.mul_sum]
  -- ∑ i, ↑λⱼ * (star (v i) * (fⱼ)ᵢ) * (∑ k, star ((fⱼ)ₖ) * v k)
  -- Factor outer i-sum:
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- LHS now: ↑λⱼ * (∑ i, star (v i) * (fⱼ)ᵢ) * (∑ k, star ((fⱼ)ₖ) * v k)
  -- RHS:     ↑λⱼ * (star v ⬝ᵥ ⇑(fⱼ)) * (star ⇑(fⱼ) ⬝ᵥ v)
  -- Unfold dotProduct + Pi.star_apply to match (`star (v i)` = `star v i`).
  simp only [dotProduct, Pi.star_apply]

/-! ### Bridging to Mathlib's spectral theorem -/

/-- **Eigenvalue of pinched state = ρ's diagonal entry at an adapted eigenvector.**

If `eᵢ := (pinchDensityOp P ρ).isHermitian.eigenvectorBasis i` happens
to satisfy `P.proj k · eᵢ = eᵢ` (i.e. is adapted to projector `k`), then
the `i`-th eigenvalue of the pinched state equals
`Re (eᵢᴴ · ρ · eᵢ)`.

Proof: Mathlib's `Matrix.IsHermitian.eigenvalues_eq` gives
`μᵢ = Re (eᵢᴴ · Δρ · eᵢ)`, and `pinch_quadratic_form_adapted` then
replaces `Δρ` with `ρ` on the diagonal at the adapted `eᵢ`.

This converts the eigenvalues of the pinched state into ρ-diagonals
— the *second key step* of Lemma 3b-eig.  The remaining step is
expanding `eᵢᴴ · ρ · eᵢ` as `Σⱼ λⱼ |⟨fⱼ, eᵢ⟩|²` using the spectral
decomposition of ρ. -/
theorem pinch_eigenvalue_eq_orig_diagonal
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) (i : Fin n) (k : Fin m)
    (h_adapt : P.proj k *ᵥ
      ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i) =
        ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i)) :
    ((pinchDensityOp P ρ).isHermitian).eigenvalues i =
      RCLike.re (star (⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i)) ⬝ᵥ
        ρ.M *ᵥ ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i)) := by
  rw [Matrix.IsHermitian.eigenvalues_eq]
  congr 1
  -- `(pinchDensityOp P ρ).M = P.pinch ρ.M` by definition.
  change star _ ⬝ᵥ (P.pinch ρ.M) *ᵥ _ = star _ ⬝ᵥ ρ.M *ᵥ _
  exact pinch_quadratic_form_adapted P ρ.M _ k h_adapt

/-! ### Lemma 2 — pinching preserves trace against any commuting observable -/

/-- The cyclic identity used in Lemma 2:
`Tr(Pₖ * ρ * Pₖ * A) = Tr(Pₖ * (ρ * A))` whenever `Pₖ` commutes
with `A` (and `Pₖ` is idempotent).

Computation:
`P ρ P A = (Pρ)(PA) = (Pρ)(AP) = P (ρ A) P`  (commutation +
associativity), then `Tr(P X P) = Tr(P²X) = Tr(P X)` for `X = ρ A`. -/
theorem trace_pinch_mul_term (P : ProjectorFamily n m)
    (ρ A : Matrix (Fin n) (Fin n) ℂ)
    (h_comm : ∀ k, P.proj k * A = A * P.proj k) (k : Fin m) :
    (P.proj k * ρ * P.proj k * A).trace = (P.proj k * (ρ * A)).trace := by
  have h_assoc : P.proj k * ρ * P.proj k * A = P.proj k * (ρ * A) * P.proj k := by
    rw [Matrix.mul_assoc (P.proj k * ρ) (P.proj k) A,
        h_comm,
        ← Matrix.mul_assoc (P.proj k * ρ) A,
        Matrix.mul_assoc (P.proj k) ρ A]
  rw [h_assoc, Matrix.trace_mul_cycle, P.idem]

/-- **Lemma 2 (constraint preservation).**  If an observable `A`
commutes with every projector `Pₖ`, then `Tr(Δρ · A) = Tr(ρ · A)`. -/
theorem pinch_preserves_trace_mul (P : ProjectorFamily n m)
    (ρ A : Matrix (Fin n) (Fin n) ℂ)
    (h_comm : ∀ k, P.proj k * A = A * P.proj k) :
    (P.pinch ρ * A).trace = (ρ * A).trace := by
  unfold ProjectorFamily.pinch
  rw [Matrix.sum_mul, Matrix.trace_sum]
  -- Each term equals `Tr(Pₖ * (ρ * A))`; summing and using `∑ Pₖ = I`:
  simp_rw [trace_pinch_mul_term P ρ A h_comm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, P.sum_eq_one, Matrix.one_mul]

/-! ### Lemma 3 by composition

Below we state VCT Lemma 3 as a *fully proved theorem* parameterized
on the eigenvalue-equation hypothesis.  When the eigenvalue equation
is supplied (the next milestone — the genuinely-quantum step
involving the spectral theorem for commuting Hermitians), VCT
Lemma 3 holds for the concrete pinching map as a one-line corollary. -/

/-- **VCT Lemma 3 — composition form.**

Assuming a density operator `ρ`, its pinched form `pinched`, and the
eigenvalue equation `μ = M(e, f) · λ` (where `e, f` are ONBs and
`M(e, f)` is the transition matrix of `OrthonormalBridge`), we have
`S(ρ) ≤ S(pinched)`.

This is proved by composing three previously-established facts:

* `OrthonormalBridge.transitionMatrix_doublyStochastic` — `M(e, f)`
  is doubly stochastic.
* `SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic` —
  Shannon entropy is non-decreased by doubly-stochastic averaging.
* `DensityOp.vonNeumannEntropy` — entropy as eigenvalue sum.

The hypothesis `h_eig_eq` is exactly what an eigenvalue-bridge
construction from pinching must supply (= "Lemma 3b-eig"). -/
theorem vct_lemma_3_composed
    {n : ℕ}
    (ρ pinched : MacadayPhysicsLean.DensityOp n)
    (e f : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (lam mu : Fin n → ℝ)
    (h_lam_nonneg : ∀ i, 0 ≤ lam i)
    (h_eig_eq :
        mu = (MacadayPhysicsLean.OrthonormalBridge.transitionMatrix
                (𝕜 := ℂ) (fun k => e k) (fun k => f k)).mulVec lam)
    (h_ρ_entropy :
        MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
          = ∑ i, Real.negMulLog (lam i))
    (h_pinched_entropy :
        MacadayPhysicsLean.DensityOp.vonNeumannEntropy pinched
          = ∑ i, Real.negMulLog (mu i)) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy pinched := by
  rw [h_ρ_entropy, h_pinched_entropy, h_eig_eq]
  exact MacadayPhysicsLean.SchurConcavity.shannon_entropy_le_mulVec_of_doublyStochastic
    _ (MacadayPhysicsLean.OrthonormalBridge.transitionMatrix_doublyStochastic e f)
    lam h_lam_nonneg

/-! ### Closing Lemma 3b-eig: composing the spectral expansion with the bridge

We package the remaining quantum content as two clean named
hypotheses on the inputs:

* `IsSpectralExpansion ρ.M` — the (matrix-theoretic) spectral expansion
  of the quadratic form, a *pure Mathlib lemma* about Hermitian matrices.
* An **adaptation map** `k_of : Fin n → Fin m` — telling us which projector
  each Mathlib-supplied eigenvector of `pinchDensityOp P ρ` belongs to —
  together with the proof that `P.proj (k_of i) · eᵢ = eᵢ`.  This is the
  joint-diagonalization existence step.

Given these two inputs, `Lemma3bEig P ρ` is fully discharged below.  The
remaining work for unconditional VCT Lemma 3 is to prove both inputs from
first principles. -/

/-! ### The full VCT Lemma 3, modulo the remaining quantum hypothesis

We package the *one* remaining quantum step ("Lemma 3b-eig") as a
named hypothesis on a concrete `ProjectorFamily` + `DensityOp`.
Then VCT Lemma 3 — entropy non-decrease for the concrete
`pinchDensityOp` — follows unconditionally. -/

/-- **Lemma 3b-eig hypothesis.**  The eigenvalue equation for the
concrete pinching map: there exist orthonormal eigenbases `e` of
`pinchDensityOp P ρ` and `f` of `ρ` (with eigenvalues `μ` and `λ`
respectively) such that `μ = M(e, f) · λ`, where `M(e, f)` is the
transition-matrix from `OrthonormalBridge`.

Discharging this hypothesis requires the spectral theorem for
commuting Hermitians (since `pinchDensityOp P ρ` commutes with every
`P.proj k`), plus the observation that an `e`-vector lying in
`range (P.proj k)` satisfies `(P.proj k) eᵢ = eᵢ`. -/
def Lemma3bEig {n m : ℕ} (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) : Prop :=
  ∃ (e f : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (lam mu : Fin n → ℝ),
    (∀ i, 0 ≤ lam i) ∧
    mu = (MacadayPhysicsLean.OrthonormalBridge.transitionMatrix
            (𝕜 := ℂ) (fun k => e k) (fun k => f k)).mulVec lam ∧
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ = ∑ i, Real.negMulLog (lam i) ∧
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ)
      = ∑ i, Real.negMulLog (mu i)

/-- **VCT Lemma 3 — full concrete form.**

Given a projector family `P` and a density operator `ρ`, assuming
the eigenvalue equation `Lemma3bEig P ρ`, the von Neumann entropy
of the pinched state is at least the entropy of the original.

This is the **full VCT Lemma 3 reduced to a single, narrow,
named quantum hypothesis** — the only remaining work for the
crown-jewel theorem.  Once `Lemma3bEig P ρ` is discharged
(by the spectral theorem for commuting Hermitians), VCT Lemma 3
is *unconditional*. -/
theorem vct_lemma_3 (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (h : Lemma3bEig P ρ) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ) := by
  obtain ⟨e, f, lam, mu, h_nonneg, h_eig, h_ρ, h_pinched⟩ := h
  exact vct_lemma_3_composed ρ (pinchDensityOp P ρ) e f lam mu
    h_nonneg h_eig h_ρ h_pinched


/-! ### Closing Lemma3bEig from just the adaptation hypothesis -/

/-- Helper: `Re((lam : ℂ) · c · star c) = lam · ‖c‖²`.

`c · star c = c · conj c = ↑(‖c‖²)` via `RCLike.mul_conj`,
where the cast wraps `(↑‖c‖)^2 = ↑(‖c‖^2)` by `Complex.ofReal_pow`. -/
private lemma re_lam_mul_self_star (lam : ℝ) (c : ℂ) :
    RCLike.re ((lam : ℂ) * c * star c) = lam * ‖c‖^2 := by
  change ((lam : ℂ) * c * star c).re = lam * ‖c‖^2
  rw [mul_assoc, show star c = (starRingEnd ℂ) c from rfl, Complex.mul_conj]
  rw [show ((↑lam : ℂ) * ↑(Complex.normSq c)) = ((lam * Complex.normSq c : ℝ) : ℂ) from by
        push_cast; ring]
  rw [Complex.ofReal_re]
  congr 1
  exact RCLike.normSq_eq_def' c

/-- Companion: dot-product conjugate-swap.
`star (star a ⬝ᵥ b) = star b ⬝ᵥ a` for `a, b : Fin n → ℂ`. -/
private lemma star_dotProduct_star (a b : Fin n → ℂ) :
    star (star a ⬝ᵥ b) = star b ⬝ᵥ a := by
  simp [dotProduct, star_sum, StarMul.star_mul, mul_comm]

/-- **`Lemma3bEig` from the adaptation hypothesis.**

If each Mathlib-supplied eigenvector of `pinchDensityOp P ρ` lies in
the range of the corresponding projector, then `Lemma3bEig P ρ`
holds, by composition of:
* `pinch_eigenvalue_eq_orig_diagonal` ⇒ `μᵢ = Re(eᵢᴴ · ρ · eᵢ)`,
* `isSpectralExpansion_of_hermitian` ⇒ spectral expansion of `eᵢᴴ ρ eᵢ`,
* `Re` distributes over `Finset.sum` (`map_sum`),
* `star_dotProduct_star` for the conjugate-swap `c2 = star c1`,
* `re_lam_mul_self_star` per summand,
* `EuclideanSpace.inner_eq_star_dotProduct` + `dotProduct_comm`
  for the transitionMatrix bridge. -/
theorem Lemma3bEig_of_adapted
    {n m : ℕ}
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (k_of : Fin n → Fin m)
    (h_adapt : ∀ i, P.proj (k_of i) *ᵥ
        ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i) =
          ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i)) :
    Lemma3bEig P ρ := by
  refine ⟨(pinchDensityOp P ρ).isHermitian.eigenvectorBasis,
          ρ.isHermitian.eigenvectorBasis,
          ρ.isHermitian.eigenvalues,
          (pinchDensityOp P ρ).isHermitian.eigenvalues,
          ?_, ?_, ?_, ?_⟩
  · intro i; exact Matrix.PosSemidef.eigenvalues_nonneg ρ.posSemidef i
  · funext i
    rw [pinch_eigenvalue_eq_orig_diagonal P ρ i (k_of i) (h_adapt i)]
    rw [isSpectralExpansion_of_hermitian ρ.M ρ.isHermitian _]
    rw [map_sum]
    -- LHS: ∑ j, Re((λⱼ:ℂ) · c1 · c2).  RHS: (transitionMatrix.mulVec lam) i.
    -- Expand only RHS mulVec to a sum (keep dotProducts intact for star_dotProduct_star).
    change _ = (MacadayPhysicsLean.OrthonormalBridge.transitionMatrix (𝕜 := ℂ) _ _) i ⬝ᵥ
              ρ.isHermitian.eigenvalues
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- Per j: Re((λⱼ:ℂ) · c1 · c2) = M i j * λⱼ
    -- Apply conjugate swap on c2:
    rw [show (star ⇑(ρ.isHermitian.eigenvectorBasis j) ⬝ᵥ
                ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i))
            = star (star ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i) ⬝ᵥ
                ⇑(ρ.isHermitian.eigenvectorBasis j))
        from (star_dotProduct_star _ _).symm]
    rw [re_lam_mul_self_star]
    -- LHS: ρ.isHermitian.eigenvalues j * ‖star ⇑(eᵢ) ⬝ᵥ ⇑(fⱼ)‖²
    -- RHS: M i j * λⱼ where M = transitionMatrix
    rw [mul_comm]
    congr 1
    -- transitionMatrix i j = ‖inner ℂ (e i) (f j)‖² = ‖star ⇑(e i) ⬝ᵥ ⇑(f j)‖²
    -- Use `EuclideanSpace.inner_eq_star_dotProduct` + `dotProduct_comm`.
    change ‖star (⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i)) ⬝ᵥ
            ⇑(ρ.isHermitian.eigenvectorBasis j)‖^2
        = MacadayPhysicsLean.OrthonormalBridge.transitionMatrix (𝕜 := ℂ)
            (fun k => (pinchDensityOp P ρ).isHermitian.eigenvectorBasis k)
            (fun k => ρ.isHermitian.eigenvectorBasis k) i j
    unfold MacadayPhysicsLean.OrthonormalBridge.transitionMatrix
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    -- Goal: ‖star ⇑(eᵢ) ⬝ᵥ ⇑(fⱼ)‖² = ‖ofLp (fⱼ) ⬝ᵥ star (ofLp (eᵢ))‖²
    -- `⇑` and `ofLp` are the same for EuclideanSpace; use dotProduct_comm.
    congr 1
    rw [dotProduct_comm]
  · rfl
  · rfl

/-- **VCT Lemma 3 — unconditional, modulo the single adaptation hypothesis.**

Composes `Lemma3bEig_of_adapted` with `vct_lemma_3`.  Given just an
adaptation map `k_of` and the proof that each Mathlib-eigenvector of
`pinchDensityOp P ρ` is in the range of its assigned projector, the
von Neumann entropy of the pinched state is at least that of `ρ`.

This is the **single-hypothesis form of VCT Lemma 3**.  The only
remaining work for fully unconditional VCT Lemma 3 is to *construct*
the adapted eigenbasis from `pinch_commutes` (joint diagonalization
of commuting Hermitians). -/
theorem vct_lemma_3_of_adapted
    {n m : ℕ}
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (k_of : Fin n → Fin m)
    (h_adapt : ∀ i, P.proj (k_of i) *ᵥ
        ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i) =
          ⇑((pinchDensityOp P ρ).isHermitian.eigenvectorBasis i)) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ) :=
  vct_lemma_3 P ρ (Lemma3bEig_of_adapted P ρ k_of h_adapt)

/-! ### Generalized form for a custom adapted ONB

The above `Lemma3bEig_of_adapted` uses Mathlib's *canonical* eigenvector
basis for `pinchDensityOp P ρ`.  For joint diagonalization, however, we
construct a *custom* adapted ONB whose eigenvalue ordering may differ.
The version below accepts any such custom orthonormal eigenbasis and
its eigenvalues as input. -/

/-- **Helper**: for an orthonormal basis vector `e i` in
`EuclideanSpace ℂ (Fin n)`, the self-dot-product `star ⇑(e i) ⬝ᵥ ⇑(e i)`
equals `1 : ℂ`.

Bridges the matrix-level dotProduct to the inner-product space norm
via `EuclideanSpace.inner_eq_star_dotProduct` + `inner_self_eq_norm_sq_to_K`
+ the ONB unit-norm hypothesis. -/
private lemma orthonormalBasis_self_dotProduct
    {n : ℕ} (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (i : Fin n) :
    (star ⇑(e i) ⬝ᵥ ⇑(e i) : ℂ) = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
  norm_num

/-- **`Lemma3bEig` from a custom adapted ONB.**

Accepts a custom orthonormal eigenbasis `e` of `pinchDensityOp P ρ`
with eigenvalues `mu : Fin n → ℝ`, an adaptation map `k_of : Fin n → Fin m`
saying each `e i` lies in the range of `P.proj (k_of i)`, and a separately-
supplied entropy equation
  `vonNeumannEntropy (pinchDensityOp P ρ) = ∑ i, negMulLog (mu i)`
(which says `mu` is a valid eigenvalue assignment for the pinched
state in the von-Neumann-entropy sense — provable from spectral
multiset uniqueness, which is a separate Mathlib lemma).

Conclusion: `Lemma3bEig P ρ`.

Combined with a joint-diagonalization existence theorem (which produces
just such an `e, mu, k_of`), this gives the path to unconditional
VCT Lemma 3. -/
theorem Lemma3bEig_of_adapted_custom
    {n m : ℕ}
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (mu : Fin n → ℝ)
    (k_of : Fin n → Fin m)
    (h_eig : ∀ i, (pinchDensityOp P ρ).M *ᵥ ⇑(e i)
        = (mu i : ℂ) • (⇑(e i) : Fin n → ℂ))
    (h_adapt : ∀ i, P.proj (k_of i) *ᵥ ⇑(e i) = ⇑(e i))
    (h_entropy : MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ)
                   = ∑ i, Real.negMulLog (mu i)) :
    Lemma3bEig P ρ := by
  refine ⟨e, ρ.isHermitian.eigenvectorBasis,
          ρ.isHermitian.eigenvalues, mu,
          ?_, ?_, ?_, h_entropy⟩
  · intro i; exact Matrix.PosSemidef.eigenvalues_nonneg ρ.posSemidef i
  · funext i
    -- Step A: `(mu i : ℂ) = star ⇑(e i) ⬝ᵥ Δρ *ᵥ ⇑(e i)` via h_eig + unit norm.
    have h_quad_pinch :
        star (⇑(e i) : Fin n → ℂ) ⬝ᵥ (pinchDensityOp P ρ).M *ᵥ ⇑(e i)
          = (mu i : ℂ) := by
      rw [h_eig i, dotProduct_smul, orthonormalBasis_self_dotProduct,
          smul_eq_mul, mul_one]
    -- Step B: adaptation transfers Δρ-form to ρ-form on `e i`.
    have h_quad_eq :
        star (⇑(e i) : Fin n → ℂ) ⬝ᵥ (pinchDensityOp P ρ).M *ᵥ ⇑(e i)
          = star ⇑(e i) ⬝ᵥ ρ.M *ᵥ ⇑(e i) := by
      change star ⇑(e i) ⬝ᵥ (P.pinch ρ.M) *ᵥ ⇑(e i) = _
      exact pinch_quadratic_form_adapted P ρ.M ⇑(e i) (k_of i) (h_adapt i)
    have h_mu_eq :
        (mu i : ℂ) = star (⇑(e i) : Fin n → ℂ) ⬝ᵥ ρ.M *ᵥ ⇑(e i) :=
      h_quad_pinch.symm.trans h_quad_eq
    -- Step C: spectral expansion of ρ.M at `v = ⇑(e i)`.
    rw [isSpectralExpansion_of_hermitian ρ.M ρ.isHermitian ⇑(e i)] at h_mu_eq
    -- Step D: take Re of both sides, match to transitionMatrix entries.
    have h_re_cast : mu i = RCLike.re ((mu i : ℂ)) := by simp
    rw [h_re_cast, h_mu_eq, map_sum]
    change _ = (MacadayPhysicsLean.OrthonormalBridge.transitionMatrix (𝕜 := ℂ) _ _) i ⬝ᵥ
              ρ.isHermitian.eigenvalues
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show (star ⇑(ρ.isHermitian.eigenvectorBasis j) ⬝ᵥ
                (⇑(e i) : Fin n → ℂ))
            = star (star (⇑(e i) : Fin n → ℂ) ⬝ᵥ
                ⇑(ρ.isHermitian.eigenvectorBasis j))
        from (star_dotProduct_star _ _).symm]
    rw [re_lam_mul_self_star]
    rw [mul_comm]
    congr 1
    change ‖star (⇑(e i) : Fin n → ℂ) ⬝ᵥ
            ⇑(ρ.isHermitian.eigenvectorBasis j)‖^2
        = MacadayPhysicsLean.OrthonormalBridge.transitionMatrix (𝕜 := ℂ)
            (fun k => e k) (fun k => ρ.isHermitian.eigenvectorBasis k) i j
    unfold MacadayPhysicsLean.OrthonormalBridge.transitionMatrix
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    congr 1
    rw [dotProduct_comm]
  · rfl

/-- **VCT Lemma 3 — custom-basis form.**

Composes `Lemma3bEig_of_adapted_custom` with `vct_lemma_3`.  Given
a custom adapted ONB + eigenvalues + entropy equation, the von
Neumann entropy of the pinched state dominates that of `ρ`. -/
theorem vct_lemma_3_of_adapted_custom
    {n m : ℕ}
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (mu : Fin n → ℝ)
    (k_of : Fin n → Fin m)
    (h_eig : ∀ i, (pinchDensityOp P ρ).M *ᵥ ⇑(e i)
        = (mu i : ℂ) • (⇑(e i) : Fin n → ℂ))
    (h_adapt : ∀ i, P.proj (k_of i) *ᵥ ⇑(e i) = ⇑(e i))
    (h_entropy : MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ)
                   = ∑ i, Real.negMulLog (mu i)) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ) :=
  vct_lemma_3 P ρ
    (Lemma3bEig_of_adapted_custom P ρ e mu k_of h_eig h_adapt h_entropy)

end MacadayPhysicsLean.Pinching
