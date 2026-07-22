/-
Joint diagonalization of `pinchDensityOp P ρ` and the projector family `P`.

The remaining gap for unconditional VCT Lemma 3.  We use Mathlib's
joint-eigenspace decomposition:

* `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute` — for
  a family of pairwise-commuting symmetric operators in finite dim,
  the space decomposes as an internal direct sum of joint eigenspaces.
* `DirectSum.IsInternal.subordinateOrthonormalBasis` — given such a
  decomposition, builds an ONB whose vectors are each in one of the
  components.

For our setting:

* `T 0 := (pinchDensityOp P ρ).M.toEuclideanLin` (symmetric: pinchDensityOp is Hermitian)
* `T (k+1) := (P.proj k).toEuclideanLin` (symmetric: each projector is Hermitian)
* All pairwise commute (`pinch_commutes` + projector orthogonality)

Then the joint eigenspace decomposition gives an adapted ONB.  Each ONB
vector is in `⨅ j, eigenspace (T j) (joint_eigenvalues j)` — for our
projector operators (eigenvalues `{0, 1}`), exactly one projector has
eigenvalue `1`, identifying the projector range that contains the vector.

**Scope of this file**: state the existence of the adapted ONB.  The
full discharge of VCT Lemma 3 from this existence (composing with
`Lemma3bEig_of_adapted` requires a custom basis, not Mathlib's
default) is the natural follow-up.
-/

import MacadayPhysicsLean.Pinching
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Tactic

namespace MacadayPhysicsLean.JointDiagonalization

open Matrix LinearMap
open MacadayPhysicsLean.Pinching

/-! ### Symmetry / Hermitian bridge -/

variable {n m : ℕ}

/-- `pinchDensityOp P ρ` viewed as a symmetric linear endomorphism of
`EuclideanSpace ℂ (Fin n)`. -/
noncomputable def pinch_sym (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    (EuclideanSpace ℂ (Fin n)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) :=
  (pinchDensityOp P ρ).M.toEuclideanLin

/-- Each projector `P.proj k` as a symmetric linear endomorphism. -/
noncomputable def proj_sym (P : ProjectorFamily n m) (k : Fin m) :
    (EuclideanSpace ℂ (Fin n)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) :=
  (P.proj k).toEuclideanLin

/-! ### Path to existence (sketch)

The full existence theorem `exists_adapted_orthonormal_eigenbasis`
would say:

```
∃ (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
  (μ : Fin n → ℝ) (k_of : Fin n → Fin m),
  (∀ i, pinch_sym P ρ (e i) = (μ i : ℂ) • e i) ∧
  (∀ i, proj_sym P (k_of i) (e i) = e i)
```

The construction:

1. Set up a family `T : Fin (m+1) → LinearMap`:
   - `T 0 := pinch_sym P ρ`
   - `T ⟨k+1, _⟩ := proj_sym P k`
2. Each `T j` is symmetric (Hermitian → IsSymmetric).
3. Pairwise commutativity:
   * `pinch_sym` commutes with each `proj_sym` (`pinch_commutes`).
   * `proj_sym k` commutes with `proj_sym l` (orthogonal projectors commute).
4. Apply `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`
   ⇒ joint eigenspace decomposition.
5. Apply `DirectSum.IsInternal.subordinateOrthonormalBasis`
   ⇒ adapted ONB `e`.
6. For each `e i`, extract joint eigenvalue tuple `(α 0, α 1, …, α m)`:
   * `α 0` is the `pinch_sym` eigenvalue (= μ i).
   * For each `k`: `α (k+1) ∈ {0, 1}` is the projector eigenvalue.
   * Exactly one `k` has `α (k+1) = 1` — call it `k_of i`.
7. The conditions follow:
   * `pinch_sym (e i) = (μ i : ℂ) • e i` — from being in `pinch_sym`-eigenspace.
   * `proj_sym (k_of i) (e i) = e i` — from being in the `k_of i`-th projector's
     eigenspace for eigenvalue 1 (i.e. the range of that projector).

The remaining Lean work: each of steps 1-7 is one named Mathlib invocation
plus careful index management.  This is bounded, mechanical, several hundred
lines.  Once landed, combining with `Lemma3bEig_of_adapted` (after
generalizing it to accept a custom adapted basis) closes VCT Lemma 3
unconditionally. -/

/-! ### Symmetry of the operators -/

/-- `pinch_sym P ρ` is symmetric (since `pinchDensityOp P ρ` is Hermitian). -/
theorem pinch_sym_isSymmetric (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    (pinch_sym P ρ).IsSymmetric := by
  unfold pinch_sym
  exact Matrix.isHermitian_iff_isSymmetric.mp (pinchDensityOp P ρ).isHermitian

/-- `proj_sym P k` is symmetric (since `P.proj k` is Hermitian). -/
theorem proj_sym_isSymmetric (P : ProjectorFamily n m) (k : Fin m) :
    (proj_sym P k).IsSymmetric := by
  unfold proj_sym
  exact Matrix.isHermitian_iff_isSymmetric.mp (P.isHermitian k)

/-! ### Commutativity in the linear-map world -/

/-- `pinch_sym P ρ` commutes with each `proj_sym P k`, via lifting
the matrix-level `pinch_commutes` through `toLpLinAlgEquiv`'s
multiplicativity. -/
theorem pinch_proj_commute (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (k : Fin m) : Commute (pinch_sym P ρ) (proj_sym P k) := by
  have h : Commute (P.pinch ρ.M) (P.proj k) := pinch_commutes P ρ.M k
  exact h.map (Matrix.toLpLinAlgEquiv (n := Fin n) 2)

/-- Distinct projectors commute (since they're orthogonal). -/
theorem proj_proj_commute (P : ProjectorFamily n m) (k l : Fin m) :
    Commute (proj_sym P k) (proj_sym P l) := by
  by_cases hkl : k = l
  · rw [hkl]
  · have h : Commute (P.proj k) (P.proj l) := by
      change P.proj k * P.proj l = P.proj l * P.proj k
      rw [P.ortho k l hkl, P.ortho l k (Ne.symm hkl)]
    exact h.map (Matrix.toLpLinAlgEquiv (n := Fin n) 2)

/-! ### Joint diagonalization: the bundled family `opFamily` -/

/-- The bundled operator family for joint diagonalization, indexed by
`Option (Fin m)`:

* `opFamily P ρ none = pinch_sym P ρ`
* `opFamily P ρ (some k) = proj_sym P k`

The four atomic ingredients above (`pinch_sym_isSymmetric`,
`proj_sym_isSymmetric`, `pinch_proj_commute`, `proj_proj_commute`)
combine to satisfy the hypotheses of
`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`. -/
noncomputable def opFamily (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    Option (Fin m) → Module.End ℂ (EuclideanSpace ℂ (Fin n))
  | none => pinch_sym P ρ
  | some k => proj_sym P k

/-- Every operator in `opFamily` is symmetric. -/
theorem opFamily_isSymmetric (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    ∀ i, (opFamily P ρ i).IsSymmetric := by
  intro i
  cases i with
  | none => exact pinch_sym_isSymmetric P ρ
  | some k => exact proj_sym_isSymmetric P k

open scoped Function in
/-- All operators in `opFamily` pairwise commute. -/
theorem opFamily_pairwise_commute (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    Pairwise (Commute on (opFamily P ρ)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some k => exact pinch_proj_commute P ρ k
  | some k =>
    cases j with
    | none => exact (pinch_proj_commute P ρ k).symm
    | some l => exact proj_proj_commute P k l

/-! ### The joint eigenspace decomposition (Mathlib's
`directSum_isInternal_of_pairwise_commute` applied) -/

open Module Module.End

/-- **Joint eigenspace decomposition.**

`EuclideanSpace ℂ (Fin n)` decomposes as an internal direct sum of
joint eigenspaces of `pinch_sym P ρ` and all `proj_sym P k`, indexed
by joint-eigenvalue tuples `α : Option (Fin m) → ℂ`.  Direct corollary
of Mathlib's `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`
applied to `opFamily`.

NOTE: the actual Mathlib name is double-prefixed —
`LinearMap.IsSymmetric.LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`
— due to a quirk in the Mathlib declaration (theorem inside
`namespace LinearMap.IsSymmetric` re-declared with the full path). -/
theorem joint_isInternal (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    DirectSum.IsInternal
      (fun α : Option (Fin m) → ℂ ↦
        ⨅ j, eigenspace (opFamily P ρ j) (α j)) := by
  classical
  exact LinearMap.IsSymmetric.LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    (opFamily_isSymmetric P ρ) (opFamily_pairwise_commute P ρ)

/-- The orthogonal-family witness for the joint eigenspaces of `opFamily`. -/
theorem joint_orthogonalFamily (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    OrthogonalFamily ℂ
      (fun α : Option (Fin m) → ℂ ↦
        (⨅ j, eigenspace (opFamily P ρ j) (α j) : Submodule ℂ _))
      (fun α : Option (Fin m) → ℂ ↦
        (⨅ j, eigenspace (opFamily P ρ j) (α j)).subtypeₗᵢ) :=
  LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (opFamily_isSymmetric P ρ)

/-! ### Phase 17 — Projector-induced direct sum (Fin m-indexed)

The 1-eigenspaces of `proj_sym P k` give a `Fin m`-indexed direct sum
decomposition of `EuclideanSpace ℂ (Fin n)`.  Unlike `joint_isInternal`
(indexed by the infinite function-type `Option (Fin m) → ℂ`), this
decomposition is over the *finite* index `Fin m`, avoiding the Fintype
obstruction that blocks `subordinateOrthonormalBasis`.

Each `proj_sym P k` is an orthogonal projection (Hermitian + idempotent
via `P.isHermitian`, `P.idem`), so its 1-eigenspace equals its range;
distinct ranges are orthogonal (from `P.ortho`), and they span E
(from `P.sum_eq_one`). -/

/-- The 1-eigenspace of `proj_sym P k`. -/
noncomputable def projSubmodule (P : ProjectorFamily n m) (k : Fin m) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  eigenspace (proj_sym P k) 1

/-- A vector lies in `projSubmodule P k` iff it is fixed by `proj_sym P k`. -/
theorem mem_projSubmodule_iff {P : ProjectorFamily n m} {k : Fin m}
    {v : EuclideanSpace ℂ (Fin n)} :
    v ∈ projSubmodule P k ↔ proj_sym P k v = v := by
  unfold projSubmodule
  rw [mem_eigenspace_iff, one_smul]

/-- Distinct projectors compose to zero as `Module.End`, lifting `P.ortho`
through the algebra equiv `Matrix.toLpLinAlgEquiv 2`. -/
theorem proj_sym_mul_eq_zero_of_ne (P : ProjectorFamily n m)
    {k l : Fin m} (hkl : k ≠ l) :
    proj_sym P k * proj_sym P l = 0 := by
  change Matrix.toLpLinAlgEquiv (n := Fin n) 2 (P.proj k) *
       Matrix.toLpLinAlgEquiv (n := Fin n) 2 (P.proj l) = 0
  rw [← map_mul, P.ortho k l hkl, map_zero]

/-- If `v ∈ projSubmodule P k`, then `proj_sym P l v = 0` for every `l ≠ k`. -/
theorem proj_sym_apply_zero_of_mem {P : ProjectorFamily n m}
    {k l : Fin m} (hkl : k ≠ l)
    {v : EuclideanSpace ℂ (Fin n)} (hv : v ∈ projSubmodule P k) :
    proj_sym P l v = 0 := by
  have h1 : proj_sym P k v = v := mem_projSubmodule_iff.mp hv
  have h2 : proj_sym P l v = (proj_sym P l * proj_sym P k) v := by
    rw [Module.End.mul_apply, h1]
  rw [h2, proj_sym_mul_eq_zero_of_ne P (Ne.symm hkl)]
  rfl

/-- **Projector submodules form an orthogonal family.** -/
theorem projSubmodule_orthogonalFamily (P : ProjectorFamily n m) :
    OrthogonalFamily ℂ (fun k ↦ (projSubmodule P k : Submodule ℂ _))
        (fun k ↦ (projSubmodule P k).subtypeₗᵢ) := by
  intro k l hkl v w
  have h_sym := proj_sym_isSymmetric P l v.val w.val
  have h_w : proj_sym P l w.val = w.val :=
    mem_projSubmodule_iff.mp w.property
  have h_v_zero : proj_sym P l v.val = 0 :=
    proj_sym_apply_zero_of_mem hkl v.property
  change inner ℂ v.val w.val = 0
  rw [← h_w, ← h_sym, h_v_zero, inner_zero_left]

/-! ### Idempotence + spanning, for the `IsInternal` step -/

/-- Each `proj_sym P k` is idempotent (lifted from `P.idem`). -/
theorem proj_sym_idem (P : ProjectorFamily n m) (k : Fin m) :
    proj_sym P k * proj_sym P k = proj_sym P k := by
  change Matrix.toLpLinAlgEquiv (n := Fin n) 2 (P.proj k) *
         Matrix.toLpLinAlgEquiv (n := Fin n) 2 (P.proj k) =
         Matrix.toLpLinAlgEquiv (n := Fin n) 2 (P.proj k)
  rw [← map_mul, P.idem k]

/-- `proj_sym P k v` always lies in `projSubmodule P k`. -/
theorem proj_sym_apply_mem (P : ProjectorFamily n m) (k : Fin m)
    (v : EuclideanSpace ℂ (Fin n)) :
    proj_sym P k v ∈ projSubmodule P k := by
  rw [mem_projSubmodule_iff, ← Module.End.mul_apply, proj_sym_idem]

/-- The sum of all `proj_sym P k` is the identity `Module.End`,
lifted from `P.sum_eq_one`. -/
theorem sum_proj_sym_eq_one (P : ProjectorFamily n m) :
    ∑ k, proj_sym P k = (1 : Module.End ℂ (EuclideanSpace ℂ (Fin n))) := by
  change ∑ k, Matrix.toLpLinAlgEquiv (n := Fin n) 2 (P.proj k) = 1
  rw [← map_sum, P.sum_eq_one, map_one]

/-- **Projector submodules span E.** -/
theorem projSubmodule_iSup_eq_top (P : ProjectorFamily n m) :
    ⨆ k, projSubmodule P k = ⊤ := by
  rw [eq_top_iff]
  intro v _
  -- v = (∑ k, proj_sym k) v = ∑ k, proj_sym k v, each in projSubmodule k.
  have h_sum_id : ∑ k, proj_sym P k v = v := by
    rw [← LinearMap.sum_apply, sum_proj_sym_eq_one P, Module.End.one_apply]
  rw [← h_sum_id]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  exact Submodule.mem_iSup_of_mem k (proj_sym_apply_mem P k v)

/-- **Projector-induced direct sum decomposition.**

`EuclideanSpace ℂ (Fin n)` is the internal direct sum of the
1-eigenspaces of the projectors `proj_sym P k`, indexed by `Fin m`.
This is the *finite-index* decomposition that sidesteps the Fintype
obstruction in `joint_isInternal`. -/
theorem projSubmodule_isInternal (P : ProjectorFamily n m) :
    DirectSum.IsInternal (projSubmodule P) := by
  classical
  rw [(projSubmodule_orthogonalFamily P).isInternal_iff]
  rw [projSubmodule_iSup_eq_top, Submodule.top_orthogonal_eq_bot]

/-! ### `pinch_sym` preserves each `projSubmodule` -/

/-- **`pinch_sym P ρ` preserves each `projSubmodule P k`.**

If `v ∈ projSubmodule P k`, then `pinch_sym P ρ v ∈ projSubmodule P k`,
because `pinch_sym` commutes with each `proj_sym` (= `pinch_proj_commute`).

This is the key invariance fact needed to refine the projector-induced
direct sum into an *adapted* eigenbasis for `pinch_sym`: restrict
`pinch_sym P ρ` to each `projSubmodule P k`, apply Mathlib's
single-operator spectral theorem to each restriction, and collect
the resulting bases. -/
theorem pinch_sym_mapsTo_projSubmodule (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (k : Fin m)
    {v : EuclideanSpace ℂ (Fin n)} (hv : v ∈ projSubmodule P k) :
    pinch_sym P ρ v ∈ projSubmodule P k := by
  have h_v_fixed : proj_sym P k v = v := mem_projSubmodule_iff.mp hv
  rw [mem_projSubmodule_iff]
  -- Goal: proj_sym P k (pinch_sym P ρ v) = pinch_sym P ρ v
  -- Use Commute.eq: proj_sym k ∘ pinch_sym = pinch_sym ∘ proj_sym k.
  have h_comm : proj_sym P k * pinch_sym P ρ = pinch_sym P ρ * proj_sym P k :=
    (pinch_proj_commute P ρ k).symm
  calc proj_sym P k (pinch_sym P ρ v)
      = (proj_sym P k * pinch_sym P ρ) v := by rw [Module.End.mul_apply]
    _ = (pinch_sym P ρ * proj_sym P k) v := by rw [h_comm]
    _ = pinch_sym P ρ (proj_sym P k v) := by rw [Module.End.mul_apply]
    _ = pinch_sym P ρ v := by rw [h_v_fixed]

/-! ### Phase 18 — Restricted `pinch_sym` + per-cell eigenbasis

With `projSubmodule_isInternal` (`Fin m`-indexed `IsInternal`) and
`pinch_sym_mapsTo_projSubmodule` (invariance) in hand, we restrict
`pinch_sym P ρ` to each `projSubmodule P k` (symmetric on that
subspace by `restrict_invariant`) and apply Mathlib's
`LinearMap.IsSymmetric.eigenvectorBasis` per cell.  Each per-cell
basis vector is automatically adapted — it lies in its
`projSubmodule P k` by construction. -/

/-- Restriction of `pinch_sym P ρ` to a `projSubmodule P k`. -/
noncomputable def pinch_sym_restrict (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (k : Fin m) :
    Module.End ℂ (projSubmodule P k) :=
  (pinch_sym P ρ).restrict
    (fun _ hv => pinch_sym_mapsTo_projSubmodule P ρ k hv)

/-- The restriction inherits symmetry from `pinch_sym`. -/
theorem pinch_sym_restrict_isSymmetric (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (k : Fin m) :
    (pinch_sym_restrict P ρ k).IsSymmetric :=
  (pinch_sym_isSymmetric P ρ).restrict_invariant _

/-- Per-cell ONB of pinch-`sym` eigenvectors within `projSubmodule P k`,
sorted by Mathlib's eigenvalue convention. -/
noncomputable def cellBasis (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (k : Fin m) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (projSubmodule P k))) ℂ (projSubmodule P k) :=
  (pinch_sym_restrict_isSymmetric P ρ k).eigenvectorBasis rfl

/-- Per-cell pinch-`sym` eigenvalues (sorted descending, real-valued). -/
noncomputable def cellEigenvalues (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (k : Fin m) :
    Fin (Module.finrank ℂ (projSubmodule P k)) → ℝ :=
  (pinch_sym_restrict_isSymmetric P ρ k).eigenvalues rfl

/-- **Adaptation**: each cellBasis vector lies in its `projSubmodule`
(hence `proj_sym P k` fixes it). -/
theorem cellBasis_adapted (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (k : Fin m) (i : Fin (Module.finrank ℂ (projSubmodule P k))) :
    proj_sym P k ((cellBasis P ρ k i : EuclideanSpace ℂ (Fin n))) =
      ((cellBasis P ρ k i : EuclideanSpace ℂ (Fin n))) :=
  mem_projSubmodule_iff.mp (cellBasis P ρ k i).property

/-- **Eigenvector property**: each cellBasis vector is a pinch-`sym`
eigenvector with eigenvalue `cellEigenvalues P ρ k i`. -/
theorem cellBasis_apply_pinch_sym (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (k : Fin m) (i : Fin (Module.finrank ℂ (projSubmodule P k))) :
    pinch_sym P ρ ((cellBasis P ρ k i : EuclideanSpace ℂ (Fin n))) =
      (cellEigenvalues P ρ k i : ℂ) •
        ((cellBasis P ρ k i : EuclideanSpace ℂ (Fin n))) := by
  -- Mathlib's per-cell eigenvector equation lives in the submodule:
  -- pinch_sym_restrict (cellBasis i) = (cellEigenvalues i : ℂ) • cellBasis i
  have h := (pinch_sym_restrict_isSymmetric P ρ k).apply_eigenvectorBasis rfl i
  -- Push to the ambient space by taking `Subtype.val` of both sides.
  have h_val : ((pinch_sym_restrict P ρ k (cellBasis P ρ k i) :
                  projSubmodule P k) : EuclideanSpace ℂ (Fin n)) =
               (((cellEigenvalues P ρ k i : ℂ) • cellBasis P ρ k i :
                  projSubmodule P k) : EuclideanSpace ℂ (Fin n)) := by
    exact congrArg Subtype.val h
  -- Unfold LHS via `restrict_coe_apply`, RHS via `Submodule.coe_smul`.
  unfold pinch_sym_restrict at h_val
  rw [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h_val
  exact h_val

/-! ### Phase 19 — Collected adapted ONB on E (Fin n-indexed) -/

/-- The collected ONB on E built from per-cell pinch-eigenvector bases,
indexed by `Σ k, Fin (finrank (projSubmodule P k))`.

By Mathlib's `IsInternal.collectedOrthonormalBasis`, the value at `⟨k, j⟩`
is the embedding of `cellBasis P ρ k j` into the ambient space. -/
noncomputable def collectedAdaptedBasis (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    OrthonormalBasis (Σ k, Fin (Module.finrank ℂ (projSubmodule P k))) ℂ
      (EuclideanSpace ℂ (Fin n)) := by
  classical
  exact (projSubmodule_isInternal P).collectedOrthonormalBasis
    (projSubmodule_orthogonalFamily P) (cellBasis P ρ)

/-- The cardinality-match equivalence `(Σ k, Fin (finrank (projSubmodule P k))) ≃ Fin n`,
provided by Mathlib via `sigmaOrthonormalBasisIndexEquiv` (the sum of cell
dimensions equals `n` because the cells form an internal direct sum).

Depends only on the projector family (not on `ρ`), since
`sigmaOrthonormalBasisIndexEquiv` uses `stdOrthonormalBasis` internally
and the cardinality is invariant of choice. -/
noncomputable def adaptedBasisIndexEquiv (P : ProjectorFamily n m) :
    (Σ k, Fin (Module.finrank ℂ (projSubmodule P k))) ≃ Fin n := by
  classical
  exact (projSubmodule_isInternal P).sigmaOrthonormalBasisIndexEquiv
    finrank_euclideanSpace_fin (projSubmodule_orthogonalFamily P)

/-- **The adapted orthonormal basis of `EuclideanSpace ℂ (Fin n)`** —
indexed by `Fin n`, every vector lies in some `projSubmodule P k`
(adaptation) and is a pinch-sym eigenvector. -/
noncomputable def adaptedBasis (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  (collectedAdaptedBasis P ρ).reindex (adaptedBasisIndexEquiv P)

/-- For each `s : Fin n`, the projector cell containing `adaptedBasis P ρ s`. -/
noncomputable def k_of (P : ProjectorFamily n m) (s : Fin n) : Fin m :=
  ((adaptedBasisIndexEquiv P).symm s).fst

/-- For each `s : Fin n`, the within-cell index of `adaptedBasis P ρ s`. -/
noncomputable def cellIdx_of (P : ProjectorFamily n m)
    (s : Fin n) : Fin (Module.finrank ℂ (projSubmodule P (k_of P s))) :=
  ((adaptedBasisIndexEquiv P).symm s).snd

/-- For each `s : Fin n`, the pinch eigenvalue at `adaptedBasis P ρ s`. -/
noncomputable def mu (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (s : Fin n) : ℝ :=
  cellEigenvalues P ρ (k_of P s) (cellIdx_of P s)

/-! ### Relating `adaptedBasis` to `cellBasis` -/

/-- **Decoded coordinate**: `adaptedBasis P ρ s` is the embedded image
of `cellBasis P ρ (k_of s) (cellIdx_of s)`. -/
theorem adaptedBasis_eq_cellBasis (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    (adaptedBasis P ρ s : EuclideanSpace ℂ (Fin n)) =
      ((cellBasis P ρ (k_of P s) (cellIdx_of P s)) :
        EuclideanSpace ℂ (Fin n)) := by
  classical
  unfold adaptedBasis collectedAdaptedBasis k_of cellIdx_of
  rw [OrthonormalBasis.reindex_apply]
  unfold DirectSum.IsInternal.collectedOrthonormalBasis
  rw [Module.Basis.coe_toOrthonormalBasis,
      DirectSum.IsInternal.collectedBasis_coe]
  rfl

/-- **Adaptation of `adaptedBasis`**: each `adaptedBasis P ρ s` is fixed
by `proj_sym P (k_of s)` (which transfers to `P.proj (k_of s) *ᵥ _ = _`
when interpreted at the matrix level). -/
theorem adaptedBasis_adapted (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    proj_sym P (k_of P s) ((adaptedBasis P ρ s : EuclideanSpace ℂ (Fin n))) =
      ((adaptedBasis P ρ s : EuclideanSpace ℂ (Fin n))) := by
  rw [adaptedBasis_eq_cellBasis]
  exact cellBasis_adapted P ρ (k_of P s) (cellIdx_of P s)

/-- **Pinch-eigenvector property of `adaptedBasis`**: each
`adaptedBasis P ρ s` is a `pinch_sym P ρ` eigenvector with
eigenvalue `mu P ρ s`. -/
theorem adaptedBasis_eigenvector_pinch_sym (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    pinch_sym P ρ ((adaptedBasis P ρ s : EuclideanSpace ℂ (Fin n))) =
      (mu P ρ s : ℂ) •
        ((adaptedBasis P ρ s : EuclideanSpace ℂ (Fin n))) := by
  rw [adaptedBasis_eq_cellBasis]
  unfold mu
  exact cellBasis_apply_pinch_sym P ρ (k_of P s) (cellIdx_of P s)

/-! ### Matrix-level (mulVec) form, matching `Lemma3bEig_of_adapted_custom` -/

/-- **Matrix-level adaptation**: `P.proj (k_of s) *ᵥ ⇑(adaptedBasis s) = ⇑(adaptedBasis s)`. -/
theorem adaptedBasis_adapted_mulVec (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    P.proj (k_of P s) *ᵥ ⇑(adaptedBasis P ρ s) = ⇑(adaptedBasis P ρ s) := by
  have h := adaptedBasis_adapted P ρ s
  -- h : proj_sym P (k_of P s) (adaptedBasis P ρ s) = adaptedBasis P ρ s
  -- Push to coordinate-vector form via `ofLp`.
  have h_val := congrArg
    (fun v : EuclideanSpace ℂ (Fin n) => (v : Fin n → ℂ)) h
  -- Unfold proj_sym = (P.proj k).toEuclideanLin and use ofLp_toLpLin.
  simpa [proj_sym, Matrix.toLin'_apply] using h_val

/-- **Matrix-level eigenvalue equation**:
`(pinchDensityOp P ρ).M *ᵥ ⇑(adaptedBasis s) = (mu s : ℂ) • ⇑(adaptedBasis s)`. -/
theorem adaptedBasis_eigenvector_pinch_mulVec (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (s : Fin n) :
    (pinchDensityOp P ρ).M *ᵥ ⇑(adaptedBasis P ρ s) =
      (mu P ρ s : ℂ) • (⇑(adaptedBasis P ρ s) : Fin n → ℂ) := by
  have h := adaptedBasis_eigenvector_pinch_sym P ρ s
  -- h : pinch_sym P ρ (adaptedBasis P ρ s) = (mu : ℂ) • adaptedBasis P ρ s
  have h_val := congrArg
    (fun v : EuclideanSpace ℂ (Fin n) => (v : Fin n → ℂ)) h
  -- Unfold pinch_sym = .toEuclideanLin and ofLp on smul.
  simpa [pinch_sym, Matrix.toLin'_apply] using h_val

/-! ### Composition: `Lemma3bEig P ρ` modulo entropy uniqueness -/

/-- **Joint diagonalization closes `Lemma3bEig P ρ`**, modulo a single
hypothesis: that the custom eigenvalues `mu` agree with Mathlib's
canonical eigenvalues of `pinchDensityOp P ρ` in the entropy sense.

`h_entropy` is the *spectral-uniqueness* condition — for any Hermitian
matrix and any orthonormal eigenbasis, `∑ negMulLog (custom λ)` equals
the von-Neumann entropy.  This is a separate matrix-theoretic fact
(provable from functional-calculus / characteristic-polynomial uniqueness),
left as a hypothesis here. -/
theorem vct_lemma_3_joint
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n)
    (h_entropy : MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ)
                   = ∑ s, Real.negMulLog (mu P ρ s)) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ) :=
  MacadayPhysicsLean.Pinching.vct_lemma_3_of_adapted_custom P ρ
    (adaptedBasis P ρ) (mu P ρ) (k_of P)
    (adaptedBasis_eigenvector_pinch_mulVec P ρ)
    (adaptedBasis_adapted_mulVec P ρ)
    h_entropy

/-! ### Phase 20 — Unitary diagonalization for the custom basis

To close the entropy hypothesis we need to show that
`(pinchDensityOp P ρ).M.charpoly = ∏ s, (X - mu P ρ s : ℂ)`,
yielding multiset equality of `mu` and Mathlib's eigenvalues
(both are the multiset of roots of the charpoly).  The standard
way to prove this is the unitary diagonalization
`M = U · diag(↑μ) · U*` for `U` built from `adaptedBasis`. -/

open Unitary Matrix

/-- The unitary matrix whose columns are the adapted basis vectors. -/
noncomputable def adaptedUnitary (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  exact ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix
          (adaptedBasis P ρ).toBasis,
        (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary
          (adaptedBasis P ρ)⟩

/-- Apply: the `(i, j)` entry of `adaptedUnitary` is the `i`-th
coordinate of the `j`-th adapted basis vector. -/
@[simp]
theorem adaptedUnitary_apply (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (i j : Fin n) :
    (adaptedUnitary P ρ : Matrix (Fin n) (Fin n) ℂ) i j =
      ⇑(adaptedBasis P ρ j) i :=
  rfl

/-- The `j`-th column of `adaptedUnitary` is the `j`-th adapted basis vector. -/
@[simp]
theorem adaptedUnitary_col_eq (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (j : Fin n) :
    Matrix.col (adaptedUnitary P ρ) j = ⇑(adaptedBasis P ρ j) :=
  rfl

/-- `adaptedUnitary *ᵥ Pi.single j 1 = ⇑(adaptedBasis P ρ j)`. -/
theorem adaptedUnitary_mulVec (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (j : Fin n) :
    (adaptedUnitary P ρ : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single j 1 =
      ⇑(adaptedBasis P ρ j) := by
  simp_rw [Matrix.mulVec_single_one, adaptedUnitary_col_eq]

/-- `(star adaptedUnitary) *ᵥ ⇑(adaptedBasis P ρ j) = Pi.single j 1`. -/
theorem star_adaptedUnitary_mulVec (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) (j : Fin n) :
    (star (adaptedUnitary P ρ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ
      ⇑(adaptedBasis P ρ j) = Pi.single j 1 := by
  rw [← adaptedUnitary_mulVec, Matrix.mulVec_mulVec,
      Unitary.coe_star_mul_self, Matrix.one_mulVec]

/-- **Unitary diagonalization** (one half): conjugating `(pinchDensityOp P ρ).M`
by `star adaptedUnitary` gives a diagonal matrix with entries `↑(mu P ρ s)`. -/
theorem conjStarAlgAut_star_adaptedUnitary (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    conjStarAlgAut ℂ _ (star (adaptedUnitary P ρ)) (pinchDensityOp P ρ).M =
      Matrix.diagonal (RCLike.ofReal ∘ mu P ρ) := by
  apply Matrix.toEuclideanLin.injective <|
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.ext fun i ↦ ?_
  simp only [conjStarAlgAut_star_apply, Matrix.toLpLin_apply,
    OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← Matrix.mulVec_mulVec,
    adaptedUnitary_mulVec, adaptedBasis_eigenvector_pinch_mulVec,
    Matrix.diagonal_mulVec_single, Matrix.mulVec_smul,
    star_adaptedUnitary_mulVec, WithLp.toLp_smul, PiLp.toLp_single,
    Function.comp_apply, mul_one]
  apply PiLp.ext fun j ↦ ?_
  by_cases hji : j = i
  · simp only [hji, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, if_true,
      mul_one]
    rfl
  · simp [hji]

/-- **Spectral theorem for the custom adapted basis**:
`M = adaptedUnitary · diag(↑μ) · star adaptedUnitary`. -/
theorem spectral_theorem_adapted (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    (pinchDensityOp P ρ).M =
      conjStarAlgAut ℂ _ (adaptedUnitary P ρ)
        (Matrix.diagonal (RCLike.ofReal ∘ mu P ρ)) := by
  rw [← conjStarAlgAut_star_adaptedUnitary, ← conjStarAlgAut_mul_apply]
  simp

/-! ### Charpoly factorization and multiset equality -/

open Polynomial in
/-- **Charpoly factorization via the custom basis**:
`M.charpoly = ∏ s, (X - C (mu P ρ s : ℂ))`. -/
theorem charpoly_eq_mu (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    (pinchDensityOp P ρ).M.charpoly = ∏ s, (X - C ((mu P ρ s : ℂ))) := by
  conv_lhs => rw [spectral_theorem_adapted, conjStarAlgAut_apply,
    Matrix.charpoly_mul_comm, ← mul_assoc]
  simp [Matrix.charpoly_diagonal]

/-- **Multiset equality (over ℂ)**: the multiset of `↑(mu P ρ s)` (as ℂ)
equals the multiset of charpoly roots, equals the multiset of Mathlib's
canonical eigenvalues (as ℂ). -/
theorem multiset_mu_eq_eigenvalues_complex (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    Multiset.map (fun s => ((mu P ρ s : ℝ) : ℂ))
        (Finset.univ : Finset (Fin n)).val =
      Multiset.map (fun i => ((pinchDensityOp P ρ).isHermitian.eigenvalues i : ℂ))
        (Finset.univ : Finset (Fin n)).val := by
  -- Both equal M.charpoly.roots.
  have h1 : (pinchDensityOp P ρ).M.charpoly.roots =
            Multiset.map (fun s => ((mu P ρ s : ℝ) : ℂ))
              (Finset.univ : Finset (Fin n)).val := by
    rw [charpoly_eq_mu]
    rw [Polynomial.roots_prod
          (fun s => Polynomial.X - Polynomial.C ((mu P ρ s : ℝ) : ℂ))
          Finset.univ
          (Finset.prod_ne_zero_iff.mpr
            (fun _ _ ↦ Polynomial.X_sub_C_ne_zero _))]
    simp [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have h2 := (pinchDensityOp P ρ).isHermitian.roots_charpoly_eq_eigenvalues
  rw [h2] at h1
  exact h1.symm

/-- **Multiset equality (over ℝ)** via `RCLike.ofReal` injectivity. -/
theorem multiset_mu_eq_eigenvalues (P : ProjectorFamily n m)
    (ρ : MacadayPhysicsLean.DensityOp n) :
    Multiset.map (mu P ρ) (Finset.univ : Finset (Fin n)).val =
      Multiset.map ((pinchDensityOp P ρ).isHermitian.eigenvalues)
        (Finset.univ : Finset (Fin n)).val := by
  apply Multiset.map_injective Complex.ofReal_injective
  rw [Multiset.map_map, Multiset.map_map]
  exact multiset_mu_eq_eigenvalues_complex P ρ

/-! ### Sum equality and final discharge -/

/-- **Sum invariance**: for any function `f : ℝ → ℝ`,
`∑ s, f (mu P ρ s) = ∑ i, f ((pinchDensityOp P ρ).isHermitian.eigenvalues i)`. -/
theorem sum_eq_of_multiset_mu_eq_eigenvalues
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) (f : ℝ → ℝ) :
    ∑ s, f (mu P ρ s) =
      ∑ i, f ((pinchDensityOp P ρ).isHermitian.eigenvalues i) := by
  have h := multiset_mu_eq_eigenvalues P ρ
  -- Compare via Multiset.map and .sum.
  have h_lhs : ∑ s, f (mu P ρ s)
              = (Multiset.map f
                  (Multiset.map (mu P ρ) (Finset.univ : Finset (Fin n)).val)).sum := by
    rw [Multiset.map_map]; rfl
  have h_rhs : ∑ i, f ((pinchDensityOp P ρ).isHermitian.eigenvalues i)
              = (Multiset.map f
                  (Multiset.map ((pinchDensityOp P ρ).isHermitian.eigenvalues)
                    (Finset.univ : Finset (Fin n)).val)).sum := by
    rw [Multiset.map_map]; rfl
  rw [h_lhs, h_rhs, h]

/-- **Entropy equation**: the sum of `negMulLog (mu P ρ s)` equals the
von-Neumann entropy of the pinched state.  This is the missing hypothesis
in `vct_lemma_3_joint`. -/
theorem vonNeumannEntropy_pinched_eq_sum_negMulLog_mu
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ) =
      ∑ s, Real.negMulLog (mu P ρ s) := by
  unfold MacadayPhysicsLean.DensityOp.vonNeumannEntropy MacadayPhysicsLean.DensityOp.eigenvalues
  exact (sum_eq_of_multiset_mu_eq_eigenvalues P ρ Real.negMulLog).symm

/-- **VCT Lemma 3 — UNCONDITIONAL.**

The entropy of a density operator is at most the entropy of its
pinched form.  All hypotheses of `vct_lemma_3_joint` are now
discharged via the joint diagonalization framework. -/
theorem vct_lemma_3_unconditional
    (P : ProjectorFamily n m) (ρ : MacadayPhysicsLean.DensityOp n) :
    MacadayPhysicsLean.DensityOp.vonNeumannEntropy ρ
      ≤ MacadayPhysicsLean.DensityOp.vonNeumannEntropy (pinchDensityOp P ρ) :=
  vct_lemma_3_joint P ρ
    (vonNeumannEntropy_pinched_eq_sum_negMulLog_mu P ρ)

end MacadayPhysicsLean.JointDiagonalization
