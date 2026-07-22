/-
E₈ root system (Paper YH, Paper B prerequisite).

The 240 minimal vectors of the E₈ lattice in two families:

* **Integer type** (112 roots): two coordinates are `±1`, the
  remaining six are `0`.  C(8,2)·2² = 28·4 = 112.
* **Half-integer type** (128 roots): all eight coordinates are
  `±½`, with an even number of minus signs.  2⁷ = 128.

Every root has squared norm 2.  Total: 112 + 128 = 240.

**Representation.**  To stay in `ℤ` (and let `native_decide` carry
the arithmetic), we work in *twice-scaled* coordinates:
integer-type roots become `±2` at two positions; half-integer-type
roots become `±1` at every position.  The physical squared norm
`‖r‖² = 2` corresponds to `∑ vᵢ² = 8` in these coordinates.

All theorems below compile via `native_decide` on small `Fintype`
exhaustions; the style linter complains about `native_decide`
relying on the compiler in addition to the kernel, but the
propositions here are concrete numerical equalities over small
finite types, so the use is appropriate.
-/

import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MacadayPhysicsLean.E8Roots

/-! ### Indexing types for the two root families -/

/-- Index for an integer-type E₈ root: an ordered pair of distinct
positions `(i, j)` with `i < j`, plus two sign bits.  Cardinality
`C(8,2) · 2² = 28 · 4 = 112`. -/
abbrev IntIdx : Type :=
  { p : Fin 8 × Fin 8 // p.1 < p.2 } × Bool × Bool

/-- Index for a half-integer-type E₈ root: a sign vector
`s : Fin 8 → Bool` with an even number of "false" entries
(an even number of minus signs).  Cardinality `2⁷ = 128`. -/
abbrev HalfIdx : Type :=
  { s : Fin 8 → Bool // (Finset.univ.filter (fun k => s k = false)).card % 2 = 0 }

theorem int_idx_card : Fintype.card IntIdx = 112 := by native_decide

theorem half_idx_card : Fintype.card HalfIdx = 128 := by native_decide

/-! ### Vector embeddings into `Fin 8 → ℤ` (2×-scaled) -/

/-- Build the integer-type root vector from its index. -/
def fromInt (idx : IntIdx) : Fin 8 → ℤ := fun k =>
  let i := idx.1.val.1
  let j := idx.1.val.2
  if k = i then (if idx.2.1 then 2 else -2)
  else if k = j then (if idx.2.2 then 2 else -2)
  else 0

/-- Build the half-integer-type root vector from its index. -/
def fromHalf (idx : HalfIdx) : Fin 8 → ℤ :=
  fun k => if idx.val k then 1 else -1

/-! ### Squared-norm theorems -/

/-- Every integer-type root has squared norm 8. -/
theorem fromInt_norm_sq (idx : IntIdx) :
    ∑ k, (fromInt idx k) ^ 2 = 8 := by
  revert idx; native_decide

/-- Every half-integer-type root has squared norm 8. -/
theorem fromHalf_norm_sq (idx : HalfIdx) :
    ∑ k, (fromHalf idx k) ^ 2 = 8 := by
  revert idx; native_decide

/-! ### Injectivity and disjointness -/

theorem fromInt_inj : Function.Injective fromInt := by
  intro a b h
  revert a b h; native_decide

theorem fromHalf_inj : Function.Injective fromHalf := by
  intro a b h
  revert a b h; native_decide

theorem fromInt_ne_fromHalf :
    ∀ (a : IntIdx) (b : HalfIdx), fromInt a ≠ fromHalf b := by
  native_decide

/-! ### The 240-element root set -/

/-- The 240 E₈ roots in 2×-scaled integer coordinates. -/
def rootSet : Finset (Fin 8 → ℤ) :=
  Finset.univ.image fromInt ∪ Finset.univ.image fromHalf

/-- The image of `fromInt` has cardinality 112. -/
theorem int_image_card :
    (Finset.univ.image fromInt).card = 112 := by
  rw [Finset.card_image_of_injective _ fromInt_inj, Finset.card_univ, int_idx_card]

/-- The image of `fromHalf` has cardinality 128. -/
theorem half_image_card :
    (Finset.univ.image fromHalf).card = 128 := by
  rw [Finset.card_image_of_injective _ fromHalf_inj, Finset.card_univ, half_idx_card]

/-- The two image families are disjoint. -/
theorem images_disjoint :
    Disjoint (Finset.univ.image fromInt) (Finset.univ.image fromHalf) := by
  rw [Finset.disjoint_left]
  intro v hI hH
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hH
  exact fromInt_ne_fromHalf a b hb.symm

/-- **The E₈ root system has 240 elements.** -/
theorem rootSet_card : rootSet.card = 240 := by
  unfold rootSet
  rw [Finset.card_union_of_disjoint images_disjoint, int_image_card, half_image_card]

/-- **Every E₈ root has squared norm 8** (in 2×-scaled integer coords;
equivalently `‖r‖² = 2` in physical coords). -/
theorem rootSet_norm_sq (v : Fin 8 → ℤ) (hv : v ∈ rootSet) :
    ∑ k, (v k) ^ 2 = 8 := by
  rcases Finset.mem_union.mp hv with h | h
  · obtain ⟨idx, _, rfl⟩ := Finset.mem_image.mp h
    exact fromInt_norm_sq idx
  · obtain ⟨idx, _, rfl⟩ := Finset.mem_image.mp h
    exact fromHalf_norm_sq idx

end MacadayPhysicsLean.E8Roots
