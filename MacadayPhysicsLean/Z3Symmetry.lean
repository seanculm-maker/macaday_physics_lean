/-
A concrete order-3 symmetry σ of the E₈ root system (Paper F1
companion).

We take σ to be the cyclic permutation of the first three coordinates
(`(0, 1, 2) ↦ (1, 2, 0)`, identity on `{3, …, 7}`).  This is an
*honest* automorphism of the E₈ root system as a Finset of integer
8-tuples (both integer- and half-integer-type families are preserved
because both depend only on the *multiset* of coordinate values).

What we verify:

* **`sigma_root` is well-defined and `sigma_root³ = id`**.
* **`sigma_root` preserves `rootSet`** (sends roots to roots
  bijectively).
* **Exactly 72 roots are σ-fixed** — matching the F1 prediction
  `num_roots_fixed = 72` (defined in `Z3Branching.lean`).

Caveat: this σ is *not* identical to the F1 σ.  The full F1 ℤ₃
decomposition `240 = 72 + 84 + 84` refers to eigenspaces of an
*inner automorphism* of `E₈` (the conjugation by
`exp(2πi/3 · H)` for an A₂ Cartan element `H`), which acts as
*phases* on root spaces rather than as a permutation.  Under our
*permutation* σ, the 168 non-fixed roots split into 56 size-3 orbits,
contributing `56` to each of the ω- and ω̄-eigenspaces of σ on
`ℂ²⁴⁰` (plus another 56 to the 1-eigenspace from orbit-symmetric
combinations).  This gives 128 + 56 + 56 = 240, not 72 + 84 + 84.

The fixed-root count `72` does match F1 exactly, however — a
non-trivial structural coincidence.
-/

import MacadayPhysicsLean.E8Roots
import MacadayPhysicsLean.Z3Branching
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MacadayPhysicsLean.Z3Symmetry

open MacadayPhysicsLean.E8Roots

/-! ### The σ permutation on `Fin 8` -/

/-- σ permutes positions: `(0, 1, 2) ↦ (1, 2, 0)`, identity on
`{3, 4, 5, 6, 7}`. -/
def sigma : Fin 8 → Fin 8
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0
  | ⟨k+3, h⟩ => ⟨k+3, h⟩

/-- σ has order 3 as a function on `Fin 8`. -/
theorem sigma_cube : sigma ∘ sigma ∘ sigma = id := by
  funext i
  fin_cases i <;> rfl

/-! ### The induced action on root vectors -/

/-- σ acts on root vectors by *push-forward of coordinates*:
`(sigma_root v) k = v (sigma⁻¹ k)`.  Using our specific σ, this is
the cyclic rotation `v ↦ (v 2, v 0, v 1, v 3, v 4, v 5, v 6, v 7)`. -/
def sigma_root (v : Fin 8 → ℤ) : Fin 8 → ℤ
  | ⟨0, _⟩ => v 2
  | ⟨1, _⟩ => v 0
  | ⟨2, _⟩ => v 1
  | ⟨k+3, h⟩ => v ⟨k+3, h⟩

/-- `sigma_root` has order 3. -/
theorem sigma_root_cube (v : Fin 8 → ℤ) :
    sigma_root (sigma_root (sigma_root v)) = v := by
  funext i
  fin_cases i <;> rfl

/-! ### σ preserves the root families -/

/-- σ sends each integer-type root index to another (via index-level
permutation): if `idx : IntIdx` with positions `(i, j)` and signs
`(s₁, s₂)`, then `sigma_root (fromInt idx) = fromInt (σ idx)`
for some `σ` on `IntIdx`.  We don't need this directly; we just
verify that `sigma_root` maps `rootSet` into itself via native_decide
over the index types. -/
theorem sigma_root_preserves_int (idx : IntIdx) :
    sigma_root (fromInt idx) ∈ rootSet := by
  revert idx; native_decide

theorem sigma_root_preserves_half (idx : HalfIdx) :
    sigma_root (fromHalf idx) ∈ rootSet := by
  revert idx; native_decide

/-- **σ preserves `rootSet`.**  Combines the two family-level checks. -/
theorem sigma_root_preserves_rootSet :
    ∀ v ∈ rootSet, sigma_root v ∈ rootSet := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · obtain ⟨idx, _, rfl⟩ := Finset.mem_image.mp h
    exact sigma_root_preserves_int idx
  · obtain ⟨idx, _, rfl⟩ := Finset.mem_image.mp h
    exact sigma_root_preserves_half idx

/-! ### Counting σ-fixed roots: exactly 72 -/

/-- The σ-fixed subset of `rootSet`. -/
def fixedRoots : Finset (Fin 8 → ℤ) :=
  rootSet.filter (fun v => sigma_root v = v)

/-- **Exactly 72 E₈ roots are σ-fixed.**  Matches F1's
`num_roots_fixed = 72`. -/
theorem fixedRoots_card : fixedRoots.card = 72 := by
  unfold fixedRoots
  native_decide

/-- The 72 fixed roots match F1's `num_roots_fixed`. -/
theorem fixedRoots_card_eq_F1 :
    fixedRoots.card = MacadayPhysicsLean.Z3Branching.num_roots_fixed := by
  rw [fixedRoots_card]; rfl

/-! ### The TRUE inner-ℤ₃ phase action (Paper F1)

The F1 inner ℤ₃ is `Ad(exp(2πi/3 · H))` for an A₂ Cartan element
`H ∈ E₈`.  Acting on a root `α`, it multiplies the root space by the
phase `ω^{α · H}` (where `ω = exp(2πi/3)`).  The three eigenspaces
correspond to `α · H mod 3 ∈ {0, 1, 2}`.

**Key discovery.**  Taking `H = (1, 1, 1, 1, 1, 0, 0, 0)` (in our
2×-scaled coordinates, this is `α · H = sum of first 5 coords`), the
240 E₈ roots split as

  `240 = 72 + 84 + 84`

matching F1 exactly:

* `α · H ≡ 0 mod 3`: **72 roots** (the F1 `78 − 6` adjoint-minus-rank).
* `α · H ≡ 1 mod 3`: **84 roots** (one of the ω, ω̄ eigenspaces).
* `α · H ≡ 2 mod 3`: **84 roots** (the other).

This is the genuine inner-ℤ₃ phase decomposition — *not* a coordinate
permutation, but a *grading* of the root system into three "phases". -/

/-- The F1 Cartan vector `H = (1, 1, 1, 1, 1, 0, 0, 0)`. -/
def F1_Cartan : Fin 8 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => 0
  | ⟨7, _⟩ => 0

/-- The ℤ₃ phase of a root under the F1 inner-ℤ₃: `(α · H) mod 3`. -/
def F1_phase (v : Fin 8 → ℤ) : ℤ :=
  (∑ i, v i * F1_Cartan i) % 3

/-! ### The three F1 eigenspaces -/

/-- The 1-eigenspace (fixed roots): `α · H ≡ 0 mod 3`. -/
def F1_fixed : Finset (Fin 8 → ℤ) :=
  rootSet.filter (fun v => F1_phase v = 0)

/-- The ω-eigenspace: `α · H ≡ 1 mod 3`. -/
def F1_omega : Finset (Fin 8 → ℤ) :=
  rootSet.filter (fun v => F1_phase v = 1)

/-- The ω̄-eigenspace: `α · H ≡ 2 mod 3`. -/
def F1_omega_bar : Finset (Fin 8 → ℤ) :=
  rootSet.filter (fun v => F1_phase v = 2)

/-! ### The F1 splitting `240 = 72 + 84 + 84` -/

/-- **F1 inner-ℤ₃: 72 roots fixed.** -/
theorem F1_fixed_card : F1_fixed.card = 72 := by
  unfold F1_fixed F1_phase F1_Cartan
  native_decide

/-- **F1 inner-ℤ₃: 84 roots in the ω-eigenspace.** -/
theorem F1_omega_card : F1_omega.card = 84 := by
  unfold F1_omega F1_phase F1_Cartan
  native_decide

/-- **F1 inner-ℤ₃: 84 roots in the ω̄-eigenspace.** -/
theorem F1_omega_bar_card : F1_omega_bar.card = 84 := by
  unfold F1_omega_bar F1_phase F1_Cartan
  native_decide

/-- The three eigenspace cardinalities sum to 240. -/
theorem F1_splitting_sum :
    F1_fixed.card + F1_omega.card + F1_omega_bar.card = 240 := by
  rw [F1_fixed_card, F1_omega_card, F1_omega_bar_card]

/-- **The F1 splitting matches F1's `num_roots = 240 = 72 + 84 + 84`.** -/
theorem F1_splitting_eq_F1 :
    F1_fixed.card + F1_omega.card + F1_omega_bar.card
      = MacadayPhysicsLean.Z3Branching.num_roots_fixed
        + MacadayPhysicsLean.Z3Branching.num_roots_omega
        + MacadayPhysicsLean.Z3Branching.num_roots_omegaBar := by
  rw [F1_fixed_card, F1_omega_card, F1_omega_bar_card]
  rfl

/-- Each F1 eigenspace cardinality matches the F1 branching data. -/
theorem F1_fixed_card_eq_F1 :
    F1_fixed.card = MacadayPhysicsLean.Z3Branching.num_roots_fixed := by
  rw [F1_fixed_card]; rfl

theorem F1_omega_card_eq_F1 :
    F1_omega.card = MacadayPhysicsLean.Z3Branching.num_roots_omega := by
  rw [F1_omega_card]; rfl

theorem F1_omega_bar_card_eq_F1 :
    F1_omega_bar.card = MacadayPhysicsLean.Z3Branching.num_roots_omegaBar := by
  rw [F1_omega_bar_card]; rfl

end MacadayPhysicsLean.Z3Symmetry
