/-
ℤ₃ branching of E₈ (Paper F1).

E₈ has **no outer automorphisms**; it admits exactly **two**
conjugacy classes of order-3 *inner* automorphisms, and this file
records the arithmetic of both (Borel–de Siebenthal theory):

**Class A — fixed subalgebra `E₆ ⊕ A₂`** (dim 86).  The adjoint
`248` decomposes as

    248 = (78, 1) ⊕ (1, 8) ⊕ (27, 3) ⊕ (27̄, 3̄)

with dimensions `78 + 8 + 81 + 81 = 248`.  The 240 roots split
into σ-eigenspaces as

    240 = 78 + 81 + 81

(78 fixed roots = 72 E₆ roots + 6 A₂ roots; the 81-dimensional
ω- and ω̄-eigenspaces are the root spaces of `(27, 3)` and
`(27̄, 3̄)`).  The 8-dim E₈ Cartan lies in the fixed subalgebra
and splits `6 + 2 = 8` (E₆ Cartan ⊕ A₂ Cartan):
`8 + 78 = 86 = dim(E₆ ⊕ A₂)`.

**Class B — fixed subalgebra `su(9)`** (dim 80).  The adjoint
decomposes as

    248 = 80 ⊕ 84 ⊕ 84̄

(84 = Λ³ of the su(9) fundamental).  The 240 roots split as

    240 = 72 + 84 + 84

and the fixed sector is `8 + 72 = 80 = dim su(9)`.

**This file** proves the arithmetic identities of both classes:
component-dimension sums, root-count sums, Cartan split, and
fixed-sector reconstructions.  The explicit root-level gradings
realizing both classes (as phase decompositions of the concrete
`E8Roots.rootSet`) are constructed in `Z3Symmetry.lean`:
Class B via the Cartan vector `H = (1,1,1,1,1,0,0,0)`,
Class A via the mark-3 coweight `H′ = (0,0,0,0,0,1,1,2)`.
-/

import MacadayPhysicsLean.E8Roots
import Mathlib.Tactic

namespace MacadayPhysicsLean.Z3Branching

/-! ### Component dimensions of E₆, A₂ -/

/-- `dim(adjoint E₆) = 78`. -/
def dim_E6_adj : ℕ := 78
/-- `dim(adjoint A₂) = dim(su(3)) = 8`. -/
def dim_A2_adj : ℕ := 8
/-- `dim(fundamental 27 of E₆) = 27`. -/
def dim_E6_fund : ℕ := 27
/-- `dim(fundamental 3 of A₂) = 3`. -/
def dim_A2_fund : ℕ := 3

/-- Tensor-block dimension. -/
def dim_tensor (a b : ℕ) : ℕ := a * b

/-! ### Class A: the four branching components and their dimensions -/

/-- `(78, 1)` block: gauge bosons of `E₆ × A₂`-singlet sector. -/
def dim_block_78_1 : ℕ := dim_tensor dim_E6_adj 1
/-- `(1, 8)` block: hidden family-SU(3) gauge bosons. -/
def dim_block_1_8 : ℕ := dim_tensor 1 dim_A2_adj
/-- `(27, 3)` block: three generations of E₆ fundamental. -/
def dim_block_27_3 : ℕ := dim_tensor dim_E6_fund dim_A2_fund
/-- `(27̄, 3̄)` block: conjugate generations. -/
def dim_block_27b_3b : ℕ := dim_tensor dim_E6_fund dim_A2_fund

@[simp] theorem dim_block_78_1_eq : dim_block_78_1 = 78 := rfl
@[simp] theorem dim_block_1_8_eq : dim_block_1_8 = 8 := rfl
@[simp] theorem dim_block_27_3_eq : dim_block_27_3 = 81 := rfl
@[simp] theorem dim_block_27b_3b_eq : dim_block_27b_3b = 81 := rfl

/-! ### Class A: master dimension identity -/

/-- **F1 component-dimension identity (Class A).**  The four branching
components sum to `dim(E₈) = 248`. -/
theorem F1_dim_sum :
    dim_block_78_1 + dim_block_1_8 + dim_block_27_3 + dim_block_27b_3b = 248 := by
  decide

/-! ### Cartan data -/

/-- E₈ Cartan dimension (rank). -/
def dim_cartan_E8 : ℕ := 8
/-- E₆ Cartan dimension. -/
def dim_cartan_E6 : ℕ := 6
/-- A₂ Cartan dimension. -/
def dim_cartan_A2 : ℕ := 2

/-- **F1 Cartan-split identity (Class A).**  E₆ ⊕ A₂ Cartans = E₈ Cartan. -/
theorem F1_cartan_sum :
    dim_cartan_E6 + dim_cartan_A2 = dim_cartan_E8 := by decide

/-! ### Class B (su(9)): root + Cartan partition -/

/-- Class B: size of the σ-fixed root eigenspace (su(9) class). -/
def num_roots_fixed : ℕ := 72
/-- Class B: size of the σ-ω root eigenspace. -/
def num_roots_omega : ℕ := 84
/-- Class B: size of the σ-ω̄ root eigenspace. -/
def num_roots_omegaBar : ℕ := 84

/-- `dim su(9) = 80`. -/
def dim_su9 : ℕ := 80

/-- **F1 root-count identity (Class B).**  σ-eigenspace sizes sum to 240. -/
theorem F1_root_sum :
    num_roots_fixed + num_roots_omega + num_roots_omegaBar = 240 := by decide

/-- **Class B fixed-sector identity.**  E₈ Cartan (8) + 72 fixed
roots = 80 = dim su(9): the fixed subalgebra of the Class B inner
automorphism is `su(9)`, not `E₆ ⊕ A₂`. -/
theorem su9_fixed_sector :
    dim_cartan_E8 + num_roots_fixed = dim_su9 := by decide

/-- **Class B branching identity.**  `248 = 80 + 84 + 84̄`. -/
theorem su9_branching :
    dim_su9 + num_roots_omega + num_roots_omegaBar = 248 := by decide

/-! ### Class A (E₆ ⊕ A₂): root partition -/

/-- Class A: number of σ-fixed roots (72 E₆ roots + 6 A₂ roots). -/
def num_roots_fixed_E6A2 : ℕ := 78
/-- Class A: size of the ω root eigenspace (root spaces of `(27, 3)`). -/
def num_roots_omega_E6A2 : ℕ := 81
/-- Class A: size of the ω̄ root eigenspace (root spaces of `(27̄, 3̄)`). -/
def num_roots_omegaBar_E6A2 : ℕ := 81

/-- `dim(E₆ ⊕ A₂) = 86`. -/
def dim_E6A2 : ℕ := 86

/-- **Class A root-count identity.**  σ-eigenspace sizes sum to 240. -/
theorem E6A2_root_sum :
    num_roots_fixed_E6A2 + num_roots_omega_E6A2 + num_roots_omegaBar_E6A2 = 240 := by
  decide

/-- **Class A fixed-root decomposition.**  The 78 fixed roots are the
72 E₆ roots together with the 6 A₂ roots. -/
theorem E6A2_fixed_roots_decomp :
    num_roots_fixed_E6A2 = 72 + 6 := by decide

/-- **Class A fixed-sector identity.**  E₈ Cartan (8) + 78 fixed
roots = 86 = dim(E₆ ⊕ A₂) = 78 + 8. -/
theorem E6A2_fixed_sector :
    dim_cartan_E8 + num_roots_fixed_E6A2 = dim_E6A2 ∧
    dim_E6_adj + dim_A2_adj = dim_E6A2 := by
  constructor <;> decide

/-- **Class A eigenspace ↔ branching-block match.**  The ω- and
ω̄-eigenspace root counts equal the `(27, 3)` and `(27̄, 3̄)` block
dimensions. -/
theorem E6A2_root_spaces_match :
    num_roots_omega_E6A2 = dim_block_27_3 ∧
    num_roots_omegaBar_E6A2 = dim_block_27b_3b := by
  constructor <;> decide

/-! ### Class-independent identities -/

/-- **F1 root-count agrees with `E8Roots.rootSet`.** -/
theorem F1_root_count_matches :
    MacadayPhysicsLean.E8Roots.rootSet.card = 240 :=
  MacadayPhysicsLean.E8Roots.rootSet_card

/-- **F1 adjoint-from-data identity.**  Total Cartan (8) + total
roots (240) reconstruct the E₈ adjoint dimension (248).  This holds
independently of which order-3 class partitions the roots; the root
total is written here in its Class B partition. -/
theorem F1_adjoint_from_data :
    dim_cartan_E8 +
      (num_roots_fixed + num_roots_omega + num_roots_omegaBar) = 248 := by
  decide

end MacadayPhysicsLean.Z3Branching
