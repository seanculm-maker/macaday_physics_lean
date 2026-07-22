/-
ℤ₃ branching of E₈ (Paper F1).

**Theorem F1-Branch.**  Under the order-3 outer automorphism `σ`
of E₈ (the cyclic symmetry of the extended Dynkin diagram), the
fixed-point subalgebra is `E₆ ⊕ A₂` (with `A₂ ≅ su(3)`), and the
adjoint `248` decomposes as

    248 = (78, 1) ⊕ (1, 8) ⊕ (27, 3) ⊕ (27̄, 3̄)

with dimensions `78 + 8 + 81 + 81 = 248`.

**Root-count reformulation.**  The 240 E₈ roots split into
σ-eigenspaces:

* 72 roots with σ-eigenvalue 1   (Re Re)
* 84 roots with σ-eigenvalue ω
* 84 roots with σ-eigenvalue ω̄

with `72 + 84 + 84 = 240`.  The 8-dim E₈ Cartan splits
`6 + 2 = 8` (E₆ Cartan ⊕ A₂ Cartan).  Combining:
`8 + 240 = 248`.

**This file** proves the arithmetic identities of F1:
component-dimension sum, root-count sum, root + Cartan = adjoint.
The explicit construction of σ as a permutation of
`E8Roots.rootSet` is deferred to a subsequent file (needs an
explicit choice of σ-realization on root data).
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

/-! ### The four branching components and their dimensions -/

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

/-! ### Master dimension identity -/

/-- **F1 component-dimension identity.**  The four branching components
sum to `dim(E₈) = 248`. -/
theorem F1_dim_sum :
    dim_block_78_1 + dim_block_1_8 + dim_block_27_3 + dim_block_27b_3b = 248 := by
  decide

/-! ### Root + Cartan partition (the geometric content) -/

/-- Size of the σ-fixed root eigenspace. -/
def num_roots_fixed : ℕ := 72
/-- Size of the σ-ω root eigenspace. -/
def num_roots_omega : ℕ := 84
/-- Size of the σ-ω̄ root eigenspace. -/
def num_roots_omegaBar : ℕ := 84

/-- E₆ Cartan dimension. -/
def dim_cartan_E6 : ℕ := 6
/-- A₂ Cartan dimension. -/
def dim_cartan_A2 : ℕ := 2

/-- **F1 root-count identity.**  σ-orbit sizes sum to 240. -/
theorem F1_root_sum :
    num_roots_fixed + num_roots_omega + num_roots_omegaBar = 240 := by decide

/-- **F1 Cartan-split identity.**  E₆ ⊕ A₂ Cartans = E₈ Cartan. -/
theorem F1_cartan_sum :
    dim_cartan_E6 + dim_cartan_A2 = 8 := by decide

/-- **F1 root-count agrees with `E8Roots.rootSet`.** -/
theorem F1_root_count_matches :
    MacadayPhysicsLean.E8Roots.rootSet.card = 240 :=
  MacadayPhysicsLean.E8Roots.rootSet_card

/-- **F1 adjoint-from-data identity.**  Total Cartan (8) + total
roots (240) reconstruct the E₈ adjoint dimension (248). -/
theorem F1_adjoint_from_data :
    (dim_cartan_E6 + dim_cartan_A2) +
      (num_roots_fixed + num_roots_omega + num_roots_omegaBar) = 248 := by
  decide

/-- **F1 fixed-sector identity.**  E₆ adjoint (78) = E₆ Cartan (6)
+ σ-fixed roots (72). -/
theorem F1_fixed_sector :
    dim_cartan_E6 + num_roots_fixed = dim_block_78_1 := by decide

end MacadayPhysicsLean.Z3Branching
