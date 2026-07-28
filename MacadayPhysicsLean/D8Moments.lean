/-
D₈ first-shell moments — the design-failure contrast to E₈ (Paper Z §2.2).

The 112 D₈ roots are `±eᵢ ± eⱼ` (`i < j`), of squared length 2.  Over this
first shell we compute the same degree-4 fingerprint as `E8Moments`:

* `Σ rᵢ⁴ = 28`  (28 roots touch coordinate `i`, each with `rᵢ⁴ = 1`);
* `Σ rᵢ² rⱼ² = 4`  (`i ≠ j`: only the 4 sign choices of the single root `±eᵢ±eⱼ`).

The **degree-4 design deviation** `Σ rᵢ⁴ − 3·Σ rᵢ² rⱼ² = 28 − 12 = 16 ≠ 0`, whereas
for E₈ the same combination vanishes (`E8Moments`: `576 − 3·192 = 0`).  This is
Paper Z's central structural claim at the first-shell level: the degree-4 channel
switches on exactly where the shell fails to be a spherical 4-design.

All moment sums are decided by `native_decide` over the explicit 112-root set.
-/

import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MacadayPhysicsLean.D8Moments

/-- A single D₈ root `s_i eᵢ + s_j eⱼ` with signs `s_i, s_j ∈ {±1}`. -/
def d8Vec (i j : Fin 8) (si sj : Bool) : Fin 8 → ℤ :=
  fun k => (if k = i then (if si then 1 else -1) else 0)
         + (if k = j then (if sj then 1 else -1) else 0)

/-- The 112 D₈ roots `±eᵢ ± eⱼ` for `i < j`. -/
def rootSet : Finset (Fin 8 → ℤ) :=
  (Finset.univ.filter (fun p : Fin 8 × Fin 8 => p.1 < p.2)).biUnion (fun p =>
    ({d8Vec p.1 p.2 true true, d8Vec p.1 p.2 true false,
      d8Vec p.1 p.2 false true, d8Vec p.1 p.2 false false} : Finset (Fin 8 → ℤ)))

/-- There are exactly 112 D₈ roots. -/
theorem rootSet_card : rootSet.card = 112 := by native_decide

/-! ### Degree-2 fingerprint (balance) -/

/-- Each coordinate sums to zero (`±`-symmetry). -/
theorem sum_coord_zero (i : Fin 8) : rootSet.sum (fun v => v i) = 0 := by
  fin_cases i <;> native_decide

/-- Diagonal second moment: `Σ rᵢ² = 28` for each `i`. -/
theorem sum_coord_sq (i : Fin 8) : rootSet.sum (fun v => (v i) ^ 2) = 28 := by
  fin_cases i <;> native_decide

/-! ### Degree-4 fingerprint -/

/-- `Σ rᵢ⁴ = 28` for each `i`. -/
theorem sum_coord_fourth (i : Fin 8) : rootSet.sum (fun v => (v i) ^ 4) = 28 := by
  fin_cases i <;> native_decide

/-- `Σ rᵢ² rⱼ² = 4` for `i ≠ j`. -/
theorem sum_coord_sq_product_offdiag (i j : Fin 8) (hij : i ≠ j) :
    rootSet.sum (fun v => (v i) ^ 2 * (v j) ^ 2) = 4 := by
  fin_cases i <;> fin_cases j <;>
    first
      | (exact absurd rfl hij)
      | native_decide

/-- **Design deviation is nonzero.** `Σ rᵢ⁴ − 3·Σ rᵢ² rⱼ² = 16` for `i ≠ j`.

Contrast E₈, where the same combination is `576 − 3·192 = 0`
(`E8Moments.sum_coord_fourth`, `E8Moments.sum_coord_sq_product_offdiag`): the D₈
first shell is **not** a spherical 4-design, and the degree-4 invariant it carries
is exactly the third channel of Paper Z's decomposition. -/
theorem design_deviation (i j : Fin 8) (hij : i ≠ j) :
    rootSet.sum (fun v => (v i) ^ 4) - 3 * rootSet.sum (fun v => (v i) ^ 2 * (v j) ^ 2)
      = 16 := by
  rw [sum_coord_fourth i, sum_coord_sq_product_offdiag i j hij]; norm_num

/-- The deviation coefficient is genuinely nonzero. -/
theorem design_deviation_ne_zero (i j : Fin 8) (hij : i ≠ j) :
    rootSet.sum (fun v => (v i) ^ 4) - 3 * rootSet.sum (fun v => (v i) ^ 2 * (v j) ^ 2)
      ≠ 0 := by
  rw [design_deviation i j hij]; decide

end MacadayPhysicsLean.D8Moments
