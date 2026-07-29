/-
CDT Gluing — Paper V, Theorem B (spatial cross-moment cancellation).

The key finitary step behind Paper V's Theorem B: on a periodic spatial slice
of `l` sites (indices in `ZMod l`), the shift-average of a two-field spatial
cross-moment factorizes into the product of the individual field averages.
Equivalently, averaged over all cyclic shifts the covariance cross-term
vanishes — which is exactly the additivity of the curvature variance used in
the boundary/bulk decomposition (given a zero cross term, `Var` is additive).

This is pure combinatorics: a double-sum reindexing (`Finset.sum_comm` plus the
shift bijection `Equiv.addLeft` on `ZMod l`), with no analysis or probability.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MacadayPhysicsLean.CDTGluing

variable {l : ℕ} [NeZero l]

/-- **Shift-sum factorization.**  Summed over all cyclic shifts `s`, the spatial
cross-moment `∑ᵢ f i · g (i + s)` totals `(∑ f)(∑ g)`.  The inner reindexing
`∑ₛ g (i + s) = ∑ⱼ g j` is the shift bijection `Equiv.addLeft i` on `ZMod l`. -/
theorem shift_sum_cross_moment (f g : ZMod l → ℚ) :
    ∑ s, ∑ i, f i * g (i + s) = (∑ i, f i) * ∑ j, g j := by
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft i) (fun s => f i * g (i + s))
    (fun j => f i * g j) (fun s => by rw [Equiv.coe_addLeft])

/-- **Averaged form.**  Dividing by the shift and space normalizations, the
shift-averaged spatial cross-moment equals the product of the two field means:
`⟨⟨f · g∘shift⟩⟩ = ⟨f⟩ ⟨g⟩`.  This is Paper V's Theorem B cross-term identity. -/
theorem shift_average_eq_product_of_means (f g : ZMod l → ℚ) :
    (1 / (l : ℚ)) * ∑ s, (1 / (l : ℚ)) * ∑ i, f i * g (i + s)
      = ((1 / (l : ℚ)) * ∑ i, f i) * ((1 / (l : ℚ)) * ∑ j, g j) := by
  rw [← Finset.mul_sum, shift_sum_cross_moment]
  ring

end MacadayPhysicsLean.CDTGluing
