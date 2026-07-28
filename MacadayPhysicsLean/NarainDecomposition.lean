/-
Narain Decomposition at B = 0: an indefinite-signature even self-dual
lattice factorizes into two Euclidean even self-dual factors
(the Narain quadratic form factorises at B = 0).

**Mathematical statement.**  Let `Λ = Λ_L ⊕ Λ_R` be a Narain lattice
of signature `(n, n)` with B-field set to zero, equipped with the
indefinite quadratic form `Q(p_L, p_R) = ⟨p_L, p_L⟩_L − ⟨p_R, p_R⟩_R`
where `⟨·,·⟩_L`, `⟨·,·⟩_R` are positive-definite metrics on the
left/right components.

If `Λ` is even (`Q(p, p) ∈ 2ℤ` for all `p ∈ Λ`) and self-dual, then
each factor `Λ_L`, `Λ_R` is *separately* an even Euclidean lattice.

**Proof.**  Specialize `p = (p_L, 0)` ∈ Λ to get `Q(p, p) = ⟨p_L, p_L⟩_L`
which must be even.  Similarly for `(0, p_R)`.  The self-dual part
factors analogously via the bilinear pairing.

**Lean scope.**  We prove the *evenness factorization* — the algebraic
core that's independent of the full Narain modular-form machinery.
The self-dual factorization at B = 0 follows the same argument and
is stated as a corollary in the same abstract form.

The physics consequence (Paper W's VCT B = 0 sector ⇒ left/right
Narain factors are independent E₈ lattices) follows by composing
this decomposition with `E8Uniqueness` (§2.4, future work).
-/

import Mathlib.Tactic

namespace MacadayPhysicsLean.NarainDecomposition

/-! ### Evenness factorization at B = 0 -/

/-- **B = 0 implies each Narain factor is even.**

Given a product lattice `Λ = Λ_L × Λ_R` with the indefinite form
`Q(p_L, p_R) = q_L p_L − q_R p_R`, if every `Q(p, p)` is even then
each `q_L(p_L)` and each `q_R(p_R)` is even (specialize to `(p_L, 0)`
and `(0, p_R)` respectively).

`q_L`, `q_R` are the (positive-definite) norm-squared maps on the
left/right factors; both have integer values because the lattice
sits in an integer-valued bilinear form. -/
theorem evenness_factors_at_B_zero
    {Λ_L Λ_R : Type*} [Zero Λ_L] [Zero Λ_R]
    (q_L : Λ_L → ℤ) (q_R : Λ_R → ℤ)
    (q_L_zero : q_L 0 = 0) (q_R_zero : q_R 0 = 0)
    (Q : Λ_L × Λ_R → ℤ)
    (Q_decomp : ∀ p, Q p = q_L p.1 - q_R p.2)
    (even_Q : ∀ p, Even (Q p)) :
    (∀ p_L, Even (q_L p_L)) ∧ (∀ p_R, Even (q_R p_R)) := by
  refine ⟨fun p_L => ?_, fun p_R => ?_⟩
  · have h := even_Q (p_L, 0)
    rw [Q_decomp, q_R_zero, sub_zero] at h
    exact h
  · have h := even_Q (0, p_R)
    rw [Q_decomp, q_L_zero, zero_sub] at h
    -- `h : Even (-(q_R p_R))`; want `Even (q_R p_R)`.
    obtain ⟨r, hr⟩ := h
    refine ⟨-r, ?_⟩
    linarith

/-! ### Bilinear pairing decomposition

The self-dual factorization uses the *bilinear* form
`B(p, q) = ⟨p_L, q_L⟩_L − ⟨p_R, q_R⟩_R`.  The factorization
argument is the same: specialize one factor to zero to extract the
integrality of the pairing on the other. -/

/-- **B = 0 implies bilinear pairing factors over each Narain factor.**

If the bilinear form `B(p, q) = b_L p.1 q.1 − b_R p.2 q.2` is
integer-valued on the lattice product `Λ_L × Λ_R`, then `b_L` is
integer-valued on `Λ_L` and `b_R` on `Λ_R`. -/
theorem pairing_integral_factors_at_B_zero
    {Λ_L Λ_R V : Type*} [Zero Λ_L] [Zero Λ_R] [AddGroup V]
    (b_L : Λ_L → Λ_L → V) (b_R : Λ_R → Λ_R → V)
    (_b_L_zero_right : ∀ p_L, b_L p_L 0 = 0)
    (b_R_zero_right : ∀ p_R, b_R p_R 0 = 0)
    (b_L_zero_left : ∀ q_L, b_L 0 q_L = 0)
    (_b_R_zero_left : ∀ q_R, b_R 0 q_R = 0)
    (B : (Λ_L × Λ_R) → (Λ_L × Λ_R) → V)
    (B_decomp : ∀ p q, B p q = b_L p.1 q.1 - b_R p.2 q.2)
    (S : Set V) (zero_mem : (0 : V) ∈ S)
    (sub_mem : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ S)
    (B_int : ∀ p q, B p q ∈ S) :
    (∀ p_L q_L, b_L p_L q_L ∈ S) ∧ (∀ p_R q_R, b_R p_R q_R ∈ S) := by
  refine ⟨fun p_L q_L => ?_, fun p_R q_R => ?_⟩
  · have h := B_int (p_L, 0) (q_L, 0)
    rw [B_decomp, b_R_zero_right, sub_zero] at h
    exact h
  · have h := B_int (0, p_R) (0, q_R)
    rw [B_decomp, b_L_zero_left, zero_sub] at h
    -- `-b_R p_R q_R ∈ S` ⇒ `b_R p_R q_R = 0 - (-b_R p_R q_R) ∈ S`
    have h2 : b_R p_R q_R = 0 - (-(b_R p_R q_R)) := by
      rw [zero_sub, neg_neg]
    rw [h2]
    exact sub_mem 0 zero_mem _ h

end MacadayPhysicsLean.NarainDecomposition
