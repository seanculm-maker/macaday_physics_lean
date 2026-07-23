/-
Harmonic functions on a compact manifold without boundary are
constant (Paper T3).

**Mathematical statement.**  On a compact Riemannian manifold
without boundary, if `Δf = 0` (f is harmonic), then `f` is constant.

**Proof.**  Integration by parts on a closed manifold gives
`∫ |∇f|² = -∫ f · Δf`.  When `Δf = 0`, the RHS vanishes, so
`∫ |∇f|² = 0`; pointwise non-negativity then forces `∇f = 0`
almost everywhere, and connectedness gives `f` constant.

**Lean formalization scope.**  Mathlib's Riemannian / elliptic-PDE
infrastructure is substantial machinery.  As with `StokesExactForm`,
we instead capture the *abstract algebraic core* of the argument:
given an integration-by-parts identity and the "squared-gradient
integrates to zero ⇒ gradient is zero" implication, harmonicity
forces zero gradient.  The final step (zero gradient ⇒ constant on
a connected manifold) is taken as a hypothesis.

The physics consequence (Paper T3, the boundary extrinsic curvature
satisfies a Codazzi equation forcing it to be harmonic, hence
constant, hence zero by the Stokes argument) follows as a one-line
instantiation.
-/

import Mathlib.Tactic

namespace MacadayPhysicsLean.HarmonicConstant

/-! ### Abstract harmonic ⇒ gradient zero -/

/-- **Harmonic implies zero gradient — abstract.**

Given a function space `F` and operators `grad`, `lap : F → F`
together with a "squared gradient integral" `sq_grad_int : F → ℝ`
satisfying

* `sq_grad_int` is non-negative,
* `sq_grad_int f = 0 ⇒ grad f = 0` (pointwise non-negativity + total
  integral zero forces vanishing),
* `lap f = 0 ⇒ sq_grad_int f = 0` (integration by parts on a closed
  manifold),

every harmonic `f` (i.e. `lap f = 0`) has zero gradient.

This packages the core estimate of the harmonic-constant theorem
in a Mathlib-free abstract form. -/
theorem grad_zero_of_harmonic_compact_closed
    {F : Type*} [Zero F]
    (grad : F → F) (lap : F → F)
    (sq_grad_int : F → ℝ)
    (_sq_grad_int_nonneg : ∀ f, 0 ≤ sq_grad_int f)
    (sq_grad_int_eq_zero_imp : ∀ f, sq_grad_int f = 0 → grad f = 0)
    (ibp_harmonic : ∀ f, lap f = 0 → sq_grad_int f = 0)
    (f : F) (h_harmonic : lap f = 0) :
    grad f = 0 :=
  sq_grad_int_eq_zero_imp f (ibp_harmonic f h_harmonic)

/-- **Harmonic implies constant — abstract, with connectedness.**

Adding the "zero gradient ⇒ constant" hypothesis (which on a
*connected* manifold is the ungraded statement of constancy),
harmonic functions are constant. -/
theorem const_of_harmonic_compact_closed_connected
    {F : Type*} [Zero F]
    (grad : F → F) (lap : F → F)
    (sq_grad_int : F → ℝ)
    (sq_grad_int_nonneg : ∀ f, 0 ≤ sq_grad_int f)
    (sq_grad_int_eq_zero_imp : ∀ f, sq_grad_int f = 0 → grad f = 0)
    (ibp_harmonic : ∀ f, lap f = 0 → sq_grad_int f = 0)
    (is_const : F → Prop)
    (const_of_grad_zero : ∀ f, grad f = 0 → is_const f)
    (f : F) (h_harmonic : lap f = 0) :
    is_const f :=
  const_of_grad_zero f
    (grad_zero_of_harmonic_compact_closed grad lap sq_grad_int
      sq_grad_int_nonneg sq_grad_int_eq_zero_imp ibp_harmonic f h_harmonic)

end MacadayPhysicsLean.HarmonicConstant
