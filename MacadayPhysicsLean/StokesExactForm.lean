/-
Stokes' theorem on a closed manifold: the integral of an exact form
vanishes (Paper T).

**Mathematical statement.**  On a compact oriented manifold without
boundary, for every exact form `dα`, `∫_M dα = 0`.

**Proof.**  Stokes' theorem gives `∫_M dα = ∫_{∂M} α`; on a closed
manifold `∂M = ∅`, and integrating over the empty set yields zero.

**Lean formalization scope.**  Mathlib's full differential-geometric
Stokes' theorem (for arbitrary smooth manifolds with boundary) is
substantial machinery that exceeds the scope of this file.  We
instead state the *abstract algebraic shape* of the argument —
the only mathematical content is the chaining
`∫_M (dα) = ∫_{∂M} α = ∫_0 α = 0` — and prove it as a clean lemma
parameterized on `(∫, d, ∂)`.

The physics consequence (Paper T, holographic-screen extrinsic
curvature `K_⊥ = dφ` is exact, so `∫_S K_⊥ dA = 0`) follows as a
one-line instantiation of `integral_exact_form_eq_zero_of_closed`
to the singular cochain-level Stokes operator in any differential-
geometric library where Stokes' theorem is supplied as a hypothesis.
-/

import Mathlib.Tactic

namespace MacadayPhysicsLean.StokesExactForm

/-! ### Abstract Stokes / closed-manifold algebra -/

/-- **Stokes for closed manifolds — abstract.**

Given:

* a chain type `Chain` with a zero,
* a boundary operator `bdry : Chain → Chain`,
* a form type `Form`,
* an exterior derivative `d : Form → Form`,
* an integration pairing `integral : Chain → Form → ℝ` satisfying
  - **Stokes** `integral M (d α) = integral (bdry M) α`,
  - **integral over empty chain vanishes** `integral 0 α = 0`,

then for any *closed* chain `M` (i.e. `bdry M = 0`), the integral of
any exact form `d α` over `M` is zero:

  `integral M (d α) = 0`.

This is the *abstract algebraic core* of Stokes' theorem on a closed
manifold.  Instantiate `integral`, `d`, `bdry` from any differential-
geometric library to recover the geometric statement. -/
theorem integral_exact_form_eq_zero_of_closed
    {Chain Form : Type*} [Zero Chain]
    (bdry : Chain → Chain) (d : Form → Form)
    (integral : Chain → Form → ℝ)
    (integral_zero_chain : ∀ α, integral 0 α = 0)
    (stokes : ∀ M α, integral M (d α) = integral (bdry M) α)
    (M : Chain) (h_closed : bdry M = 0)
    (α : Form) :
    integral M (d α) = 0 := by
  rw [stokes, h_closed, integral_zero_chain]

/-- **Closed-chain corollary.**

When the boundary operator is *globally* zero (the chain type
consists entirely of closed chains — e.g. cycles in a complex of
fundamental classes), every exact form integrates to zero on every
chain. -/
theorem integral_exact_form_eq_zero_of_all_closed
    {Chain Form : Type*} [Zero Chain]
    (bdry : Chain → Chain) (d : Form → Form)
    (integral : Chain → Form → ℝ)
    (integral_zero_chain : ∀ α, integral 0 α = 0)
    (stokes : ∀ M α, integral M (d α) = integral (bdry M) α)
    (all_closed : ∀ M, bdry M = 0)
    (M : Chain) (α : Form) :
    integral M (d α) = 0 :=
  integral_exact_form_eq_zero_of_closed bdry d integral integral_zero_chain stokes
    M (all_closed M) α

/-! ### Linearity-based form

The same conclusion via a different hypothesis: instead of requiring
`integral 0 α = 0` directly, require that `integral` is additive in
its chain slot.  This matches how Mathlib's measure-theoretic
integrals typically package things. -/

/-- **Stokes for closed manifolds — linearity form.**

If `integral` is additive in its chain slot (so `integral 0 α = 0`
is automatic from `AddMonoidHom`), then for any closed `M`, exact
forms integrate to zero. -/
theorem integral_exact_form_eq_zero_of_closed_linear
    {Chain Form : Type*} [AddCommGroup Chain]
    (bdry : Chain →+ Chain) (d : Form → Form)
    (integral : Chain →+ (Form → ℝ))
    (stokes : ∀ M α, integral M (d α) = integral (bdry M) α)
    (M : Chain) (h_closed : bdry M = 0)
    (α : Form) :
    integral M (d α) = 0 := by
  rw [stokes, h_closed]
  simp

end MacadayPhysicsLean.StokesExactForm
