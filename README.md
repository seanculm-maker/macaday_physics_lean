# Machine-Verified Mathematical Foundations

**Author:** Sean Eric Culm Macaday (ORCID: [0009-0009-8957-5516](https://orcid.org/0009-0009-8957-5516))

Formal verification of mathematical theorems in mathematical physics, using
[Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4).

Every theorem here is kernel-verified with **zero `sorry`** — no unproved
assumptions, no gaps, no placeholders.

## Build

```bash
git clone https://github.com/seanculm-maker/macaday_physics_lean.git
cd macaday_physics_lean
lake exe cache get    # download precompiled Mathlib (~5 min)
lake build            # verify all theorems (~2 min)
```

Requires [elan](https://github.com/leanprover/elan). The `lean-toolchain` file
pins the exact Lean version.

## Verified Papers

Files are added as papers are published. The **Title** column gives the paper
title; the **Result** column names the principal theorem verified.

| Paper | Title | Result | DOI | Files | Key Theorems |
|-------|-------|--------|-----|-------|--------------|
| **W** | Maximum Entropy under Commuting Constraints: A Classicality Theorem | The Variance Classicality Theorem | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `VCT`, `Pinching`, `SchurConcavity`, `DensityOp`, `OrthonormalBridge`, `JointDiagonalization`, `VCTCorollary`, `BlockDepolarization`, `EigenprojectorFamily` | VCT Lemma 3 (unconditional), Schur concavity (Hardy–Littlewood–Pólya), spectral expansion, joint diagonalisation, Step-2 scalarity, max-entropy uniqueness, eigenprojector resolution of identity |
| **C** | Corner Symmetry of Dirac and Yang-Mills Fields at Codimension-2 Surfaces: Presymplectic Structure, Statistics, and Central Charges of Matter Edge Modes | The Statistics Inheritance Theorem | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `SIT`, `SectorDecomposition` | Statistics inheritance (Theorem 1), no c-number eigenvalues, FKS cocycle sign (k=1), bilinear parity contrast, sector decomposition (8+4+4+48=64) |
| **F1** | Wilson-Line Determinant Theorems for Yukawa Matrices | ℤ₃ Branching of E₈ | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `E8Roots`, `Z3Branching`, `Z3Symmetry` | All 240 E₈ roots with norms, 112/128 split, 248 = 78+8+81+81, inner-ℤ₃ phase action giving 240 = 72+84+84 |
| **M** | Moncrief's Reduced Phase Space from Symplectic Reduction of the Corner Symmetry Group | Moncrief Reduction and Holonomy Rigidity | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `HolonomyRigidity`, `MoncriefA2`, `MoncriefA4` | cosh β > 1 for β ≠ 0 (equality iff β = 0), and the full ℂ² holonomy rigidity — a non-trivial SO(1,1) boost or SO(2) rotation fixes only the zero vector, since det(R − I) = 2 − 2cosh β (resp. 2 − 2cos α) ≠ 0; Theorem A.2 — flatness and torsion-freeness of the four-parameter family for **any** alternating bilinear form, the Chern–Simons symplectic-coefficient 2-form identity, and the (β,λ) ↦ (p₁,p₂) Jacobian = p₂; the g = 1 real-proportionality criterion; the York-map Jacobian −1/(4τ₂); the SL(2,ℤ) S/TS chart-coverage identities; and Theorem A.4 (fixed-area slice) — flatness and torsion-freeness of the unit-area family for every cross-product signature, unit induced-metric determinant, the dτ₂- and δs-coefficient collapses of the symplectic potential, the momentum identities s q₁ = P₁ and s(q₂² − q₁²)/(2q₂) = P₂ with their Theorem A.2 forms, the fibre Jacobian β((τ₁−λ)² + τ₂²)/(2τ₂³) (nonzero over ℝ), and fibre coverage — every (p, q) ≠ (0, 0) is hit by (β, λ) ↦ (P₁, P₂) at some β ≠ 0 |
| **T** | The Genus-One Screen: Enstrophy, Riemann-Roch, and Gaussian Holographic Saturation | The Genus Tower | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `GenusTower`, `HolonomyRigidity`, `StokesExactForm`, `HarmonicConstant`, `T2HolomorphicConstant` | Genus tower formula (g=0: 0, g=1: 1, g≥2: 3g−3), conditional on Riemann–Roch (g≥2); the g=1 entry is **unconditional** — a holomorphic doubly-periodic function on ℂ is constant (Liouville), so dim H⁰(T², K²) = 1; integral of an exact form vanishes on a closed manifold; harmonic ⇒ constant on a compact manifold without boundary |
| **R** | Relative-Entropy Classicality under Commuting Constraints: Prior Memory and Exact Defect Decompositions | The Relative Classicality Theorem | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `RelativeEntropy`, `CfcEigenvector`, `RelEntropyPinching`, `RelEntropyKlein`, `RelEntropyKleinEq`, `ChainRule`, `BlockChainRule`, `ThreeDefect`, `RelEntropySupport`, `MinimizerR`, `NeutralBridge` | Umegaki relative entropy nonnegativity (Klein's inequality) with its equality case; the pinching Pythagorean identity; the direct-sum chain rule; the prior-relative and equilibrium-defect decompositions with the reset-channel form; the support lemma (ker Δρ ⊆ ker ρ); the **Relative Classicality Theorem** — the unique divergence minimiser over commuting constraints is the block-diagonal reset ⊕_λ p_λ σ_λ, reducing quantum inference to a classical Kullback–Leibler projection; and the neutral-prior bridge D(ρ‖I/d) = log d − S(ρ) |
| **V** | Exact Boundary and Bulk Curvature Variance in Two-Dimensional Causal Dynamical Triangulations | The CDT Variance Identity | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `CDTVariance`, `CDTGluing` | Mean coordination number is constant (= 3) along every strip word; the word ↔ composition correspondence is a genuine bijection (both inverses), with the count-preservation lemmas (parts = #U + 1, part-sum = #D) restricting it to {words with l U's and l D's} ↔ {compositions of l into l+1 parts}; the closing algebraic identity (11l + 7)/(l + 1) − 9 = 2(l − 1)/(l + 1); and the Theorem B cross-moment identity — the shift-average over ℤ/l of the spatial two-field cross-moment equals the product of the field means (covariance cross-term cancellation) |
| **Z** | The Torus Partition-Function Hessian at the E₈ Narain Point: An Exact Three-Channel Decomposition | E₈ First-Shell Design Moments | [10.5281/zenodo.21650666](https://doi.org/10.5281/zenodo.21650666) | `E8Moments`, `ThetaMaximization`, `D8Moments`, `NarainDecomposition`, `NarainEven`, `NarainSelfDual` | The complete degree ≤ 7 moment identities of the E₈ 240-root first shell, pinning the fourth-moment tensor to 12(δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk) (spherical-design collapse, Σ r_i⁴ − 3 Σ r_i² r_j² = 0); term-by-term monotonicity of the Boltzmann weight in a chirality-mixing norm-sum model (maximised at zero mixing), together with the finite cosine-bound inequality step of the paper's Poisson argument — the model omits the actual Narain quadratic form's cross term, so the true global B-maximum (proved by Poisson summation) is not formalized; the contrasting D₈ first shell, whose design deviation 28 − 3·4 = 16 ≠ 0 shows the degree-4 channel switches on exactly where the design property fails; and the Narain §1.1 inputs — T-invariance forces an even lattice, S-invariance forces self-duality (algebraic core, modulo the Poisson/eta transforms and theta-determines-lattice as explicit hypotheses), and the B = 0 factorization into Euclidean even self-dual factors. E₈/D₈ moment sums are decided by `native_decide` over the explicit root sets (compiler-trusted, not kernel-clean) |

## What "zero sorry" means

In Lean 4, `sorry` is the only way to admit an unproved statement. This
repository contains none — every theorem has a complete proof checked by Lean's
trusted kernel. To confirm:

```bash
grep -rn "sorry" MacadayPhysicsLean/ --include="*.lean" | grep -v "^\s*--"
# should return nothing
```

## Conditional vs unconditional theorems

Some theorems take well-known published results as explicit hypotheses (e.g.
Conway–Sloane rank-8 uniqueness, Riemann–Roch). These are marked in the source.
The deductions *from* those hypotheses are fully machine-verified; the
hypotheses themselves are peer-reviewed theorems that Mathlib does not yet have
the infrastructure to formalise.

## Citation

```bibtex
@software{culm_lean_2026,
  author    = {Culm Macaday, Sean Eric},
  title     = {Machine-Verified Mathematical Foundations},
  year      = {2026},
  publisher = {GitHub},
  url       = {https://github.com/seanculm-maker/macaday_physics_lean}
}
```

## License

MIT
