# Machine-Verified Mathematical Foundations

**Author:** Sean Eric Macaday Culm (ORCID: [0009-0009-8957-5516](https://orcid.org/0009-0009-8957-5516))

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
| **W** | Maximum Entropy under Commuting Constraints: A Classicality Theorem | The Variance Classicality Theorem | _DOI pending_ | `VCT`, `Pinching`, `SchurConcavity`, `DensityOp`, `OrthonormalBridge`, `JointDiagonalization`, `VCTCorollary`, `BlockDepolarization`, `EigenprojectorFamily` | VCT Lemma 3 (unconditional), Schur concavity (Hardy–Littlewood–Pólya), spectral expansion, joint diagonalisation, Step-2 scalarity, max-entropy uniqueness, eigenprojector resolution of identity |
| **C** | Corner Symmetry of Dirac and Yang-Mills Fields at Codimension-2 Surfaces: Presymplectic Structure, Statistics, and Central Charges of Matter Edge Modes | The Statistics Inheritance Theorem | _DOI pending_ | `SIT`, `SectorDecomposition` | Statistics inheritance (Theorem 1), no c-number eigenvalues, FKS cocycle sign (k=1), bilinear parity contrast, sector decomposition (8+4+4+48=64) |
| **F1** | Wilson-Line Determinant Theorems for Yukawa Matrices | ℤ₃ Branching of E₈ | _DOI pending_ | `E8Roots`, `Z3Branching`, `Z3Symmetry` | All 240 E₈ roots with norms, 112/128 split, 248 = 78+8+81+81, inner-ℤ₃ phase action giving 240 = 72+84+84 |
| **M** | Moncrief's Reduced Phase Space from Symplectic Reduction of the Corner Symmetry Group | Moncrief Reduction and Holonomy Rigidity | _DOI pending_ | `HolonomyRigidity`, `MoncriefA2` | cosh β > 1 for β ≠ 0 (equality iff β = 0), and the full ℂ² holonomy rigidity — a non-trivial SO(1,1) boost or SO(2) rotation fixes only the zero vector, since det(R − I) = 2 − 2cosh β (resp. 2 − 2cos α) ≠ 0; Theorem A.2 — flatness and torsion-freeness of the four-parameter family for **any** alternating bilinear form, the Chern–Simons symplectic-coefficient 2-form identity, and the (β,λ) ↦ (p₁,p₂) Jacobian = p₂; the g = 1 real-proportionality criterion; the York-map Jacobian −1/(4τ₂); and the SL(2,ℤ) S/TS chart-coverage identities |
| **T** | The Genus-One Screen: Enstrophy, Riemann-Roch, and Gaussian Holographic Saturation | The Genus Tower | _DOI pending_ | `GenusTower`, `HolonomyRigidity`, `StokesExactForm`, `HarmonicConstant`, `T2HolomorphicConstant` | Genus tower formula (g=0: 0, g=1: 1, g≥2: 3g−3), conditional on Riemann–Roch (g≥2); the g=1 entry is **unconditional** — a holomorphic doubly-periodic function on ℂ is constant (Liouville), so dim H⁰(T², K²) = 1; integral of an exact form vanishes on a closed manifold; harmonic ⇒ constant on a compact manifold without boundary |
| **R** | Relative-Entropy Classicality under Commuting Constraints: Prior Memory and Exact Defect Decompositions | The Relative Classicality Theorem | _DOI pending_ | `RelativeEntropy`, `CfcEigenvector`, `RelEntropyPinching`, `RelEntropyKlein`, `RelEntropyKleinEq`, `ChainRule`, `BlockChainRule`, `ThreeDefect`, `RelEntropySupport`, `MinimizerR`, `NeutralBridge` | Umegaki relative entropy nonnegativity (Klein's inequality) with its equality case; the pinching Pythagorean identity; the direct-sum chain rule; the prior-relative and equilibrium-defect decompositions with the reset-channel form; the support lemma (ker Δρ ⊆ ker ρ); the **Relative Classicality Theorem** — the unique divergence minimiser over commuting constraints is the block-diagonal reset ⊕_λ p_λ σ_λ, reducing quantum inference to a classical Kullback–Leibler projection; and the neutral-prior bridge D(ρ‖I/d) = log d − S(ρ) |
| **V** | The Intrinsic Curvature Variance of 2D Causal Dynamical Triangulations | The CDT Variance Identity | _DOI pending_ | `CDTVariance` | Mean coordination number is constant (= 3) along every strip word; the word ↔ composition correspondence is a genuine bijection (both inverses); and the closing algebraic identity (11l + 7)/(l + 1) − 9 = 2(l − 1)/(l + 1) |
| **Z** | The Zamolodchikov Metric at the E₈ Narain Point: A Three-Channel Decomposition | E₈ First-Shell Design Moments | _DOI pending_ | `E8Moments`, `ThetaMaximization`, `D8Moments`, `NarainDecomposition`, `NarainEven`, `NarainSelfDual` | The complete degree ≤ 7 moment identities of the E₈ 240-root first shell, pinning the fourth-moment tensor to 12(δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk) (spherical-design collapse, Σ r_i⁴ − 3 Σ r_i² r_j² = 0); term-by-term monotonicity of the Narain Boltzmann weight in B, equality iff the B-coupling is trivial; the contrasting D₈ first shell, whose design deviation 28 − 3·4 = 16 ≠ 0 shows the degree-4 channel switches on exactly where the design property fails; and the Narain §1.1 inputs — T-invariance forces an even lattice, S-invariance forces self-duality (algebraic core, modulo the Poisson/eta transforms and theta-determines-lattice as explicit hypotheses), and the B = 0 factorization into Euclidean even self-dual factors. E₈/D₈ moment sums are decided by `native_decide` over the explicit root sets (compiler-trusted, not kernel-clean) |

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
  author    = {Culm, Sean Eric Macaday},
  title     = {Machine-Verified Mathematical Foundations},
  year      = {2026},
  publisher = {GitHub},
  url       = {https://github.com/seanculm-maker/macaday_physics_lean}
}
```

## License

MIT
