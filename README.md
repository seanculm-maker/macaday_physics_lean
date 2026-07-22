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

Files are added as papers are published. The **Result** column names the
principal theorem verified; full paper titles are added with each DOI.

| Paper | Result | DOI | Files | Key Theorems |
|-------|--------|-----|-------|--------------|
| **W** | The Variance Classicality Theorem | _DOI pending_ | `VCT`, `Pinching`, `SchurConcavity`, `DensityOp`, `OrthonormalBridge`, `JointDiagonalization`, `VCTCorollary`, `BlockDepolarization`, `EigenprojectorFamily` | VCT Lemma 3 (unconditional), Schur concavity (Hardy–Littlewood–Pólya), spectral expansion, joint diagonalisation, Step-2 scalarity, max-entropy uniqueness, eigenprojector resolution of identity |
| **C** | The Statistics Inheritance Theorem | _DOI pending_ | `SIT`, `SectorDecomposition` | Statistics inheritance (Theorem 1), no c-number eigenvalues, FKS cocycle sign (k=1), bilinear parity contrast, sector decomposition (8+4+4+48=64) |
| **F1** | ℤ₃ Branching of E₈ | _DOI pending_ | `E8Roots`, `Z3Branching`, `Z3Symmetry` | All 240 E₈ roots with norms, 112/128 split, 248 = 78+8+81+81, inner-ℤ₃ phase action giving 240 = 72+84+84 |
| **M** | Moncrief Reduction and Holonomy Rigidity | _DOI pending_ | `HolonomyRigidity` | cosh β > 1 for β ≠ 0, with equality iff β = 0 |
| **T** | The Genus Tower | _DOI pending_ | `GenusTower` | Genus tower formula (g=0: 0, g=1: 1, g≥2: 3g−3), conditional on Riemann–Roch |

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
