/-
Machine-Verified Mathematical Foundations

Author: Sean Eric Macaday Culm (ORCID: 0009-0009-8957-5516)

Formal verification of theorems in mathematical physics.
Files are added as the corresponding papers are published.

NOTE: this must be a plain block comment `/- -/`, not a module docstring
`/-! -/`. A module docstring is a Lean *command*, and `import` lines are
only legal before the first command — the stage scripts append imports here.
-/
import MacadayPhysicsLean.VCT
import MacadayPhysicsLean.Pinching
import MacadayPhysicsLean.SchurConcavity
import MacadayPhysicsLean.DensityOp
import MacadayPhysicsLean.OrthonormalBridge
import MacadayPhysicsLean.JointDiagonalization
import MacadayPhysicsLean.VCTCorollary
import MacadayPhysicsLean.BlockDepolarization
import MacadayPhysicsLean.EigenprojectorFamily
import MacadayPhysicsLean.SIT
import MacadayPhysicsLean.SectorDecomposition
import MacadayPhysicsLean.E8Roots
import MacadayPhysicsLean.Z3Branching
import MacadayPhysicsLean.Z3Symmetry
import MacadayPhysicsLean.HolonomyRigidity
import MacadayPhysicsLean.GenusTower
import MacadayPhysicsLean.StokesExactForm
import MacadayPhysicsLean.HarmonicConstant
import MacadayPhysicsLean.T2HolomorphicConstant
