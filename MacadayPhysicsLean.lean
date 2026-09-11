/-
Machine-Verified Mathematical Foundations

Author: Sean Eric Culm Macaday (ORCID: 0009-0009-8957-5516)

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
import MacadayPhysicsLean.VCTScalarity
import MacadayPhysicsLean.BlockDepolarization
import MacadayPhysicsLean.EigenprojectorFamily
import MacadayPhysicsLean.SIT
import MacadayPhysicsLean.SectorDecomposition
import MacadayPhysicsLean.E8Roots
import MacadayPhysicsLean.Z3Branching
import MacadayPhysicsLean.Z3Symmetry
import MacadayPhysicsLean.HolonomyRigidity
import MacadayPhysicsLean.MoncriefA2
import MacadayPhysicsLean.MoncriefA4
import MacadayPhysicsLean.MoncriefA5
import MacadayPhysicsLean.GenusTower
import MacadayPhysicsLean.StokesExactForm
import MacadayPhysicsLean.HarmonicConstant
import MacadayPhysicsLean.T2HolomorphicConstant
import MacadayPhysicsLean.RelativeEntropy
import MacadayPhysicsLean.CfcEigenvector
import MacadayPhysicsLean.RelEntropyPinching
import MacadayPhysicsLean.RelEntropyKlein
import MacadayPhysicsLean.RelEntropyKleinEq
import MacadayPhysicsLean.ChainRule
import MacadayPhysicsLean.BlockChainRule
import MacadayPhysicsLean.ThreeDefect
import MacadayPhysicsLean.RelEntropySupport
import MacadayPhysicsLean.MinimizerR
import MacadayPhysicsLean.NeutralBridge
import MacadayPhysicsLean.CDTVariance
import MacadayPhysicsLean.CDTGluing
import MacadayPhysicsLean.E8Moments
import MacadayPhysicsLean.ThetaMaximization
import MacadayPhysicsLean.D8Moments
import MacadayPhysicsLean.NarainDecomposition
import MacadayPhysicsLean.NarainEven
import MacadayPhysicsLean.NarainSelfDual
