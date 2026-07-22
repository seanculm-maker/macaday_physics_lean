/-
Screen Sector Decomposition — Paper C.

The 64 corner modes decompose into four sectors by Grassmann parity:

* gravity (`c = 8`,  bosonic)
* gauge   (`c = 4`,  bosonic)
* higgs   (`c = 4`,  bosonic)
* matter  (`c = 48`, fermionic)

Total: `16` bosonic + `48` fermionic = `64`.

This file contains *only* the sector-decomposition data and totals.
The Paper-MP uniqueness theorem (`heisenberg_cut_unique`) and the
generation-count ratio (`c_quantum / c_classical = 3`) live in
`HeisenbergCut.lean`, which is published separately and builds on
the definitions below.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace MacadayPhysicsLean.SectorDecomposition

/-- The four screen sectors. -/
inductive Sector
  | gravity
  | gauge
  | higgs
  | matter
  deriving DecidableEq, Fintype, Repr

/-- Central charge of each sector. -/
def centralCharge : Sector → ℕ
  | .gravity => 8
  | .gauge   => 4
  | .higgs   => 4
  | .matter  => 48

/-- Bosonic/fermionic label. `true` = bosonic, `false` = fermionic. -/
def isBosonic : Sector → Bool
  | .gravity => true
  | .gauge   => true
  | .higgs   => true
  | .matter  => false

/-- **Total central charge**: `8 + 4 + 4 + 48 = 64`. -/
theorem total_central_charge :
    centralCharge .gravity + centralCharge .gauge +
      centralCharge .higgs + centralCharge .matter = 64 := by decide

/-- **Bosonic central charge**: `8 + 4 + 4 = 16`. -/
theorem bosonic_central_charge :
    centralCharge .gravity + centralCharge .gauge +
      centralCharge .higgs = 16 := by decide

/-- **Fermionic central charge**: matter sector contributes `48`. -/
theorem fermionic_central_charge :
    centralCharge .matter = 48 := by decide

end MacadayPhysicsLean.SectorDecomposition
