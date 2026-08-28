import Formulas.ConversionDepth
import Formulas.Eval
import Formulas.Properties
import Mathlib.Data.PNat.Basic

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

def UFIFormulaOfSizeAtMostPolyNAndDepthAtMostD
  (n c k d : Nat) :=
  {
      circuit : UnboundedFanInFormula //
      ufiFormulaDepth circuit ≤ d
      ∧ ufiFormulaCircuitSize circuit ≤ c * n ^ k
      ∧ d > 0
      ∧ ufiLargestInput circuit < n
    }

/-- Leveled variant of
    `UFIFormulaOfSizeAtMostPolyNAndDepthAtMostD`:
    the circuit additionally satisfies the fused leveling predicate
    `Leveling.IsProperlyLeveled circuit d`, i.e. its syntax tree has no
    `notGate` constructors, the AND/OR layers strictly alternate with
    the root at level `d`, and the bottom two layers form proper
    CNF/DNF clauses.  This single predicate subsumes both
    `UnboundedFanInFormula.IsAlternatingAndLeveledAt circuit d` and
    `HasProperBottomsAt circuit d` (recovered via
    `Leveling.isProperlyLeveled_imp_strict` /
    `Leveling.isProperlyLeveled_imp_proper`). -/
def LeveledUFIFormulaOfSizePolyNAndDepthD
  (n c k d : Nat) :=
  {
      circuit : UnboundedFanInFormula //
      ufiLargestInput circuit < n
      ∧ ufiFormulaDepth circuit ≤ d
      ∧ ufiFormulaCircuitSize circuit ≤ c * n ^ k
      ∧ d > 0
      ∧ Leveling.IsProperlyLeveled circuit d
    }

/-- Bounded-fan-in formulas on inputs below `n`, of polynomial size and
    logarithmic depth. -/
def BFIFormulaOfSizeAtMostPolyNAndDepthAtMostLogCircuitSize
    (n c k depthFactor : Nat) :=
  {
    circuit : BoundedFanInFormula //
    bfiLargestInput circuit < n
      ∧ bfiFormulaDepth circuit ≤ Nat.clog 2 (c * n ^ k) * depthFactor
      ∧ bfiFormulaCircuitSize circuit ≤ c * n ^ k
  }

/-- A family of bounded-fan-in formulas with polynomial size and logarithmic
    depth, indexed by positive input lengths. -/
def NC1FormulaFamily (c k depthFactor : Nat) :=
  (n : PNat) →
    BFIFormulaOfSizeAtMostPolyNAndDepthAtMostLogCircuitSize
      n.val c k depthFactor

end Circuits
