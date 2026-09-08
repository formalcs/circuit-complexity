import Mathlib.Data.PNat.Basic
import ACC.Formula.Basic

namespace Circuits.ACC.ACCFormula

/-! ## Constant-depth polynomial-size ACC formula families -/

/-- ACC formulas over fixed modulus `p`, on positive input length `n`, with
formula-tree size at most `c * n^k` and depth at most the fixed constant `d`.

Formula size is `nodeCount`: input occurrences are part of a formula's
representation and must be bounded for unbounded fan-in transformations. -/
def OfSizeAtMostPolyNAndDepthAtMostD
    (p : Nat) (n : PNat) (c k d : Nat) :=
  { formula : ACCFormula p //
    formula.WellFormed ∧
    formula.numInputs ≤ n.val ∧
    formula.depth ≤ d ∧
    formula.nodeCount ≤ c * n.val ^ k ∧
    d > 0 }

/-- A constant-depth polynomial-size ACC formula family with fixed modulus
`p`, indexed directly by positive input lengths. -/
def ACCFormulaFamily (p c k d : Nat) :=
  (n : PNat) → OfSizeAtMostPolyNAndDepthAtMostD p n c k d

end Circuits.ACC.ACCFormula
