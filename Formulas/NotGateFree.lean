import Formulas.Basic

/-!
# Not-gate-free formulas

This module provides the shared predicate used by formula transformations and
the parity-leveling pipeline.
-/

namespace Circuits.Leveling
open Circuits

/-- A UFI formula contains **no `notGate` constructor** anywhere in its
    syntax tree. Negation is carried only on `inputGate` literals (the `Bool`
    flag) once this holds. -/
def HasNoNotGates : UnboundedFanInFormula → Prop
  | .inputGate _ _     => True
  | .constant _ _  => True
  | .notGate _     => False
  | .andGate gates => ∀ g ∈ gates, HasNoNotGates g
  | .orGate gates  => ∀ g ∈ gates, HasNoNotGates g

end Circuits.Leveling
