import Formulas.Basic

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
/-! ## Circuit foundation

A more general circuit model where a Boolean circuit is a finite directed
acyclic graph. Each node (gate) carries a unique `Nat` identifier
and is one of:

* **`input`** – a primary input to the circuit (no incoming edges),
  optionally negated
* **`output`** – a primary output of the circuit (exactly one incoming edge)
* **`andGate`** – computes the conjunction of its inputs
* **`orGate`** – computes the disjunction of its inputs
* **`notGate`** – computes the negation of its single input

Edges represent wires: an edge `(src, dst)` means the output of gate
`src` feeds into gate `dst`.
-/

/-- The type of operation performed by a gate. -/
inductive GateType where
  | input (negated : Bool) : GateType
  | output : GateType
  | andGate : GateType
  | orGate : GateType
  | notGate : GateType
  deriving Repr, BEq, DecidableEq

/-- Check whether a gate type is an input (negated or non-negated). -/
def GateType.isInput : GateType → Bool
  | .input _ => true
  | _        => false

/-- A gate in a circuit, identified by a unique natural number. -/
structure Gate where
  id : Nat
  type : GateType
  deriving Repr, BEq, DecidableEq

/-- A directed edge (wire) from the output of gate `src` to an input of gate `dst`. -/
structure Edge where
  src : Nat
  dst : Nat
  deriving Repr, BEq, DecidableEq

end Circuits
