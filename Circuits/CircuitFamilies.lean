import «Circuits».Circuit

namespace Circuits

def UFICircuitOfSizeAtMostPolyNAndDepthAtMostD
  (n c k d : Nat) :=
  {
    circuit : Circuit //
    circuit.WellFormed
    ∧ circuit.inputWidth = n
    ∧ circuit.depth ≤ d
    ∧ circuit.circuitSize ≤ c * n ^ k
    ∧ d > 0
  }

def AC0CircuitFamily (c k d : Nat) :=
  (n : PNat) ->
    UFICircuitOfSizeAtMostPolyNAndDepthAtMostD n c k d

end Circuits
