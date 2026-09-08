import ACC.Circuit.Basic

namespace Circuits.DAG.ACCCircuit

/-- A circuit computes a target Boolean function on all lists of length `n`.

For a possibly multi-output circuit, its Boolean value is its first output,
or `false` when it has no output. -/
def ComputesAtLength (circuit : ACCCircuit) (n : ℕ)
    (target : List Bool → Bool) : Prop :=
  ∀ inputs : List Bool, inputs.length = n →
    (circuit.evalCanonical inputs).head?.getD false = target inputs

end Circuits.DAG.ACCCircuit
