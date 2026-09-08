import Mathlib.Data.PNat.Basic
import ACC.Circuit.Semantics

namespace Circuits.DAG.ACCCircuit

/-! ## Constant-depth polynomial-size ACC circuit families -/

/-- ACC circuits with fixed modulus `p`, on positive input length `n`, with
size at most `c * n^k` and depth at most the fixed constant `d`. -/
def OfSizeAtMostPolyNAndDepthAtMostD
    (p : Nat) (n : PNat) (c k d : Nat) :=
  { circuit : ACCCircuit //
    circuit.WellFormed ∧
    circuit.p = p ∧
    circuit.inputWidth = n.val ∧
    circuit.depth ≤ d ∧
    circuit.circuitSize ≤ c * n.val ^ k ∧
    d > 0 }

/-- A constant-depth polynomial-size ACC circuit family, indexed directly by
positive input lengths, with a globally fixed modulus `p`. -/
def ACCCircuitFamily (p c k d : Nat) :=
  (n : PNat) → OfSizeAtMostPolyNAndDepthAtMostD p n c k d

end Circuits.DAG.ACCCircuit

namespace Circuits

/-- An ACC circuit family recognizes `language` when its first output agrees
with membership in `language` at every positive input length. -/
def ACCRecognizes
    {p sizeCoefficient sizeExponent depthBound : Nat}
    (family : DAG.ACCCircuit.ACCCircuitFamily p sizeCoefficient sizeExponent
      depthBound)
    (language : Set (List Bool)) : Prop :=
  ∀ n : PNat, ∀ inputs : List Bool, inputs.length = n.val →
    ((((family n).val.evalCanonical inputs).head?.getD false = true) ↔
      inputs ∈ language)

/-- A language is in nonuniform `ACC[p]` when a constant-depth,
polynomial-size ACC circuit family with modulus `p` recognizes it. -/
def InACC (p : Nat) (language : Set (List Bool)) : Prop :=
  ∃ sizeCoefficient sizeExponent depthBound : Nat,
    ∃ family : DAG.ACCCircuit.ACCCircuitFamily p sizeCoefficient sizeExponent
      depthBound,
      ACCRecognizes family language

end Circuits
