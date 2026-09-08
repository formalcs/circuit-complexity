import ACC.Formula.Basic

namespace Circuits.ACC.ACCFormula

/-- A formula computes a target Boolean function on all lists of length `n`. -/
def ComputesAtLength {p : ℕ} (formula : ACCFormula p) (n : ℕ)
    (target : List Bool → Bool) : Prop :=
  ∀ inputs : List Bool, inputs.length = n →
    eval formula inputs = target inputs

end Circuits.ACC.ACCFormula
