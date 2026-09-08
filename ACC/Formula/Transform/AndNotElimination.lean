import ACC.Formula.Transform.AndElimination
import ACC.Formula.Transform.NotElimination

namespace Circuits.ACC.ACCFormula

/-! ## AND- and NOT-gate elimination

Eliminating AND gates first and NOT gates second leaves only OR and modulo
gates as internal nodes. Input and constant leaves remain unchanged.
-/

/-- Eliminate AND gates using De Morgan's law, then replace all resulting
    NOT gates by single-input modulo gates. -/
def eliminateAndNotGates {p : Nat} (formula : ACCFormula p) : ACCFormula p :=
  eliminateNotGates (eliminateAndGates formula)

/-- Every internal node of an ACC formula is either an OR gate or a modulo
    gate. -/
def HasOnlyOrAndModGates {p : Nat} (formula : ACCFormula p) : Prop :=
  HasNoAndGates formula ∧ HasNoNotGates formula

mutual
/-- NOT-gate elimination preserves the absence of AND gates. -/
theorem eliminateNotGates_hasNoAndGates_of_hasNoAndGates {p : Nat}
    (formula : ACCFormula p) (h_formula : HasNoAndGates formula) :
    HasNoAndGates (eliminateNotGates formula) := by
  match formula with
  | .input idx negated =>
      simp [eliminateNotGates, HasNoAndGates]
  | .constant value label =>
      simp [eliminateNotGates, HasNoAndGates]
  | .notGate child =>
      simpa [eliminateNotGates, HasNoAndGates] using
        eliminateNotGates_hasNoAndGates_of_hasNoAndGates child
          (by simpa [HasNoAndGates] using h_formula)
  | .andGate children =>
      simp [HasNoAndGates] at h_formula
  | .orGate children =>
      simpa [eliminateNotGates, HasNoAndGates] using
        eliminateNotGatesList_hasNoAndGates_of_hasNoAndGates children
          (by simpa [HasNoAndGates] using h_formula)
  | .modGate children =>
      simpa [eliminateNotGates, HasNoAndGates] using
        eliminateNotGatesList_hasNoAndGates_of_hasNoAndGates children
          (by simpa [HasNoAndGates] using h_formula)

/-- Pointwise NOT-gate elimination preserves the absence of AND gates in a
    list of formulas. -/
theorem eliminateNotGatesList_hasNoAndGates_of_hasNoAndGates {p : Nat}
    (formulas : List (ACCFormula p))
    (h_formulas : ∀ formula ∈ formulas, HasNoAndGates formula) :
    ∀ formula ∈ eliminateNotGatesList formulas, HasNoAndGates formula := by
  match formulas with
  | [] => simp [eliminateNotGatesList]
  | formula :: formulas =>
      intro transformed h_transformed
      simp only [eliminateNotGatesList, List.mem_cons] at h_transformed
      rcases h_transformed with h_head | h_tail
      · subst transformed
        apply eliminateNotGates_hasNoAndGates_of_hasNoAndGates
        exact h_formulas formula (by simp)
      · apply eliminateNotGatesList_hasNoAndGates_of_hasNoAndGates formulas
          (formula := transformed)
        · intro child h_child
          exact h_formulas child (by simp [h_child])
        · exact h_tail
end

/-- Composing AND-gate and NOT-gate elimination produces a formula whose
    internal nodes are only OR and modulo gates. -/
theorem eliminateAndNotGates_hasOnlyOrAndModGates {p : Nat}
    (formula : ACCFormula p) :
    HasOnlyOrAndModGates (eliminateAndNotGates formula) := by
  constructor
  · exact eliminateNotGates_hasNoAndGates_of_hasNoAndGates
      (eliminateAndGates formula) (eliminateAndGates_hasNoAndGates formula)
  · exact eliminateNotGates_hasNoNotGates (eliminateAndGates formula)

/-- The composed transformation preserves evaluation for nondegenerate
    moduli. -/
theorem eliminateAndNotGates_eval {p : Nat} (hp : 1 < p)
    (formula : ACCFormula p) (inputs : List Bool) :
    eval (eliminateAndNotGates formula) inputs = eval formula inputs := by
  calc
    eval (eliminateAndNotGates formula) inputs =
        eval (eliminateAndGates formula) inputs := by
      exact eliminateNotGates_eval hp (eliminateAndGates formula) inputs
    _ = eval formula inputs := eliminateAndGates_eval formula inputs

/-- The composed transformation increases circuit size by at most a factor
    of two. -/
theorem eliminateAndNotGates_circuitSize_le {p : Nat}
    (formula : ACCFormula p) :
    circuitSize (eliminateAndNotGates formula) ≤ 2 * circuitSize formula := by
  rw [eliminateAndNotGates, eliminateNotGates_circuitSize_eq]
  exact eliminateAndGates_circuitSize_le formula

/-- The composed transformation increases full formula-tree size by at most
a factor of two. -/
theorem eliminateAndNotGates_nodeCount_le {p : Nat}
    (formula : ACCFormula p) :
    nodeCount (eliminateAndNotGates formula) ≤ 2 * nodeCount formula := by
  rw [eliminateAndNotGates, eliminateNotGates_nodeCount_eq]
  exact eliminateAndGates_nodeCount_le formula

/-- The composed transformation increases depth by at most a factor of two. -/
theorem eliminateAndNotGates_depth_le {p : Nat} (formula : ACCFormula p) :
    depth (eliminateAndNotGates formula) ≤ 2 * depth formula := by
  rw [eliminateAndNotGates, eliminateNotGates_depth_eq]
  exact eliminateAndGates_depth_le formula

end Circuits.ACC.ACCFormula
