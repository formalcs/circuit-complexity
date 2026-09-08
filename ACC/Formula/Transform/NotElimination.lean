import ACC.Formula.Basic

namespace Circuits.ACC.ACCFormula

/-! ## NOT-gate elimination

This module replaces each `notGate` in an `ACCFormula p` by a single-input
`modGate`. When `1 < p`, a modulo-`p` gate on one Boolean input evaluates to
true exactly when that input is false.
-/

mutual
/-- Replace every NOT gate by a single-input modulo gate. -/
def eliminateNotGates {p : Nat} : ACCFormula p → ACCFormula p
  | .input idx negated => .input idx negated
  | .constant value label => .constant value label
  | .notGate formula => .modGate [eliminateNotGates formula]
  | .andGate formulas => .andGate (eliminateNotGatesList formulas)
  | .orGate formulas => .orGate (eliminateNotGatesList formulas)
  | .modGate formulas => .modGate (eliminateNotGatesList formulas)

/-- Apply `eliminateNotGates` to a list of formulas. -/
def eliminateNotGatesList {p : Nat} :
    List (ACCFormula p) → List (ACCFormula p)
  | [] => []
  | formula :: formulas =>
      eliminateNotGates formula :: eliminateNotGatesList formulas
end

/-- An ACC formula contains no `notGate` constructor. -/
def HasNoNotGates {p : Nat} : ACCFormula p → Prop
  | .input _ _ => True
  | .constant _ _ => True
  | .notGate _ => False
  | .andGate formulas => ∀ formula ∈ formulas, HasNoNotGates formula
  | .orGate formulas => ∀ formula ∈ formulas, HasNoNotGates formula
  | .modGate formulas => ∀ formula ∈ formulas, HasNoNotGates formula

mutual
/-- The transformation removes every NOT gate. -/
theorem eliminateNotGates_hasNoNotGates {p : Nat} (formula : ACCFormula p) :
    HasNoNotGates (eliminateNotGates formula) := by
  match formula with
  | .input idx negated =>
      simp [eliminateNotGates, HasNoNotGates]
  | .constant value label =>
      simp [eliminateNotGates, HasNoNotGates]
  | .notGate child =>
      simpa [eliminateNotGates, HasNoNotGates] using
        eliminateNotGates_hasNoNotGates child
  | .andGate children =>
      simpa [eliminateNotGates, HasNoNotGates] using
        eliminateNotGatesList_hasNoNotGates children
  | .orGate children =>
      simpa [eliminateNotGates, HasNoNotGates] using
        eliminateNotGatesList_hasNoNotGates children
  | .modGate children =>
      simpa [eliminateNotGates, HasNoNotGates] using
        eliminateNotGatesList_hasNoNotGates children

/-- Every member produced by the list transformation contains no NOT gate. -/
theorem eliminateNotGatesList_hasNoNotGates {p : Nat}
    (formulas : List (ACCFormula p)) :
    ∀ formula ∈ eliminateNotGatesList formulas, HasNoNotGates formula := by
  match formulas with
  | [] => simp [eliminateNotGatesList]
  | formula :: formulas =>
      intro transformed h_transformed
      simp only [eliminateNotGatesList, List.mem_cons] at h_transformed
      rcases h_transformed with h_head | h_tail
      · subst transformed
        exact eliminateNotGates_hasNoNotGates formula
      · exact eliminateNotGatesList_hasNoNotGates formulas transformed h_tail
end

private lemma eval_modGate_singleton_eq_not {p : Nat} (hp : 1 < p)
    (formula : ACCFormula p) (inputs : List Bool) :
    eval (.modGate [formula]) inputs = !(eval formula inputs) := by
  cases h_value : eval formula inputs with
  | false => simp [eval, h_value]
  | true => simp [eval, h_value, Nat.mod_eq_of_lt hp]

mutual
/-- Replacing NOT gates by single-input modulo gates preserves evaluation
    whenever the modulus is nondegenerate. -/
theorem eliminateNotGates_eval {p : Nat} (hp : 1 < p)
    (formula : ACCFormula p) (inputs : List Bool) :
    eval (eliminateNotGates formula) inputs = eval formula inputs := by
  match formula with
  | .input idx negated =>
      simp [eliminateNotGates, eval]
  | .constant value label =>
      simp [eliminateNotGates, eval]
  | .notGate child =>
      simp only [eliminateNotGates]
      rw [eval_modGate_singleton_eq_not hp,
        eliminateNotGates_eval hp child inputs]
      simp only [eval]
  | .andGate children =>
      simp only [eliminateNotGates, eval]
      rw [eliminateNotGatesList_eval hp children inputs]
  | .orGate children =>
      simp only [eliminateNotGates, eval]
      rw [eliminateNotGatesList_eval hp children inputs]
  | .modGate children =>
      simp only [eliminateNotGates, eval]
      rw [eliminateNotGatesList_eval hp children inputs]

/-- Evaluation commutes with the list transformation. -/
theorem eliminateNotGatesList_eval {p : Nat} (hp : 1 < p)
    (formulas : List (ACCFormula p)) (inputs : List Bool) :
    (eliminateNotGatesList formulas).map (fun formula => eval formula inputs) =
      formulas.map (fun formula => eval formula inputs) := by
  match formulas with
  | [] => simp [eliminateNotGatesList]
  | formula :: formulas =>
      simp only [eliminateNotGatesList, List.map_cons]
      rw [eliminateNotGates_eval hp formula inputs,
        eliminateNotGatesList_eval hp formulas inputs]
end

mutual
/-- Replacing NOT gates by single-input modulo gates preserves circuit size. -/
theorem eliminateNotGates_circuitSize_eq {p : Nat} (formula : ACCFormula p) :
    circuitSize (eliminateNotGates formula) = circuitSize formula := by
  match formula with
  | .input idx negated =>
      simp [eliminateNotGates, circuitSize]
  | .constant value label =>
      simp [eliminateNotGates, circuitSize]
  | .notGate child =>
      simp [eliminateNotGates, circuitSize,
        eliminateNotGates_circuitSize_eq child]
  | .andGate children =>
      simp only [eliminateNotGates, circuitSize]
      rw [eliminateNotGatesList_circuitSize_map_eq children]
  | .orGate children =>
      simp only [eliminateNotGates, circuitSize]
      rw [eliminateNotGatesList_circuitSize_map_eq children]
  | .modGate children =>
      simp only [eliminateNotGates, circuitSize]
      rw [eliminateNotGatesList_circuitSize_map_eq children]

/-- The list transformation preserves every member's circuit size. -/
theorem eliminateNotGatesList_circuitSize_map_eq {p : Nat}
    (formulas : List (ACCFormula p)) :
    (eliminateNotGatesList formulas).map circuitSize =
      formulas.map circuitSize := by
  match formulas with
  | [] => simp [eliminateNotGatesList]
  | formula :: formulas =>
      simp only [eliminateNotGatesList, List.map_cons]
      rw [eliminateNotGates_circuitSize_eq formula,
        eliminateNotGatesList_circuitSize_map_eq formulas]
end

/-- Eliminating NOT gates does not increase circuit size. -/
theorem eliminateNotGates_circuitSize_le {p : Nat} (formula : ACCFormula p) :
    circuitSize (eliminateNotGates formula) ≤ circuitSize formula :=
  (eliminateNotGates_circuitSize_eq formula).le

mutual
/-- Replacing NOT gates by unary modulo gates preserves full formula-tree
size. -/
theorem eliminateNotGates_nodeCount_eq {p : Nat} (formula : ACCFormula p) :
    nodeCount (eliminateNotGates formula) = nodeCount formula := by
  match formula with
  | .input idx negated => simp [eliminateNotGates, nodeCount]
  | .constant value label => simp [eliminateNotGates, nodeCount]
  | .notGate child =>
      simp only [eliminateNotGates, nodeCount, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      rw [eliminateNotGates_nodeCount_eq child]
      omega
  | .andGate children =>
      simp only [eliminateNotGates, nodeCount]
      rw [eliminateNotGatesList_nodeCount_map_eq children]
  | .orGate children =>
      simp only [eliminateNotGates, nodeCount]
      rw [eliminateNotGatesList_nodeCount_map_eq children]
  | .modGate children =>
      simp only [eliminateNotGates, nodeCount]
      rw [eliminateNotGatesList_nodeCount_map_eq children]

/-- The list transformation preserves every member's full node count. -/
theorem eliminateNotGatesList_nodeCount_map_eq {p : Nat}
    (formulas : List (ACCFormula p)) :
    (eliminateNotGatesList formulas).map nodeCount = formulas.map nodeCount := by
  match formulas with
  | [] => simp [eliminateNotGatesList]
  | formula :: formulas =>
      simp only [eliminateNotGatesList, List.map_cons]
      rw [eliminateNotGates_nodeCount_eq formula,
        eliminateNotGatesList_nodeCount_map_eq formulas]
end

/-- NOT-gate elimination does not increase full formula-tree size. -/
theorem eliminateNotGates_nodeCount_le {p : Nat} (formula : ACCFormula p) :
    nodeCount (eliminateNotGates formula) ≤ nodeCount formula :=
  (eliminateNotGates_nodeCount_eq formula).le

mutual
/-- Replacing NOT gates by single-input modulo gates preserves depth. -/
theorem eliminateNotGates_depth_eq {p : Nat} (formula : ACCFormula p) :
    depth (eliminateNotGates formula) = depth formula := by
  match formula with
  | .input idx negated =>
      simp [eliminateNotGates, depth]
  | .constant value label =>
      simp [eliminateNotGates, depth]
  | .notGate child =>
      simp [eliminateNotGates, depth, eliminateNotGates_depth_eq child,
        Nat.add_comm]
  | .andGate children =>
      simp only [eliminateNotGates, depth]
      rw [eliminateNotGatesList_depth_map_eq children]
  | .orGate children =>
      simp only [eliminateNotGates, depth]
      rw [eliminateNotGatesList_depth_map_eq children]
  | .modGate children =>
      simp only [eliminateNotGates, depth]
      rw [eliminateNotGatesList_depth_map_eq children]

/-- The list transformation preserves every member's depth. -/
theorem eliminateNotGatesList_depth_map_eq {p : Nat}
    (formulas : List (ACCFormula p)) :
    (eliminateNotGatesList formulas).map depth = formulas.map depth := by
  match formulas with
  | [] => simp [eliminateNotGatesList]
  | formula :: formulas =>
      simp only [eliminateNotGatesList, List.map_cons]
      rw [eliminateNotGates_depth_eq formula,
        eliminateNotGatesList_depth_map_eq formulas]
end

/-- Eliminating NOT gates does not increase depth. -/
theorem eliminateNotGates_depth_le {p : Nat} (formula : ACCFormula p) :
    depth (eliminateNotGates formula) ≤ depth formula :=
  (eliminateNotGates_depth_eq formula).le

end Circuits.ACC.ACCFormula
