import Mathlib.Data.List.MinMax
import ACC.Formula.Basic

namespace Circuits.ACC.ACCFormula

/-! ## AND-gate elimination

This module eliminates every `andGate` from an `ACCFormula` using De Morgan's
law. The auxiliary polarity-aware transformation avoids inserting one new NOT
gate per child of an unbounded-fan-in AND gate.
-/

mutual
/-- Transform a formula, computing its negation when `negated` is `true`,
    without producing any `andGate`s. -/
def eliminateAndGatesWithPolarity {p : Nat} (negated : Bool) :
    ACCFormula p → ACCFormula p
  | .input idx inputNegated => .input idx (Bool.xor negated inputNegated)
  | .constant value label =>
      .constant (if negated then !value else value) label
  | .notGate formula => eliminateAndGatesWithPolarity (!negated) formula
  | .andGate formulas =>
      let transformed := eliminateAndGatesList true formulas
      if negated then .orGate transformed else .notGate (.orGate transformed)
  | .orGate formulas =>
      let transformed := eliminateAndGatesList false formulas
      if negated then .notGate (.orGate transformed) else .orGate transformed
  | .modGate formulas =>
      let transformed := eliminateAndGatesList false formulas
      if negated then .notGate (.modGate transformed) else .modGate transformed

/-- Apply `eliminateAndGatesWithPolarity` to a list of formulas. -/
def eliminateAndGatesList {p : Nat} (negated : Bool) :
    List (ACCFormula p) → List (ACCFormula p)
  | [] => []
  | formula :: formulas =>
      eliminateAndGatesWithPolarity negated formula ::
        eliminateAndGatesList negated formulas
end

/-- Replace every AND gate by OR and NOT gates using De Morgan's law. -/
def eliminateAndGates {p : Nat} (formula : ACCFormula p) : ACCFormula p :=
  eliminateAndGatesWithPolarity false formula

/-- An ACC formula contains no `andGate` constructor. -/
def HasNoAndGates {p : Nat} : ACCFormula p → Prop
  | .input _ _ => True
  | .constant _ _ => True
  | .notGate formula => HasNoAndGates formula
  | .andGate _ => False
  | .orGate formulas => ∀ formula ∈ formulas, HasNoAndGates formula
  | .modGate formulas => ∀ formula ∈ formulas, HasNoAndGates formula

mutual
/-- The polarity-aware transformation never produces an AND gate. -/
theorem eliminateAndGatesWithPolarity_hasNoAndGates {p : Nat}
    (negated : Bool) (formula : ACCFormula p) :
    HasNoAndGates (eliminateAndGatesWithPolarity negated formula) := by
  match formula with
  | .input idx inputNegated =>
      simp [eliminateAndGatesWithPolarity, HasNoAndGates]
  | .constant value label =>
      simp [eliminateAndGatesWithPolarity, HasNoAndGates]
  | .notGate child =>
      simpa [eliminateAndGatesWithPolarity] using
        eliminateAndGatesWithPolarity_hasNoAndGates (!negated) child
  | .andGate children =>
      cases negated <;>
        simpa [eliminateAndGatesWithPolarity, HasNoAndGates] using
          eliminateAndGatesList_hasNoAndGates true children
  | .orGate children =>
      cases negated <;>
        simpa [eliminateAndGatesWithPolarity, HasNoAndGates] using
          eliminateAndGatesList_hasNoAndGates false children
  | .modGate children =>
      cases negated <;>
        simpa [eliminateAndGatesWithPolarity, HasNoAndGates] using
          eliminateAndGatesList_hasNoAndGates false children

/-- Every member produced by the list transformation contains no AND gate. -/
theorem eliminateAndGatesList_hasNoAndGates {p : Nat}
    (negated : Bool) (formulas : List (ACCFormula p)) :
    ∀ formula ∈ eliminateAndGatesList negated formulas, HasNoAndGates formula := by
  match formulas with
  | [] => simp [eliminateAndGatesList]
  | formula :: formulas =>
      intro transformed h_transformed
      simp only [eliminateAndGatesList, List.mem_cons] at h_transformed
      rcases h_transformed with h_head | h_tail
      · subst transformed
        exact eliminateAndGatesWithPolarity_hasNoAndGates negated formula
      · exact eliminateAndGatesList_hasNoAndGates negated formulas transformed h_tail
end

/-- `eliminateAndGates` removes every `andGate` constructor. -/
theorem eliminateAndGates_hasNoAndGates {p : Nat} (formula : ACCFormula p) :
    HasNoAndGates (eliminateAndGates formula) :=
  eliminateAndGatesWithPolarity_hasNoAndGates false formula

private lemma any_map_not_eq_not_all (values : List Bool) :
    (values.map (!·)).any (· == true) = !(values.all (· == true)) := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      cases value with
      | false => simp
      | true => simpa [Function.comp_def] using ih

mutual
/-- The polarity-aware transformation evaluates to the original formula or
    its negation, according to `negated`. -/
theorem eliminateAndGatesWithPolarity_eval {p : Nat}
    (negated : Bool) (formula : ACCFormula p) (inputs : List Bool) :
    eval (eliminateAndGatesWithPolarity negated formula) inputs =
      if negated then !(eval formula inputs) else eval formula inputs := by
  match formula with
  | .input idx inputNegated =>
      simp only [eliminateAndGatesWithPolarity, eval]
      generalize inputs[idx]?.getD false = value
      cases negated <;> cases inputNegated <;> cases value <;> rfl
  | .constant value label =>
      cases negated <;> cases value <;>
        simp [eliminateAndGatesWithPolarity, eval]
  | .notGate child =>
      simp only [eliminateAndGatesWithPolarity, eval]
      rw [eliminateAndGatesWithPolarity_eval (!negated) child inputs]
      cases negated <;> cases eval child inputs <;> rfl
  | .andGate children =>
      have h_values := any_map_not_eq_not_all (children.map (fun child => eval child inputs))
      simp only [List.map_map, Function.comp_def] at h_values
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false, eval]
          rw [eliminateAndGatesList_eval true children inputs]
          simp only [if_true]
          rw [h_values]
          cases (children.map (fun child => eval child inputs)).all (· == true) <;> rfl
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, eval]
          rw [eliminateAndGatesList_eval true children inputs]
          simp only [if_true]
          rw [h_values]
          cases (children.map (fun child => eval child inputs)).all (· == true) <;> rfl
  | .orGate children =>
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false, eval]
          rw [eliminateAndGatesList_eval false children inputs]
          simp
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, eval]
          rw [eliminateAndGatesList_eval false children inputs]
          simp
  | .modGate children =>
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false, eval]
          rw [eliminateAndGatesList_eval false children inputs]
          simp
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, eval]
          rw [eliminateAndGatesList_eval false children inputs]
          simp

/-- Evaluation commutes with the list transformation. -/
theorem eliminateAndGatesList_eval {p : Nat}
    (negated : Bool) (formulas : List (ACCFormula p)) (inputs : List Bool) :
    (eliminateAndGatesList negated formulas).map (fun formula => eval formula inputs) =
      formulas.map (fun formula =>
        if negated then !(eval formula inputs) else eval formula inputs) := by
  match formulas with
  | [] => simp [eliminateAndGatesList]
  | formula :: formulas =>
      simp only [eliminateAndGatesList, List.map_cons]
      rw [eliminateAndGatesWithPolarity_eval negated formula inputs,
        eliminateAndGatesList_eval negated formulas inputs]
end

/-- Eliminating AND gates preserves evaluation. -/
theorem eliminateAndGates_eval {p : Nat}
    (formula : ACCFormula p) (inputs : List Bool) :
    eval (eliminateAndGates formula) inputs = eval formula inputs := by
  simpa [eliminateAndGates] using
    eliminateAndGatesWithPolarity_eval false formula inputs

mutual
/-- The polarity-aware transformation increases circuit size by at most a
    factor of two. -/
theorem eliminateAndGatesWithPolarity_circuitSize_le {p : Nat}
    (negated : Bool) (formula : ACCFormula p) :
    circuitSize (eliminateAndGatesWithPolarity negated formula) ≤
      2 * circuitSize formula := by
  match formula with
  | .input idx inputNegated =>
      cases negated <;>
        simp [eliminateAndGatesWithPolarity, circuitSize]
  | .constant value label =>
      cases negated <;>
        simp [eliminateAndGatesWithPolarity, circuitSize]
  | .notGate child =>
      simp only [eliminateAndGatesWithPolarity, circuitSize]
      exact Nat.le_trans
        (eliminateAndGatesWithPolarity_circuitSize_le (!negated) child) (by omega)
  | .andGate children =>
      have h_children := eliminateAndGatesList_circuitSize_le true children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false,
            circuitSize]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, circuitSize]
          omega
  | .orGate children =>
      have h_children := eliminateAndGatesList_circuitSize_le false children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false,
            circuitSize]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, circuitSize]
          omega
  | .modGate children =>
      have h_children := eliminateAndGatesList_circuitSize_le false children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false,
            circuitSize]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, circuitSize]
          omega

/-- The sum of circuit sizes grows by at most a factor of two under the list
    transformation. -/
theorem eliminateAndGatesList_circuitSize_le {p : Nat}
    (negated : Bool) (formulas : List (ACCFormula p)) :
    ((eliminateAndGatesList negated formulas).map circuitSize).sum ≤
      2 * (formulas.map circuitSize).sum := by
  match formulas with
  | [] => simp [eliminateAndGatesList]
  | formula :: formulas =>
      simp only [eliminateAndGatesList, List.map_cons, List.sum_cons]
      have h_formula := eliminateAndGatesWithPolarity_circuitSize_le negated formula
      have h_formulas := eliminateAndGatesList_circuitSize_le negated formulas
      omega
end

/-- Eliminating AND gates increases circuit size by at most a factor of two. -/
theorem eliminateAndGates_circuitSize_le {p : Nat} (formula : ACCFormula p) :
    circuitSize (eliminateAndGates formula) ≤ 2 * circuitSize formula := by
  simpa [eliminateAndGates] using
    eliminateAndGatesWithPolarity_circuitSize_le false formula

mutual
/-- The polarity-aware transformation increases full formula-tree size by at
most a factor of two. -/
theorem eliminateAndGatesWithPolarity_nodeCount_le {p : Nat}
    (negated : Bool) (formula : ACCFormula p) :
    nodeCount (eliminateAndGatesWithPolarity negated formula) ≤
      2 * nodeCount formula := by
  match formula with
  | .input idx inputNegated =>
      cases negated <;> simp [eliminateAndGatesWithPolarity, nodeCount]
  | .constant value label =>
      cases negated <;> simp [eliminateAndGatesWithPolarity, nodeCount]
  | .notGate child =>
      simp only [eliminateAndGatesWithPolarity, nodeCount]
      exact Nat.le_trans
        (eliminateAndGatesWithPolarity_nodeCount_le (!negated) child) (by omega)
  | .andGate children =>
      have h_children := eliminateAndGatesList_nodeCount_le true children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true,
            if_false, nodeCount]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, nodeCount]
          omega
  | .orGate children =>
      have h_children := eliminateAndGatesList_nodeCount_le false children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true,
            if_false, nodeCount]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, nodeCount]
          omega
  | .modGate children =>
      have h_children := eliminateAndGatesList_nodeCount_le false children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true,
            if_false, nodeCount]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, nodeCount]
          omega

/-- The sum of full node counts grows by at most a factor of two under the
list transformation. -/
theorem eliminateAndGatesList_nodeCount_le {p : Nat}
    (negated : Bool) (formulas : List (ACCFormula p)) :
    ((eliminateAndGatesList negated formulas).map nodeCount).sum ≤
      2 * (formulas.map nodeCount).sum := by
  match formulas with
  | [] => simp [eliminateAndGatesList]
  | formula :: formulas =>
      simp only [eliminateAndGatesList, List.map_cons, List.sum_cons]
      have h_formula := eliminateAndGatesWithPolarity_nodeCount_le negated formula
      have h_formulas := eliminateAndGatesList_nodeCount_le negated formulas
      omega
end

/-- Eliminating AND gates increases full formula-tree size by at most a
factor of two. -/
theorem eliminateAndGates_nodeCount_le {p : Nat} (formula : ACCFormula p) :
    nodeCount (eliminateAndGates formula) ≤ 2 * nodeCount formula := by
  simpa [eliminateAndGates] using
    eliminateAndGatesWithPolarity_nodeCount_le false formula

private lemma max?_getD_cons (value : Nat) (values : List Nat) :
    (value :: values).max?.getD 0 = max value (values.max?.getD 0) := by
  cases h_maximum : values.max? with
  | none =>
      have h_nil : values = [] := List.max?_eq_none_iff.mp h_maximum
      subst values
      simp
  | some maximum =>
      have h_properties := List.max?_eq_some_iff.mp h_maximum
      have h_cons : (value :: values).max? = some (max value maximum) := by
        apply List.max?_eq_some_iff.mpr
        constructor
        · by_cases h_le : value ≤ maximum
          · rw [max_eq_right h_le]
            exact List.mem_cons_of_mem value h_properties.1
          · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h_le))]
            exact List.mem_cons_self
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Nat.le_max_left _ _
          · exact Nat.le_trans (h_properties.2 x hx) (Nat.le_max_right _ _)
      rw [h_cons]
      simp only [Option.getD_some]

mutual
/-- The polarity-aware transformation increases depth by at most a factor of
    two. -/
theorem eliminateAndGatesWithPolarity_depth_le {p : Nat}
    (negated : Bool) (formula : ACCFormula p) :
    depth (eliminateAndGatesWithPolarity negated formula) ≤ 2 * depth formula := by
  match formula with
  | .input idx inputNegated =>
      cases negated <;>
        simp [eliminateAndGatesWithPolarity, depth]
  | .constant value label =>
      cases negated <;>
        simp [eliminateAndGatesWithPolarity, depth]
  | .notGate child =>
      simp only [eliminateAndGatesWithPolarity, depth]
      exact Nat.le_trans
        (eliminateAndGatesWithPolarity_depth_le (!negated) child) (by omega)
  | .andGate children =>
      have h_children := eliminateAndGatesList_depth_le true children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false, depth]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, depth]
          omega
  | .orGate children =>
      have h_children := eliminateAndGatesList_depth_le false children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false, depth]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, depth]
          omega
  | .modGate children =>
      have h_children := eliminateAndGatesList_depth_le false children
      cases negated with
      | false =>
          simp only [eliminateAndGatesWithPolarity, Bool.false_eq_true, if_false, depth]
          omega
      | true =>
          simp only [eliminateAndGatesWithPolarity, if_true, depth]
          omega

/-- The maximum depth of a transformed formula list increases by at most a
    factor of two. -/
theorem eliminateAndGatesList_depth_le {p : Nat}
    (negated : Bool) (formulas : List (ACCFormula p)) :
    ((eliminateAndGatesList negated formulas).map depth).max?.getD 0 ≤
      2 * (formulas.map depth).max?.getD 0 := by
  match formulas with
  | [] => simp [eliminateAndGatesList]
  | formula :: formulas =>
      simp only [eliminateAndGatesList, List.map_cons, max?_getD_cons]
      have h_formula := eliminateAndGatesWithPolarity_depth_le negated formula
      have h_formulas := eliminateAndGatesList_depth_le negated formulas
      apply max_le
      · exact Nat.le_trans h_formula
          (Nat.mul_le_mul_left 2 (Nat.le_max_left _ _))
      · exact Nat.le_trans h_formulas
          (Nat.mul_le_mul_left 2 (Nat.le_max_right _ _))
end

/-- Eliminating AND gates increases depth by at most a factor of two. -/
theorem eliminateAndGates_depth_le {p : Nat} (formula : ACCFormula p) :
    depth (eliminateAndGates formula) ≤ 2 * depth formula := by
  simpa [eliminateAndGates] using
    eliminateAndGatesWithPolarity_depth_le false formula

end Circuits.ACC.ACCFormula
