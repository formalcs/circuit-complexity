import Formulas.Basic

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

def ufiFormulaEval (c : UnboundedFanInFormula) (inputs : List Bool) : Bool :=
  match c with
  | inputGate index negated =>
      match inputs[index]? with
      | none => false
      | some input =>
          match negated with
          | true => not input
          | false => input
  | constant bit _ => bit
  | notGate gate => not (ufiFormulaEval gate inputs)
  | andGate gates =>
    match gates with
    | .nil => true
    | .cons gate other_gates =>
    match (ufiFormulaEval gate inputs) with
    | false => false
    | true => ufiFormulaEval (andGate other_gates) inputs
  | orGate gates =>
    match gates with
    | .nil => false
    | .cons gate other_gates =>
    match (ufiFormulaEval gate inputs) with
    | false => ufiFormulaEval (orGate other_gates) inputs
    | true => true

/-- Evaluate a bounded-fan-in formula on a list of input bits. Missing inputs
    evaluate to `false`, consistently with `ufiFormulaEval`. -/
def bfiFormulaEval (formula : BoundedFanInFormula) (inputs : List Bool) : Bool :=
  match formula with
  | .inputGate index negated =>
      match inputs[index]? with
      | none => false
      | some input => if negated then !input else input
  | .constant bit _ => bit
  | .notGate gate => !(bfiFormulaEval gate inputs)
  | .andGate left right =>
      if bfiFormulaEval left inputs then bfiFormulaEval right inputs else false
  | .orGate left right =>
      if bfiFormulaEval left inputs then true else bfiFormulaEval right inputs

@[simp] theorem bfiFormulaEval_input_none (index : Nat) (negated : Bool)
    (inputs : List Bool) (h : inputs[index]? = none) :
    bfiFormulaEval (.inputGate index negated) inputs = false := by
  simp [bfiFormulaEval, h]

@[simp] theorem bfiFormulaEval_input_some (index : Nat) (negated input : Bool)
    (inputs : List Bool) (h : inputs[index]? = some input) :
    bfiFormulaEval (.inputGate index negated) inputs =
      if negated then !input else input := by
  simp [bfiFormulaEval, h]

@[simp] theorem ufiFormulaEval_input_none (index : Nat) (negated : Bool)
    (inputs : List Bool) (h : inputs[index]? = none) :
    ufiFormulaEval (inputGate index negated) inputs = false := by
  unfold ufiFormulaEval
  rw [h]

@[simp] theorem ufiFormulaEval_input_some (index : Nat) (negated input : Bool)
    (inputs : List Bool) (h : inputs[index]? = some input) :
    ufiFormulaEval (inputGate index negated) inputs =
      if negated then Bool.not input else input := by
  unfold ufiFormulaEval
  rw [h]
  cases negated <;> rfl

/-- `ufiFormulaEval (andGate cs) inputs` agrees with `List.all`. -/
theorem ufi_eval_andGate_eq_all (cs : List UnboundedFanInFormula)
    (inputs : List Bool) :
    ufiFormulaEval (andGate cs) inputs =
    if (cs.map fun c => ufiFormulaEval c inputs).all (· == true)
    then true else false := by
  induction cs with
  | nil => simp [ufiFormulaEval, List.map, List.all]
  | cons hd tl ih =>
    have match_and : ∀ (b r : Bool),
        (match b with | false => false | true => r) =
        if b == true then r else false := by
      intro b r; cases b <;> rfl
    simp only [ufiFormulaEval, match_and, ih, List.map_cons, List.all_cons]
    by_cases h : (ufiFormulaEval hd inputs == true) = true <;> simp [h]

/-- `ufiFormulaEval (orGate cs) inputs` agrees with `List.any`. -/
theorem ufi_eval_orGate_eq_any (cs : List UnboundedFanInFormula)
    (inputs : List Bool) :
    ufiFormulaEval (orGate cs) inputs =
    if (cs.map fun c => ufiFormulaEval c inputs).any (· == true)
    then true else false := by
  induction cs with
  | nil => simp [ufiFormulaEval, List.map, List.any]
  | cons hd tl ih =>
    have match_or : ∀ (b r : Bool),
        (match b with | false => r | true => true) =
        if b == true then true else r := by
      intro b r; cases b <;> rfl
    simp only [ufiFormulaEval, match_or, ih, List.map_cons, List.any_cons]
    by_cases h : (ufiFormulaEval hd inputs == true) = true <;> simp [h]

end Circuits
