import ACC.Formula.Probabilistic.Basic

namespace Circuits.ACC.ProbabilisticACCFormula

/-! ## Merging connected AND gates

Conjunction is associative, including the empty and singleton cases used by
`ProbabilisticACCFormula.eval`.  Hence an AND gate occurring directly below
another AND gate can be removed by splicing its children into the parent.

`mergeConnectedAndGates` performs this operation throughout a probabilistic
ACC formula.  It first recursively normalizes all children and then flattens
the child list of every AND gate.  The transformation neither inspects nor
changes input tags, so its equivalence theorem is pointwise in both external
inputs and random bits.
-/

/-- Replace one child of an outer AND gate by the list that should be spliced
into the parent.  An AND child contributes its own children; every other
formula contributes a singleton list containing itself. -/
def mergeAndChild {p : Nat} :
    ProbabilisticACCFormula p → List (ProbabilisticACCFormula p)
  | .andGate formulas => formulas
  | formula => [formula]

mutual

/-- Recursively merge every pair of directly connected AND gates. -/
def mergeConnectedAndGates {p : Nat} :
    ProbabilisticACCFormula p → ProbabilisticACCFormula p
  | .input inputRef negated => .input inputRef negated
  | .constant value label => .constant value label
  | .notGate formula => .notGate (mergeConnectedAndGates formula)
  | .andGate formulas =>
      .andGate ((mergeConnectedAndGatesList formulas).flatMap mergeAndChild)
  | .orGate formulas => .orGate (mergeConnectedAndGatesList formulas)
  | .modGate formulas => .modGate (mergeConnectedAndGatesList formulas)

/-- Apply `mergeConnectedAndGates` to every formula in a list. -/
def mergeConnectedAndGatesList {p : Nat} :
    List (ProbabilisticACCFormula p) → List (ProbabilisticACCFormula p)
  | [] => []
  | formula :: formulas =>
      mergeConnectedAndGates formula :: mergeConnectedAndGatesList formulas

end

/-- A formula is not itself an AND gate. -/
def IsNotAndGate {p : Nat} : ProbabilisticACCFormula p → Prop
  | .andGate _ => False
  | _ => True

/-- No AND gate in the formula has an AND gate as a direct child. -/
def HasNoConnectedAndGates {p : Nat} : ProbabilisticACCFormula p → Prop
  | .input _ _ => True
  | .constant _ _ => True
  | .notGate formula => HasNoConnectedAndGates formula
  | .andGate formulas =>
      (∀ formula ∈ formulas, IsNotAndGate formula) ∧
        ∀ formula ∈ formulas, HasNoConnectedAndGates formula
  | .orGate formulas =>
      ∀ formula ∈ formulas, HasNoConnectedAndGates formula
  | .modGate formulas =>
      ∀ formula ∈ formulas, HasNoConnectedAndGates formula

/-- Splicing one AND child preserves the conjunction contributed to its
parent. -/
theorem mergeAndChild_eval_all {p : Nat}
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool) :
    ((mergeAndChild formula).map fun child =>
      eval child inputs randomBits).all (· == true) =
      eval formula inputs randomBits := by
  cases formula with
  | andGate formulas =>
      induction formulas with
      | nil => simp [mergeAndChild, eval]
      | cons formula formulas ih =>
          cases h_formula : eval formula inputs randomBits with
          | false => simp [mergeAndChild, eval, h_formula]
          | true => simpa [mergeAndChild, eval, h_formula] using ih
  | input inputRef negated => simp [mergeAndChild]
  | constant value label => simp [mergeAndChild]
  | notGate formula => simp [mergeAndChild]
  | orGate formulas => simp [mergeAndChild]
  | modGate formulas => simp [mergeAndChild]

/-- Splicing all direct AND children preserves the conjunction of the entire
child list. -/
theorem mergeAndChildren_eval_all {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    (((formulas.flatMap mergeAndChild).map fun formula =>
      eval formula inputs randomBits).all (· == true)) =
      ((formulas.map fun formula =>
        eval formula inputs randomBits).all (· == true)) := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      rw [List.flatMap_cons, List.map_append, List.all_append,
        mergeAndChild_eval_all, ih]
      simp

mutual

/-- Merging connected AND gates preserves evaluation. -/
theorem mergeConnectedAndGates_eval {p : Nat}
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool) :
    eval (mergeConnectedAndGates formula) inputs randomBits =
      eval formula inputs randomBits := by
  match formula with
  | .input inputRef negated => rfl
  | .constant value label => rfl
  | .notGate formula =>
      simp only [mergeConnectedAndGates, eval]
      rw [mergeConnectedAndGates_eval]
  | .andGate formulas =>
      simp only [mergeConnectedAndGates, eval]
      rw [mergeAndChildren_eval_all, mergeConnectedAndGatesList_eval]
  | .orGate formulas =>
      simp only [mergeConnectedAndGates, eval]
      rw [mergeConnectedAndGatesList_eval]
  | .modGate formulas =>
      simp only [mergeConnectedAndGates, eval]
      rw [mergeConnectedAndGatesList_eval]

/-- List form of `mergeConnectedAndGates_eval`. -/
theorem mergeConnectedAndGatesList_eval {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    (mergeConnectedAndGatesList formulas).map
        (fun formula => eval formula inputs randomBits) =
      formulas.map (fun formula => eval formula inputs randomBits) := by
  match formulas with
  | [] => rfl
  | formula :: formulas =>
      simp only [mergeConnectedAndGatesList, List.map_cons]
      rw [mergeConnectedAndGates_eval,
        mergeConnectedAndGatesList_eval]

end

/-- Merging connected AND gates preserves error probability. -/
theorem mergeConnectedAndGates_errorProbability_eq {p : Nat}
    (formula : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (inputs : List Bool) (expected : Bool) :
    errorProbability (mergeConnectedAndGates formula) randomBitCount
        inputs expected =
      errorProbability formula randomBitCount inputs expected := by
  apply errorProbability_congr
  intro randomBits
  exact mergeConnectedAndGates_eval formula inputs randomBits

private theorem mergeAndChild_isNotAndGate {p : Nat}
    (formula : ProbabilisticACCFormula p)
    (h_formula : HasNoConnectedAndGates formula) :
    ∀ output ∈ mergeAndChild formula, IsNotAndGate output := by
  cases formula with
  | input inputRef negated => simp [mergeAndChild, IsNotAndGate]
  | constant value label => simp [mergeAndChild, IsNotAndGate]
  | notGate formula => simp [mergeAndChild, IsNotAndGate]
  | orGate formulas => simp [mergeAndChild, IsNotAndGate]
  | modGate formulas => simp [mergeAndChild, IsNotAndGate]
  | andGate formulas =>
      have h_formula' :
          (∀ child ∈ formulas, IsNotAndGate child) ∧
            ∀ child ∈ formulas, HasNoConnectedAndGates child := by
        simpa only [HasNoConnectedAndGates] using h_formula
      simpa [mergeAndChild] using h_formula'.1

private theorem mergeAndChild_hasNoConnectedAndGates {p : Nat}
    (formula : ProbabilisticACCFormula p)
    (h_formula : HasNoConnectedAndGates formula) :
    ∀ output ∈ mergeAndChild formula, HasNoConnectedAndGates output := by
  cases formula with
  | input inputRef negated => simpa [mergeAndChild] using h_formula
  | constant value label => simpa [mergeAndChild] using h_formula
  | notGate formula => simpa [mergeAndChild] using h_formula
  | orGate formulas => simpa [mergeAndChild] using h_formula
  | modGate formulas => simpa [mergeAndChild] using h_formula
  | andGate formulas =>
      have h_formula' :
          (∀ child ∈ formulas, IsNotAndGate child) ∧
            ∀ child ∈ formulas, HasNoConnectedAndGates child := by
        simpa only [HasNoConnectedAndGates] using h_formula
      simpa [mergeAndChild] using h_formula'.2

mutual

/-- The recursive transformation removes every direct edge between two AND
gates. -/
theorem mergeConnectedAndGates_hasNoConnectedAndGates {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    HasNoConnectedAndGates (mergeConnectedAndGates formula) := by
  match formula with
  | .input inputRef negated =>
      simp [mergeConnectedAndGates, HasNoConnectedAndGates]
  | .constant value label =>
      simp [mergeConnectedAndGates, HasNoConnectedAndGates]
  | .notGate formula =>
      simpa [mergeConnectedAndGates, HasNoConnectedAndGates] using
        mergeConnectedAndGates_hasNoConnectedAndGates formula
  | .andGate formulas =>
      simp only [mergeConnectedAndGates, HasNoConnectedAndGates]
      have h_children :=
        mergeConnectedAndGatesList_hasNoConnectedAndGates formulas
      constructor
      · intro output h_output
        obtain ⟨formula, h_formula, h_output⟩ :=
          List.mem_flatMap.mp h_output
        exact mergeAndChild_isNotAndGate formula
          (h_children formula h_formula) output h_output
      · intro output h_output
        obtain ⟨formula, h_formula, h_output⟩ :=
          List.mem_flatMap.mp h_output
        exact mergeAndChild_hasNoConnectedAndGates formula
          (h_children formula h_formula) output h_output
  | .orGate formulas =>
      simpa [mergeConnectedAndGates, HasNoConnectedAndGates] using
        mergeConnectedAndGatesList_hasNoConnectedAndGates formulas
  | .modGate formulas =>
      simpa [mergeConnectedAndGates, HasNoConnectedAndGates] using
        mergeConnectedAndGatesList_hasNoConnectedAndGates formulas

/-- Every result in a recursively transformed list has no connected AND
gates. -/
theorem mergeConnectedAndGatesList_hasNoConnectedAndGates {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    ∀ formula ∈ mergeConnectedAndGatesList formulas,
      HasNoConnectedAndGates formula := by
  match formulas with
  | [] => simp [mergeConnectedAndGatesList]
  | formula :: formulas =>
      intro output h_output
      simp only [mergeConnectedAndGatesList, List.mem_cons] at h_output
      rcases h_output with rfl | h_output
      · exact mergeConnectedAndGates_hasNoConnectedAndGates formula
      · exact mergeConnectedAndGatesList_hasNoConnectedAndGates formulas
          output h_output

end

/-- Splicing one AND child into its parent does not increase the sum of
circuit sizes contributed by that child. -/
theorem mergeAndChild_circuitSize_sum_le {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    ((mergeAndChild formula).map circuitSize).sum ≤ circuitSize formula := by
  cases formula <;> simp [mergeAndChild, circuitSize]

/-- Flattening all direct AND children does not increase their aggregate
circuit size. -/
theorem mergeAndChildren_circuitSize_sum_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    (((formulas.flatMap mergeAndChild).map circuitSize).sum) ≤
      (formulas.map circuitSize).sum := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (mergeAndChild_circuitSize_sum_le formula) ih

mutual

/-- Merging connected AND gates does not increase circuit size.  Equality is
not expected when an AND-to-AND edge is actually removed. -/
theorem mergeConnectedAndGates_circuitSize_le {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    circuitSize (mergeConnectedAndGates formula) ≤ circuitSize formula := by
  match formula with
  | .input inputRef negated =>
      simp [mergeConnectedAndGates, circuitSize]
  | .constant value label =>
      simp [mergeConnectedAndGates, circuitSize]
  | .notGate formula =>
      simp only [mergeConnectedAndGates, circuitSize]
      exact Nat.add_le_add_right
        (mergeConnectedAndGates_circuitSize_le formula) 1
  | .andGate formulas =>
      simp only [mergeConnectedAndGates, circuitSize]
      exact Nat.add_le_add_right
        ((mergeAndChildren_circuitSize_sum_le
          (mergeConnectedAndGatesList formulas)).trans
            (mergeConnectedAndGatesList_circuitSize_sum_le formulas)) 1
  | .orGate formulas =>
      simp only [mergeConnectedAndGates, circuitSize]
      exact Nat.add_le_add_right
        (mergeConnectedAndGatesList_circuitSize_sum_le formulas) 1
  | .modGate formulas =>
      simp only [mergeConnectedAndGates, circuitSize]
      exact Nat.add_le_add_right
        (mergeConnectedAndGatesList_circuitSize_sum_le formulas) 1

/-- The aggregate circuit size of a recursively transformed formula list
does not increase. -/
theorem mergeConnectedAndGatesList_circuitSize_sum_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    ((mergeConnectedAndGatesList formulas).map circuitSize).sum ≤
      (formulas.map circuitSize).sum := by
  match formulas with
  | [] => simp [mergeConnectedAndGatesList]
  | formula :: formulas =>
      simp only [mergeConnectedAndGatesList, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (mergeConnectedAndGates_circuitSize_le formula)
        (mergeConnectedAndGatesList_circuitSize_sum_le formulas)

end

private theorem max?_getD_cons (value : Nat) (values : List Nat) :
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
        · intro x h_x
          rcases List.mem_cons.mp h_x with rfl | h_x
          · exact Nat.le_max_left _ _
          · exact Nat.le_trans (h_properties.2 x h_x)
              (Nat.le_max_right _ _)
      rw [h_cons]
      simp only [Option.getD_some]

private theorem max?_getD_append (left right : List Nat) :
    (left ++ right).max?.getD 0 =
      max (left.max?.getD 0) (right.max?.getD 0) := by
  induction left with
  | nil => simp
  | cons value values ih =>
      simp only [List.cons_append, max?_getD_cons, ih]
      omega

/-- Splicing one AND child into its parent does not increase the maximum
depth contributed by that child. -/
theorem mergeAndChild_depth_max_le {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    ((mergeAndChild formula).map depth).max?.getD 0 ≤ depth formula := by
  cases formula <;> simp [mergeAndChild, depth]

/-- Flattening all direct AND children does not increase their maximum
depth. -/
theorem mergeAndChildren_depth_max_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    (((formulas.flatMap mergeAndChild).map depth).max?.getD 0) ≤
      (formulas.map depth).max?.getD 0 := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      rw [List.flatMap_cons, List.map_append, max?_getD_append,
        List.map_cons, max?_getD_cons]
      apply max_le
      · exact Nat.le_trans (mergeAndChild_depth_max_le formula)
          (Nat.le_max_left _ _)
      · exact Nat.le_trans ih (Nat.le_max_right _ _)

mutual

/-- Merging connected AND gates does not increase formula depth.  The
inequality can be strict when a longest path contains connected AND gates. -/
theorem mergeConnectedAndGates_depth_le {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    depth (mergeConnectedAndGates formula) ≤ depth formula := by
  match formula with
  | .input inputRef negated =>
      simp [mergeConnectedAndGates, depth]
  | .constant value label =>
      simp [mergeConnectedAndGates, depth]
  | .notGate formula =>
      simp only [mergeConnectedAndGates, depth]
      exact Nat.add_le_add_right (mergeConnectedAndGates_depth_le formula) 1
  | .andGate formulas =>
      simp only [mergeConnectedAndGates, depth]
      exact Nat.add_le_add_left
        ((mergeAndChildren_depth_max_le
          (mergeConnectedAndGatesList formulas)).trans
            (mergeConnectedAndGatesList_depth_max_le formulas)) 1
  | .orGate formulas =>
      simp only [mergeConnectedAndGates, depth]
      exact Nat.add_le_add_left
        (mergeConnectedAndGatesList_depth_max_le formulas) 1
  | .modGate formulas =>
      simp only [mergeConnectedAndGates, depth]
      exact Nat.add_le_add_left
        (mergeConnectedAndGatesList_depth_max_le formulas) 1

/-- The maximum depth of a recursively transformed formula list does not
increase. -/
theorem mergeConnectedAndGatesList_depth_max_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    ((mergeConnectedAndGatesList formulas).map depth).max?.getD 0 ≤
      (formulas.map depth).max?.getD 0 := by
  match formulas with
  | [] => simp [mergeConnectedAndGatesList]
  | formula :: formulas =>
      simp only [mergeConnectedAndGatesList, List.map_cons, max?_getD_cons]
      apply max_le
      · exact Nat.le_trans (mergeConnectedAndGates_depth_le formula)
          (Nat.le_max_left _ _)
      · exact Nat.le_trans
          (mergeConnectedAndGatesList_depth_max_le formulas)
          (Nat.le_max_right _ _)

end

end Circuits.ACC.ProbabilisticACCFormula
