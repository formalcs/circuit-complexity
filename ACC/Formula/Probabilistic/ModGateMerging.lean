import ACC.Formula.Probabilistic.AndModSwap

namespace Circuits.ACC.ProbabilisticACCFormula

/-! ## Merging connected modulo gates

A modulo gate whose child is another modulo gate contains the Boolean
zero-indicator of an inner sum as one term of its outer sum.  For prime `p`,
Fermat's little theorem rewrites that indicator as

```text
MOD_p(F₁, …, Fₘ) = 1 - (F₁ + ⋯ + Fₘ)^(p - 1)  in ZMod p.
```

`mergeModChild` implements this identity syntactically.  The constant `1` is
an empty AND gate, which evaluates to true.  The power is expanded into
ordered tuples by `powerTuples`; every tuple becomes an AND gate.  Finally,
`p - 1` copies of every monomial encode the negative coefficient modulo `p`.

`mergeConnectedModGates` first normalizes every subtree and then applies this
replacement to every modulo child of a modulo gate.  Consequently its result
has no edge directly connecting two modulo gates.  The construction is
deterministic and introduces no random inputs; its equivalence theorem is
pointwise in the existing external and random assignments.
-/

/-- Replace one child of an outer modulo gate.

Non-modulo children remain unchanged.  A modulo child is replaced by the
expanded input list for `1 - x^(p - 1)`: one empty AND gate followed by
`p - 1` copies of every degree-`p - 1` AND monomial. -/
def mergeModChild {p : Nat} :
    ProbabilisticACCFormula p → List (ProbabilisticACCFormula p)
  | .modGate formulas =>
      .andGate [] ::
        (List.replicate (p - 1)
          ((powerTuples formulas (p - 1)).map .andGate)).flatten
  | formula => [formula]

mutual

/-- Recursively merge every pair of directly connected modulo gates. -/
def mergeConnectedModGates {p : Nat} :
    ProbabilisticACCFormula p → ProbabilisticACCFormula p
  | .input inputRef negated => .input inputRef negated
  | .constant value label => .constant value label
  | .notGate formula => .notGate (mergeConnectedModGates formula)
  | .andGate formulas => .andGate (mergeConnectedModGatesList formulas)
  | .orGate formulas => .orGate (mergeConnectedModGatesList formulas)
  | .modGate formulas =>
      .modGate ((mergeConnectedModGatesList formulas).flatMap mergeModChild)

/-- Apply `mergeConnectedModGates` to every formula in a list. -/
def mergeConnectedModGatesList {p : Nat} :
    List (ProbabilisticACCFormula p) → List (ProbabilisticACCFormula p)
  | [] => []
  | formula :: formulas =>
      mergeConnectedModGates formula :: mergeConnectedModGatesList formulas

end

/-- A formula is not itself a modulo gate. -/
def IsNotModGate {p : Nat} : ProbabilisticACCFormula p → Prop
  | .modGate _ => False
  | _ => True

/-- No modulo gate in the formula has a modulo gate as a direct child. -/
def HasNoConnectedModGates {p : Nat} : ProbabilisticACCFormula p → Prop
  | .input _ _ => True
  | .constant _ _ => True
  | .notGate formula => HasNoConnectedModGates formula
  | .andGate formulas =>
      ∀ formula ∈ formulas, HasNoConnectedModGates formula
  | .orGate formulas =>
      ∀ formula ∈ formulas, HasNoConnectedModGates formula
  | .modGate formulas =>
      (∀ formula ∈ formulas, IsNotModGate formula) ∧
        ∀ formula ∈ formulas, HasNoConnectedModGates formula

private theorem mapSum_replicateFlatten {α R : Type} [AddCommMonoid R]
    (value : α → R) (count : Nat) (values : List α) :
    ((List.replicate count values).flatten.map value).sum =
      count • (values.map value).sum := by
  induction count with
  | zero => simp
  | succ count ih => simp

/-- Replacing one modulo child preserves its contribution to the sum of the
outer modulo gate. -/
theorem mergeModChild_eval_sum {p : Nat} (hp : p.Prime)
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool) :
    ((mergeModChild formula).map fun child =>
      ((eval child inputs randomBits).toNat : ZMod p)).sum =
      ((eval formula inputs randomBits).toNat : ZMod p) := by
  cases formula with
  | modGate formulas =>
      have h_coefficient : ((p - 1 : Nat) : ZMod p) = -1 := by
        rw [Nat.cast_sub hp.one_le]
        simp
      simp only [mergeModChild, List.map_cons, List.sum_cons]
      rw [mapSum_replicateFlatten, nsmul_eq_mul,
        powerTuples_andGate_eval_sum, h_coefficient,
        eval_modGate_cast hp]
      simp only [eval, List.map_nil, List.all_nil, if_true, Bool.toNat_true,
        Nat.cast_one]
      ring
  | input input negated => simp [mergeModChild]
  | constant value label => simp [mergeModChild]
  | notGate formula => simp [mergeModChild]
  | andGate formulas => simp [mergeModChild]
  | orGate formulas => simp [mergeModChild]

/-- Replacing every direct modulo child preserves the complete input sum of
an outer modulo gate. -/
theorem mergeModChildren_eval_sum {p : Nat} (hp : p.Prime)
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    (((formulas.flatMap mergeModChild).map fun formula =>
      ((eval formula inputs randomBits).toNat : ZMod p)).sum) =
      (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        mergeModChild_eval_sum hp, ih]
      simp

private theorem eval_modGate_eq_of_sum_cast_eq {p : Nat}
    (left right : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool)
    (h_sum :
      (left.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum =
      (right.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum) :
    eval (.modGate left) inputs randomBits =
      eval (.modGate right) inputs randomBits := by
  have h_true :
      eval (.modGate left) inputs randomBits = true ↔
        eval (.modGate right) inputs randomBits = true := by
    rw [eval_modGate_eq_true_iff, eval_modGate_eq_true_iff, h_sum]
  cases h_left : eval (.modGate left) inputs randomBits <;>
    cases h_right : eval (.modGate right) inputs randomBits <;>
    simp_all

mutual

/-- Merging connected modulo gates preserves evaluation for prime `p`. -/
theorem mergeConnectedModGates_eval {p : Nat} (hp : p.Prime)
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool) :
    eval (mergeConnectedModGates formula) inputs randomBits =
      eval formula inputs randomBits := by
  match formula with
  | .input inputRef negated => rfl
  | .constant value label => rfl
  | .notGate formula =>
      simp only [mergeConnectedModGates, eval]
      rw [mergeConnectedModGates_eval hp]
  | .andGate formulas =>
      simp only [mergeConnectedModGates, eval]
      rw [mergeConnectedModGatesList_eval hp]
  | .orGate formulas =>
      simp only [mergeConnectedModGates, eval]
      rw [mergeConnectedModGatesList_eval hp]
  | .modGate formulas =>
      simp only [mergeConnectedModGates]
      apply eval_modGate_eq_of_sum_cast_eq
      calc
        ((((mergeConnectedModGatesList formulas).flatMap mergeModChild).map
            fun formula =>
              ((eval formula inputs randomBits).toNat : ZMod p)).sum) =
            ((mergeConnectedModGatesList formulas).map fun formula =>
              ((eval formula inputs randomBits).toNat : ZMod p)).sum :=
          mergeModChildren_eval_sum hp _ inputs randomBits
        _ = (formulas.map fun formula =>
              ((eval formula inputs randomBits).toNat : ZMod p)).sum := by
          have h_children :=
            mergeConnectedModGatesList_eval hp formulas inputs randomBits
          have h_cast := congrArg (fun values : List Bool =>
            (values.map fun value => (value.toNat : ZMod p)).sum) h_children
          rw [List.map_map, List.map_map] at h_cast
          exact h_cast

/-- List form of `mergeConnectedModGates_eval`. -/
theorem mergeConnectedModGatesList_eval {p : Nat} (hp : p.Prime)
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    (mergeConnectedModGatesList formulas).map
        (fun formula => eval formula inputs randomBits) =
      formulas.map (fun formula => eval formula inputs randomBits) := by
  match formulas with
  | [] => rfl
  | formula :: formulas =>
      simp only [mergeConnectedModGatesList, List.map_cons]
      rw [mergeConnectedModGates_eval hp,
        mergeConnectedModGatesList_eval hp]

end

/-- For prime `p`, merging connected modulo gates preserves error
probability. -/
theorem mergeConnectedModGates_errorProbability_eq {p : Nat} (hp : p.Prime)
    (formula : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (inputs : List Bool) (expected : Bool) :
    errorProbability (mergeConnectedModGates formula) randomBitCount
        inputs expected =
      errorProbability formula randomBitCount inputs expected := by
  apply errorProbability_congr
  intro randomBits
  exact mergeConnectedModGates_eval hp formula inputs randomBits

private theorem powerTuples_forall {α : Type} (property : α → Prop)
    (formulas : List α) (degree : Nat)
    (h_formulas : ∀ formula ∈ formulas, property formula) :
    ∀ monomial ∈ powerTuples formulas degree,
      ∀ formula ∈ monomial, property formula := by
  induction degree with
  | zero => simp [powerTuples]
  | succ degree ih =>
      intro monomial h_monomial formula h_formula
      simp only [powerTuples, List.mem_flatMap, List.mem_map] at h_monomial
      obtain ⟨head, h_head, tail, h_tail, rfl⟩ := h_monomial
      simp only [List.mem_cons] at h_formula
      rcases h_formula with rfl | h_formula
      · exact h_formulas _ h_head
      · exact ih tail h_tail formula h_formula

private theorem powerTuples_andGate_hasNoConnectedModGates {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (degree : Nat)
    (h_formulas : ∀ formula ∈ formulas,
      HasNoConnectedModGates formula) :
    ∀ monomial ∈ powerTuples formulas degree,
      HasNoConnectedModGates (.andGate monomial) := by
  intro monomial h_monomial
  simp only [HasNoConnectedModGates]
  exact powerTuples_forall HasNoConnectedModGates formulas degree
    h_formulas monomial h_monomial

private theorem mergeModChild_isNotModGate {p : Nat}
    (formula output : ProbabilisticACCFormula p)
    (h_output : output ∈ mergeModChild formula) :
    IsNotModGate output := by
  cases formula <;> cases output <;>
    simp_all [mergeModChild, IsNotModGate]

private theorem mergeModChild_hasNoConnectedModGates {p : Nat}
    (formula : ProbabilisticACCFormula p)
    (h_formula : HasNoConnectedModGates formula) :
    ∀ output ∈ mergeModChild formula, HasNoConnectedModGates output := by
  cases formula with
  | input inputRef negated => simpa [mergeModChild] using h_formula
  | constant value label => simpa [mergeModChild] using h_formula
  | notGate formula => simpa [mergeModChild] using h_formula
  | andGate formulas => simpa [mergeModChild] using h_formula
  | orGate formulas => simpa [mergeModChild] using h_formula
  | modGate formulas =>
      intro output h_output
      simp only [mergeModChild, List.mem_cons] at h_output
      rcases h_output with rfl | h_output
      · simp [HasNoConnectedModGates]
      · simp only [List.mem_flatten, List.mem_replicate] at h_output
        obtain ⟨outputs, ⟨_, rfl⟩, h_output⟩ := h_output
        simp only [List.mem_map] at h_output
        obtain ⟨monomial, h_monomial, rfl⟩ := h_output
        have h_formula' :
            (∀ child ∈ formulas, IsNotModGate child) ∧
              ∀ child ∈ formulas, HasNoConnectedModGates child := by
          simpa only [HasNoConnectedModGates] using h_formula
        exact powerTuples_andGate_hasNoConnectedModGates formulas (p - 1)
          h_formula'.2 monomial h_monomial

mutual

/-- The recursive transformation removes every direct edge between two
modulo gates. -/
theorem mergeConnectedModGates_hasNoConnectedModGates {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    HasNoConnectedModGates (mergeConnectedModGates formula) := by
  match formula with
  | .input inputRef negated =>
      simp [mergeConnectedModGates, HasNoConnectedModGates]
  | .constant value label =>
      simp [mergeConnectedModGates, HasNoConnectedModGates]
  | .notGate formula =>
      simpa [mergeConnectedModGates, HasNoConnectedModGates] using
        mergeConnectedModGates_hasNoConnectedModGates formula
  | .andGate formulas =>
      simpa [mergeConnectedModGates, HasNoConnectedModGates] using
        mergeConnectedModGatesList_hasNoConnectedModGates formulas
  | .orGate formulas =>
      simpa [mergeConnectedModGates, HasNoConnectedModGates] using
        mergeConnectedModGatesList_hasNoConnectedModGates formulas
  | .modGate formulas =>
      simp only [mergeConnectedModGates, HasNoConnectedModGates]
      have h_children :=
        mergeConnectedModGatesList_hasNoConnectedModGates formulas
      constructor
      · intro output h_output
        obtain ⟨formula, h_formula, h_output⟩ :=
          List.mem_flatMap.mp h_output
        exact mergeModChild_isNotModGate formula output h_output
      · intro output h_output
        obtain ⟨formula, h_formula, h_output⟩ :=
          List.mem_flatMap.mp h_output
        exact mergeModChild_hasNoConnectedModGates formula
          (h_children formula h_formula) output h_output

/-- Every result in a recursively transformed list has no connected modulo
gates. -/
theorem mergeConnectedModGatesList_hasNoConnectedModGates {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    ∀ formula ∈ mergeConnectedModGatesList formulas,
      HasNoConnectedModGates formula := by
  match formulas with
  | [] => simp [mergeConnectedModGatesList]
  | formula :: formulas =>
      intro output h_output
      simp only [mergeConnectedModGatesList, List.mem_cons] at h_output
      rcases h_output with rfl | h_output
      · exact mergeConnectedModGates_hasNoConnectedModGates formula
      · exact mergeConnectedModGatesList_hasNoConnectedModGates formulas
          output h_output

end

end Circuits.ACC.ProbabilisticACCFormula
