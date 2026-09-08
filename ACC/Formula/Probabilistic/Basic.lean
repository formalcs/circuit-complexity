import ACC.Formula.Basic

namespace Circuits.ACC

/-! ## Probabilistic ACC formulas

A `ProbabilisticACCFormula p` is an ACC formula whose input leaves are tagged
as either external inputs or random bits. Both kinds of inputs are indexed by
natural numbers, but they are evaluated against separate input lists.
-/

/-- A reference to either an external input or a random bit. -/
inductive ACCInput where
  | external : Nat → ACCInput
  | random : Nat → ACCInput
  deriving Repr, BEq, DecidableEq

/-- ACC formulas with separately indexed external inputs and random bits. -/
inductive ProbabilisticACCFormula (p : Nat) where
  | input : ACCInput → Bool → ProbabilisticACCFormula p
  | constant : Bool → Nat → ProbabilisticACCFormula p
  | notGate : ProbabilisticACCFormula p → ProbabilisticACCFormula p
  | andGate : List (ProbabilisticACCFormula p) → ProbabilisticACCFormula p
  | orGate : List (ProbabilisticACCFormula p) → ProbabilisticACCFormula p
  | modGate : List (ProbabilisticACCFormula p) → ProbabilisticACCFormula p
  deriving Repr

namespace ProbabilisticACCFormula

/-- Evaluate a probabilistic ACC formula using separate external inputs and
    random bits.

    Missing inputs evaluate to `false`. Empty `andGate`s evaluate to `true`;
    empty `orGate`s evaluate to `false`; and `modGate []` evaluates to `true`,
    since the empty sum is `0`. -/
def eval {p : Nat} : ProbabilisticACCFormula p → List Bool → List Bool → Bool
  | .input (.external idx) negated, inputs, _randomBits =>
      let value := inputs[idx]?.getD false
      if negated then !value else value
  | .input (.random idx) negated, _inputs, randomBits =>
      let value := randomBits[idx]?.getD false
      if negated then !value else value
  | .constant value _, _, _ => value
  | .notGate formula, inputs, randomBits =>
      !(eval formula inputs randomBits)
  | .andGate formulas, inputs, randomBits =>
      if (formulas.map (fun formula => eval formula inputs randomBits)).all (· == true) then
        true
      else
        false
  | .orGate formulas, inputs, randomBits =>
      if (formulas.map (fun formula => eval formula inputs randomBits)).any (· == true) then
        true
      else
        false
  | .modGate formulas, inputs, randomBits =>
      let values := formulas.map (fun formula => eval formula inputs randomBits)
      if (values.map Bool.toNat).sum % p == 0 then true else false

/-- Depth of a probabilistic ACC formula. Inputs and constants have depth
`0`; each gate contributes one level above the maximum child depth. -/
def depth {p : Nat} : ProbabilisticACCFormula p → Nat
  | .input _ _ => 0
  | .constant _ _ => 0
  | .notGate formula => depth formula + 1
  | .andGate formulas => 1 + (formulas.map depth).max?.getD 0
  | .orGate formulas => 1 + (formulas.map depth).max?.getD 0
  | .modGate formulas => 1 + (formulas.map depth).max?.getD 0

/-- Count non-input nodes in a probabilistic ACC formula. Random and external
inputs both have size zero; constants and gates each contribute one. -/
def circuitSize {p : Nat} : ProbabilisticACCFormula p → Nat
  | .input _ _ => 0
  | .constant _ _ => 1
  | .notGate formula => circuitSize formula + 1
  | .andGate formulas => (formulas.map circuitSize).sum + 1
  | .orGate formulas => (formulas.map circuitSize).sum + 1
  | .modGate formulas => (formulas.map circuitSize).sum + 1

/-- Number of syntax-tree nodes, including external and random input
occurrences.  Unlike `circuitSize`, this measure controls the amount of
syntax duplicated by unbounded-fan-in transformations. -/
def nodeCount {p : Nat} : ProbabilisticACCFormula p → Nat
  | .input _ _ => 1
  | .constant _ _ => 1
  | .notGate formula => nodeCount formula + 1
  | .andGate formulas => (formulas.map nodeCount).sum + 1
  | .orGate formulas => (formulas.map nodeCount).sum + 1
  | .modGate formulas => (formulas.map nodeCount).sum + 1

/-- Every probabilistic formula has at least its root node. -/
theorem nodeCount_pos {p : Nat} (formula : ProbabilisticACCFormula p) :
    0 < nodeCount formula := by
  cases formula <;> simp [nodeCount]

/-- Every random-input leaf of `formula` has an index in the half-open
interval `[lower, upper)`.  External inputs do not contribute to this
predicate. -/
def UsesRandomInputsIn {p : Nat} :
    ProbabilisticACCFormula p → Nat → Nat → Prop
  | .input (.external _) _, _, _ => True
  | .input (.random idx) _, lower, upper => lower ≤ idx ∧ idx < upper
  | .constant _ _, _, _ => True
  | .notGate formula, lower, upper => UsesRandomInputsIn formula lower upper
  | .andGate formulas, lower, upper =>
      ∀ formula ∈ formulas, UsesRandomInputsIn formula lower upper
  | .orGate formulas, lower, upper =>
      ∀ formula ∈ formulas, UsesRandomInputsIn formula lower upper
  | .modGate formulas, lower, upper =>
      ∀ formula ∈ formulas, UsesRandomInputsIn formula lower upper

mutual

/-- Evaluation only observes random bits whose indices occur in the formula.
In particular, two random-bit lists that agree on a support interval give the
same value to every formula supported in that interval. -/
theorem eval_eq_of_randomBits_eq_on {p : Nat}
    (formula : ProbabilisticACCFormula p) (lower upper : Nat)
    (inputs leftRandomBits rightRandomBits : List Bool)
    (h_support : UsesRandomInputsIn formula lower upper)
    (h_agree : ∀ idx, lower ≤ idx → idx < upper →
      leftRandomBits[idx]?.getD false =
        rightRandomBits[idx]?.getD false) :
    eval formula inputs leftRandomBits =
      eval formula inputs rightRandomBits := by
  match formula with
  | .input (.external idx) negated => simp [eval]
  | .input (.random idx) negated =>
      simp only [UsesRandomInputsIn] at h_support
      simp only [eval]
      rw [h_agree idx h_support.1 h_support.2]
  | .constant value label => simp [eval]
  | .notGate child =>
      simp only [UsesRandomInputsIn] at h_support
      simp only [eval]
      rw [eval_eq_of_randomBits_eq_on child lower upper inputs
        leftRandomBits rightRandomBits h_support h_agree]
  | .andGate children =>
      simp only [UsesRandomInputsIn] at h_support
      simp only [eval]
      rw [evalList_eq_of_randomBits_eq_on children lower upper inputs
        leftRandomBits rightRandomBits h_support h_agree]
  | .orGate children =>
      simp only [UsesRandomInputsIn] at h_support
      simp only [eval]
      rw [evalList_eq_of_randomBits_eq_on children lower upper inputs
        leftRandomBits rightRandomBits h_support h_agree]
  | .modGate children =>
      simp only [UsesRandomInputsIn] at h_support
      simp only [eval]
      rw [evalList_eq_of_randomBits_eq_on children lower upper inputs
        leftRandomBits rightRandomBits h_support h_agree]

/-- List form of `eval_eq_of_randomBits_eq_on`. -/
theorem evalList_eq_of_randomBits_eq_on {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (lower upper : Nat)
    (inputs leftRandomBits rightRandomBits : List Bool)
    (h_support : ∀ formula ∈ formulas,
      UsesRandomInputsIn formula lower upper)
    (h_agree : ∀ idx, lower ≤ idx → idx < upper →
      leftRandomBits[idx]?.getD false =
        rightRandomBits[idx]?.getD false) :
    formulas.map (fun formula => eval formula inputs leftRandomBits) =
      formulas.map (fun formula => eval formula inputs rightRandomBits) := by
  match formulas with
  | [] => rfl
  | formula :: formulas =>
      simp only [List.map_cons]
      rw [eval_eq_of_randomBits_eq_on formula lower upper inputs
        leftRandomBits rightRandomBits (h_support formula (by simp)) h_agree]
      rw [evalList_eq_of_randomBits_eq_on formulas lower upper inputs
        leftRandomBits rightRandomBits (by
          intro child h_child
          exact h_support child (by simp [h_child])) h_agree]

end

mutual

/-- Enlarge the interval witnessing the random-input support of a formula. -/
theorem usesRandomInputsIn_mono {p : Nat}
    (formula : ProbabilisticACCFormula p)
    (lower upper widerLower widerUpper : Nat)
    (h_support : UsesRandomInputsIn formula lower upper)
    (h_lower : widerLower ≤ lower) (h_upper : upper ≤ widerUpper) :
    UsesRandomInputsIn formula widerLower widerUpper := by
  match formula with
  | .input (.external idx) negated => simp [UsesRandomInputsIn]
  | .input (.random idx) negated =>
      simp only [UsesRandomInputsIn] at h_support ⊢
      exact ⟨h_lower.trans h_support.1, h_support.2.trans_le h_upper⟩
  | .constant value label => simp [UsesRandomInputsIn]
  | .notGate child =>
      simp only [UsesRandomInputsIn] at h_support ⊢
      exact usesRandomInputsIn_mono child lower upper widerLower widerUpper
        h_support h_lower h_upper
  | .andGate children =>
      simp only [UsesRandomInputsIn] at h_support ⊢
      exact usesRandomInputsInList_mono children lower upper widerLower
        widerUpper h_support h_lower h_upper
  | .orGate children =>
      simp only [UsesRandomInputsIn] at h_support ⊢
      exact usesRandomInputsInList_mono children lower upper widerLower
        widerUpper h_support h_lower h_upper
  | .modGate children =>
      simp only [UsesRandomInputsIn] at h_support ⊢
      exact usesRandomInputsInList_mono children lower upper widerLower
        widerUpper h_support h_lower h_upper

/-- List form of `usesRandomInputsIn_mono`. -/
theorem usesRandomInputsInList_mono {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (lower upper widerLower widerUpper : Nat)
    (h_support : ∀ formula ∈ formulas,
      UsesRandomInputsIn formula lower upper)
    (h_lower : widerLower ≤ lower) (h_upper : upper ≤ widerUpper) :
    ∀ formula ∈ formulas,
      UsesRandomInputsIn formula widerLower widerUpper := by
  intro formula h_formula
  exact usesRandomInputsIn_mono formula lower upper widerLower widerUpper
    (h_support formula h_formula) h_lower h_upper

end

/-- Number of uniformly chosen random assignments on which `formula` differs
    from `expected`. -/
def errorCount {p : Nat} (formula : ProbabilisticACCFormula p)
    (randomBitCount : Nat) (inputs : List Bool) (expected : Bool) : Nat :=
  ((Finset.univ : Finset (Fin randomBitCount → Bool)).filter fun randomBits =>
    eval formula inputs (List.ofFn randomBits) ≠ expected).card

/-- Error probability under the uniform distribution on the indicated number
    of random bits. -/
def errorProbability {p : Nat} (formula : ProbabilisticACCFormula p)
    (randomBitCount : Nat) (inputs : List Bool) (expected : Bool) : ℚ :=
  errorCount formula randomBitCount inputs expected / 2 ^ randomBitCount

/-- Pointwise equivalent probabilistic formulas have the same error count. -/
theorem errorCount_congr {p : Nat}
    (left right : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (inputs : List Bool) (expected : Bool)
    (h_eval : ∀ randomBits : List Bool,
      eval left inputs randomBits = eval right inputs randomBits) :
    errorCount left randomBitCount inputs expected =
      errorCount right randomBitCount inputs expected := by
  unfold errorCount
  congr 1
  ext randomAssignment
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h_eval]

/-- Pointwise equivalent probabilistic formulas have the same error
probability for every choice of random-bit count and expected value. -/
theorem errorProbability_congr {p : Nat}
    (left right : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (inputs : List Bool) (expected : Bool)
    (h_eval : ∀ randomBits : List Bool,
      eval left inputs randomBits = eval right inputs randomBits) :
    errorProbability left randomBitCount inputs expected =
      errorProbability right randomBitCount inputs expected := by
  unfold errorProbability
  rw [errorCount_congr left right randomBitCount inputs expected h_eval]

end ProbabilisticACCFormula

end Circuits.ACC
