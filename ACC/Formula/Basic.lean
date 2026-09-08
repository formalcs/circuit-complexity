import Formulas.Basic

namespace Circuits.ACC

/-! ## ACC formulas

An `ACCFormula p` is an unbounded fan-in Boolean formula whose modulo gates
all use the same fixed modulus `p`.  A `modGate cs` evaluates its children,
sums their Boolean values as natural numbers, and returns `true` exactly when
that sum is congruent to `0` modulo the ambient `p`.
-/

/-- ACC formulas over Boolean inputs.  `input i negated` reads input `i`,
    negating it when `negated = true`.  `constant` carries a label matching
    the existing formula style in `Formulas.Basic`.

    The modulus is an index of the type, so formulas with different moduli
    cannot be mixed in the same gate. -/
inductive ACCFormula (p : Nat) where
  | input : Nat → Bool → ACCFormula p
  | constant : Bool → Nat → ACCFormula p
  | notGate : ACCFormula p → ACCFormula p
  | andGate : List (ACCFormula p) → ACCFormula p
  | orGate : List (ACCFormula p) → ACCFormula p
  | modGate : List (ACCFormula p) → ACCFormula p
  deriving Repr

namespace ACCFormula

/-- Check whether the top-level node is an input. -/
def isInput {p : Nat} : ACCFormula p → Bool
  | .input _ _ => true
  | _          => false

/-- Evaluate an ACC formula on Boolean inputs.

    Empty `andGate`s evaluate to `true`; empty `orGate`s evaluate to `false`.
    `modGate []` evaluates to `true`, since the empty sum is `0`. -/
def eval {p : Nat} : ACCFormula p → List Bool → Bool
  | .input idx negated, inputs =>
      let value := inputs[idx]?.getD false
      if negated then !value else value
  | .constant value _, _ => value
  | .notGate f, inputs => !(eval f inputs)
  | .andGate fs, inputs =>
      if (fs.map (fun f => eval f inputs)).all (· == true) then true else false
  | .orGate fs, inputs =>
      if (fs.map (fun f => eval f inputs)).any (· == true) then true else false
  | .modGate fs, inputs =>
      let values := fs.map (fun f => eval f inputs)
      if (values.map Bool.toNat).sum % p == 0 then true else false

/-- A syntactic well-formedness predicate for ACC formulas.  Since the
    modulus is fixed by the type, well-formedness just rules out the
    degenerate moduli `0` and `1`. -/
def WellFormed {p : Nat} (_f : ACCFormula p) : Prop :=
  p > 1

/-- An ACC formula is of order `r` when every AND gate in the formula has
    fan-in at most `r`. -/
def IsOfOrder {p : Nat} : ACCFormula p → Nat → Prop
  | .input _ _, _ => True
  | .constant _ _, _ => True
  | .notGate formula, r => IsOfOrder formula r
  | .andGate formulas, r =>
      formulas.length ≤ r ∧ ∀ formula ∈ formulas, IsOfOrder formula r
  | .orGate formulas, r => ∀ formula ∈ formulas, IsOfOrder formula r
  | .modGate formulas, r => ∀ formula ∈ formulas, IsOfOrder formula r

/-- The number of primary inputs required by an ACC formula: one more than
    the largest input index that appears, or `0` when no input appears. -/
def numInputs {p : Nat} : ACCFormula p → Nat
  | .input idx _ => idx + 1
  | .constant _ _ => 0
  | .notGate f => numInputs f
  | .andGate [] => 0
  | .andGate (f :: fs) => max (numInputs f) (numInputs (.andGate fs))
  | .orGate [] => 0
  | .orGate (f :: fs) => max (numInputs f) (numInputs (.orGate fs))
  | .modGate [] => 0
  | .modGate (f :: fs) => max (numInputs f) (numInputs (.modGate fs))

/-- Depth of an ACC formula.  Inputs and constants have depth `0`; each
    gate contributes one level above the maximum child depth. -/
def depth {p : Nat} : ACCFormula p → Nat
  | .input _ _ => 0
  | .constant _ _ => 0
  | .notGate f => depth f + 1
  | .andGate fs => 1 + (fs.map depth).max?.getD 0
  | .orGate fs => 1 + (fs.map depth).max?.getD 0
  | .modGate fs => 1 + (fs.map depth).max?.getD 0

/-- Count every node in an ACC formula. -/
def nodeCount {p : Nat} : ACCFormula p → Nat
  | .input _ _ => 1
  | .constant _ _ => 1
  | .notGate f => nodeCount f + 1
  | .andGate fs => 1 + (fs.map nodeCount).sum
  | .orGate fs => 1 + (fs.map nodeCount).sum
  | .modGate fs => 1 + (fs.map nodeCount).sum

/-- Count non-input nodes in an ACC formula. -/
def circuitSize {p : Nat} : ACCFormula p → Nat
  | .input _ _ => 0
  | .constant _ _ => 1
  | .notGate f => circuitSize f + 1
  | .andGate fs => (fs.map circuitSize).sum + 1
  | .orGate fs => (fs.map circuitSize).sum + 1
  | .modGate fs => (fs.map circuitSize).sum + 1

end ACCFormula

end Circuits.ACC
