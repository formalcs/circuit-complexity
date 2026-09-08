/-
A MOD_p-∧-circuit (ModPAndCircuit) is a depth-3 (ACCFormula p) of this form:

- The output gate is a MOD_p gate
- The predecessors to the MOD_p gate are ∧ gates
- The predecessors to the ∧ gates are negated or non-negated inputs
-/
import ACC.Formula.Basic
import ACC.Formula.Probabilistic.Basic

namespace Circuits.ACC

/-- Whether an ACC formula is a (possibly negated) input literal.  Negation is
    represented by the Boolean flag carried by `ACCFormula.input`. -/
def IsModPAndLiteral {p : Nat} : ACCFormula p → Prop
  | .input _ _ => True
  | _ => False

/-- Whether an ACC formula is an AND gate all of whose children are input
    literals. -/
def IsAndOfModPAndLiterals {p : Nat} : ACCFormula p → Prop
  | .andGate children => ∀ child ∈ children, IsModPAndLiteral child
  | _ => False

/-- The syntactic predicate characterizing `MOD_p-∧` circuits. -/
def IsModPAndCircuit {p : Nat} : ACCFormula p → Prop
  | .modGate children => ∀ child ∈ children, IsAndOfModPAndLiterals child
  | _ => False

/-- The subtype of `ACCFormula p` consisting of a `MOD_p` output gate whose
    children are AND gates over (possibly negated) input literals. -/
def ModPAndCircuit (p : Nat) :=
  { formula : ACCFormula p // IsModPAndCircuit formula }

namespace ModPAndCircuit

/-- Regard a `MOD_p-∧` circuit as an `ACCFormula p`. -/
def toACCFormula {p : Nat} (c : ModPAndCircuit p) : ACCFormula p :=
  c.1

end ModPAndCircuit

/-- Whether a probabilistic ACC formula is an external or random input
literal. Negation is represented by the Boolean flag on `input`. -/
def IsProbabilisticModPAndLiteral {p : Nat} :
    ProbabilisticACCFormula p → Prop
  | .input _ _ => True
  | _ => False

/-- Whether a probabilistic ACC formula is an AND gate over input literals. -/
def IsAndOfProbabilisticModPAndLiterals {p : Nat} :
    ProbabilisticACCFormula p → Prop
  | .andGate children =>
      ∀ child ∈ children, IsProbabilisticModPAndLiteral child
  | _ => False

/-- The syntactic predicate for probabilistic `MOD_p-AND` circuits: one
modulo output gate above AND gates whose children are external or random
input literals. -/
def IsProbabilisticModPAndCircuit {p : Nat} :
    ProbabilisticACCFormula p → Prop
  | .modGate children =>
      ∀ child ∈ children, IsAndOfProbabilisticModPAndLiterals child
  | _ => False

/-- A probabilistic `MOD_p-AND` circuit. The number of random bits used to
evaluate it is supplied separately at the family level. -/
def ProbabilisticModPAndCircuit (p : Nat) :=
  { formula : ProbabilisticACCFormula p //
    IsProbabilisticModPAndCircuit formula }

namespace ProbabilisticModPAndCircuit

/-- Regard a probabilistic `MOD_p-AND` circuit as a probabilistic ACC
formula. -/
def toProbabilisticACCFormula {p : Nat}
    (circuit : ProbabilisticModPAndCircuit p) :
    ProbabilisticACCFormula p :=
  circuit.1

end ProbabilisticModPAndCircuit

end Circuits.ACC
