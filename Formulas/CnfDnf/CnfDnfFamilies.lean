import Formulas.Basic
import Formulas.Properties
import Formulas.CnfDnf.CnfDnfBasic

namespace Circuits.CnfDnf.Families

def UnboundedFanInCNF
  (n : Nat) :=
  {
    circuit : UnboundedFanInFormula //
    ufiLargestInput circuit < n
    ∧ isCNF circuit
  }

def UnboundedFanInDNF
  (n : Nat) :=
  {
    circuit : UnboundedFanInFormula //
    ufiLargestInput circuit < n
    ∧ isDNF circuit
  }

/-- A "proper" DNF: an `UnboundedFanInDNF` whose clauses are all non-empty
    and whose clauses each have no duplicated variables (Nodup on `Prod.fst`).
    An empty `andGate []` clause semantically denotes the constant `True`,
    which makes the whole DNF a tautology and is normally optimized away.
    The switching lemma is stated on this wrapper so nonempty-clause and
    per-clause `Nodup` assumptions are bundled into the input.
    NOTE: the no-empty-clauses invariant is NOT preserved by `restrictDNF`
    (which can produce empty clauses when all literals of a clause are
    satisfied), so we only use it for the input DNF to
    `switching_lemma_exact`. -/
def UnboundedFanInProperDNF
  (n : Nat) :=
  {
    circuit : UnboundedFanInFormula //
    ufiLargestInput circuit < n
    ∧ IsProperDNF circuit
  }

/-- A "proper" CNF: a UFI formula with bounded input indices, CNF shape,
    nonempty clauses, and no duplicated variables in a clause.  This is the
    CNF counterpart of `UnboundedFanInProperDNF` and deliberately uses the
    same flat subtype representation.

    An empty `orGate []` clause semantically denotes the constant `False`,
    which makes the whole CNF unsatisfiable and is normally optimized away. -/
def UnboundedFanInProperCNF
  (n : Nat) :=
  {
    circuit : UnboundedFanInFormula //
    ufiLargestInput circuit < n
    ∧ IsProperCNF circuit
  }

end Circuits.CnfDnf.Families
