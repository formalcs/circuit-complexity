import ACC.Circuit.Basic
import ACC.Formula.Basic

namespace Circuits

namespace DAG.ACCCircuit

/-- Input index used when translating canonical ACC input gates to formulas.
    Positive input gates keep their id; negative input gates live in the
    canonical block `inputWidth + i` and translate back to index `i`. -/
def formulaInputIndex (c : ACCCircuit) (id : Nat) (negated : Bool) : Nat :=
  if negated then id - c.inputWidth else id

/-- Convert the gate with id `id` into an `ACCFormula c.p` by recursively
    unrolling its predecessor DAG for at most `fuel` steps.

    The fallback cases make the function total.  On a well-formed,
    topologically ordered ACC circuit with enough fuel, the fallbacks are not
    the intended path. -/
def gateToACCFormula (c : ACCCircuit) : Nat → Nat → ACC.ACCFormula c.p
  | 0, id => .constant false id
  | fuel + 1, id =>
      match c.findGate id with
      | none => .constant false id
      | some g =>
          match g.type with
          | ACCGateType.input negated =>
              .input (c.formulaInputIndex g.id negated) negated
          | ACCGateType.output =>
              match (c.inEdges g.id).head? with
              | some e => gateToACCFormula c fuel e.src
              | none => .constant false g.id
          | ACCGateType.notGate =>
              match (c.inEdges g.id).head? with
              | some e => .notGate (gateToACCFormula c fuel e.src)
              | none => .constant false g.id
          | ACCGateType.andGate =>
              .andGate ((c.inEdges g.id).map (fun e => gateToACCFormula c fuel e.src))
          | ACCGateType.orGate =>
              .orGate ((c.inEdges g.id).map (fun e => gateToACCFormula c fuel e.src))
          | ACCGateType.modGate =>
              .modGate ((c.inEdges g.id).map (fun e => gateToACCFormula c fuel e.src))

/-- Convert the gate with id `id`, using the circuit's own depth estimate as
    fuel. -/
def gateToACCFormulaAtDepth (c : ACCCircuit) (id : Nat) : ACC.ACCFormula c.p :=
  c.gateToACCFormula (c.depthOf c.size id + 1) id

/-- The fuel used by the top-level conversion.  Using the circuit-level depth
    keeps the conversion's depth bound stated against `c.depth` rather than a
    particular selected output. -/
def toACCFormulaFuel (c : ACCCircuit) : Nat :=
  c.depth + 1

/-- Convert a specific output id to an ACC formula. -/
def outputToACCFormula (c : ACCCircuit) (outputId : Nat) : ACC.ACCFormula c.p :=
  c.gateToACCFormula c.toACCFormulaFuel outputId

/-- Convert all output gates of an ACC circuit to ACC formulas, preserving
    output order. -/
def toACCFormulas (c : ACCCircuit) : List (ACC.ACCFormula c.p) :=
  c.outputGateIds.map c.outputToACCFormula

/-- Convert an ACC circuit to a single ACC formula by taking the first output
    gate.  If the circuit has no output gate, return the constant `false`
    formula.  Well-formed circuits have at least one Reachable output by
    `input_reaches_output`. -/
def toACCFormula (c : ACCCircuit) : ACC.ACCFormula c.p :=
  match c.outputGateIds.head? with
  | some outputId => c.outputToACCFormula outputId
  | none => .constant false 0

/-- Version of `toACCFormula` whose domain explicitly carries the
    well-formedness proof. -/
def toACCFormulaOfWellFormed (c : ACCCircuit) (_h : c.WellFormed) :
    ACC.ACCFormula c.p :=
  c.toACCFormula

end DAG.ACCCircuit

end Circuits
