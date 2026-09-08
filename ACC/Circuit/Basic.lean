import Formulas.Basic

namespace Circuits.DAG

/-! ## DAG-based ACC Circuit Definition

A more general circuit model where a Boolean circuit is a finite directed
acyclic graph (DAG).  Each node (gate) carries a unique `Nat` identifier
and is one of:

* **`input`**  – a primary input to the circuit (no incoming edges),
               optionally negated
* **`output`** – a primary output of the circuit (exactly one incoming edge)
* **`andGate`** – computes the conjunction of its inputs
* **`orGate`** – computes the disjunction of its inputs
* **`notGate`** – computes the negation of its single input
* **`modGate`** – outputs 1 iff the sum of its inputs is congruent to 0
               modulo the circuit parameter

Edges represent wires: an edge `(src, dst)` means the output of gate
`src` feeds into gate `dst`.
-/

/-- The type of operation performed by a gate. -/
inductive ACCGateType where
  | input (negated : Bool) : ACCGateType
  | output : ACCGateType
  | andGate : ACCGateType
  | orGate : ACCGateType
  | notGate : ACCGateType
  | modGate : ACCGateType
  deriving Repr, BEq, DecidableEq

/-- Check whether a gate type is an input (negated or non-negated). -/
def ACCGateType.isInput : ACCGateType → Bool
  | .input _ => true
  | _        => false

/-- A gate in a circuit, identified by a unique natural number. -/
structure ACCGate where
  id : Nat
  type : ACCGateType
  deriving Repr, BEq, DecidableEq

/-- A directed edge (wire) from the output of gate `src` to an input of gate `dst`. -/
structure Edge where
  src : Nat
  dst : Nat
  deriving Repr, BEq, DecidableEq

structure ACCCircuit where
  p : Nat
  gates : List ACCGate
  edges : List Edge
  deriving Repr

namespace ACCCircuit

/-- The set of all gate ids in the circuit. -/
def gateIds (c : ACCCircuit) : List Nat :=
  c.gates.map ACCGate.id

/-- Return the list of incoming edges for the gate with the given id. -/
def inEdges (c : ACCCircuit) (id : Nat) : List Edge :=
  c.edges.filter (fun e => e.dst == id)

/-- Return the list of outgoing edges for the gate with the given id. -/
def outEdges (c : ACCCircuit) (id : Nat) : List Edge :=
  c.edges.filter (fun e => e.src == id)

/-- Fan-in of a gate: number of incoming edges. -/
def fanIn (c : ACCCircuit) (id : Nat) : Nat :=
  (c.inEdges id).length

/-- Fan-out of a gate: number of outgoing edges. -/
def fanOut (c : ACCCircuit) (id : Nat) : Nat :=
  (c.outEdges id).length

/-- Look up a gate by its identifier. -/
def findGate (c : ACCCircuit) (id : Nat) : Option ACCGate :=
  c.gates.find? (fun g => g.id == id)

-- ── reachability & acyclicity ───────────────────────────────────────

/-- `Reachable c u v` holds when there is a directed path from `u` to `v`
    through edges in `c`. -/
inductive Reachable (c : ACCCircuit) : Nat → Nat → Prop where
  | edge : ∀ {u v}, Edge.mk u v ∈ c.edges → Reachable c u v
  | trans : ∀ {u w v}, Reachable c u w → Reachable c w v → Reachable c u v

/-- The ACC DAG is acyclic: no gate can reach itself. -/
def IsAcyclic (c : ACCCircuit) : Prop :=
  ∀ v, ¬ Reachable c v v

-- ── input/output structure ──────────────────────────────────────────

/-- The list of input gate ids (any polarity). -/
def inputGateIds (c : ACCCircuit) : List Nat :=
  (c.gates.filter (fun g => g.type.isInput)).map ACCGate.id

/-- The IDs of `c`'s positive primary input gates, in the order they
    appear in `c.gates`. -/
def positiveInputIds (c : ACCCircuit) : List Nat :=
  (c.gates.filter (fun g => g.type == ACCGateType.input false)).map ACCGate.id

/-- The IDs of `c`'s negative primary input gates, in the order they
    appear in `c.gates`. -/
def negativeInputIds (c : ACCCircuit) : List Nat :=
  (c.gates.filter (fun g => g.type == ACCGateType.input true)).map ACCGate.id

/-- The input width of `c`, pairing positive and negative input copies by
    index as in the DAG circuit evaluator. -/
def inputWidth (c : ACCCircuit) : Nat :=
  max c.positiveInputIds.length c.negativeInputIds.length

/-- The list of output gate ids. -/
def outputGateIds (c : ACCCircuit) : List Nat :=
  (c.gates.filter (fun g => g.type == ACCGateType.output)).map ACCGate.id

/-- Number of gates in the circuit. -/
def size (c : ACCCircuit) : Nat :=
  c.gates.length

/-- Number of non-input gates in the circuit. -/
def circuitSize (c : ACCCircuit) : Nat :=
  (c.gates.filter (fun g => !g.type.isInput)).length

/-- Depth of a single gate `id`, computed by a fuel-bounded DFS through
    predecessor edges. -/
def depthOf (c : ACCCircuit) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, id =>
      let preds := (c.inEdges id).map Edge.src
      match (preds.map (depthOf c fuel)).max? with
      | some d => d + 1
      | none => 0

/-- Depth of the circuit: the largest predecessor-path depth of an output. -/
def depth (c : ACCCircuit) : Nat :=
  ((c.outputGateIds.map (c.depthOf c.size)).max?).getD 0

/-- **Canonical input layout.**  An `ACCCircuit` `c` has canonical input
    ids when, with `n := c.inputWidth`, positive inputs occupy
    `0, …, n - 1` and negative inputs occupy `n, …, 2 * n - 1`. -/
def HasCanonicalInputIds (c : ACCCircuit) : Prop :=
  c.positiveInputIds = List.range c.inputWidth ∧
  c.negativeInputIds = (List.range c.inputWidth).map (fun i => c.inputWidth + i)

-- ── well-formedness ─────────────────────────────────────────────────

/-- An `ACCCircuit` is well-formed when it satisfies the same structural
    requirements as `DAGCircuit.WellFormed`, with the additional ACC
    modulus condition `p > 1` and a fan-in clause for unbounded `Mod`
    gates. -/
structure WellFormed (c : ACCCircuit) : Prop where
  modulus_gt_one : c.p > 1
  unique_ids   : c.gateIds.Nodup
  edges_closed : ∀ e ∈ c.edges, e.src ∈ c.gateIds ∧ e.dst ∈ c.gateIds
  edges_nodup  : c.edges.Nodup
  acyclic      : c.IsAcyclic
  fanin_input  : ∀ g ∈ c.gates, g.type.isInput = true → c.fanIn g.id = 0
  fanin_output : ∀ g ∈ c.gates, g.type = ACCGateType.output → c.fanIn g.id = 1
  fanin_not    : ∀ g ∈ c.gates, g.type = ACCGateType.notGate → c.fanIn g.id = 1
  fanin_and    : ∀ g ∈ c.gates, g.type = ACCGateType.andGate → c.fanIn g.id ≥ 0
  fanin_or     : ∀ g ∈ c.gates, g.type = ACCGateType.orGate → c.fanIn g.id ≥ 0
  fanin_mod    : ∀ g ∈ c.gates, g.type = ACCGateType.modGate → c.fanIn g.id ≥ 0
  cons_ids     : ∀ k (hk : k < c.gates.length), (c.gates[k]'hk).id = k
  topo         : ∀ e ∈ c.edges, e.src < e.dst
  /-- Every non-input gate is itself an `output`, or has a directed path to
      some `output` gate.  Inputs may dangle freely. -/
  non_input_reaches_output :
    ∀ g ∈ c.gates, g.type.isInput = false →
      g.type = ACCGateType.output ∨
      ∃ o ∈ c.gates, o.type = ACCGateType.output ∧ c.Reachable g.id o.id
  has_canonical_input_ids : c.HasCanonicalInputIds
  /-- `output` gates are sinks: they have no outgoing edges. -/
  fanout_output : ∀ g ∈ c.gates, g.type = ACCGateType.output → c.fanOut g.id = 0
  /-- The circuit is non-trivial: at least one `input` gate has a directed
      path to some `output` gate. -/
  input_reaches_output :
    ∃ i ∈ c.gates, i.type.isInput = true ∧
      ∃ o ∈ c.gates, o.type = ACCGateType.output ∧ c.Reachable i.id o.id

-- ── evaluation ──────────────────────────────────────────────────────

/-- Evaluate a single ACC gate.

    `modGate` gates use the circuit parameter `c.p`: they sum the predecessor
    bits as natural numbers and output `true` iff that sum is `0`
    modulo `c.p`. -/
def evalGate (c : ACCCircuit) (initEnv env : Nat → Bool) (g : ACCGate) : Bool :=
  match g.type with
  | ACCGateType.input neg =>
      if neg then !(initEnv g.id) else initEnv g.id
  | ACCGateType.output =>
      match (c.inEdges g.id).head? with
      | some e => env e.src
      | none   => false
  | ACCGateType.notGate =>
      match (c.inEdges g.id).head? with
      | some e => !(env e.src)
      | none   => false
  | ACCGateType.andGate =>
      let srcs := (c.inEdges g.id).map (fun e => env e.src)
      if srcs.all (· == true) then true else false
  | ACCGateType.orGate =>
      let srcs := (c.inEdges g.id).map (fun e => env e.src)
      if srcs.any (· == true) then true else false
  | ACCGateType.modGate =>
      let srcs := (c.inEdges g.id).map (fun e => env e.src)
      if (srcs.map Bool.toNat).sum % c.p == 0 then true else false

/-- Evaluate the full ACC circuit given input bit values.
    `inputValues` provides values for positive and negative input gates by
    index; negative input gates negate their corresponding value. -/
def eval (c : ACCCircuit) (inputValues : List Bool) : List Bool :=
  if inputValues.length < c.inputWidth then
    c.outputGateIds.map (fun _ => false)
  else
  let posPairs := c.positiveInputIds.zip inputValues
  let negPairs := c.negativeInputIds.zip inputValues
  let initEnv : Nat → Bool := fun id =>
    match posPairs.find? (fun p => p.1 == id) with
    | some (_, v) => v
    | none =>
      match negPairs.find? (fun p => p.1 == id) with
      | some (_, v) => v
      | none        => false
  let finalEnv := c.gates.foldl
    (fun (env : Nat → Bool) (g : ACCGate) =>
      let val := c.evalGate initEnv env g
      fun id => if id == g.id then val else env id)
    initEnv
  c.outputGateIds.map finalEnv

/-- Initial environment for canonical-input ACC circuits.  Maps positive
    slot `i` and negative slot `n + i` to `inputValues[i]`, defaulting to
    `false` for out-of-range ids. -/
def canonicalInitEnv (n : Nat) (inputValues : List Bool) (id : Nat) : Bool :=
  if id < n then
    inputValues[id]?.getD false
  else if id < 2 * n then
    inputValues[id - n]?.getD false
  else
    false

/-- Evaluate an ACC circuit using the canonical input layout required by
    `ACCCircuit.HasCanonicalInputIds`. -/
def evalCanonical (c : ACCCircuit) (inputValues : List Bool) : List Bool :=
  if inputValues.length < c.inputWidth then
    c.outputGateIds.map (fun _ => false)
  else
  let n := c.inputWidth
  let initEnv : Nat → Bool := canonicalInitEnv n inputValues
  let finalEnv := c.gates.foldl
    (fun (env : Nat → Bool) (g : ACCGate) =>
      let val := c.evalGate initEnv env g
      fun id => if id == g.id then val else env id)
    initEnv
  c.outputGateIds.map finalEnv

end ACCCircuit

end Circuits.DAG
