import Formulas.Basic
import «Circuits».CircuitFoundation

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

/-- A Boolean circuit represented as a finite directed acyclic graph of gates and wires.

    Well-formedness is captured by the predicate `Circuit.WellFormed`. -/
structure Circuit where
  gates : List Gate
  edges : List Edge
  deriving Repr

namespace Circuit

-- ── helper projections ──────────────────────────────────────────────

/-- The set of all gate ids in the circuit. -/
def gateIds (c : Circuit) : List Nat :=
  c.gates.map Gate.id

/-- Return the list of incoming edges for the gate with the given id. -/
def inEdges (c : Circuit) (id : Nat) : List Edge :=
  c.edges.filter (fun e => e.dst == id)

/-- Return the list of outgoing edges for the gate with the given id. -/
def outEdges (c : Circuit) (id : Nat) : List Edge :=
  c.edges.filter (fun e => e.src == id)

/-- Fan-in of a gate: number of incoming edges. -/
def fanIn (c : Circuit) (id : Nat) : Nat :=
  (c.inEdges id).length

/-- Fan-out of a gate: number of outgoing edges. -/
def fanOut (c : Circuit) (id : Nat) : Nat :=
  (c.outEdges id).length

-- ── reachability & acyclicity ───────────────────────────────────────

/-- `Reachable c u v` holds when there is a directed path from `u` to `v`
    through edges in `c`. -/
inductive Reachable (c : Circuit) : Nat → Nat → Prop where
  | edge : ∀ {u v}, Edge.mk u v ∈ c.edges → Reachable c u v
  | trans : ∀ {u w v}, Reachable c u w → Reachable c w v → Reachable c u v

/-- The circuit is acyclic: no gate can reach itself. -/
def IsAcyclic (c : Circuit) : Prop :=
  ∀ v, ¬ Reachable c v v

-- ── well-formedness ─────────────────────────────────────────────────

/-- A `Circuit` is well-formed when:

1. **Unique ids** – no two gates share the same identifier.
2. **Closed edges** – every edge endpoint refers to an existing gate.
3. **Acyclicity** – the directed graph has no cycles.
4. **Fan-in constraints** –
   * `.input` gates have fan-in 0.
   * `.output` gates have fan-in 1.
   * `.notGate` gates have fan-in 1.
5. **Input gates have no predecessors** – implied by fan-in 0 and listed for clarity.
6. **Consecutive ids** – gate at position k has id k.
7. **Topological ordering** – every edge goes from lower id to higher id. -/
structure WellFormed (c : Circuit) : Prop where
  unique_ids   : c.gateIds.Nodup
  edges_closed : ∀ e ∈ c.edges, e.src ∈ c.gateIds ∧ e.dst ∈ c.gateIds
  edges_nodup  : c.edges.Nodup
  acyclic      : c.IsAcyclic
  fanin_input  : ∀ g ∈ c.gates, g.type.isInput = true → c.fanIn g.id = 0
  fanin_output : ∀ g ∈ c.gates, g.type = GateType.output → c.fanIn g.id = 1
  fanin_not    : ∀ g ∈ c.gates, g.type = GateType.notGate    → c.fanIn g.id = 1
  cons_ids     : ∀ k (hk : k < c.gates.length), (c.gates[k]'hk).id = k
  topo         : ∀ e ∈ c.edges, e.src < e.dst
  /-- Every non-input gate is itself an output, or has a directed path to
      some output gate. Inputs may dangle freely. -/
  non_input_reaches_output :
    ∀ g ∈ c.gates, g.type.isInput = false →
      g.type = GateType.output ∨
      ∃ o ∈ c.gates, o.type = GateType.output ∧ c.Reachable g.id o.id
  /-- The circuit's input gates use the canonical layout: positive
      inputs occupy ids `0, …, n-1` and negative inputs occupy
      ids `n, …, 2n-1`, where `n` is the input width.  Stated inline
      to avoid forward-referencing `HasCanonicalInputIds`. -/
  has_canonical_input_ids :
    let posIds := (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id
    let negIds := (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id
    let n := max posIds.length negIds.length
    posIds = List.range n ∧
    negIds = (List.range n).map (fun i => n + i)
  /-- Output gates are sinks: they have no outgoing edges. -/
  fanout_output : ∀ g ∈ c.gates, g.type = GateType.output → c.fanOut g.id = 0
  /-- The circuit is non-trivial: at least one input gate has a directed
      path to some output gate.  Rules out empty / disconnected /
      constant-only circuits. -/
  input_reaches_output :
    ∃ i ∈ c.gates, i.type.isInput = true ∧
      ∃ o ∈ c.gates, o.type = GateType.output ∧ c.Reachable i.id o.id

-- ── evaluation ──────────────────────────────────────────────────────

/-- The IDs of `c`'s positive primary input gates, in the order they
    appear in `c.gates`. -/
def positiveInputIds (c : Circuit) : List Nat :=
  (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id

/-- The IDs of `c`'s negative primary input gates, in the order they
    appear in `c.gates`. -/
def negativeInputIds (c : Circuit) : List Nat :=
  (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id

/-- The input width of `c`: the maximum of the number of positive
    primary input gates (`GateType.input false`) and the number of
    negative primary input gates (`GateType.input true`).  This is
    the `n` used by the canonical `2 * n`-gate input prefix, chosen so
    that positive and negative inputs have matching canonical slots. -/
def inputWidth (c : Circuit) : Nat :=
  max c.positiveInputIds.length c.negativeInputIds.length

/-- **Canonical input layout.**  A `Circuit` `c` "has canonical
    input ids" when, with `n := c.inputWidth`,

    * its `n` positive primary input gates have ids `0, 1, …, n - 1`
      (in that order), and
    * its `n` negative primary input gates have ids
      `n, n + 1, …, 2 * n - 1` (in that order).

    Equivalently, `c.positiveInputIds = List.range n` and
    `c.negativeInputIds = (List.range n).map (n + ·)`. -/
def HasCanonicalInputIds (c : Circuit) : Prop :=
  c.positiveInputIds = List.range c.inputWidth ∧
  c.negativeInputIds = (List.range c.inputWidth).map (fun i => c.inputWidth + i)

/-- Evaluate a single gate.  `initEnv` supplies the external input
    values keyed by gate id (used by both `GateType.input false` and `GateType.input true`
    gates — the latter simply negates the looked-up value); `env`
    supplies predecessor values (used by all other gate types). -/
def evalGate (c : Circuit) (initEnv env : Nat → Bool) (g : Gate) : Bool :=
  match g.type with
  | GateType.input neg =>
      if neg then Bool.not (initEnv g.id) else initEnv g.id
  | GateType.output =>
      match (c.inEdges g.id).head? with
      | some e => env e.src
      | none   => false               -- ill-formed fallback
  | GateType.notGate =>
      match (c.inEdges g.id).head? with
      | some e => Bool.not (env e.src)
      | none   => false
  | GateType.andGate =>
      let srcs := (c.inEdges g.id).map (fun e => env e.src)
      if srcs.all (· == true) then true else false
  | GateType.orGate =>
      let srcs := (c.inEdges g.id).map (fun e => env e.src)
      if srcs.any (· == true) then true else false

/-- Number of gates in the circuit (size). -/
def size (c : Circuit) : Nat := c.gates.length

/-- Number of non-input gates in the circuit. -/
def circuitSize (c : Circuit) : Nat :=
  (c.gates.filter (fun g => !g.type.isInput)).length

/-- Depth of a single gate `id`, computed by a fuel-bounded DFS through
    the predecessor edges.  Returns `0` once `fuel` is exhausted or when
    the gate has no predecessors. -/
def depthOf (c : Circuit) : Nat → Nat → Nat
  | 0,        _  => 0
  | fuel + 1, id =>
      let preds := (c.inEdges id).map Edge.src
      match preds with
      | []  => 0
      | _   => 1 + (List.foldr max 0) (preds.map (depthOf c fuel))

/-- Depth of the circuit: length of the longest path from any input to
    any output. Uses a fuel-bounded DFS with `size` as the initial fuel. -/
def depth (c : Circuit) : Nat :=
  let outputIds := (c.gates.filter (fun g => g.type == GateType.output)).map Gate.id
  (List.foldr max 0) (outputIds.map (c.depthOf c.size))

/-- The list of output gate ids. -/
def outputGateIds (c : Circuit) : List Nat :=
  (c.gates.filter (fun g => g.type == GateType.output)).map Gate.id

/-- Evaluate the full circuit given input bit values.
    `inputValues` provides values for input gates in the order they appear
    in `positiveInputIds`. Returns the values at output gates in the order
    they appear in `outputGateIds`.

    Assumes gates are listed in topological order, which the construction
    discipline guarantees (each gate's id is strictly greater than all previously
    allocated ids, and edges always point from lower to higher ids). -/
def eval (c : Circuit) (inputValues : List Bool) : List Bool :=
  -- Guard: if the caller supplied fewer values than the circuit's
  -- input width, return a list of `false`s of the canonical
  -- output length.  This makes `eval` totally defined while making
  -- under-provisioned calls trivially identifiable.
  if inputValues.length < c.inputWidth then
    c.outputGateIds.map (fun _ => false)
  else
  -- Positive input gate ids, paired 1-1 with the user-supplied values.
  let posIds := (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id
  -- Negated input *reference* gate ids, paired 1-1 by index with `posIds`:
  -- the i-th `GateType.input true` gate shares the value of the i-th
  -- `GateType.input false`
  -- gate (and `evalGate` flips it).
  let negIds := (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id
  let posPairs := posIds.zip inputValues
  let negPairs := negIds.zip inputValues
  let initEnv : Nat → Bool := fun id =>
    match posPairs.find? (fun p => p.1 == id) with
    | some (_, v) => v
    | none =>
      match negPairs.find? (fun p => p.1 == id) with
      | some (_, v) => v
      | none        => false
  -- Fold over gates in topological order, evaluating each gate and
  -- recording its value in the environment
  let finalEnv := c.gates.foldl
    (fun (env : Nat → Bool) (g : Gate) =>
      let val := c.evalGate initEnv env g
      fun id => if id == g.id then val else env id)
    initEnv
  -- Collect output gate values
  c.outputGateIds.map finalEnv

/-! ### Evaluation under `HasCanonicalInputIds`

When a circuit `c` has its input ids in the canonical layout
(`HasCanonicalInputIds c`), the initial environment lookup degenerates
into a simple positional read of `inputValues`:

  * `id < n`              ↦ `inputValues[id]`        (positive copy)
  * `n ≤ id < 2 * n`      ↦ `inputValues[id - n]`    (negative copy)
  * `id ≥ 2 * n`          ↦ `false`               (non-input gate)

`evalCanonical` implements this directly without the `zip + find?`
machinery used by the general-purpose `eval`.  It is intended to be
called only when `HasCanonicalInputIds c` holds; otherwise the input
lookup it performs may not match `eval`. -/

/-- Initial environment for canonical-input circuits.  Maps the
    canonical positive slot `i ∈ [0, n)` and canonical negative slot
    `n + i ∈ [n, 2 * n)` to `inputValues[i]` (with `false` as a
    safe default for missing slots and out-of-range ids). -/
def canonicalInitEnv (n : Nat) (inputValues : List Bool) (id : Nat) : Bool :=
  if id < n then
    inputValues[id]?.getD false
  else if id < 2 * n then
    inputValues[id - n]?.getD false
  else
    false

/-- Evaluate a circuit assumed to satisfy `HasCanonicalInputIds`.

    The initial environment is computed by `canonicalInitEnv`, bypassing
    the `zip + find?` lookup used by `eval`.  The fold over gates and
    the output-collection step are otherwise identical to `eval`.

    This is provably equal to `eval` whenever `HasCanonicalInputIds c`
    holds (proved separately); for non-canonical circuits the two
    functions may disagree on the initial environment. -/
def evalCanonical (c : Circuit) (inputValues : List Bool) : List Bool :=
  -- Same guard as `eval`: under-provisioned inputs yield a list of
  -- `false`s of the output length.
  if inputValues.length < c.inputWidth then
    c.outputGateIds.map (fun _ => false)
  else
  let n := c.inputWidth
  let initEnv : Nat → Bool := canonicalInitEnv n inputValues
  let finalEnv := c.gates.foldl
    (fun (env : Nat → Bool) (g : Gate) =>
      let val := c.evalGate initEnv env g
      fun id => if id == g.id then val else env id)
    initEnv
  c.outputGateIds.map finalEnv

/-! ### Length lemmas for `eval` and `evalCanonical`

Both functions return a list of length `c.outputGateIds.length`,
regardless of whether the input-width guard fires.  These length
lemmas are used by downstream callers that establish list equality
via `List.ext_getElem`. -/

/-- The result of `evalCanonical` always has length `c.outputGateIds.length`. -/
@[simp] lemma evalCanonical_length (c : Circuit) (inputValues : List Bool) :
    (c.evalCanonical inputValues).length = c.outputGateIds.length := by
  unfold evalCanonical
  by_cases h : inputValues.length < c.inputWidth
  · rw [if_pos h, List.length_map]
  · rw [if_neg h, List.length_map]

end Circuit

end Circuits
