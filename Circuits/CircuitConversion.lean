import «Circuits».CircuitFamilies
import Formulas.Basic
import Formulas.Eval
import Formulas.Properties

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

/-! ### General circuit evaluation framework

For a `Circuit`, the gates have consecutive
IDs starting from 0 and edges always point from lower to higher IDs
(topological ordering).  The lemmas in this section provide a general
framework for reasoning about the `foldl`-based evaluation in
`Circuit.eval`. -/

/-- Helper: membership from `List.head? = some a`. -/
theorem mem_of_head?_some' {α : Type} {l : List α} {a : α}
    (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x t => simp [List.head?] at h; subst h; exact List.Mem.head _

namespace Circuit

/-- Partial evaluation: environment after processing the first `k` gates. -/
def evalS (c : Circuit) (initEnv : Nat → Bool) (k : Nat) : Nat → Bool :=
  (c.gates.take k).foldl
    (fun (env : Nat → Bool) (g : Gate) =>
      fun id => if id == g.id then c.evalGate initEnv env g else env id)
    initEnv

/-- Step equation for `evalS`. -/
theorem evalS_succ (c : Circuit) (initEnv : Nat → Bool)
    (k : Nat) (hk : k < c.gates.length) :
    c.evalS initEnv (k + 1) =
    fun id => if id == (c.gates[k]'hk).id
              then c.evalGate initEnv (c.evalS initEnv k) (c.gates[k]'hk)
              else c.evalS initEnv k id := by
  change (c.gates.take (k + 1)).foldl _ initEnv = _
  conv_lhs => rw [show c.gates.take (k + 1) = c.gates.take k ++ [c.gates[k]'hk] from by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hk]]
  rw [List.foldl_append]; rfl

/-- Pointwise step equation. -/
theorem evalS_succ_apply (c : Circuit) (initEnv : Nat → Bool)
    (k : Nat) (hk : k < c.gates.length) (id : Nat) :
    c.evalS initEnv (k + 1) id =
    if id == (c.gates[k]'hk).id
    then c.evalGate initEnv (c.evalS initEnv k) (c.gates[k]'hk)
    else c.evalS initEnv k id := by
  rw [evalS_succ c initEnv k hk]

/-- Stability: once a gate has been evaluated, its value does not change. -/
theorem evalS_stable (c : Circuit) (initEnv : Nat → Bool)
    (h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length) (hj : j < c.gates.length),
              i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id)
    (j k : Nat) (hjk : j < k) (hk : k ≤ c.gates.length) (hj : j < c.gates.length) :
    c.evalS initEnv k (c.gates[j]'hj).id =
    c.evalS initEnv (j + 1) (c.gates[j]'hj).id := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hjk' : j < k'
    · have hk'lt : k' < c.gates.length := by omega
      rw [evalS_succ_apply c initEnv k' hk'lt]
      have hne : (c.gates[j]'hj).id ≠ (c.gates[k']'hk'lt).id :=
        h_uniq j k' hj hk'lt (by omega)
      simp [beq_iff_eq, hne]
      exact ih hjk' (by omega)
    · have hjeq : j = k' := by omega
      subst hjeq; rfl

/-- `evalGate` depends only on predecessor values.
    Input gates read from the shared `initEnv`, so two environments
    that agree on predecessors give the same result. -/
theorem evalGate_ext (c : Circuit) (initEnv : Nat → Bool)
    (env₁ env₂ : Nat → Bool) (g : Gate)
    (h_pred : ∀ e ∈ c.inEdges g.id, env₁ e.src = env₂ e.src) :
    c.evalGate initEnv env₁ g = c.evalGate initEnv env₂ g := by
  -- `evalGate` handles `input`, `output`, `notGate`, `andGate`, and `orGate` in order.
  unfold evalGate
  split
  · -- `input`: reads from `initEnv`, not `env₁` or `env₂`.
    rfl
  · -- `output`: read its sole predecessor when present.
    split
    · next e _ => exact h_pred e (mem_of_head?_some' (by assumption))
    · rfl
  · -- `notGate`: negate its sole predecessor when present.
    split
    · next e _ => congr 1; exact h_pred e (mem_of_head?_some' (by assumption))
    · rfl
  · -- `andGate`: conjoin all predecessor values.
    have hm : (c.inEdges g.id).map (fun e => env₁ e.src) =
              (c.inEdges g.id).map (fun e => env₂ e.src) :=
      List.map_congr_left fun e he => h_pred e he
    simp only [hm]
  · -- Or (map/any)
    have hm : (c.inEdges g.id).map (fun e => env₁ e.src) =
              (c.inEdges g.id).map (fun e => env₂ e.src) :=
      List.map_congr_left fun e he => h_pred e he
    simp only [hm]

/-- inEdges membership implies edges membership. -/
theorem inEdges_sub (c : Circuit) (gid : Nat) (e : Edge)
    (he : e ∈ c.inEdges gid) : e ∈ c.edges := (List.mem_filter.mp he).1

/-- inEdges destination. -/
theorem inEdges_dst' (c : Circuit) (gid : Nat) (e : Edge)
    (he : e ∈ c.inEdges gid) : e.dst = gid := by
  have := (List.mem_filter.mp he).2; simp [beq_iff_eq] at this; exact this

/-- **Fixed-point property**: for a topologically ordered circuit with
    consecutively numbered gate IDs, the final evaluation environment
    satisfies `finalEnv(k) = evalGate(finalEnv, gates[k])` for every
    gate index `k`.  This is the central structural lemma for
    reasoning about `Circuit.eval`. -/
theorem evalS_fp (c : Circuit) (initEnv : Nat → Bool)
    (h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length) (hj : j < c.gates.length),
              i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id)
    (h_ids : ∀ (k : Nat) (hk : k < c.gates.length), (c.gates[k]'hk).id = k)
    (h_topo : ∀ e ∈ c.edges, e.src < e.dst) :
    ∀ (k : Nat) (hk : k < c.gates.length),
    c.evalS initEnv c.gates.length k =
    c.evalGate initEnv (c.evalS initEnv c.gates.length) (c.gates[k]'hk) := by
  intro k hk
  have hid : (c.gates[k]'hk).id = k := h_ids k hk
  -- (1) stability
  conv_lhs => rw [show k = (c.gates[k]'hk).id from hid.symm]
  rw [evalS_stable c initEnv h_uniq k c.gates.length (by omega) le_rfl hk]
  -- (2) step equation
  rw [evalS_succ_apply c initEnv k hk (c.gates[k]'hk).id, hid]; simp
  -- (3) evalGate(initEnv, evalS k, g_k) = evalGate(initEnv, evalS N, g_k)
  symm; apply evalGate_ext
  -- Predecessors: evalS k and evalS N agree on predecessor ids
  intro e he
  have he_edges := inEdges_sub c _ e he
  have hdst := inEdges_dst' c _ e he
  have hsrc_lt : e.src < k := by
    have := h_topo e he_edges; rw [hid] at hdst; omega
  have hsrc_len : e.src < c.gates.length := by omega
  have hsrc_id : (c.gates[e.src]'hsrc_len).id = e.src := h_ids e.src hsrc_len
  conv_lhs => rw [show e.src = (c.gates[e.src]'hsrc_len).id from hsrc_id.symm]
  conv_rhs => rw [show e.src = (c.gates[e.src]'hsrc_len).id from hsrc_id.symm]
  rw [evalS_stable c initEnv h_uniq e.src c.gates.length (by omega) le_rfl hsrc_len]
  rw [evalS_stable c initEnv h_uniq e.src k (by omega) (by omega) hsrc_len]

/-- For input gates, the evaluation equals `evalGate initEnv initEnv`. -/
theorem evalS_input (c : Circuit) (initEnv : Nat → Bool)
    (h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length) (hj : j < c.gates.length),
              i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id)
    (h_ids : ∀ (k : Nat) (hk : k < c.gates.length), (c.gates[k]'hk).id = k)
    (k : Nat) (hk : k < c.gates.length)
    (htype : (c.gates[k]'hk).type.isInput = true) :
    c.evalS initEnv c.gates.length k = c.evalGate initEnv initEnv (c.gates[k]'hk) := by
  have hid := h_ids k hk
  conv_lhs => rw [show k = (c.gates[k]'hk).id from hid.symm]
  rw [evalS_stable c initEnv h_uniq k c.gates.length (by omega) le_rfl hk]
  rw [evalS_succ_apply c initEnv k hk (c.gates[k]'hk).id, hid]; simp
  -- Both sides read from `initEnv` for input gates.
  show c.evalGate initEnv (c.evalS initEnv k) (c.gates[k]'hk) = c.evalGate initEnv initEnv (c.gates[k]'hk)
  unfold evalGate
  cases hgt : (c.gates[k]'hk).type with
  | input _ => rfl
  | _ => simp [hgt, GateType.isInput] at htype

/-- The `eval` function equals `outputGateIds.map (evalS initEnv N)`.
    This connects the top-level API to the `evalS` framework.

    Requires that the caller supplied at least `c.inputWidth` input
    values, so that `eval` does not short-circuit to the zero list. -/
theorem eval_eq_map_evalS (c : Circuit) (inputValues : List Bool)
    (hlen : c.inputWidth ≤ inputValues.length) :
    c.eval inputValues =
    c.outputGateIds.map
      (c.evalS
        (fun id =>
          let posIds := (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id
          let negIds := (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id
          match (posIds.zip inputValues).find? (fun p => p.1 == id) with
          | some (_, v) => v
          | none =>
            match (negIds.zip inputValues).find? (fun p => p.1 == id) with
            | some (_, v) => v
            | none        => false)
        c.gates.length) := by
  unfold Circuit.eval
  rw [if_neg (Nat.not_lt.mpr hlen)]
  simp only [evalS, List.take_length]
  rfl

end Circuit

/-- Output-gate IDs are valid gate indices in a circuit whose gate IDs
    are consecutively numbered 0, 1, 2, … -/
theorem outputGateIds_valid (c : Circuit)
    (h_ids : ∀ (k : Nat) (hk : k < c.gates.length),
             (c.gates[k]'hk).id = k) :
    ∀ k ∈ c.outputGateIds, k < c.gates.length := by
  intro k hk
  simp only [Circuit.outputGateIds, List.mem_map] at hk
  obtain ⟨g, hg_filt, rfl⟩ := hk
  simp only [List.mem_filter] at hg_filt
  obtain ⟨hg_mem, _⟩ := hg_filt
  -- g ∈ c.gates, so g = c.gates[i] for some i < c.gates.length.
  -- By h_ids, (c.gates[i]).id = i, hence g.id = i < c.gates.length.
  obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hg_mem
  rw [← hi_eq, h_ids i hi_lt]
  exact hi_lt

/-- Standalone gate-depth function: computes the depth of the subcircuit
    rooted at gate `id`, using fuel-bounded recursion.
    Equivalent to the internal `depthOf` inside `Circuit.depth`. -/
def Circuit.gateDepth (c : Circuit) (fuel : Nat) (id : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    let preds := (c.inEdges id).map Edge.src
    match preds with
    | [] => 0
    | _ => 1 + (List.foldr max 0) (preds.map (c.gateDepth fuel'))

/-- `gateDepth` agrees with the top-level `depthOf` used in `Circuit.depth`. -/
theorem gateDepth_eq_depth_depthOf (c : Circuit) :
    ∀ fuel id, c.gateDepth fuel id = Circuit.depthOf c fuel id := by
  intro fuel
  induction fuel with
  | zero => intro id; rfl
  | succ n ih =>
    intro id
    simp only [Circuit.gateDepth, Circuit.depthOf]
    split <;> simp_all
    congr 1; congr 1
    funext e; exact ih (Edge.src e)

/-- `Circuit.depth = (List.foldr max 0) (outputGateIds.map (gateDepth c c.size))`. -/
theorem depth_eq_gateDepth (c : Circuit) :
    c.depth = (List.foldr max 0) (c.outputGateIds.map (c.gateDepth c.size)) := by
  simp only [Circuit.depth, Circuit.outputGateIds]
  congr 1
  exact List.map_congr_left (fun x _ => (gateDepth_eq_depth_depthOf c c.size x).symm)

end Circuits
