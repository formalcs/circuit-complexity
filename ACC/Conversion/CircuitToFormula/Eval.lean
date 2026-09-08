import ACC.Conversion.CircuitToFormula.Basic

set_option linter.style.setOption false
set_option linter.flexible false

namespace Circuits

namespace DAG.ACCCircuit

theorem mem_of_head?_some' {α : Type} {l : List α} {a : α}
    (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x t =>
      simp [List.head?] at h
      subst h
      exact List.Mem.head _

/-! ## Evaluation preservation for `ACCCircuit.toACCFormula`

The conversion recursively unrolls predecessor gates.  This file first defines
the matching recursive semantic evaluator and proves that the generated formula
evaluates exactly like that unrolling.  The final theorem relates this to
`evalCanonical` whenever the fold-based evaluator agrees with the same
unrolling semantics on the circuit outputs.
-/

/-- Recursive semantic unrolling for the gate with id `id`, using `fuel` to
    make the evaluator total.  Inputs are read with the same canonical input
    environment used by `ACCCircuit.evalCanonical`. -/
def unrollEval (c : ACCCircuit) (inputValues : List Bool) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, id =>
      match c.findGate id with
      | none => false
      | some g =>
          match g.type with
          | ACCGateType.input negated =>
              let idx := c.formulaInputIndex g.id negated
              let value := inputValues[idx]?.getD false
              if negated then !value else value
          | ACCGateType.output =>
              match (c.inEdges g.id).head? with
              | some e => unrollEval c inputValues fuel e.src
              | none => false
          | ACCGateType.notGate =>
              match (c.inEdges g.id).head? with
              | some e => !(unrollEval c inputValues fuel e.src)
              | none => false
          | ACCGateType.andGate =>
              let srcs := (c.inEdges g.id).map
                (fun e => unrollEval c inputValues fuel e.src)
              if srcs.all (· == true) then true else false
          | ACCGateType.orGate =>
              let srcs := (c.inEdges g.id).map
                (fun e => unrollEval c inputValues fuel e.src)
              if srcs.any (· == true) then true else false
          | ACCGateType.modGate =>
              let srcs := (c.inEdges g.id).map
                (fun e => unrollEval c inputValues fuel e.src)
              if (srcs.map Bool.toNat).sum % c.p == 0 then true else false

/-- Partial evaluation: environment after processing the first `k` gates. -/
def evalS (c : ACCCircuit) (initEnv : Nat → Bool) (k : Nat) : Nat → Bool :=
  (c.gates.take k).foldl
    (fun (env : Nat → Bool) (g : ACCGate) =>
      fun id => if id == g.id then c.evalGate initEnv env g else env id)
    initEnv

/-- Step equation for `evalS`. -/
theorem evalS_succ (c : ACCCircuit) (initEnv : Nat → Bool)
    (k : Nat) (hk : k < c.gates.length) :
    c.evalS initEnv (k + 1) =
    fun id => if id == (c.gates[k]'hk).id
              then c.evalGate initEnv (c.evalS initEnv k) (c.gates[k]'hk)
              else c.evalS initEnv k id := by
  change (c.gates.take (k + 1)).foldl _ initEnv = _
  conv_lhs =>
    rw [show c.gates.take (k + 1) = c.gates.take k ++ [c.gates[k]'hk] from by
      rw [List.take_add_one]
      simp [List.getElem?_eq_getElem hk]]
  rw [List.foldl_append]
  rfl

/-- Pointwise step equation. -/
theorem evalS_succ_apply (c : ACCCircuit) (initEnv : Nat → Bool)
    (k : Nat) (hk : k < c.gates.length) (id : Nat) :
    c.evalS initEnv (k + 1) id =
    if id == (c.gates[k]'hk).id
    then c.evalGate initEnv (c.evalS initEnv k) (c.gates[k]'hk)
    else c.evalS initEnv k id := by
  rw [evalS_succ c initEnv k hk]

/-- Stability: once a gate has been evaluated, its value does not change. -/
theorem evalS_stable (c : ACCCircuit) (initEnv : Nat → Bool)
    (h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length)
      (hj : j < c.gates.length), i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id)
    (j k : Nat) (hjk : j < k) (hk : k ≤ c.gates.length)
    (hj : j < c.gates.length) :
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
        subst hjeq
        rfl

/-- `evalGate` depends only on predecessor values. -/
theorem evalGate_ext (c : ACCCircuit) (initEnv : Nat → Bool)
    (env₁ env₂ : Nat → Bool) (g : ACCGate)
    (h_pred : ∀ e ∈ c.inEdges g.id, env₁ e.src = env₂ e.src) :
    c.evalGate initEnv env₁ g = c.evalGate initEnv env₂ g := by
  unfold evalGate
  split
  · rfl
  · split
    · next e hhead => exact h_pred e (mem_of_head?_some' hhead)
    · rfl
  · split
    · next e hhead =>
        congr 1
        exact h_pred e (mem_of_head?_some' hhead)
    · rfl
  · have hm : (c.inEdges g.id).map (fun e => env₁ e.src) =
        (c.inEdges g.id).map (fun e => env₂ e.src) :=
      List.map_congr_left fun e he => h_pred e he
    simp only [hm]
  · have hm : (c.inEdges g.id).map (fun e => env₁ e.src) =
        (c.inEdges g.id).map (fun e => env₂ e.src) :=
      List.map_congr_left fun e he => h_pred e he
    simp only [hm]
  · have hm : (c.inEdges g.id).map (fun e => env₁ e.src) =
        (c.inEdges g.id).map (fun e => env₂ e.src) :=
      List.map_congr_left fun e he => h_pred e he
    simp only [hm]

theorem inEdges_sub (c : ACCCircuit) (gid : Nat) (e : Edge)
    (he : e ∈ c.inEdges gid) : e ∈ c.edges :=
  (List.mem_filter.mp he).1

theorem inEdges_dst' (c : ACCCircuit) (gid : Nat) (e : Edge)
    (he : e ∈ c.inEdges gid) : e.dst = gid := by
  have := (List.mem_filter.mp he).2
  simp [beq_iff_eq] at this
  exact this

/-- Fixed-point property of final step evaluation. -/
theorem evalS_fp (c : ACCCircuit) (initEnv : Nat → Bool)
    (h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length)
      (hj : j < c.gates.length), i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id)
    (h_ids : ∀ (k : Nat) (hk : k < c.gates.length), (c.gates[k]'hk).id = k)
    (h_topo : ∀ e ∈ c.edges, e.src < e.dst) :
    ∀ (k : Nat) (hk : k < c.gates.length),
    c.evalS initEnv c.gates.length k =
    c.evalGate initEnv (c.evalS initEnv c.gates.length) (c.gates[k]'hk) := by
  intro k hk
  have hid : (c.gates[k]'hk).id = k := h_ids k hk
  conv_lhs => rw [show k = (c.gates[k]'hk).id from hid.symm]
  rw [evalS_stable c initEnv h_uniq k c.gates.length (by omega) le_rfl hk]
  rw [evalS_succ_apply c initEnv k hk (c.gates[k]'hk).id, hid]
  simp
  symm
  apply evalGate_ext
  intro e he
  have he_edges := inEdges_sub c _ e he
  have hdst := inEdges_dst' c _ e he
  have hsrc_lt : e.src < k := by
    have := h_topo e he_edges
    rw [hid] at hdst
    omega
  have hsrc_len : e.src < c.gates.length := by omega
  have hsrc_id : (c.gates[e.src]'hsrc_len).id = e.src := h_ids e.src hsrc_len
  conv_lhs => rw [show e.src = (c.gates[e.src]'hsrc_len).id from hsrc_id.symm]
  conv_rhs => rw [show e.src = (c.gates[e.src]'hsrc_len).id from hsrc_id.symm]
  rw [evalS_stable c initEnv h_uniq e.src c.gates.length (by omega) le_rfl hsrc_len]
  rw [evalS_stable c initEnv h_uniq e.src k (by omega) (by omega) hsrc_len]

/-- Input gates read directly from the initial environment. -/
theorem evalS_input (c : ACCCircuit) (initEnv : Nat → Bool)
    (h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length)
      (hj : j < c.gates.length), i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id)
    (h_ids : ∀ (k : Nat) (hk : k < c.gates.length), (c.gates[k]'hk).id = k)
    (k : Nat) (hk : k < c.gates.length)
    (htype : (c.gates[k]'hk).type.isInput = true) :
    c.evalS initEnv c.gates.length k = c.evalGate initEnv initEnv (c.gates[k]'hk) := by
  have hid := h_ids k hk
  conv_lhs => rw [show k = (c.gates[k]'hk).id from hid.symm]
  rw [evalS_stable c initEnv h_uniq k c.gates.length (by omega) le_rfl hk]
  rw [evalS_succ_apply c initEnv k hk (c.gates[k]'hk).id, hid]
  simp
  show c.evalGate initEnv (c.evalS initEnv k) (c.gates[k]'hk) =
    c.evalGate initEnv initEnv (c.gates[k]'hk)
  unfold evalGate
  cases hgt : (c.gates[k]'hk).type with
  | input _ => rfl
  | _ => simp [hgt, ACCGateType.isInput] at htype

/-- `findGate` finds the gate at its consecutive id in a well-formed circuit. -/
lemma findGate_of_getElem (c : ACCCircuit) (hwf : c.WellFormed)
    (k : Nat) (hk : k < c.gates.length) :
    c.findGate k = some (c.gates[k]'hk) := by
  unfold findGate
  have hid : (c.gates[k]'hk).id = k := hwf.cons_ids k hk
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · simp [hid]
  · exact ⟨k, hk, rfl, by
      intro j hj
      have hjlen : j < c.gates.length := by omega
      have hjid : (c.gates[j]'hjlen).id = j := hwf.cons_ids j hjlen
      simp [hjid]
      omega⟩

lemma positive_input_id_lt_inputWidth (c : ACCCircuit) (hwf : c.WellFormed)
    {k : Nat} {hk : k < c.gates.length}
    (htype : (c.gates[k]'hk).type = ACCGateType.input false) :
    k < c.inputWidth := by
  have hmem : k ∈ c.positiveInputIds := by
    unfold positiveInputIds
    rw [List.mem_map]
    refine ⟨c.gates[k]'hk, ?_, hwf.cons_ids k hk⟩
    rw [List.mem_filter]
    exact ⟨List.getElem_mem hk, by rw [htype]; rfl⟩
  rw [hwf.has_canonical_input_ids.1] at hmem
  simpa using List.mem_range.mp hmem

lemma negative_input_id_bounds (c : ACCCircuit) (hwf : c.WellFormed)
    {k : Nat} {hk : k < c.gates.length}
    (htype : (c.gates[k]'hk).type = ACCGateType.input true) :
    c.inputWidth ≤ k ∧ k < 2 * c.inputWidth := by
  have hmem : k ∈ c.negativeInputIds := by
    unfold negativeInputIds
    rw [List.mem_map]
    refine ⟨c.gates[k]'hk, ?_, hwf.cons_ids k hk⟩
    rw [List.mem_filter]
    exact ⟨List.getElem_mem hk, by rw [htype]; rfl⟩
  rw [hwf.has_canonical_input_ids.2] at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, rfl⟩
  have hi' : i < c.inputWidth := by simpa using List.mem_range.mp hi
  omega

/-- Final step evaluation agrees with recursive unrolling when the unrolling
    fuel exceeds the predecessor depth of the gate. -/
theorem unrollEval_eq_evalS_of_depth_lt_fuel (c : ACCCircuit) (hwf : c.WellFormed)
    (inputValues : List Bool) :
    ∀ (k fuel depthFuel : Nat), k < c.gates.length → k < depthFuel →
      c.depthOf depthFuel k < fuel →
      c.unrollEval inputValues fuel k =
        c.evalS (canonicalInitEnv c.inputWidth inputValues) c.gates.length k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
      intro fuel depthFuel hk hk_depthFuel hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨depthFuel', hdepthFuel⟩ : ∃ d, depthFuel = d + 1 :=
        ⟨depthFuel - 1, by omega⟩
      subst hdepthFuel
      have hfind := findGate_of_getElem c hwf k hk
      have h_uniq : ∀ (i : Nat) (j : Nat) (hi : i < c.gates.length)
          (hj : j < c.gates.length), i ≠ j →
          (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id := by
        intro i j hi hj hij
        rw [hwf.cons_ids i hi, hwf.cons_ids j hj]
        exact hij
      have pred_info : ∀ e, e ∈ c.inEdges k →
          e.src < k ∧ e.src < c.gates.length := by
        intro e he
        have he_edge := inEdges_sub c _ e he
        have hdst := inEdges_dst' c _ e he
        have := hwf.topo e he_edge
        exact ⟨by omega, by omega⟩
      have pred_depth_lt : ∀ e ∈ c.inEdges k, c.depthOf depthFuel' e.src < fuel' := by
        intro e he
        have hsrc_mem :
            c.depthOf depthFuel' e.src ∈
              List.map (c.depthOf depthFuel' ∘ Edge.src) (c.inEdges k) := by
          rw [List.mem_map]
          exact ⟨e, he, rfl⟩
        change
          (match (((c.inEdges k).map Edge.src).map (c.depthOf depthFuel')).max? with
          | some d => d + 1
          | none => 0) < fuel' + 1 at hfuel
        cases hmax : (List.map (c.depthOf depthFuel' ∘ Edge.src) (c.inEdges k)).max? with
        | none =>
            have hnil := List.max?_eq_none_iff.mp hmax
            simp [hnil] at hsrc_mem
        | some d =>
            have hle : c.depthOf depthFuel' e.src ≤ d := by
              have hmax_info := (List.max?_eq_some_iff.mp hmax).2
              exact hmax_info (c.depthOf depthFuel' e.src) hsrc_mem
            simp [hmax] at hfuel
            omega
      have hfp := evalS_fp c (canonicalInitEnv c.inputWidth inputValues)
        h_uniq hwf.cons_ids hwf.topo k hk
      cases htype : (c.gates[k]'hk).type with
      | input negated =>
          have hinput : (c.gates[k]'hk).type.isInput = true := by simp [htype, ACCGateType.isInput]
          rw [evalS_input c (canonicalInitEnv c.inputWidth inputValues)
            h_uniq hwf.cons_ids k hk hinput]
          unfold unrollEval
          simp [hfind, htype, evalGate, hwf.cons_ids k hk, formulaInputIndex]
          cases negated with
          | false =>
              have hpos := positive_input_id_lt_inputWidth c hwf htype
              simp [canonicalInitEnv, hpos]
          | true =>
              have hneg := negative_input_id_bounds c hwf htype
              simp [canonicalInitEnv, hneg.1, hneg.2]
      | output =>
          rw [hfp]
          unfold unrollEval evalGate
          simp [hfind, htype, hwf.cons_ids k hk]
          cases hhead : (c.inEdges k).head? with
          | none => simp
          | some e =>
              have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
              have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
              have ih_e := ih e.src hsrc_lt fuel' depthFuel' hsrc_len
                (by omega) (pred_depth_lt e he)
              simp [ih_e]
      | notGate =>
          rw [hfp]
          unfold unrollEval evalGate
          simp [hfind, htype, hwf.cons_ids k hk]
          cases hhead : (c.inEdges k).head? with
          | none => simp
          | some e =>
              have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
              have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
              have ih_e := ih e.src hsrc_lt fuel' depthFuel' hsrc_len
                (by omega) (pred_depth_lt e he)
              simp [ih_e]
      | andGate =>
          rw [hfp]
          unfold unrollEval evalGate
          simp [hfind, htype, hwf.cons_ids k hk]
          have hpoint : ∀ e ∈ c.inEdges k,
              c.unrollEval inputValues fuel' e.src =
                c.evalS (canonicalInitEnv c.inputWidth inputValues)
                  c.gates.length e.src := by
            intro e he
            have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
            exact ih e.src hsrc_lt fuel' depthFuel' hsrc_len (by omega)
              (pred_depth_lt e he)
          constructor
          · intro h e he
            rw [← hpoint e he]
            exact h e he
          · intro h e he
            rw [hpoint e he]
            exact h e he
      | orGate =>
          rw [hfp]
          unfold unrollEval evalGate
          simp [hfind, htype, hwf.cons_ids k hk]
          have hpoint : ∀ e ∈ c.inEdges k,
              c.unrollEval inputValues fuel' e.src =
                c.evalS (canonicalInitEnv c.inputWidth inputValues)
                  c.gates.length e.src := by
            intro e he
            have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
            exact ih e.src hsrc_lt fuel' depthFuel' hsrc_len (by omega)
              (pred_depth_lt e he)
          constructor
          · intro h
            rcases h with ⟨e, he, hev⟩
            exact ⟨e, he, by rwa [← hpoint e he]⟩
          · intro h
            rcases h with ⟨e, he, hev⟩
            exact ⟨e, he, by rwa [hpoint e he]⟩
      | modGate =>
          rw [hfp]
          unfold unrollEval evalGate
          simp [hfind, htype, hwf.cons_ids k hk]
          have hmap :
              List.map (Bool.toNat ∘ fun e => c.unrollEval inputValues fuel' e.src)
                  (c.inEdges k) =
                List.map
                  (Bool.toNat ∘ fun e =>
                    c.evalS (canonicalInitEnv c.inputWidth inputValues)
                      c.gates.length e.src)
                  (c.inEdges k) := by
            apply List.map_congr_left
            intro e he
            have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
            simp [Function.comp,
              ih e.src hsrc_lt fuel' depthFuel' hsrc_len (by omega) (pred_depth_lt e he)]
          rw [hmap]

/-- The formula produced by `gateToACCFormula` evaluates exactly like the
    recursive semantic unrolling with the same fuel. -/
lemma gateToACCFormula_eval_eq_unrollEval
    (c : ACCCircuit) (inputValues : List Bool) :
    ∀ (fuel id : Nat),
      ACC.ACCFormula.eval (c.gateToACCFormula fuel id) inputValues =
        c.unrollEval inputValues fuel id := by
  intro fuel
  induction fuel with
  | zero =>
      intro id
      simp [gateToACCFormula, unrollEval, ACC.ACCFormula.eval]
  | succ fuel ih =>
      intro id
      unfold gateToACCFormula unrollEval
      split
      · rename_i hfind
        simp [hfind, ACC.ACCFormula.eval]
      · rename_i g hfind
        cases htype : g.type with
        | input negated =>
            simp [hfind, htype, ACC.ACCFormula.eval, formulaInputIndex]
        | output =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simp [hfind, htype, hhead, ACC.ACCFormula.eval]
            | some e =>
                simp [hfind, htype, hhead, ih]
        | andGate =>
            simp [hfind, htype, ACC.ACCFormula.eval, ih]
        | orGate =>
            simp [hfind, htype, ACC.ACCFormula.eval, ih]
        | notGate =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simp [hfind, htype, hhead, ACC.ACCFormula.eval]
            | some e =>
                simp [hfind, htype, hhead, ACC.ACCFormula.eval, ih]
        | modGate =>
            have hmap :
                List.map
                    (Bool.toNat ∘ (fun f => ACC.ACCFormula.eval f inputValues) ∘
                      fun e => c.gateToACCFormula fuel e.src)
                    (c.inEdges g.id) =
                  List.map
                    (Bool.toNat ∘ fun e => c.unrollEval inputValues fuel e.src)
                    (c.inEdges g.id) := by
              apply List.map_congr_left
              intro e _he
              simp [Function.comp, ih e.src]
            simp [hfind, htype, ACC.ACCFormula.eval, hmap]

/-- All converted output formulas agree with recursive semantic unrolling. -/
theorem toACCFormulas_eval_eq_unrollEval
    (c : ACCCircuit) (inputValues : List Bool) :
    (c.toACCFormulas.map (fun f => ACC.ACCFormula.eval f inputValues)) =
      c.outputGateIds.map (fun id => c.unrollEval inputValues c.toACCFormulaFuel id) := by
  unfold toACCFormulas outputToACCFormula
  simp [gateToACCFormula_eval_eq_unrollEval]

/-- Single-output version: `toACCFormula` agrees with recursive semantic
    unrolling of the first output gate, with `false` as the no-output fallback. -/
theorem toACCFormula_eval_eq_unrollEval_head
    (c : ACCCircuit) (inputValues : List Bool) :
    ACC.ACCFormula.eval c.toACCFormula inputValues =
      match c.outputGateIds.head? with
      | some outputId => c.unrollEval inputValues c.toACCFormulaFuel outputId
      | none => false := by
  unfold toACCFormula outputToACCFormula
  cases hhead : c.outputGateIds.head? with
  | none =>
      simp [ACC.ACCFormula.eval]
  | some outputId =>
      simp [gateToACCFormula_eval_eq_unrollEval]

/-- If the fold-based canonical evaluator agrees with recursive unrolling on
    every output, then every converted output formula evaluates to the same
    Boolean output.  This isolates the remaining fold-vs-recursion invariant
    from the formula conversion proof. -/
theorem toACCFormulas_eval_eq_evalCanonical_of_unrollEval_outputs
    (c : ACCCircuit) (inputValues : List Bool)
    (h :
      c.evalCanonical inputValues =
        c.outputGateIds.map (fun id => c.unrollEval inputValues c.toACCFormulaFuel id)) :
    (c.toACCFormulas.map (fun f => ACC.ACCFormula.eval f inputValues)) =
      c.evalCanonical inputValues := by
  rw [toACCFormulas_eval_eq_unrollEval, h]

/-- Single-output preservation statement for `toACCFormula`, assuming the
    corresponding first canonical output agrees with recursive unrolling. -/
theorem toACCFormula_eval_eq_evalCanonical_head_of_unrollEval
    (c : ACCCircuit) (inputValues : List Bool)
    (h :
      (c.evalCanonical inputValues).head?.getD false =
        (match c.outputGateIds.head? with
        | some outputId => c.unrollEval inputValues c.toACCFormulaFuel outputId
        | none => false)) :
    ACC.ACCFormula.eval c.toACCFormula inputValues =
      (c.evalCanonical inputValues).head?.getD false := by
  rw [toACCFormula_eval_eq_unrollEval_head, ← h]

/-- With enough input values, `evalCanonical` is the final step evaluator
    mapped over the output ids. -/
theorem evalCanonical_eq_map_evalS (c : ACCCircuit) (inputValues : List Bool)
    (hlen : c.inputWidth ≤ inputValues.length) :
    c.evalCanonical inputValues =
      c.outputGateIds.map
        (c.evalS (canonicalInitEnv c.inputWidth inputValues) c.gates.length) := by
  unfold evalCanonical
  rw [if_neg (Nat.not_lt.mpr hlen)]
  simp only [evalS, List.take_length]

lemma output_gate_id_lt_size (c : ACCCircuit) (hwf : c.WellFormed)
    {id : Nat} (hid : id ∈ c.outputGateIds) : id < c.size := by
  unfold outputGateIds at hid
  rw [List.mem_map] at hid
  rcases hid with ⟨g, hg, hgid⟩
  rw [List.mem_filter] at hg
  rcases hg with ⟨hgates, _htype⟩
  rw [List.mem_iff_getElem] at hgates
  rcases hgates with ⟨k, hk, hg_eq⟩
  subst hg_eq
  rw [← hgid, hwf.cons_ids k hk]
  unfold size
  exact hk

lemma output_gate_depth_lt_toACCFormulaFuel (c : ACCCircuit)
    {id : Nat} (hid : id ∈ c.outputGateIds) :
    c.depthOf c.size id < c.toACCFormulaFuel := by
  have hmem_depth :
      c.depthOf c.size id ∈ c.outputGateIds.map (c.depthOf c.size) :=
    List.mem_map_of_mem (f := c.depthOf c.size) hid
  unfold toACCFormulaFuel depth
  cases hmax : (c.outputGateIds.map (c.depthOf c.size)).max? with
  | none =>
      have hnil := List.max?_eq_none_iff.mp hmax
      simp [hnil] at hmem_depth
  | some d =>
      have hle : c.depthOf c.size id ≤ d := by
        have hmax_info := (List.max?_eq_some_iff.mp hmax).2
        exact hmax_info (c.depthOf c.size id) hmem_depth
      simp
      omega

/-- On well-formed ACC circuits and valid-length inputs, the recursive
    unrolling semantics agrees with canonical evaluation on every output. -/
theorem evalCanonical_eq_unrollEval_outputs
    (c : ACCCircuit) (hwf : c.WellFormed) (inputValues : List Bool)
    (hlen : c.inputWidth ≤ inputValues.length) :
    c.evalCanonical inputValues =
      c.outputGateIds.map (fun id => c.unrollEval inputValues c.toACCFormulaFuel id) := by
  rw [evalCanonical_eq_map_evalS c inputValues hlen]
  apply List.map_congr_left
  intro id hid
  have hid_size : id < c.size := output_gate_id_lt_size c hwf hid
  have hdepth : c.depthOf c.size id < c.toACCFormulaFuel :=
    output_gate_depth_lt_toACCFormulaFuel c hid
  exact (unrollEval_eq_evalS_of_depth_lt_fuel c hwf inputValues
    id c.toACCFormulaFuel c.size (by simpa [size] using hid_size)
    hid_size hdepth).symm

/-- Single-output preservation for `toACCFormula`: for well-formed circuits and
    valid-length inputs, formula evaluation agrees with the first canonical
    output bit. -/
theorem toACCFormula_eval_eq_evalCanonical_head_of_ge
    (c : ACCCircuit) (hwf : c.WellFormed) (inputValues : List Bool)
    (hlen : c.inputWidth ≤ inputValues.length) :
    ACC.ACCFormula.eval c.toACCFormula inputValues =
      (c.evalCanonical inputValues).head?.getD false := by
  rw [toACCFormula_eval_eq_unrollEval_head]
  rw [evalCanonical_eq_unrollEval_outputs c hwf inputValues hlen]
  cases c.outputGateIds with
  | nil => simp
  | cons outputId rest => simp

end DAG.ACCCircuit

end Circuits
