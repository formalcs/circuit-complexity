import Parity.NormalizeNullary
import Parity.HastadParityProof.LowerBounds.Sharp

set_option linter.style.longLine false

namespace Circuits.CircuitParityLowerBounds
open UnboundedFanInFormula CnfDnf.Families

/-- Removing the output wire leaves at most `c.depth - 1` computation
layers, including when nullary AND/OR gates occur. -/
lemma output_normalizeNullary_depth_add_one_le (c : Circuit) (hwf : c.WellFormed)
    (outId : Nat) (hout : outId ∈ c.outputGateIds) :
    ufiFormulaDepth (normalizeNullary (c.toUFIByPos c.gates.length outId)) + 1 ≤ c.depth := by
  have hk := outputGateIds_valid c hwf.cons_ids outId hout
  have htype : (c.gates[outId]'hk).type = GateType.output := by
    obtain ⟨g, hg, hgid⟩ := List.mem_map.mp hout
    obtain ⟨hgmem, hgtype⟩ := List.mem_filter.mp hg
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hgmem
    have hid : i = outId := by rw [← hwf.cons_ids i hi, hgi]; exact hgid
    subst i
    rw [hgi]
    cases ht : g.type <;> simp_all <;> cases hg
  obtain ⟨f, hf⟩ : ∃ f, c.gates.length = f + 1 :=
    ⟨c.gates.length - 1, by omega⟩
  have hgate := output_gateDepth_le_depth c outId hout
  rw [hf] at hgate ⊢
  simp only [Circuit.toUFIByPos, dif_pos hk, htype]
  cases hhead : (c.inEdges outId).head? with
  | none =>
    have hfan := hwf.fanin_output (c.gates[outId]'hk) (List.getElem_mem hk) htype
    rw [hwf.cons_ids outId hk] at hfan
    have hnil : c.inEdges outId = [] := List.head?_eq_none_iff.mp hhead
    simp [Circuit.fanIn, hnil] at hfan
  | some e =>
    have he : e ∈ c.inEdges outId := mem_of_head?_some' hhead
    have hedges := (List.mem_filter.mp he).1
    have hdst : e.dst = outId := by
      simpa [Circuit.inEdges, beq_iff_eq] using (List.mem_filter.mp he).2
    have hsrc : e.src < outId := by have := hwf.topo e hedges; omega
    have hchild := normalizeNullary_toUFIByPos_depth_le_gateDepth c hwf e.src f
      (by omega) (by omega)
    have hmax := mem_le_foldr_max_map (f := fun e : Edge => c.gateDepth f e.src) he
    have hne : c.inEdges outId ≠ [] := by intro h; simp [h] at hhead
    have hstep : c.gateDepth (f + 1) outId =
        1 + (List.foldr max 0) ((c.inEdges outId).map (fun e => c.gateDepth f e.src)) := by
      cases hlist : c.inEdges outId with
      | nil => exact (hne hlist).elim
      | cons a rest => simp [Circuit.gateDepth, hlist, Function.comp_def]
    rw [hstep] at hgate
    change ufiFormulaDepth (normalizeNullary (c.toUFIByPos f e.src)) + 1 ≤ c.depth
    omega

/-- Håstad's sharp fixed-depth PARITY circuit lower bound.

The parameter `d` counts computation layers. `Circuit.depth` additionally
counts the output wire, hence the hypothesis `circuit.depth ≤ d + 1`.
For fixed `d ≥ 2`, the bound is `exp(Ω_d(n^(1/(d-1))))`. -/
theorem circuit_parity_size_lower_bound_root_sharp (d : Nat) (hd : 2 ≤ d) :
    ∃ N, ∀ n, N ≤ n →
      ∀ (circuit : Circuit),
        circuit.inputWidth = n →
        circuit.depth ≤ d + 1 →
        CircuitComputesParity n circuit →
        2 ^ (Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) /
            (8 * (d + 3))) ≤ circuit.circuitSize := by
  obtain ⟨nRoot, hn_root⟩ :=
    HastadParity.formula_parity_size_lower_bound_root_sharp d hd
  let D := d + 3
  let R := d - 1
  let C := 360 * 40 ^ (d - 2)
  let A := 16 * D
  obtain ⟨nPolylog, hn_polylog⟩ :=
    HastadParity.exists_forall_gt_polylog_le_self (C * A ^ R) R
  refine ⟨max nRoot (max (nPolylog + 1) 1), ?_⟩
  intro n hn circuit h_width h_depth h_parity
  have hn_root_le : nRoot ≤ n := by omega
  have hn_polylog_lt : nPolylog < n := by omega
  have hn_pos : 0 < n := by omega
  obtain ⟨outId, h_out⟩ :=
    outputGateIds_eq_singleton_of_computes n circuit h_parity
  have h_out_mem : outId ∈ circuit.outputGateIds := by
    rw [h_out]
    simp
  have h_out_valid : outId < circuit.gates.length :=
    outputGateIds_valid circuit h_parity.1.cons_ids outId h_out_mem
  let raw := circuit.toUFIByPos circuit.gates.length outId
  let formula := normalizeNullary raw
  have h_formula_inputs : ufiLargestInput formula < n := by
    have h_largest := toUFIByPos_largest_input_lt circuit h_parity.1 (by omega)
      outId circuit.gates.length h_out_valid (by omega)
    simpa [formula, ufiLargestInput, (normalizeNullary_spec raw).2.1, raw, h_width] using h_largest
  have h_gate_depth : circuit.gateDepth circuit.gates.length outId ≤ d + 1 :=
    (output_gateDepth_le_depth circuit outId h_out_mem).trans h_depth
  have h_formula_depth : ufiFormulaDepth formula ≤ d := by
    have h := output_normalizeNullary_depth_add_one_le circuit h_parity.1 outId h_out_mem
    change ufiFormulaDepth formula + 1 ≤ circuit.depth at h
    omega
  have h_formula_parity : FormulaComputesParity n formula := by
    intro inputs h_length
    have h_eval := eval_eq_singleton_toUFIByPos circuit h_parity.1 outId h_out inputs
      (by omega)
    have h_correct := h_parity.2 inputs h_length
    rw [h_eval] at h_correct
    simpa [formula, (normalizeNullary_spec raw).2.2, raw] using h_correct
  have h_formula_lower :=
    hn_root n hn_root_le formula h_formula_inputs h_formula_depth h_formula_parity
  let m := Nat.log 2 n + 1
  let r := Nat.nthRoot R (n / C)
  let e := r / 4
  let q := r / (8 * D)
  have h_c_pos : 0 < C := by positivity
  have h_degree : R ≠ 0 := by dsimp [R]; omega
  have h_d_pos : 0 < D := by simp [D]
  have hm_pos : 1 ≤ m := by simp [m]
  have h_root_scale : A * m ≤ r := by
    rw [show r = Nat.nthRoot R (n / C) by rfl,
      Nat.le_nthRoot_iff h_degree]
    rw [Nat.le_div_iff_mul_le h_c_pos]
    calc
      (A * m) ^ R * C = (C * A ^ R) * m ^ R := by
        rw [Nat.mul_pow]
        ring
      _ ≤ n := by simpa [m] using hn_polylog n hn_polylog_lt
  have hm_le_q : m ≤ q := by
    rw [show q = r / (8 * D) by rfl,
      Nat.le_div_iff_mul_le (by positivity : 0 < 8 * D)]
    have h_half : m * (8 * D) ≤ A * m := by
      dsimp [A]
      nlinarith
    exact h_half.trans h_root_scale
  have h_q_mul : q * (8 * D) ≤ r := by
    dsimp only [q]
    exact Nat.div_mul_le_self r (8 * D)
  have h_r_large : 16 * D ≤ r := by
    have : 16 * D ≤ A * m := by
      dsimp [A]
      nlinarith
    exact this.trans h_root_scale
  have h_exponent : D * (q + 2) ≤ e := by
    rw [show e = r / 4 by rfl,
      Nat.le_div_iff_mul_le (by omega : 0 < 4)]
    nlinarith
  have hn_lt_pow_m : n < 2 ^ m := by
    simpa [m] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hn_lt_pow_q : n < 2 ^ q :=
    lt_of_lt_of_le hn_lt_pow_m (Nat.pow_le_pow_right (by norm_num) hm_le_q)
  by_contra h_circuit_lower
  push Not at h_circuit_lower
  have h_circuit_lt : circuit.circuitSize < 2 ^ q := by
    simpa [D, R, C, r, q] using h_circuit_lower
  have h_base_lt : circuit.gates.length + 1 < 2 ^ (q + 2) := by
    rw [gates_length_eq circuit h_parity.1, h_width]
    calc
      2 * n + circuit.circuitSize + 1 <
          2 * 2 ^ q + 2 ^ q + 1 := by omega
      _ ≤ 4 * 2 ^ q := by
        have : 1 ≤ 2 ^ q := Nat.one_le_pow _ _ (by omega)
        nlinarith
      _ = 2 ^ (q + 2) := by
        rw [pow_add]
        norm_num
        ring
  have h_node_bound_raw :=
    toUFIByPos_node_count_le circuit h_parity.1
      outId circuit.gates.length h_out_valid (by omega)
  have h_node_bound :
      ufiFormulaNodeCount formula ≤ (circuit.gates.length + 1) ^ D := by
    rw [show formula = normalizeNullary raw by rfl, (normalizeNullary_spec raw).1]
    exact h_node_bound_raw.trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [D]; omega))
  have h_formula_lt : ufiFormulaCircuitSize formula < 2 ^ e := by
    calc
      ufiFormulaCircuitSize formula ≤ ufiFormulaNodeCount formula :=
        ufiFormulaCircuitSize_le_node_count formula
      _ ≤ (circuit.gates.length + 1) ^ D := h_node_bound
      _ < (2 ^ (q + 2)) ^ D := by gcongr
      _ = 2 ^ ((q + 2) * D) := by rw [pow_mul]
      _ ≤ 2 ^ e := by
        exact Nat.pow_le_pow_right (by norm_num)
          (by simpa [Nat.mul_comm] using h_exponent)
  have h_formula_lower' : 2 ^ e ≤ ufiFormulaCircuitSize formula := by
    simpa [D, R, C, r, e] using h_formula_lower
  exact (not_lt_of_ge h_formula_lower') h_formula_lt

#print axioms circuit_parity_size_lower_bound_root_sharp

end Circuits.CircuitParityLowerBounds
