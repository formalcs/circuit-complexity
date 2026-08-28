import Parity.CircuitParityLowerBounds
import Parity.HastadParityProof.LowerBounds.OneThird

set_option linter.style.longLine false

namespace Circuits

open UnboundedFanInFormula
open CnfDnf.Families
namespace CircuitParityLowerBounds

/-- One-third-live root lower bound for the size of the original circuit.

    Unfolding the unique output into a formula is only an implementation
    detail of the proof.  Absorbing the depth-`d` unfolding overhead weakens
    the formula exponent by the factor `2 * (d + 2)`, leaving a conclusion
    stated solely with `circuit.circuitSize`. -/
theorem circuit_parity_size_lower_bound_root_one_third (d : Nat) :
    ∃ N, ∀ n, N ≤ n →
      ∀ (circuit : Circuit),
        circuit.inputWidth = n →
        circuit.depth ≤ d →
        CircuitComputesParity n circuit →
        2 ^ (Nat.nthRoot (d + 2) (n / (360 * 40 ^ d)) /
            (8 * (d + 2))) ≤ circuit.circuitSize := by
  obtain ⟨nRoot, hn_root⟩ :=
    HastadParity.formula_parity_size_lower_bound_root_one_third (d + 1)
  let D := d + 2
  let C := 360 * 40 ^ d
  let A := 16 * D
  obtain ⟨nPolylog, hn_polylog⟩ :=
    HastadParity.exists_forall_gt_polylog_le_self (C * A ^ D) D
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
  let formula := circuit.toUFIByPos circuit.gates.length outId
  have h_formula_inputs : ufiLargestInput formula < n := by
    have h_largest := toUFIByPos_largest_input_lt circuit h_parity.1 (by omega)
      outId circuit.gates.length h_out_valid (by omega)
    simpa [formula, h_width] using h_largest
  have h_gate_depth : circuit.gateDepth circuit.gates.length outId ≤ d :=
    (output_gateDepth_le_depth circuit outId h_out_mem).trans h_depth
  have h_formula_depth : ufiFormulaDepth formula ≤ d + 1 := by
    have h_unfolded_depth :=
      toUFIByPos_depth_le_gateDepth_add_one circuit h_parity.1
        outId circuit.gates.length h_out_valid (by omega)
    dsimp only [formula]
    omega
  have h_formula_parity : FormulaComputesParity n formula := by
    intro inputs h_length
    have h_eval := eval_eq_singleton_toUFIByPos circuit h_parity.1 outId h_out inputs
      (by omega)
    have h_correct := h_parity.2 inputs h_length
    rw [h_eval] at h_correct
    simpa [formula] using h_correct
  have h_formula_lower :=
    hn_root n hn_root_le formula h_formula_inputs h_formula_depth h_formula_parity
  let m := Nat.log 2 n + 1
  let r := Nat.nthRoot D (n / C)
  let e := r / 4
  let q := r / (8 * D)
  have h_c_pos : 0 < C := by positivity
  have h_degree : D ≠ 0 := by simp [D]
  have h_d_pos : 0 < D := by simp [D]
  have hm_pos : 1 ≤ m := by simp [m]
  have h_root_scale : A * m ≤ r := by
    rw [show r = Nat.nthRoot D (n / C) by rfl,
      Nat.le_nthRoot_iff h_degree]
    rw [Nat.le_div_iff_mul_le h_c_pos]
    calc
      (A * m) ^ D * C = (C * A ^ D) * m ^ D := by
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
    simpa [D, C, r, q] using h_circuit_lower
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
    dsimp only [formula]
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
    simpa [D, C, r, e] using h_formula_lower
  exact (not_lt_of_ge h_formula_lower') h_formula_lt

#print axioms circuit_parity_size_lower_bound_root_one_third

/-- General eventual lower bound for polynomial-size, constant-depth
    circuits, obtained by comparing their bundled polynomial size upper bound
    directly with `circuit_parity_size_lower_bound_root_one_third`. -/
theorem hastad_parity_lower_bound_general (c k d : Nat) :
    ∃ N, ∀ n, N < n →
      ∀ (circuit : UFICircuitOfSizeAtMostPolyNAndDepthAtMostD n c k d),
        ¬ CircuitComputesParity n circuit.val := by
  obtain ⟨nRoot, hn_root⟩ := circuit_parity_size_lower_bound_root_one_third d
  let D := d + 2
  let C := 360 * 40 ^ d
  let A := 8 * D * (k + 2)
  obtain ⟨nPolylog, hn_polylog⟩ :=
    HastadParity.exists_forall_gt_polylog_le_self (C * A ^ D) D
  refine ⟨max nRoot (max nPolylog (max c 1)), ?_⟩
  intro n hn circuit h_parity
  have hn_root_le : nRoot ≤ n := by omega
  have hn_polylog_lt : nPolylog < n := by omega
  have hc_le_n : c ≤ n := by omega
  have hn_pos : 0 < n := by omega
  have h_circuit_lower :=
    hn_root n hn_root_le circuit.val circuit.property.2.1 circuit.property.2.2.1 h_parity
  let m := Nat.log 2 n + 1
  let r := Nat.nthRoot D (n / C)
  let q := r / (8 * D)
  have h_c_pos : 0 < C := by positivity
  have h_degree : D ≠ 0 := by simp [D]
  have hm_pos : 1 ≤ m := by simp [m]
  have h_root_scale : A * m ≤ r := by
    rw [show r = Nat.nthRoot D (n / C) by rfl,
      Nat.le_nthRoot_iff h_degree]
    rw [Nat.le_div_iff_mul_le h_c_pos]
    calc
      (A * m) ^ D * C = (C * A ^ D) * m ^ D := by
        rw [Nat.mul_pow]
        ring
      _ ≤ n := by simpa [m] using hn_polylog n hn_polylog_lt
  have h_exponent_scale : (k + 2) * m ≤ q := by
    rw [show q = r / (8 * D) by rfl,
      Nat.le_div_iff_mul_le (by positivity : 0 < 8 * D)]
    simpa [A, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_root_scale
  let logSize := Nat.log 2 (c * n ^ k)
  have hn_lt_pow : n < 2 ^ m := by
    simpa [m] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have h_size_poly : c * n ^ k ≤ n ^ (k + 1) := by
    calc
      c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul hc_le_n (le_refl _)
      _ = n ^ (k + 1) := by ring
  have h_pow_bound : n ^ (k + 1) ≤ 2 ^ ((k + 1) * m) := by
    calc
      n ^ (k + 1) ≤ (2 ^ m) ^ (k + 1) :=
        Nat.pow_le_pow_left (le_of_lt hn_lt_pow) (k + 1)
      _ = 2 ^ (m * (k + 1)) := by rw [← pow_mul]
      _ = 2 ^ ((k + 1) * m) := by rw [Nat.mul_comm m (k + 1)]
  have h_log_size : logSize ≤ (k + 1) * m := by
    calc
      logSize = Nat.log 2 (c * n ^ k) := rfl
      _ ≤ Nat.log 2 (n ^ (k + 1)) := Nat.log_mono_right h_size_poly
      _ ≤ Nat.log 2 (2 ^ ((k + 1) * m)) := Nat.log_mono_right h_pow_bound
      _ = (k + 1) * m := Nat.log_pow (by norm_num) _
  have h_log_succ : logSize + 1 ≤ q := by
    apply le_trans (show logSize + 1 ≤ (k + 2) * m by
      calc
        logSize + 1 ≤ (k + 1) * m + 1 := Nat.add_le_add_right h_log_size 1
        _ ≤ (k + 1) * m + m := Nat.add_le_add_left hm_pos _
        _ = (k + 2) * m := by ring)
    exact h_exponent_scale
  have h_poly_lt : c * n ^ k < 2 ^ q := by
    have h_log_lt : c * n ^ k < 2 ^ (logSize + 1) := by
      simpa [logSize] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (c * n ^ k)
    exact lt_of_lt_of_le h_log_lt
      (Nat.pow_le_pow_right (by norm_num) h_log_succ)
  have h_circuit_lt : circuit.val.circuitSize < 2 ^ q :=
    lt_of_le_of_lt circuit.property.2.2.2.1 h_poly_lt
  have h_circuit_lower' : 2 ^ q ≤ circuit.val.circuitSize := by
    simpa [D, C, r, q] using h_circuit_lower
  exact (not_lt_of_ge h_circuit_lower') h_circuit_lt

#print axioms hastad_parity_lower_bound_general

end CircuitParityLowerBounds

/-- Parity has no polynomial-size, constant-depth family of unbounded-fan-in
    circuits. The threshold is uniform over all families with fixed
    parameters `c`, `k`, and `d`. -/
theorem parity_does_not_have_ac0_circuits :
    ∀ (c k d : Nat),
      ∃ N,
        ∀ (n : PNat) (circuitFamily : AC0CircuitFamily c k d),
          n.val > N →
            ¬ CircuitComputesParity n.val (circuitFamily n).val := by
  intro c k d
  obtain ⟨N, h_n⟩ :=
    CircuitParityLowerBounds.hastad_parity_lower_bound_general c k d
  refine ⟨N, ?_⟩
  intro n circuitFamily hn
  exact h_n n.val hn (circuitFamily n)

#print axioms parity_does_not_have_ac0_circuits

end Circuits
