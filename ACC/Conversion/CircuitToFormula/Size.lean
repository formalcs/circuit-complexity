import ACC.Circuit.Properties
import ACC.Conversion.CircuitToFormula.Depth

set_option linter.style.setOption false
set_option linter.flexible false

namespace Circuits

namespace DAG.ACCCircuit

/-! ## Size bounds for `ACCCircuit.toACCFormula`

The conversion unrolls shared DAG subcircuits into a formula tree.  This can
duplicate subcircuits, so the natural bound is exponential in the unrolling
depth and polynomial when the circuit depth is constant.
-/

/-- A conservative upper bound for the fan-in branching used by the
    DAG-to-formula unrolling conversion. -/
def formulaUnrollBranchBound (c : ACCCircuit) : Nat :=
  c.edges.length + 2

/-- A conservative upper bound for the size of a formula obtained by unrolling
    a circuit for `fuel` recursive layers.  For constant `fuel`, this is a
    polynomial in the circuit size. -/
def formulaUnrollSizeBound (c : ACCCircuit) (fuel : Nat) : Nat :=
  c.formulaUnrollBranchBound ^ fuel

/-- Size bound advertised by the unrolling conversion.  If the circuit family
    has polynomially many edges and constant depth, this bound is polynomial
    in the input length. -/
def toACCFormulaSizeBound (c : ACCCircuit) : Nat :=
  c.formulaUnrollSizeBound c.toACCFormulaFuel

/-- Unfolding lemma for the advertised size bound. -/
@[simp] lemma toACCFormulaSizeBound_eq (c : ACCCircuit) :
    c.toACCFormulaSizeBound =
      c.formulaUnrollBranchBound ^ c.toACCFormulaFuel := by
  rfl

private lemma list_sum_le_length_mul {xs : List Nat} {b : Nat}
    (h : ∀ x ∈ xs, x ≤ b) : xs.sum ≤ xs.length * b := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.length_cons]
      have hx : x ≤ b := h x (by simp)
      have hxs : xs.sum ≤ xs.length * b := ih (by
        intro y hy
        exact h y (by simp [hy]))
      calc
        x + xs.sum ≤ b + xs.length * b := Nat.add_le_add hx hxs
        _ = (xs.length + 1) * b := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private lemma inEdges_length_le_edges_length (c : ACCCircuit) (id : Nat) :
    (c.inEdges id).length ≤ c.edges.length := by
  unfold ACCCircuit.inEdges
  exact List.length_filter_le _ _

private lemma sum_child_sizes_le_edges_mul_bound (c : ACCCircuit)
    (fuel : Nat) (es : List Edge)
    (hlen : es.length ≤ c.edges.length)
    (hchild : ∀ e ∈ es,
      ACC.ACCFormula.circuitSize (c.gateToACCFormula fuel e.src) ≤
        c.formulaUnrollSizeBound fuel) :
    (es.map (fun e =>
      ACC.ACCFormula.circuitSize (c.gateToACCFormula fuel e.src))).sum ≤
        c.edges.length * c.formulaUnrollSizeBound fuel := by
  apply Nat.le_trans
  · exact list_sum_le_length_mul (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
      exact hchild e he)
  · simpa [List.length_map] using Nat.mul_le_mul_right _ hlen

private lemma one_add_edges_mul_bound_le_branch_mul_bound
    (c : ACCCircuit) (fuel : Nat) :
    1 + c.edges.length * c.formulaUnrollSizeBound fuel ≤
      c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
  unfold formulaUnrollBranchBound
  have hpos : 0 < c.formulaUnrollSizeBound fuel := by
    unfold formulaUnrollSizeBound formulaUnrollBranchBound
    exact Nat.pow_pos (by omega)
  calc
    1 + c.edges.length * c.formulaUnrollSizeBound fuel
        ≤ c.formulaUnrollSizeBound fuel +
            c.edges.length * c.formulaUnrollSizeBound fuel := by
          exact Nat.add_le_add_right (Nat.succ_le_iff.mpr hpos) _
    _ = (c.edges.length + 1) * c.formulaUnrollSizeBound fuel := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ (c.edges.length + 2) * c.formulaUnrollSizeBound fuel := by
          exact Nat.mul_le_mul_right _ (by omega)

private lemma bound_add_one_le_branch_mul_bound
    (c : ACCCircuit) (fuel : Nat) :
    c.formulaUnrollSizeBound fuel + 1 ≤
      c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
  unfold formulaUnrollBranchBound
  have hpos : 0 < c.formulaUnrollSizeBound fuel := by
    unfold formulaUnrollSizeBound formulaUnrollBranchBound
    exact Nat.pow_pos (by omega)
  calc
    c.formulaUnrollSizeBound fuel + 1
        ≤ c.formulaUnrollSizeBound fuel + c.formulaUnrollSizeBound fuel := by
          exact Nat.add_le_add_left (Nat.succ_le_iff.mpr hpos) _
    _ = 2 * c.formulaUnrollSizeBound fuel := by
          rw [Nat.two_mul]
    _ ≤ (c.edges.length + 2) * c.formulaUnrollSizeBound fuel := by
          exact Nat.mul_le_mul_right _ (by omega)

private lemma one_le_formulaUnrollSizeBound (c : ACCCircuit) (fuel : Nat) :
    1 ≤ c.formulaUnrollSizeBound fuel := by
  unfold formulaUnrollSizeBound formulaUnrollBranchBound
  exact Nat.succ_le_iff.mpr (Nat.pow_pos (by omega))

private lemma formulaUnrollSizeBound_succ (c : ACCCircuit) (fuel : Nat) :
    c.formulaUnrollSizeBound (fuel + 1) =
      c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
  unfold formulaUnrollSizeBound
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Unrolling for `fuel` layers produces a formula whose circuit size is
    bounded by `(edges + 2)^fuel`. -/
lemma gateToACCFormula_circuitSize_le_unrollSizeBound (c : ACCCircuit) :
    ∀ (fuel id : Nat),
      ACC.ACCFormula.circuitSize (c.gateToACCFormula fuel id) ≤
        c.formulaUnrollSizeBound fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro id
      simp [gateToACCFormula, ACC.ACCFormula.circuitSize, formulaUnrollSizeBound]
  | succ fuel ih =>
      intro id
      unfold gateToACCFormula
      split
      · simpa [ACC.ACCFormula.circuitSize] using
          one_le_formulaUnrollSizeBound c (fuel + 1)
      · rename_i g hfind
        cases g.type with
        | input negated =>
            simp [ACC.ACCFormula.circuitSize, formulaUnrollSizeBound, formulaUnrollBranchBound]
        | output =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simpa [hhead, ACC.ACCFormula.circuitSize] using
                  one_le_formulaUnrollSizeBound c (fuel + 1)
            | some e =>
                rw [formulaUnrollSizeBound_succ]
                exact Nat.le_trans (ih e.src)
                  (Nat.le_mul_of_pos_left _
                    (by
                      unfold formulaUnrollBranchBound
                      omega))
        | notGate =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simpa [hhead, ACC.ACCFormula.circuitSize] using
                  one_le_formulaUnrollSizeBound c (fuel + 1)
            | some e =>
                rw [formulaUnrollSizeBound_succ]
                have hchild := ih e.src
                simpa [hhead, ACC.ACCFormula.circuitSize] using
                  Nat.le_trans (Nat.add_le_add_right hchild 1)
                    (bound_add_one_le_branch_mul_bound c fuel)
        | andGate =>
            rw [formulaUnrollSizeBound_succ]
            have hsum := sum_child_sizes_le_edges_mul_bound c fuel (c.inEdges g.id)
              (inEdges_length_le_edges_length c g.id)
              (by intro e he; exact ih e.src)
            have hpos : 0 < c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollSizeBound formulaUnrollBranchBound
              exact Nat.pow_pos (by omega)
            have hlt :
                c.edges.length * c.formulaUnrollSizeBound fuel <
                  c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollBranchBound
              exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
            simp only [ACC.ACCFormula.circuitSize, List.map_map, Function.comp_def]
            exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hsum hlt)
        | orGate =>
            rw [formulaUnrollSizeBound_succ]
            have hsum := sum_child_sizes_le_edges_mul_bound c fuel (c.inEdges g.id)
              (inEdges_length_le_edges_length c g.id)
              (by intro e he; exact ih e.src)
            have hpos : 0 < c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollSizeBound formulaUnrollBranchBound
              exact Nat.pow_pos (by omega)
            have hlt :
                c.edges.length * c.formulaUnrollSizeBound fuel <
                  c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollBranchBound
              exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
            simp only [ACC.ACCFormula.circuitSize, List.map_map, Function.comp_def]
            exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hsum hlt)
        | modGate =>
            rw [formulaUnrollSizeBound_succ]
            have hsum := sum_child_sizes_le_edges_mul_bound c fuel (c.inEdges g.id)
              (inEdges_length_le_edges_length c g.id)
              (by intro e he; exact ih e.src)
            have hpos : 0 < c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollSizeBound formulaUnrollBranchBound
              exact Nat.pow_pos (by omega)
            have hlt :
                c.edges.length * c.formulaUnrollSizeBound fuel <
                  c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollBranchBound
              exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
            simp only [ACC.ACCFormula.circuitSize, List.map_map, Function.comp_def]
            exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hsum hlt)

private lemma sum_child_nodeCounts_le_edges_mul_bound (c : ACCCircuit)
    (fuel : Nat) (es : List Edge)
    (hlen : es.length ≤ c.edges.length)
    (hchild : ∀ e ∈ es,
      ACC.ACCFormula.nodeCount (c.gateToACCFormula fuel e.src) ≤
        c.formulaUnrollSizeBound fuel) :
    (es.map (fun e =>
      ACC.ACCFormula.nodeCount (c.gateToACCFormula fuel e.src))).sum ≤
        c.edges.length * c.formulaUnrollSizeBound fuel := by
  apply Nat.le_trans
  · exact list_sum_le_length_mul (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
      exact hchild e he)
  · simpa [List.length_map] using Nat.mul_le_mul_right _ hlen

/-- Unrolling for `fuel` layers produces a formula whose full tree node count
is bounded by `(edges + 2)^fuel`. -/
lemma gateToACCFormula_nodeCount_le_unrollSizeBound (c : ACCCircuit) :
    ∀ (fuel id : Nat),
      ACC.ACCFormula.nodeCount (c.gateToACCFormula fuel id) ≤
        c.formulaUnrollSizeBound fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro id
      simp [gateToACCFormula, ACC.ACCFormula.nodeCount,
        formulaUnrollSizeBound, formulaUnrollBranchBound]
  | succ fuel ih =>
      intro id
      unfold gateToACCFormula
      split
      · simpa [ACC.ACCFormula.nodeCount] using
          one_le_formulaUnrollSizeBound c (fuel + 1)
      · rename_i g hfind
        cases g.type with
        | input negated =>
            simpa [ACC.ACCFormula.nodeCount] using
              one_le_formulaUnrollSizeBound c (fuel + 1)
        | output =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simpa [hhead, ACC.ACCFormula.nodeCount] using
                  one_le_formulaUnrollSizeBound c (fuel + 1)
            | some e =>
                rw [formulaUnrollSizeBound_succ]
                exact Nat.le_trans (ih e.src)
                  (Nat.le_mul_of_pos_left _ (by
                    unfold formulaUnrollBranchBound
                    omega))
        | notGate =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simpa [hhead, ACC.ACCFormula.nodeCount] using
                  one_le_formulaUnrollSizeBound c (fuel + 1)
            | some e =>
                rw [formulaUnrollSizeBound_succ]
                have hchild := ih e.src
                simpa [hhead, ACC.ACCFormula.nodeCount] using
                  Nat.le_trans (Nat.add_le_add_right hchild 1)
                    (bound_add_one_le_branch_mul_bound c fuel)
        | andGate =>
            rw [formulaUnrollSizeBound_succ]
            have hsum := sum_child_nodeCounts_le_edges_mul_bound c fuel
              (c.inEdges g.id) (inEdges_length_le_edges_length c g.id)
              (by intro e he; exact ih e.src)
            have hpos : 0 < c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollSizeBound formulaUnrollBranchBound
              exact Nat.pow_pos (by omega)
            have hlt :
                c.edges.length * c.formulaUnrollSizeBound fuel <
                  c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollBranchBound
              exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
            simp only [ACC.ACCFormula.nodeCount, List.map_map,
              Function.comp_def]
            simpa [Nat.add_comm] using
              Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hsum hlt)
        | orGate =>
            rw [formulaUnrollSizeBound_succ]
            have hsum := sum_child_nodeCounts_le_edges_mul_bound c fuel
              (c.inEdges g.id) (inEdges_length_le_edges_length c g.id)
              (by intro e he; exact ih e.src)
            have hpos : 0 < c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollSizeBound formulaUnrollBranchBound
              exact Nat.pow_pos (by omega)
            have hlt :
                c.edges.length * c.formulaUnrollSizeBound fuel <
                  c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollBranchBound
              exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
            simp only [ACC.ACCFormula.nodeCount, List.map_map,
              Function.comp_def]
            simpa [Nat.add_comm] using
              Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hsum hlt)
        | modGate =>
            rw [formulaUnrollSizeBound_succ]
            have hsum := sum_child_nodeCounts_le_edges_mul_bound c fuel
              (c.inEdges g.id) (inEdges_length_le_edges_length c g.id)
              (by intro e he; exact ih e.src)
            have hpos : 0 < c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollSizeBound formulaUnrollBranchBound
              exact Nat.pow_pos (by omega)
            have hlt :
                c.edges.length * c.formulaUnrollSizeBound fuel <
                  c.formulaUnrollBranchBound * c.formulaUnrollSizeBound fuel := by
              unfold formulaUnrollBranchBound
              exact (Nat.mul_lt_mul_right hpos).mpr (by omega)
            simp only [ACC.ACCFormula.nodeCount, List.map_map,
              Function.comp_def]
            simpa [Nat.add_comm] using
              Nat.succ_le_iff.mpr (Nat.lt_of_le_of_lt hsum hlt)

/-- The converted output formula has size at most the circuit's explicit
    unrolling size bound. -/
lemma toACCFormula_circuitSize_le_sizeBound (c : ACCCircuit) :
    ACC.ACCFormula.circuitSize c.toACCFormula ≤ c.toACCFormulaSizeBound := by
  unfold toACCFormula outputToACCFormula toACCFormulaSizeBound
  cases hhead : c.outputGateIds.head? with
  | none =>
      simpa [ACC.ACCFormula.circuitSize, toACCFormulaSizeBound, formulaUnrollSizeBound,
        toACCFormulaFuel] using one_le_formulaUnrollSizeBound c c.toACCFormulaFuel
  | some outputId =>
      exact gateToACCFormula_circuitSize_le_unrollSizeBound c c.toACCFormulaFuel outputId

/-- The converted output formula's full node count is at most the explicit
unrolling bound. -/
lemma toACCFormula_nodeCount_le_sizeBound (c : ACCCircuit) :
    ACC.ACCFormula.nodeCount c.toACCFormula ≤ c.toACCFormulaSizeBound := by
  unfold toACCFormula outputToACCFormula toACCFormulaSizeBound
  cases hhead : c.outputGateIds.head? with
  | none =>
      simpa [ACC.ACCFormula.nodeCount, toACCFormulaSizeBound,
        formulaUnrollSizeBound, toACCFormulaFuel] using
        one_le_formulaUnrollSizeBound c c.toACCFormulaFuel
  | some outputId =>
      exact gateToACCFormula_nodeCount_le_unrollSizeBound c
        c.toACCFormulaFuel outputId

/-- Public size theorem with no mention of conversion fuel.  The output formula
    size is bounded by an explicit polynomial in the wire-count base
    `edges.length + 2`, with exponent controlled by the input circuit depth. -/
theorem toACCFormula_circuitSize_le_edges_pow_depth (c : ACCCircuit) :
    ACC.ACCFormula.circuitSize c.toACCFormula ≤
      (c.edges.length + 2) ^ (c.depth + 1) := by
  simpa [toACCFormulaSizeBound_eq, toACCFormulaFuel, formulaUnrollBranchBound]
    using toACCFormula_circuitSize_le_sizeBound c

/-- Size measure for the conversion theorem: non-input gates plus wires, with
    slack for constants/unary gates.  A bound solely in terms of
    `ACCCircuit.circuitSize` is not available for arbitrary unbounded fan-in
    DAGs unless one also bounds the number of wires. -/
def formulaConversionInputSize (c : ACCCircuit) : Nat :=
  c.circuitSize + c.edges.length + 2

/-- Public polynomial size theorem with no mention of conversion fuel.  The
    output formula size is bounded by an explicit polynomial in the input
    circuit's conversion-size measure. -/
theorem toACCFormula_circuitSize_le_inputSize_pow_depth (c : ACCCircuit) :
    ACC.ACCFormula.circuitSize c.toACCFormula ≤
      c.formulaConversionInputSize ^ (c.depth + 1) := by
  apply Nat.le_trans (toACCFormula_circuitSize_le_edges_pow_depth c)
  unfold formulaConversionInputSize
  exact Nat.pow_le_pow_left (by omega) _

/-- Full formula-tree analogue of
`toACCFormula_circuitSize_le_inputSize_pow_depth`. -/
theorem toACCFormula_nodeCount_le_inputSize_pow_depth (c : ACCCircuit) :
    ACC.ACCFormula.nodeCount c.toACCFormula ≤
      c.formulaConversionInputSize ^ (c.depth + 1) := by
  apply Nat.le_trans (toACCFormula_nodeCount_le_sizeBound c)
  unfold toACCFormulaSizeBound formulaUnrollSizeBound
    formulaUnrollBranchBound formulaConversionInputSize
  exact Nat.pow_le_pow_left (by omega) _

/-- If an ACC circuit in arity `n` has polynomially many non-input gates, then
    the conversion-size measure used by `toACCFormula` is polynomial in `n`.
    The constants are deliberately simple and conservative. -/
theorem formulaConversionInputSize_le_polynomial_of_circuitSize
    (circuitCoeff circuitDegree : Nat) (n : PNat)
    (c : ACCCircuit) (hwf : c.WellFormed)
    (hwidth : c.inputWidth = n.val)
    (hsize : c.circuitSize ≤ circuitCoeff * n.val ^ circuitDegree) :
    c.formulaConversionInputSize ≤
      (circuitCoeff + (circuitCoeff + 2) ^ 2 + 2) *
        n.val ^ (2 * (2 * (circuitDegree + 1))) := by
  have hnpos : 0 < n.val := n.pos
  have hn_ne : n.val ≠ 0 := Nat.ne_of_gt hnpos
  have hpow_k_le_big :
      n.val ^ circuitDegree ≤ n.val ^ (2 * (circuitDegree + 1)) := by
    exact Nat.pow_le_pow_right hnpos (by omega)
  have hpow_one_le_big :
      n.val ≤ n.val ^ (2 * (circuitDegree + 1)) := by
    simpa using
      (Nat.le_self_pow (n := 2 * (circuitDegree + 1)) (by omega) n.val)
  have hcs_big :
      c.circuitSize ≤ circuitCoeff * n.val ^ (2 * (circuitDegree + 1)) := by
    exact Nat.le_trans hsize (Nat.mul_le_mul_left _ hpow_k_le_big)
  have hgates :
      c.gates.length ≤ (circuitCoeff + 2) *
        n.val ^ (2 * (circuitDegree + 1)) := by
    calc
      c.gates.length ≤ c.circuitSize + 2 * c.inputWidth :=
        gates_length_le_circuitSize_add_two_mul_inputWidth c hwf
      _ = c.circuitSize + 2 * n.val := by rw [hwidth]
      _ ≤ circuitCoeff * n.val ^ (2 * (circuitDegree + 1)) +
          2 * n.val ^ (2 * (circuitDegree + 1)) := by
        exact Nat.add_le_add hcs_big (Nat.mul_le_mul_left 2 hpow_one_le_big)
      _ = (circuitCoeff + 2) * n.val ^ (2 * (circuitDegree + 1)) := by
        rw [Nat.add_mul]
  have hedges :
      c.edges.length ≤ (circuitCoeff + 2) ^ 2 *
        n.val ^ (2 * (2 * (circuitDegree + 1))) := by
    calc
      c.edges.length ≤ c.gates.length * c.gates.length :=
        edges_length_le_gates_length_sq c hwf
      _ ≤ ((circuitCoeff + 2) * n.val ^ (2 * (circuitDegree + 1))) *
          ((circuitCoeff + 2) * n.val ^ (2 * (circuitDegree + 1))) :=
        Nat.mul_le_mul hgates hgates
      _ = (circuitCoeff + 2) ^ 2 *
          n.val ^ (2 * (2 * (circuitDegree + 1))) := by
        rw [Nat.pow_succ, Nat.pow_succ]
        ring
  have hpow_big_le_edgepow :
      n.val ^ (2 * (circuitDegree + 1)) ≤
        n.val ^ (2 * (2 * (circuitDegree + 1))) := by
    exact Nat.pow_le_pow_right hnpos (by omega)
  have hcs_edgepow :
      c.circuitSize ≤ circuitCoeff *
        n.val ^ (2 * (2 * (circuitDegree + 1))) := by
    exact Nat.le_trans hcs_big (Nat.mul_le_mul_left _ hpow_big_le_edgepow)
  have htwo_edgepow :
      2 ≤ 2 * n.val ^ (2 * (2 * (circuitDegree + 1))) := by
    have hone : 1 ≤ n.val ^ (2 * (2 * (circuitDegree + 1))) :=
      Nat.one_le_pow _ _ hnpos
    omega
  unfold formulaConversionInputSize
  calc
    c.circuitSize + c.edges.length + 2
        ≤ circuitCoeff * n.val ^ (2 * (2 * (circuitDegree + 1))) +
          (circuitCoeff + 2) ^ 2 * n.val ^ (2 * (2 * (circuitDegree + 1))) +
          2 * n.val ^ (2 * (2 * (circuitDegree + 1))) := by
          exact Nat.add_le_add (Nat.add_le_add hcs_edgepow hedges) htwo_edgepow
    _ = (circuitCoeff + (circuitCoeff + 2) ^ 2 + 2) *
          n.val ^ (2 * (2 * (circuitDegree + 1))) := by
      rw [Nat.add_mul, Nat.add_mul]

/-- For a constant-depth polynomial-size family member, `toACCFormula` has an
    explicit polynomial size upper bound. -/
theorem toACCFormula_circuitSize_le_polynomial_of_family_member
    (circuitCoeff circuitDegree depthBound : Nat) (n : PNat)
    (c : ACCCircuit) (hwf : c.WellFormed)
    (hwidth : c.inputWidth = n.val)
    (hdepth : c.depth ≤ depthBound)
    (hsize : c.circuitSize ≤ circuitCoeff * n.val ^ circuitDegree) :
    ACC.ACCFormula.circuitSize c.toACCFormula ≤
      (circuitCoeff + (circuitCoeff + 2) ^ 2 + 2) ^ (depthBound + 1) *
        n.val ^ ((2 * (2 * (circuitDegree + 1))) * (depthBound + 1)) := by
  let sizeBase := circuitCoeff + (circuitCoeff + 2) ^ 2 + 2
  let sizeDegree := 2 * (2 * (circuitDegree + 1))
  have hbase : c.formulaConversionInputSize ≤ sizeBase * n.val ^ sizeDegree := by
    simpa [sizeBase, sizeDegree] using
      formulaConversionInputSize_le_polynomial_of_circuitSize circuitCoeff circuitDegree
        n c hwf hwidth hsize
  have hbase_pos : 0 < sizeBase * n.val ^ sizeDegree := by
    have h_size_base : 0 < sizeBase := by unfold sizeBase; omega
    exact Nat.mul_pos h_size_base (Nat.pow_pos n.pos)
  apply Nat.le_trans (toACCFormula_circuitSize_le_inputSize_pow_depth c)
  calc
    c.formulaConversionInputSize ^ (c.depth + 1)
        ≤ (sizeBase * n.val ^ sizeDegree) ^ (c.depth + 1) :=
          Nat.pow_le_pow_left hbase _
    _ ≤ (sizeBase * n.val ^ sizeDegree) ^ (depthBound + 1) :=
          Nat.pow_le_pow_right hbase_pos (by omega)
    _ = sizeBase ^ (depthBound + 1) *
          n.val ^ (sizeDegree * (depthBound + 1)) := by
          rw [Nat.mul_pow, ← Nat.pow_mul]

/-- Full formula-tree size version of
`toACCFormula_circuitSize_le_polynomial_of_family_member`. -/
theorem toACCFormula_nodeCount_le_polynomial_of_family_member
    (circuitCoeff circuitDegree depthBound : Nat) (n : PNat)
    (c : ACCCircuit) (hwf : c.WellFormed)
    (hwidth : c.inputWidth = n.val)
    (hdepth : c.depth ≤ depthBound)
    (hsize : c.circuitSize ≤ circuitCoeff * n.val ^ circuitDegree) :
    ACC.ACCFormula.nodeCount c.toACCFormula ≤
      (circuitCoeff + (circuitCoeff + 2) ^ 2 + 2) ^ (depthBound + 1) *
        n.val ^ ((2 * (2 * (circuitDegree + 1))) * (depthBound + 1)) := by
  let sizeBase := circuitCoeff + (circuitCoeff + 2) ^ 2 + 2
  let sizeDegree := 2 * (2 * (circuitDegree + 1))
  have hbase : c.formulaConversionInputSize ≤ sizeBase * n.val ^ sizeDegree := by
    simpa [sizeBase, sizeDegree] using
      formulaConversionInputSize_le_polynomial_of_circuitSize circuitCoeff
        circuitDegree n c hwf hwidth hsize
  have hbase_pos : 0 < sizeBase * n.val ^ sizeDegree := by
    have h_size_base : 0 < sizeBase := by unfold sizeBase; omega
    exact Nat.mul_pos h_size_base (Nat.pow_pos n.pos)
  apply Nat.le_trans (toACCFormula_nodeCount_le_inputSize_pow_depth c)
  calc
    c.formulaConversionInputSize ^ (c.depth + 1)
        ≤ (sizeBase * n.val ^ sizeDegree) ^ (c.depth + 1) :=
          Nat.pow_le_pow_left hbase _
    _ ≤ (sizeBase * n.val ^ sizeDegree) ^ (depthBound + 1) :=
          Nat.pow_le_pow_right hbase_pos (by omega)
    _ = sizeBase ^ (depthBound + 1) *
          n.val ^ (sizeDegree * (depthBound + 1)) := by
          rw [Nat.mul_pow, ← Nat.pow_mul]

end DAG.ACCCircuit

end Circuits
