import ACC.Conversion.CircuitToFormula.Inputs

namespace Circuits

namespace DAG.ACCCircuit

/-! ## Depth bounds for `ACCCircuit.toACCFormula`

The conversion follows predecessor edges and spends one unit of fuel per
recursive layer, so the formula depth is controlled by the same fuel used for
unrolling.
-/

/-- A conservative upper bound for the depth of a formula obtained by unrolling
    a circuit for `fuel` recursive layers. -/
def formulaUnrollDepthBound (_c : ACCCircuit) (fuel : Nat) : Nat :=
  fuel

/-- Depth bound advertised by the unrolling conversion.  It is linear in the
    unrolling fuel; for constant-depth circuit families this is a constant
    factor/additive-constant overhead. -/
def toACCFormulaDepthBound (c : ACCCircuit) : Nat :=
  c.formulaUnrollDepthBound c.toACCFormulaFuel

/-- Unfolding lemma for the advertised depth bound. -/
@[simp] lemma toACCFormulaDepthBound_eq (c : ACCCircuit) :
    c.toACCFormulaDepthBound = c.toACCFormulaFuel := by
  rfl

private lemma foldl_max_le {xs : List Nat} {a b : Nat}
    (ha : a ≤ b) (hxs : ∀ x ∈ xs, x ≤ b) :
    xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil =>
      simpa using ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_le ha (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

private lemma max?_getD_le {xs : List Nat} {b : Nat}
    (h : ∀ x ∈ xs, x ≤ b) : xs.max?.getD 0 ≤ b := by
  cases xs with
  | nil =>
      simp
  | cons x xs =>
      change xs.foldl max x ≤ b
      exact foldl_max_le (h x (by simp)) (by
        intro y hy
        exact h y (by simp [hy]))

/-- Unrolling for `fuel` layers produces a formula of depth at most `fuel`. -/
lemma gateToACCFormula_depth_le_fuel (c : ACCCircuit) :
    ∀ (fuel id : Nat),
      ACC.ACCFormula.depth (c.gateToACCFormula fuel id) ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro id
      simp [gateToACCFormula, ACC.ACCFormula.depth]
  | succ fuel ih =>
      intro id
      unfold gateToACCFormula
      split
      · simp [ACC.ACCFormula.depth]
      · rename_i g hfind
        cases g.type with
        | input negated =>
            simp [ACC.ACCFormula.depth]
        | output =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simp [ACC.ACCFormula.depth]
            | some e =>
                exact Nat.le_trans (ih e.src) (Nat.le_succ fuel)
        | andGate =>
            simp [ACC.ACCFormula.depth]
            have hmax :
                (List.map (ACC.ACCFormula.depth ∘ fun e => c.gateToACCFormula fuel e.src)
                  (c.inEdges g.id)).max?.getD 0 ≤ fuel := by
              apply max?_getD_le
              intro x hx
              rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
              exact ih e.src
            simpa [Nat.add_comm] using Nat.add_le_add_left hmax 1
        | orGate =>
            simp [ACC.ACCFormula.depth]
            have hmax :
                (List.map (ACC.ACCFormula.depth ∘ fun e => c.gateToACCFormula fuel e.src)
                  (c.inEdges g.id)).max?.getD 0 ≤ fuel := by
              apply max?_getD_le
              intro x hx
              rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
              exact ih e.src
            simpa [Nat.add_comm] using Nat.add_le_add_left hmax 1
        | notGate =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simp [ACC.ACCFormula.depth]
            | some e =>
                simpa only [ACC.ACCFormula.depth] using
                  Nat.add_le_add_right (ih e.src) 1
        | modGate =>
            simp [ACC.ACCFormula.depth]
            have hmax :
                (List.map (ACC.ACCFormula.depth ∘ fun e => c.gateToACCFormula fuel e.src)
                  (c.inEdges g.id)).max?.getD 0 ≤ fuel := by
              apply max?_getD_le
              intro x hx
              rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
              exact ih e.src
            simpa [Nat.add_comm] using Nat.add_le_add_left hmax 1

/-- The converted output formula has depth at most the conversion fuel. -/
lemma toACCFormula_depth_le_fuel (c : ACCCircuit) :
    ACC.ACCFormula.depth c.toACCFormula ≤ c.toACCFormulaFuel := by
  unfold toACCFormula outputToACCFormula
  cases hhead : c.outputGateIds.head? with
  | none =>
      simp [ACC.ACCFormula.depth, toACCFormulaFuel]
  | some outputId =>
      exact gateToACCFormula_depth_le_fuel c c.toACCFormulaFuel outputId

/-- A fixed depth blow-up constant for `ACCCircuit.toACCFormula`. -/
def toACCFormulaDepthFactor : Nat := 2

/-- For positive-depth circuits, converting an ACC circuit to an ACC formula
    increases depth by at most the fixed constant factor `2`. -/
theorem toACCFormula_depth_le_factor_mul_depth (c : ACCCircuit)
    (hdepth : 0 < c.depth) :
    ACC.ACCFormula.depth c.toACCFormula ≤
      toACCFormulaDepthFactor * c.depth := by
  have hfuel := toACCFormula_depth_le_fuel c
  apply Nat.le_trans hfuel
  rw [toACCFormulaFuel, toACCFormulaDepthFactor, Nat.two_mul]
  exact Nat.add_le_add_left (Nat.succ_le_iff.mpr hdepth) c.depth

/-- Well-formed wrapper for the constant-factor depth theorem.  The
    well-formedness proof is carried explicitly for call sites that work with
    well-formed circuits. -/
theorem toACCFormulaOfWellFormed_depth_le_factor_mul_depth
    (c : ACCCircuit) (hwf : c.WellFormed) (hdepth : 0 < c.depth) :
    ACC.ACCFormula.depth (c.toACCFormulaOfWellFormed hwf) ≤
      toACCFormulaDepthFactor * c.depth := by
  simpa [toACCFormulaOfWellFormed] using
    toACCFormula_depth_le_factor_mul_depth c hdepth

end DAG.ACCCircuit

end Circuits
