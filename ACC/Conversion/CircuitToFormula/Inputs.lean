import ACC.Conversion.CircuitToFormula.Eval

set_option linter.style.setOption false
set_option linter.flexible false

namespace Circuits

namespace DAG.ACCCircuit

/-! ## Input bounds for `ACCCircuit.toACCFormula`

The conversion maps canonical positive and negative ACC input gates back to
formula input indices below the circuit's input width.
-/

private lemma andGate_numInputs_le {p n : Nat} :
    ∀ fs : List (ACC.ACCFormula p),
      (∀ f ∈ fs, ACC.ACCFormula.numInputs f ≤ n) →
        ACC.ACCFormula.numInputs (ACC.ACCFormula.andGate fs) ≤ n
  | [], _ => by simp [ACC.ACCFormula.numInputs]
  | f :: fs, h => by
      simp [ACC.ACCFormula.numInputs]
      constructor
      · exact h f (by simp)
      · exact andGate_numInputs_le fs (by
          intro g hg
          exact h g (by simp [hg]))

private lemma orGate_numInputs_le {p n : Nat} :
    ∀ fs : List (ACC.ACCFormula p),
      (∀ f ∈ fs, ACC.ACCFormula.numInputs f ≤ n) →
        ACC.ACCFormula.numInputs (ACC.ACCFormula.orGate fs) ≤ n
  | [], _ => by simp [ACC.ACCFormula.numInputs]
  | f :: fs, h => by
      simp [ACC.ACCFormula.numInputs]
      constructor
      · exact h f (by simp)
      · exact orGate_numInputs_le fs (by
          intro g hg
          exact h g (by simp [hg]))

private lemma modGate_numInputs_le {p n : Nat} :
    ∀ fs : List (ACC.ACCFormula p),
      (∀ f ∈ fs, ACC.ACCFormula.numInputs f ≤ n) →
        ACC.ACCFormula.numInputs (ACC.ACCFormula.modGate fs) ≤ n
  | [], _ => by simp [ACC.ACCFormula.numInputs]
  | f :: fs, h => by
      simp [ACC.ACCFormula.numInputs]
      constructor
      · exact h f (by simp)
      · exact modGate_numInputs_le fs (by
          intro g hg
          exact h g (by simp [hg]))

/-- The formula obtained by unrolling any gate of a well-formed circuit uses
    only primary input indices below the circuit input width. -/
lemma gateToACCFormula_numInputs_le_inputWidth (c : ACCCircuit)
    (hwf : c.WellFormed) :
    ∀ fuel id : Nat,
      ACC.ACCFormula.numInputs (c.gateToACCFormula fuel id) ≤ c.inputWidth := by
  intro fuel
  induction fuel with
  | zero =>
      intro id
      simp [gateToACCFormula, ACC.ACCFormula.numInputs]
  | succ fuel ih =>
      intro id
      unfold gateToACCFormula
      split
      · simp [ACC.ACCFormula.numInputs]
      · rename_i g hfind
        cases htype : g.type with
        | input negated =>
            have hgmem : g ∈ c.gates := by
              unfold findGate at hfind
              exact List.mem_of_find?_eq_some hfind
            rcases List.mem_iff_getElem.mp hgmem with ⟨k, hk, hg⟩
            have hgid : g.id = k := by
              have := hwf.cons_ids k hk
              rwa [hg] at this
            cases negated with
            | false =>
                have hpos := positive_input_id_lt_inputWidth c hwf
                  (k := k) (hk := hk) (by simp [hg, htype])
                simp [ACC.ACCFormula.numInputs, formulaInputIndex, hgid,
                  Nat.succ_le_iff.mpr hpos]
            | true =>
                have hneg := negative_input_id_bounds c hwf
                  (k := k) (hk := hk) (by simp [hg, htype])
                simp [ACC.ACCFormula.numInputs, formulaInputIndex, hgid]
                omega
        | output =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simp [ACC.ACCFormula.numInputs]
            | some e =>
                simpa [hhead] using ih e.src
        | andGate =>
            apply andGate_numInputs_le
            intro f hf
            rcases List.mem_map.mp hf with ⟨e, _he, rfl⟩
            exact ih e.src
        | orGate =>
            apply orGate_numInputs_le
            intro f hf
            rcases List.mem_map.mp hf with ⟨e, _he, rfl⟩
            exact ih e.src
        | notGate =>
            cases hhead : (c.inEdges g.id).head? with
            | none =>
                simp [ACC.ACCFormula.numInputs]
            | some e =>
                simpa [hhead, ACC.ACCFormula.numInputs] using ih e.src
        | modGate =>
            apply modGate_numInputs_le
            intro f hf
            rcases List.mem_map.mp hf with ⟨e, _he, rfl⟩
            exact ih e.src

/-- The converted output formula of a well-formed circuit uses no input index
    outside the circuit input width. -/
theorem toACCFormula_numInputs_le_inputWidth (c : ACCCircuit)
    (hwf : c.WellFormed) :
    ACC.ACCFormula.numInputs c.toACCFormula ≤ c.inputWidth := by
  unfold toACCFormula outputToACCFormula
  cases hhead : c.outputGateIds.head? with
  | none =>
      simp [ACC.ACCFormula.numInputs]
  | some outputId =>
      exact gateToACCFormula_numInputs_le_inputWidth c hwf c.toACCFormulaFuel outputId

end DAG.ACCCircuit

end Circuits
