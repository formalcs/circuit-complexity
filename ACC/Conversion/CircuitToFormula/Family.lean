import ACC.Circuit.Family
import ACC.Formula.Family
import ACC.Conversion.CircuitToFormula.Size

namespace Circuits

namespace DAG.ACCCircuit

/-! ## Family-level ACC circuit to ACC formula conversion

This file packages the single-circuit evaluation-preservation theorem into a
family-level existence statement.
-/

/-- Cast an ACC formula across an equality of moduli. -/
def castACCFormula {p q : Nat} (h : p = q) (f : ACC.ACCFormula p) :
    ACC.ACCFormula q :=
  h ▸ f

@[simp] lemma castACCFormula_eval {p q : Nat} (h : p = q)
    (f : ACC.ACCFormula p) (inputValues : List Bool) :
    ACC.ACCFormula.eval (castACCFormula h f) inputValues =
      ACC.ACCFormula.eval f inputValues := by
  cases h
  rfl

@[simp] lemma castACCFormula_wellFormed {p q : Nat} (h : p = q)
    (f : ACC.ACCFormula p) :
    ACC.ACCFormula.WellFormed (castACCFormula h f) =
      ACC.ACCFormula.WellFormed f := by
  cases h
  rfl

@[simp] lemma castACCFormula_numInputs {p q : Nat} (h : p = q)
    (f : ACC.ACCFormula p) :
    ACC.ACCFormula.numInputs (castACCFormula h f) =
      ACC.ACCFormula.numInputs f := by
  cases h
  rfl

@[simp] lemma castACCFormula_depth {p q : Nat} (h : p = q)
    (f : ACC.ACCFormula p) :
    ACC.ACCFormula.depth (castACCFormula h f) =
      ACC.ACCFormula.depth f := by
  cases h
  rfl

@[simp] lemma castACCFormula_circuitSize {p q : Nat} (h : p = q)
    (f : ACC.ACCFormula p) :
    ACC.ACCFormula.circuitSize (castACCFormula h f) =
      ACC.ACCFormula.circuitSize f := by
  cases h
  rfl

@[simp] lemma castACCFormula_nodeCount {p q : Nat} (h : p = q)
    (f : ACC.ACCFormula p) :
    ACC.ACCFormula.nodeCount (castACCFormula h f) =
      ACC.ACCFormula.nodeCount f := by
  cases h
  rfl

/-- Convert every circuit in a fixed-modulus ACC circuit family to the
    corresponding single-output ACC formula over the same fixed modulus. -/
def toACCFormulaFamily {p c k d : Nat} (circuitFamily : ACCCircuitFamily p c k d) :
    (n : PNat) → ACC.ACCFormula p :=
  fun n =>
    castACCFormula (circuitFamily n).property.2.1 (circuitFamily n).val.toACCFormula

/-- A constant-depth, polynomial-size ACC circuit family converts to a
    constant-depth, polynomial-size ACC formula family computing exactly the
    same single-output Boolean function. -/
theorem exists_constant_depth_polynomial_size_accFormula_family_exact
    {p c k d : Nat} (circuitFamily : ACCCircuitFamily p c k d) :
    ∃ formulaFamily : (n : PNat) → ACC.ACCFormula p,
      (∀ n : PNat,
        ACC.ACCFormula.WellFormed (formulaFamily n) ∧
        ACC.ACCFormula.numInputs (formulaFamily n) ≤ n.val ∧
        ACC.ACCFormula.depth (formulaFamily n) ≤ 2 * d ∧
        ACC.ACCFormula.nodeCount (formulaFamily n) ≤
          (c + (c + 2) ^ 2 + 2) ^ (d + 1) *
            n.val ^ ((2 * (2 * (k + 1))) * (d + 1)) ∧
        2 * d > 0) ∧
      (∀ (n : PNat) (inputValues : List Bool),
        n.val ≤ inputValues.length →
          ACC.ACCFormula.eval (formulaFamily n) inputValues =
            ((circuitFamily n).val.evalCanonical inputValues).head?.getD false) := by
  refine ⟨toACCFormulaFamily circuitFamily, ?_, ?_⟩
  · intro n
    rcases (circuitFamily n).property with
      ⟨hwf, hp, hwidth, hcircuitDepth, _hsizeCircuit, hdpos⟩
    constructor
    · simpa [toACCFormulaFamily, ACC.ACCFormula.WellFormed, hp] using hwf.modulus_gt_one
    constructor
    · simpa [toACCFormulaFamily, hwidth] using
        toACCFormula_numInputs_le_inputWidth (circuitFamily n).val hwf
    constructor
    · simpa [toACCFormulaFamily] using
        (Nat.le_trans ((circuitFamily n).val.toACCFormula_depth_le_fuel) (by
          unfold toACCFormulaFuel
          omega))
    constructor
    · simpa [toACCFormulaFamily] using
        toACCFormula_nodeCount_le_polynomial_of_family_member
          c k d n (circuitFamily n).val hwf hwidth hcircuitDepth _hsizeCircuit
    · omega
  · intro n inputValues hlen
    rcases (circuitFamily n).property with
      ⟨hwf, hp, hwidth, _hdepth, _hsizeCircuit, _hdpos⟩
    simpa [toACCFormulaFamily] using
      toACCFormula_eval_eq_evalCanonical_head_of_ge
        (circuitFamily n).val hwf inputValues (by omega)

/-- The converted formulas form a constant-depth polynomial-size formula family
    for some constants, and compute the same single-output Boolean function as
    the original circuit family at every input length.

    The modulus `p` is globally fixed in both the source circuit family and
    the target formula family. -/
theorem exists_accFormula_family_exact
    {p c k d : Nat} (circuitFamily : ACCCircuitFamily p c k d) :
    ∃ c' k' d' : Nat,
    ∃ formulaFamily : ACC.ACCFormula.ACCFormulaFamily p c' k' d',
      (∀ (n : PNat) (inputValues : List Bool),
        n.val = inputValues.length →
          ACC.ACCFormula.eval (formulaFamily n).val inputValues =
            ((circuitFamily n).val.evalCanonical inputValues).head?.getD false) := by
  let c' := (c + (c + 2) ^ 2 + 2) ^ (d + 1)
  let k' := (2 * (2 * (k + 1))) * (d + 1)
  let d' := 2 * d
  rcases exists_constant_depth_polynomial_size_accFormula_family_exact circuitFamily with
    ⟨formulaFamily, hbounds, heval⟩
  refine ⟨c', k', d', ?_, ?_⟩
  · intro n
    exact ⟨formulaFamily n, hbounds n⟩
  · intro n inputValues hlen
    exact heval n inputValues (by omega)

end DAG.ACCCircuit

end Circuits
