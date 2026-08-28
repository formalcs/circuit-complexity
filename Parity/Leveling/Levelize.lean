import Parity.Leveling.Invariants
import Formulas.UFITransformations

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Circuits.Leveling
open Circuits
open UnboundedFanInFormula

/-! ### `flatten` preserves collected input indices exactly -/

theorem asAndChildren_collect (y : UnboundedFanInFormula) :
    (Formulas.UFITransformations.asAndChildren y).flatMap ufiCollectInputIndices
      = ufiCollectInputIndices y := by
  cases y with
  | inputGate i n => simp [Formulas.UFITransformations.asAndChildren, ufiCollectInputIndices]
  | constant v l => simp [Formulas.UFITransformations.asAndChildren, ufiCollectInputIndices]
  | notGate g => simp [Formulas.UFITransformations.asAndChildren, ufiCollectInputIndices]
  | andGate gs => simp [Formulas.UFITransformations.asAndChildren, ufiCollectInputIndices]
  | orGate gs => simp [Formulas.UFITransformations.asAndChildren, ufiCollectInputIndices]

theorem asOrChildren_collect (y : UnboundedFanInFormula) :
    (Formulas.UFITransformations.asOrChildren y).flatMap ufiCollectInputIndices
      = ufiCollectInputIndices y := by
  cases y with
  | inputGate i n => simp [Formulas.UFITransformations.asOrChildren, ufiCollectInputIndices]
  | constant v l => simp [Formulas.UFITransformations.asOrChildren, ufiCollectInputIndices]
  | notGate g => simp [Formulas.UFITransformations.asOrChildren, ufiCollectInputIndices]
  | andGate gs => simp [Formulas.UFITransformations.asOrChildren, ufiCollectInputIndices]
  | orGate gs => simp [Formulas.UFITransformations.asOrChildren, ufiCollectInputIndices]

theorem flatMap_asAndChildren_collect (list : List UnboundedFanInFormula) :
    (list.flatMap Formulas.UFITransformations.asAndChildren).flatMap ufiCollectInputIndices
      = list.flatMap ufiCollectInputIndices := by
  induction list with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [asAndChildren_collect x, ih]

theorem flatMap_asOrChildren_collect (list : List UnboundedFanInFormula) :
    (list.flatMap Formulas.UFITransformations.asOrChildren).flatMap ufiCollectInputIndices
      = list.flatMap ufiCollectInputIndices := by
  induction list with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [asOrChildren_collect x, ih]

mutual
theorem flatten_collect (g : UnboundedFanInFormula) :
    ufiCollectInputIndices (Formulas.UFITransformations.flatten g) = ufiCollectInputIndices g := by
  cases g with
  | inputGate i n => rfl
  | constant v l => rfl
  | notGate g' =>
      change ufiCollectInputIndices (notGate (Formulas.UFITransformations.flatten g')) = _
      simp only [ufiCollectInputIndices]; exact flatten_collect g'
  | andGate gs =>
      change ufiCollectInputIndices (andGate ((Formulas.UFITransformations.flattenList gs).flatMap Formulas.UFITransformations.asAndChildren))
            = ufiCollectInputIndices (andGate gs)
      simp only [ufiCollectInputIndices]
      rw [flatMap_asAndChildren_collect (Formulas.UFITransformations.flattenList gs)]
      exact flattenList_collect gs
  | orGate gs =>
      change ufiCollectInputIndices (orGate ((Formulas.UFITransformations.flattenList gs).flatMap Formulas.UFITransformations.asOrChildren))
            = ufiCollectInputIndices (orGate gs)
      simp only [ufiCollectInputIndices]
      rw [flatMap_asOrChildren_collect (Formulas.UFITransformations.flattenList gs)]
      exact flattenList_collect gs
termination_by sizeOf g
theorem flattenList_collect (gs : List UnboundedFanInFormula) :
    (Formulas.UFITransformations.flattenList gs).flatMap ufiCollectInputIndices
      = gs.flatMap ufiCollectInputIndices := by
  cases gs with
  | nil => rfl
  | cons g rest =>
      simp only [Formulas.UFITransformations.flattenList, List.flatMap_cons]
      rw [flatten_collect g, flattenList_collect rest]
termination_by sizeOf gs
end

/-! ### Direct bridge to `IsAlternatingAndLeveledAt` -/

/-- Structural AND/OR leveling plus a depth bound directly supplies the
    occurrence-indexed numeric levels. -/
theorem hasAlternatingAndOrGates_depth_imp_strict (g : UnboundedFanInFormula) (d : Nat)
    (h_leveled : g.HasAlternatingAndOrGates) (hdepth : ufiFormulaDepth g ≤ d) :
    IsAlternatingAndLeveledAt g d := by
  cases g with
  | inputGate i n =>
      simp only [IsAlternatingAndLeveledAt]
  | constant v lbl =>
      simp only [IsAlternatingAndLeveledAt]
  | notGate g =>
      simp only [HasAlternatingAndOrGates] at h_leveled
  | andGate gs =>
      simp only [HasAlternatingAndOrGates] at h_leveled
      simp only [IsAlternatingAndLeveledAt]
      refine ⟨h_leveled.2, ?_, ?_⟩
      · intro x hx h_ao
        simp only [ufiFormulaDepth] at hdepth
        omega
      · intro x hx
        have hdx : ufiFormulaDepth x ≤ d - 1 := by
          have hle : ufiFormulaDepth x ≤
              (List.foldr max 0) (gs.map ufiFormulaDepth) :=
            mem_le_foldr_max_map hx
          simp only [ufiFormulaDepth] at hdepth
          omega
        exact hasAlternatingAndOrGates_depth_imp_strict x (d - 1) (h_leveled.1 x hx) hdx
  | orGate gs =>
      simp only [HasAlternatingAndOrGates] at h_leveled
      simp only [IsAlternatingAndLeveledAt]
      refine ⟨h_leveled.2, ?_, ?_⟩
      · intro x hx h_ao
        simp only [ufiFormulaDepth] at hdepth
        omega
      · intro x hx
        have hdx : ufiFormulaDepth x ≤ d - 1 := by
          have hle : ufiFormulaDepth x ≤
              (List.foldr max 0) (gs.map ufiFormulaDepth) :=
            mem_le_foldr_max_map hx
          simp only [ufiFormulaDepth] at hdepth
          omega
        exact hasAlternatingAndOrGates_depth_imp_strict x (d - 1) (h_leveled.1 x hx) hdx
termination_by sizeOf g

/-- **Stage-2 contract.**

    From a `notGate`-free, `n`-input formula of depth ≤ `d` with all
    indices `< n`, produce an equivalent
    formula that is additionally strictly assigned-leveled at level `d`,
    without increasing circuit size.  The spacer gadget
    above realizes leaf-lifting; the full inductive construction and its
    correctness are the isolated obligation. -/
theorem levelize_contract (d n : Nat) (f : UnboundedFanInFormula)
    (h_nn : HasNoNotGates f)
    (hlarge : ufiLargestInput f < n)
    (hdepth : ufiFormulaDepth f ≤ d) :
    ∃ g : UnboundedFanInFormula,
      IsAlternatingAndLeveledAt g d ∧
      ufiLargestInput g < n ∧
      ufiFormulaDepth g ≤ d ∧
      ufiFormulaCircuitSize g ≤ ufiFormulaCircuitSize f ∧
      AgreesOn f g n := by
  refine ⟨Formulas.UFITransformations.flatten f, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsAlternatingAndLeveledAt _ d
    have h_leveled :=
      Formulas.UFITransformations.flatten_hasAlternatingAndOrGates f h_nn
    have hdg : ufiFormulaDepth (Formulas.UFITransformations.flatten f) ≤ d :=
      le_trans (Formulas.UFITransformations.flatten_depth_le f) hdepth
    exact hasAlternatingAndOrGates_depth_imp_strict _ d h_leveled hdg
  · -- largest < n
    have hc : ufiCollectInputIndices (Formulas.UFITransformations.flatten f)
              = ufiCollectInputIndices f := flatten_collect f
    simp only [ufiLargestInput, hc]; exact hlarge
  · -- depth ≤ d
    exact le_trans (Formulas.UFITransformations.flatten_depth_le f) hdepth
  · -- circuit size does not increase
    exact Formulas.UFITransformations.flatten_size_le f
  · -- AgreesOn f g n
    intro inputs hlen
    exact (Formulas.UFITransformations.flatten_eval f inputs).symm

end Circuits.Leveling
