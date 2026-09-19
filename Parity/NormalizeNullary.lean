import Parity.CircuitParityLowerBounds

namespace Circuits.CircuitParityLowerBounds
open UnboundedFanInFormula

mutual
/-- Represent nullary gates as depth-zero constants when unfolding a circuit.
Circuit depth already assigns depth zero to every gate without predecessors. -/
def normalizeNullary : UnboundedFanInFormula → UnboundedFanInFormula
  | .inputGate i b => .inputGate i b
  | .constant b l => .constant b l
  | .notGate f => .notGate (normalizeNullary f)
  | .andGate [] => .constant true 0
  | .andGate (g :: gs) => .andGate (normalizeNullaryList (g :: gs))
  | .orGate [] => .constant false 0
  | .orGate (g :: gs) => .orGate (normalizeNullaryList (g :: gs))

def normalizeNullaryList : List UnboundedFanInFormula → List UnboundedFanInFormula
  | [] => []
  | g :: gs => normalizeNullary g :: normalizeNullaryList gs
end

lemma normalizeNullaryList_eq_map (gs : List UnboundedFanInFormula) :
    normalizeNullaryList gs = gs.map normalizeNullary := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [normalizeNullaryList, ih]

/-- Nullary normalization preserves node count, inputs, and evaluation. -/
theorem normalizeNullary_spec (f : UnboundedFanInFormula) :
    ufiFormulaNodeCount (normalizeNullary f) = ufiFormulaNodeCount f ∧
    ufiCollectInputIndices (normalizeNullary f) = ufiCollectInputIndices f ∧
    ∀ xs, ufiFormulaEval (normalizeNullary f) xs = ufiFormulaEval f xs := by
  cases f with
  | inputGate i b => exact ⟨rfl, rfl, fun _ => rfl⟩
  | constant b l => exact ⟨rfl, rfl, fun _ => rfl⟩
  | notGate f =>
    obtain ⟨hn, hi, he⟩ := normalizeNullary_spec f
    exact ⟨by simpa [normalizeNullary, ufiFormulaNodeCount] using hn,
      by simpa [normalizeNullary, ufiCollectInputIndices] using hi,
      fun xs => by simp [normalizeNullary, ufiFormulaEval, he xs]⟩
  | andGate gs | orGate gs =>
    have hn : gs.map (fun g => ufiFormulaNodeCount (normalizeNullary g)) =
        gs.map ufiFormulaNodeCount :=
      List.map_congr_left (fun g _ => (normalizeNullary_spec g).1)
    have hi : gs.flatMap (fun g => ufiCollectInputIndices (normalizeNullary g)) =
        gs.flatMap ufiCollectInputIndices := by
      rw [List.flatMap, List.flatMap]
      congr 1
      exact List.map_congr_left (fun g _ => (normalizeNullary_spec g).2.1)
    have he (xs : List Bool) :
        gs.map (fun g => ufiFormulaEval (normalizeNullary g) xs) =
          gs.map (fun g => ufiFormulaEval g xs) :=
      List.map_congr_left (fun g _ => (normalizeNullary_spec g).2.2 xs)
    cases gs with
    | nil => simp [normalizeNullary, ufiFormulaNodeCount, ufiCollectInputIndices,
        ufiFormulaEval]
    | cons g gs =>
      constructor
      · simpa only [normalizeNullary, normalizeNullaryList_eq_map,
          ufiFormulaNodeCount, List.map_map,
          Function.comp_def] using congrArg (fun l : List Nat => 1 + l.sum) hn
      constructor
      · simpa only [normalizeNullary, normalizeNullaryList_eq_map,
          ufiCollectInputIndices, List.flatMap_map,
          Function.comp_def] using hi
      · intro xs
        simp only [normalizeNullary, normalizeNullaryList_eq_map,
          ufi_eval_andGate_eq_all, ufi_eval_orGate_eq_any,
          List.map_map, Function.comp_def, he xs]
termination_by sizeOf f

lemma normalizeNullary_toUFIByPos_depth_le_gateDepth (c : Circuit)
    (hwf : c.WellFormed) :
    ∀ k fuel, k < c.gates.length → fuel > k →
      ufiFormulaDepth (normalizeNullary (c.toUFIByPos fuel k)) ≤ c.gateDepth fuel k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro fuel hk hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have pred_info : ∀ e ∈ c.inEdges k,
        e.src < k ∧ e.src < c.gates.length := by
      intro e he
      have he' := (List.mem_filter.mp he).1
      have hsrc_mem := (hwf.edges_closed e he').1
      obtain ⟨g, hg, hgid⟩ := List.mem_map.mp hsrc_mem
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
      have hsrc : e.src = i := by
        rw [← hgid, ← hgi, hwf.cons_ids i hi]
      have hdst : e.dst = k := by
        simpa [Circuit.inEdges, beq_iff_eq] using (List.mem_filter.mp he).2
      exact ⟨by have := hwf.topo e he'; omega, by omega⟩
    have child_bound : ∀ e ∈ c.inEdges k,
        ufiFormulaDepth (normalizeNullary (c.toUFIByPos f e.src)) ≤
          c.gateDepth f e.src := by
      intro e he
      obtain ⟨hsrck, hsrc⟩ := pred_info e he
      exact ih e.src hsrck f hsrc (by omega)
    have child_max_bound :
        (List.foldr max 0)
            ((c.inEdges k).map
              (fun e => ufiFormulaDepth (normalizeNullary (c.toUFIByPos f e.src)))) ≤
          (List.foldr max 0)
              ((c.inEdges k).map (fun e => c.gateDepth f e.src)) := by
      apply foldr_max_map_le
      intro e he
      exact le_trans (child_bound e he)
        (mem_le_foldr_max_map (f := fun e => c.gateDepth f e.src) he)
    simp only [Circuit.toUFIByPos, Circuit.gateDepth, dif_pos hk]
    split
    · split <;> simp [normalizeNullary, ufiFormulaDepth]
    · rename_i hout
      cases hhead : (c.inEdges k).head? with
      | none => simp [normalizeNullary, ufiFormulaDepth]
      | some e =>
        have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
        have hnonempty : (c.inEdges k).map Edge.src ≠ [] := by
          intro hempty
          have : c.inEdges k = [] := by simpa using hempty
          rw [this] at hhead
          simp at hhead
        simp only [List.map_map, Function.comp_def]
        exact le_trans (child_bound e he)
          (by
            have hemax : c.gateDepth f e.src ≤
                (List.foldr max 0)
                  ((c.inEdges k).map (fun e => c.gateDepth f e.src)) :=
              mem_le_foldr_max_map
                (f := fun e => c.gateDepth f e.src) he
            omega)
    · rename_i hnot
      cases hhead : (c.inEdges k).head? with
      | none => simp [normalizeNullary, ufiFormulaDepth]
      | some e =>
        have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
        have hnonempty : (c.inEdges k).map Edge.src ≠ [] := by
          intro hempty
          have : c.inEdges k = [] := by simpa using hempty
          rw [this] at hhead
          simp at hhead
        simp only [normalizeNullary, ufiFormulaDepth, List.map_map, Function.comp_def]
        have hemax : c.gateDepth f e.src ≤
            (List.foldr max 0) ((c.inEdges k).map (fun e => c.gateDepth f e.src)) :=
          mem_le_foldr_max_map (f := fun e => c.gateDepth f e.src) he
        have hchild := child_bound e he
        omega
    · rename_i hand
      cases h_e : c.inEdges k with
      | nil => simp [normalizeNullary, ufiFormulaDepth]
      | cons e es =>
        simp only [List.map_cons, normalizeNullary, normalizeNullaryList_eq_map,
          ufiFormulaDepth, List.map_map, List.foldr_cons, Function.comp_def]
        have hb := child_max_bound
        rw [h_e] at hb
        simp only [List.map_cons, List.foldr_cons] at hb
        omega
    · rename_i hor
      cases h_e : c.inEdges k with
      | nil => simp [normalizeNullary, ufiFormulaDepth]
      | cons e es =>
        simp only [List.map_cons, normalizeNullary, normalizeNullaryList_eq_map,
          ufiFormulaDepth, List.map_map, List.foldr_cons, Function.comp_def]
        have hb := child_max_bound
        rw [h_e] at hb
        simp only [List.map_cons, List.foldr_cons] at hb
        omega

end Circuits.CircuitParityLowerBounds
