import Parity.ParityProperties
import «Circuits».CircuitFamilies
import «Circuits».Conversion.CircuitToFormula
import «Circuits».CircuitEval

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula
open CnfDnf.Families
/-- A single-output circuit computes parity when its output list is the
    singleton containing the parity bit, on every input of the declared width. -/
def CircuitComputesParity (n : Nat) (c : Circuit) : Prop :=
  c.WellFormed ∧
  ∀ inputs : List Bool, inputs.length = n →
    c.evalCanonical inputs = [parityBit inputs]

namespace CircuitParityLowerBounds

private lemma inEdges_length_lt_succ_size (c : Circuit)
    (hwf : c.WellFormed) (k : Nat) :
    (c.inEdges k).length < c.gates.length + 1 := by
  have hnd_edges : (c.inEdges k).Nodup := hwf.edges_nodup.filter _
  have hnd_src : ((c.inEdges k).map Edge.src).Nodup := by
    apply hnd_edges.map_on
    intro e₁ he₁ e₂ he₂ hsrc
    have hdst₁ : e₁.dst = k := by
      simpa [Circuit.inEdges, beq_iff_eq] using (List.mem_filter.mp he₁).2
    have hdst₂ : e₂.dst = k := by
      simpa [Circuit.inEdges, beq_iff_eq] using (List.mem_filter.mp he₂).2
    cases e₁ with
    | mk src₁ dst₁ =>
      cases e₂ with
      | mk src₂ dst₂ => simp_all
  have hsubset : (c.inEdges k).map Edge.src ⊆ c.gateIds := by
    intro src hsrc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hsrc
    exact (hwf.edges_closed e (List.mem_filter.mp he).1).1
  have hlen := (hnd_src.subperm hsubset).length_le
  unfold Circuit.gateIds at hlen
  simpa using hlen

private lemma list_eq_singleton_of_length_one_head {α : Type*}
    (list : List α) (x : α) (hlen : list.length = 1) (hhead : list.head? = some x) :
    list = [x] := by
  cases h_l : list with
  | nil => rw [h_l] at hlen; simp at hlen
  | cons y ys =>
    have hys : ys = [] := by
      rw [h_l] at hlen
      simp only [List.length_cons] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst ys
    rw [h_l] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst y
    rfl

lemma toUFIByPos_depth_le_gateDepth_add_one (c : Circuit)
    (hwf : c.WellFormed) :
    ∀ k fuel, k < c.gates.length → fuel > k →
      ufiFormulaDepth (c.toUFIByPos fuel k) ≤ c.gateDepth fuel k + 1 := by
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
        ufiFormulaDepth (c.toUFIByPos f e.src) ≤
          c.gateDepth f e.src + 1 := by
      intro e he
      obtain ⟨hsrck, hsrc⟩ := pred_info e he
      exact ih e.src hsrck f hsrc (by omega)
    have child_max_bound :
        (List.foldr max 0)
            ((c.inEdges k).map
              (fun e => ufiFormulaDepth (c.toUFIByPos f e.src))) ≤
          (List.foldr max 0)
              ((c.inEdges k).map (fun e => c.gateDepth f e.src)) + 1 := by
      apply foldr_max_map_le
      intro e he
      exact le_trans (child_bound e he)
        (Nat.add_le_add_right
          (mem_le_foldr_max_map
            (f := fun e => c.gateDepth f e.src) he) 1)
    simp only [Circuit.toUFIByPos, Circuit.gateDepth, dif_pos hk]
    split
    · split <;> simp [ufiFormulaDepth]
    · rename_i hout
      cases hhead : (c.inEdges k).head? with
      | none => simp [ufiFormulaDepth]
      | some e =>
        have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
        have hnonempty : (c.inEdges k).map Edge.src ≠ [] := by
          intro hempty
          have : c.inEdges k = [] := by simpa using hempty
          rw [this] at hhead
          simp at hhead
        simp only [hhead, ufiFormulaDepth, List.map_map, Function.comp_def]
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
      | none => simp [ufiFormulaDepth]
      | some e =>
        have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
        have hnonempty : (c.inEdges k).map Edge.src ≠ [] := by
          intro hempty
          have : c.inEdges k = [] := by simpa using hempty
          rw [this] at hhead
          simp at hhead
        simp only [hhead, ufiFormulaDepth, List.map_map, Function.comp_def]
        have hemax : c.gateDepth f e.src ≤
            (List.foldr max 0) ((c.inEdges k).map (fun e => c.gateDepth f e.src)) :=
          mem_le_foldr_max_map (f := fun e => c.gateDepth f e.src) he
        have hchild := child_bound e he
        omega
    · rename_i hand
      simp only [ufiFormulaDepth, List.map_map, Function.comp_def]
      cases h_e : c.inEdges k with
      | nil => simp
      | cons e es =>
        simp only [h_e, List.map_cons, List.foldr_cons, Function.comp_def]
        have hb := child_max_bound
        rw [h_e] at hb
        simp only [List.map_cons, List.foldr_cons, Function.comp_def] at hb
        omega
    · rename_i hor
      simp only [ufiFormulaDepth, List.map_map, Function.comp_def]
      cases h_e : c.inEdges k with
      | nil => simp
      | cons e es =>
        simp only [h_e, List.map_cons, List.foldr_cons, Function.comp_def]
        have hb := child_max_bound
        rw [h_e] at hb
        simp only [List.map_cons, List.foldr_cons, Function.comp_def] at hb
        omega

lemma toUFIByPos_node_count_le (c : Circuit)
    (hwf : c.WellFormed) :
    ∀ k fuel, k < c.gates.length → fuel > k →
      ufiFormulaNodeCount (c.toUFIByPos fuel k) ≤
        (c.gates.length + 1) ^ (c.gateDepth fuel k + 2) := by
  have hbase : 2 ≤ c.gates.length + 1 := by
    obtain ⟨i, hi, _, _, _, _⟩ := hwf.input_reaches_output
    cases hgs : c.gates with
    | nil => rw [hgs] at hi; simp at hi
    | cons g gs => simp
  have sum_le_length_mul : ∀ (list : List Nat) (bound : Nat),
      (∀ x ∈ list, x ≤ bound) → list.sum ≤ list.length * bound := by
    intro list bound h
    induction list with
    | nil => simp
    | cons x xs ih =>
      have hx := h x List.mem_cons_self
      have hxs : ∀ y ∈ xs, y ≤ bound :=
        fun y hy => h y (List.mem_cons_of_mem x hy)
      have := ih hxs
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro fuel hk hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have pred_info : ∀ e ∈ c.inEdges k,
        e.src < k ∧ e.src < c.gates.length := by
      intro e he
      have he' := (List.mem_filter.mp he).1
      have hdst : e.dst = k := by
        simpa [Circuit.inEdges, beq_iff_eq] using (List.mem_filter.mp he).2
      have hsrc_mem := (hwf.edges_closed e he').1
      obtain ⟨g, hg, hgid⟩ := List.mem_map.mp hsrc_mem
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
      have hsrc : e.src = i := by rw [← hgid, ← hgi, hwf.cons_ids i hi]
      exact ⟨by have := hwf.topo e he'; omega, by omega⟩
    have child_bound : ∀ e ∈ c.inEdges k,
        ufiFormulaNodeCount (c.toUFIByPos f e.src) ≤
          (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) := by
      intro e he
      obtain ⟨hsrck, hsrc⟩ := pred_info e he
      exact ih e.src hsrck f hsrc (by omega)
    simp only [Circuit.toUFIByPos, Circuit.gateDepth, dif_pos hk]
    split
    · split <;> simp only [ufiFormulaNodeCount] <;>
        exact Nat.one_le_pow _ _ (by omega)
    · rename_i hout
      cases hhead : (c.inEdges k).head? with
      | none =>
        simp only [ufiFormulaNodeCount]
        exact Nat.one_le_pow _ _ (by omega)
      | some e =>
        have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
        have hfan : (c.inEdges k).length = 1 := by
          have hmem : c.gates[k]'hk ∈ c.gates := List.getElem_mem hk
          have := hwf.fanin_output (c.gates[k]'hk) hmem hout
          rw [hwf.cons_ids k hk] at this
          exact this
        have h_e : c.inEdges k = [e] :=
          list_eq_singleton_of_length_one_head _ _ hfan hhead
        simp only [hhead, List.map_map, Function.comp_def]
        have hchild := child_bound e he
        rw [h_e]
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          Function.comp_def, max_eq_left (Nat.zero_le _)]
        exact le_trans hchild
          (Nat.pow_le_pow_right (by omega)
            (show c.gateDepth f e.src + 2 ≤
              1 + c.gateDepth f e.src + 2 by omega))
    · rename_i hnot
      cases hhead : (c.inEdges k).head? with
      | none =>
        simp only [ufiFormulaNodeCount]
        exact Nat.one_le_pow _ _ (by omega)
      | some e =>
        have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
        have hfan : (c.inEdges k).length = 1 := by
          have hmem : c.gates[k]'hk ∈ c.gates := List.getElem_mem hk
          have := hwf.fanin_not (c.gates[k]'hk) hmem hnot
          rw [hwf.cons_ids k hk] at this
          exact this
        have h_e : c.inEdges k = [e] :=
          list_eq_singleton_of_length_one_head _ _ hfan hhead
        simp only [hhead, ufiFormulaNodeCount, List.map_map, Function.comp_def]
        have hchild := child_bound e he
        have hp : 1 ≤ (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) :=
          Nat.one_le_pow _ _ (by omega)
        rw [h_e]
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          Function.comp_def, max_eq_left (Nat.zero_le _)]
        calc
          1 + ufiFormulaNodeCount (c.toUFIByPos f e.src) ≤
              1 + (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) := by omega
          _ ≤ (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) +
              (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) := by omega
          _ ≤ (c.gates.length + 1) *
              (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) := by
            have hdouble :
                (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) +
                    (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) ≤
                  (c.gates.length + 1) *
                    (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) := by
              nlinarith [Nat.mul_le_mul_right
                ((c.gates.length + 1) ^ (c.gateDepth f e.src + 2)) hbase]
            exact hdouble
          _ = (c.gates.length + 1) ^ (c.gateDepth f e.src + 2) *
              (c.gates.length + 1) := Nat.mul_comm _ _
          _ = (c.gates.length + 1) ^
              ((c.gateDepth f e.src + 2) + 1) :=
            (Nat.pow_succ _ _).symm
          _ = (c.gates.length + 1) ^
              (1 + c.gateDepth f e.src + 2) := by congr 1; omega
    · rename_i hand
      simp only [ufiFormulaNodeCount, List.map_map, Function.comp_def]
      cases h_e : c.inEdges k with
      | nil => exact Nat.one_le_pow _ _ (by omega)
      | cons e es =>
        simp only [h_e, List.map_cons, List.foldr_cons, Function.comp_def]
        let M := max (c.gateDepth f e.src)
          (List.foldr max 0 (es.map (fun e => c.gateDepth f e.src)))
        let P := (c.gates.length + 1) ^ (M + 2)
        have h_each : ∀ x ∈ e :: es,
            ufiFormulaNodeCount (c.toUFIByPos f x.src) ≤ P := by
          intro x hx
          have hx' : x ∈ c.inEdges k := by rw [h_e]; exact hx
          have hgd : c.gateDepth f x.src ≤ M := by
            exact mem_le_foldr_max_map
              (f := fun y => c.gateDepth f y.src) hx
          exact le_trans (child_bound x hx')
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hsum := sum_le_length_mul
          ((e :: es).map (fun x =>
            ufiFormulaNodeCount (c.toUFIByPos f x.src))) P (by
              intro x hx
              obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
              exact h_each y hy)
        have hlen := inEdges_length_lt_succ_size c hwf k
        rw [h_e] at hlen
        have hp : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
        have hsum' :
            (ufiFormulaNodeCount (c.toUFIByPos f e.src) ::
              es.map (fun x => ufiFormulaNodeCount
                (c.toUFIByPos f x.src))).sum ≤ (e :: es).length * P := by
          simpa using hsum
        rw [show 1 + M + 2 = M + 3 by omega, pow_succ]
        dsimp only [P] at hsum' hp ⊢
        nlinarith [Nat.mul_le_mul_right
          ((c.gates.length + 1) ^ (M + 2)) (Nat.succ_le_of_lt hlen)]
    · rename_i hor
      simp only [ufiFormulaNodeCount, List.map_map, Function.comp_def]
      cases h_e : c.inEdges k with
      | nil => exact Nat.one_le_pow _ _ (by omega)
      | cons e es =>
        simp only [h_e, List.map_cons, List.foldr_cons, Function.comp_def]
        let M := max (c.gateDepth f e.src)
          (List.foldr max 0 (es.map (fun e => c.gateDepth f e.src)))
        let P := (c.gates.length + 1) ^ (M + 2)
        have h_each : ∀ x ∈ e :: es,
            ufiFormulaNodeCount (c.toUFIByPos f x.src) ≤ P := by
          intro x hx
          have hx' : x ∈ c.inEdges k := by rw [h_e]; exact hx
          have hgd : c.gateDepth f x.src ≤ M :=
            mem_le_foldr_max_map (f := fun y => c.gateDepth f y.src) hx
          exact le_trans (child_bound x hx')
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hsum := sum_le_length_mul
          ((e :: es).map (fun x =>
            ufiFormulaNodeCount (c.toUFIByPos f x.src))) P (by
              intro x hx
              obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
              exact h_each y hy)
        have hlen := inEdges_length_lt_succ_size c hwf k
        rw [h_e] at hlen
        have hp : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
        have hsum' :
            (ufiFormulaNodeCount (c.toUFIByPos f e.src) ::
              es.map (fun x => ufiFormulaNodeCount
                (c.toUFIByPos f x.src))).sum ≤ (e :: es).length * P := by
          simpa using hsum
        rw [show 1 + M + 2 = M + 3 by omega, pow_succ]
        dsimp only [P] at hsum' hp ⊢
        nlinarith [Nat.mul_le_mul_right
          ((c.gates.length + 1) ^ (M + 2)) (Nat.succ_le_of_lt hlen)]

lemma toUFIByPos_largest_input_lt (c : Circuit)
    (hwf : c.WellFormed) (hn : 0 < c.inputWidth) :
    ∀ k fuel, k < c.gates.length → fuel > k →
      ufiLargestInput (c.toUFIByPos fuel k) < c.inputWidth := by
  have hvars : ∀ k fuel, k < c.gates.length → fuel > k →
      ∀ i ∈ ufiCollectInputIndices (c.toUFIByPos fuel k),
        i < c.inputWidth := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro fuel hk hf i hi
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have pred_info : ∀ e ∈ c.inEdges k,
          e.src < k ∧ e.src < c.gates.length := by
        intro e he
        have he' := (List.mem_filter.mp he).1
        have hdst : e.dst = k := by
          simpa [Circuit.inEdges, beq_iff_eq] using (List.mem_filter.mp he).2
        have hsrc_mem := (hwf.edges_closed e he').1
        obtain ⟨g, hg, hgid⟩ := List.mem_map.mp hsrc_mem
        obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
        have hsrc : e.src = j := by rw [← hgid, ← hgj, hwf.cons_ids j hj]
        exact ⟨by have := hwf.topo e he'; omega, by omega⟩
      simp only [Circuit.toUFIByPos, dif_pos hk] at hi
      split at hi
      · rename_i neg htype
        split at hi
        · rename_i hneg
          simp only [ufiCollectInputIndices, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          subst i
          let negIds := (c.gates.filter
            (fun g => g.type == GateType.input true)).map Gate.id
          have hkneg : k ∈ negIds := by
            unfold negIds
            simp only [List.mem_map, List.mem_filter]
            refine ⟨c.gates[k]'hk, ⟨List.getElem_mem hk, ?_⟩, hwf.cons_ids k hk⟩
            rw [htype]
            subst neg
            decide
          have hfind : negIds.findIdx (· == k) < negIds.length :=
            List.findIdx_lt_length.mpr ⟨k, hkneg, by simp only [beq_self_eq_true]⟩
          have hlen : negIds.length = c.inputWidth := by
            unfold negIds
            rw [hwf.has_canonical_input_ids.2, List.length_map, List.length_range]
            rfl
          simpa [negIds] using (show negIds.findIdx (· == k) < c.inputWidth by
            rw [← hlen]; exact hfind)
        · rename_i hneg
          simp only [ufiCollectInputIndices, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          subst i
          let posIds := (c.gates.filter
            (fun g => g.type == GateType.input false)).map Gate.id
          have hkpos : k ∈ posIds := by
            unfold posIds
            simp only [List.mem_map, List.mem_filter]
            refine ⟨c.gates[k]'hk, ⟨List.getElem_mem hk, ?_⟩, hwf.cons_ids k hk⟩
            rw [htype]
            have : neg = false := by exact Bool.eq_false_of_not_eq_true hneg
            subst neg
            decide
          have hfind : posIds.findIdx (· == k) < posIds.length :=
            List.findIdx_lt_length.mpr ⟨k, hkpos, by simp only [beq_self_eq_true]⟩
          have hlen : posIds.length = c.inputWidth := by
            unfold posIds
            rw [hwf.has_canonical_input_ids.1, List.length_range]
            rfl
          simpa [posIds] using (show posIds.findIdx (· == k) < c.inputWidth by
            rw [← hlen]; exact hfind)
      · rename_i hout
        cases hhead : (c.inEdges k).head? with
        | none => simp [hhead, ufiCollectInputIndices] at hi
        | some e =>
          have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
          simp only [hhead] at hi
          obtain ⟨hsrck, hsrc⟩ := pred_info e he
          exact ih e.src hsrck f hsrc (by omega) i hi
      · rename_i hnot
        cases hhead : (c.inEdges k).head? with
        | none => simp [hhead, ufiCollectInputIndices] at hi
        | some e =>
          have he : e ∈ c.inEdges k := mem_of_head?_some' hhead
          simp only [hhead, ufiCollectInputIndices] at hi
          obtain ⟨hsrck, hsrc⟩ := pred_info e he
          exact ih e.src hsrck f hsrc (by omega) i hi
      · rename_i hand
        simp only [ufiCollectInputIndices, List.mem_flatMap, List.mem_map] at hi
        obtain ⟨child, ⟨e, he, rfl⟩, hii⟩ := hi
        obtain ⟨hsrck, hsrc⟩ := pred_info e he
        exact ih e.src hsrck f hsrc (by omega) i hii
      · rename_i hor
        simp only [ufiCollectInputIndices, List.mem_flatMap, List.mem_map] at hi
        obtain ⟨child, ⟨e, he, rfl⟩, hii⟩ := hi
        obtain ⟨hsrck, hsrc⟩ := pred_info e he
        exact ih e.src hsrck f hsrc (by omega) i hii
  intro k fuel hk hf
  unfold ufiLargestInput
  have fold_lt : ∀ L : List Nat, (∀ i ∈ L, i < c.inputWidth) →
      L.foldr max 0 < c.inputWidth := by
    intro L h
    induction L with
    | nil => simpa using hn
    | cons x xs ih =>
      simp only [List.foldr_cons]
      have hx := h x List.mem_cons_self
      have hxs := ih (fun i hi => h i (List.mem_cons_of_mem x hi))
      omega
  exact fold_lt _ (hvars k fuel hk hf)

lemma gates_length_eq (c : Circuit) (hwf : c.WellFormed) :
    c.gates.length = 2 * c.inputWidth + c.circuitSize := by
  have hcounts : c.gates.length =
      c.positiveInputIds.length + c.negativeInputIds.length + c.circuitSize := by
    unfold Circuit.positiveInputIds Circuit.negativeInputIds
      Circuit.circuitSize
    simp only [List.length_map]
    induction c.gates with
    | nil => simp
    | cons g gs ih =>
      simp only [List.length_cons, List.filter_cons]
      cases htype : g.type with
      | input neg =>
        cases neg with
        | false =>
          have hff : (GateType.input false == GateType.input false) = true := by decide
          have hft : (GateType.input false == GateType.input true) = false := by decide
          simp [GateType.isInput, htype, ih, hff, hft]; omega
        | true =>
          have htf : (GateType.input true == GateType.input false) = false := by decide
          have htt : (GateType.input true == GateType.input true) = true := by decide
          simp [GateType.isInput, htype, ih, htf, htt]; omega
      | output =>
        have hf : (GateType.output == GateType.input false) = false := by decide
        have ht : (GateType.output == GateType.input true) = false := by decide
        simp [GateType.isInput, htype, ih, hf, ht]; omega
      | notGate =>
        have hf : (GateType.notGate == GateType.input false) = false := by decide
        have ht : (GateType.notGate == GateType.input true) = false := by decide
        simp [GateType.isInput, htype, ih, hf, ht]; omega
      | andGate =>
        have hf : (GateType.andGate == GateType.input false) = false := by decide
        have ht : (GateType.andGate == GateType.input true) = false := by decide
        simp [GateType.isInput, htype, ih, hf, ht]; omega
      | orGate =>
        have hf : (GateType.orGate == GateType.input false) = false := by decide
        have ht : (GateType.orGate == GateType.input true) = false := by decide
        simp [GateType.isInput, htype, ih, hf, ht]; omega
  have hpos : c.positiveInputIds.length = c.inputWidth := by
    have := congrArg List.length hwf.has_canonical_input_ids.1
    change c.positiveInputIds.length =
      max c.positiveInputIds.length c.negativeInputIds.length
    simpa only [Circuit.positiveInputIds, Circuit.negativeInputIds,
      List.length_range] using this
  have hneg : c.negativeInputIds.length = c.inputWidth := by
    have := congrArg List.length hwf.has_canonical_input_ids.2
    change c.negativeInputIds.length =
      max c.positiveInputIds.length c.negativeInputIds.length
    simpa only [Circuit.positiveInputIds, Circuit.negativeInputIds,
      List.length_map, List.length_range] using this
  omega

lemma outputGateIds_eq_singleton_of_computes
    (n : Nat) (c : Circuit) (h : CircuitComputesParity n c) :
    ∃ outId, c.outputGateIds = [outId] := by
  let inputs := List.replicate n false
  have hlen : inputs.length = n := by simp [inputs]
  have heq := h.2 inputs hlen
  have houtlen : c.outputGateIds.length = 1 := by
    have := congrArg List.length heq
    simpa using this
  cases h_l : c.outputGateIds with
  | nil => rw [h_l] at houtlen; simp at houtlen
  | cons outId rest =>
    have hrest : rest = [] := by
      rw [h_l] at houtlen
      simp only [List.length_cons] at houtlen
      exact List.length_eq_zero_iff.mp (by omega)
    exact ⟨outId, by rw [hrest]⟩

lemma output_gateDepth_le_depth (c : Circuit) (outId : Nat)
    (hout : outId ∈ c.outputGateIds) :
    c.gateDepth c.gates.length outId ≤ c.depth := by
  rw [depth_eq_gateDepth]
  exact mem_le_foldr_max_map (f := c.gateDepth c.gates.length) hout

lemma eval_eq_singleton_toUFIByPos (c : Circuit)
    (hwf : c.WellFormed) (outId : Nat)
    (hout : c.outputGateIds = [outId]) (inputs : List Bool)
    (hlen : c.inputWidth ≤ inputs.length) :
    c.evalCanonical inputs =
      [ufiFormulaEval (c.toUFIByPos c.gates.length outId) inputs] := by
  rw [← Circuit.eval_eq_evalCanonical c inputs hwf.has_canonical_input_ids]
  rw [Circuit.eval_eq_map_evalS c inputs hlen, hout]
  simp only [List.map_cons, List.map_nil]
  have hagree := toUFIByPos_agrees_with_evalS c hwf inputs hlen outId
  have houtmem : outId ∈ c.outputGateIds := by rw [hout]; simp
  have houtvalid := outputGateIds_valid c hwf.cons_ids outId houtmem
  exact congrArg (fun b => [b]) (hagree houtvalid)

end CircuitParityLowerBounds

end Circuits
