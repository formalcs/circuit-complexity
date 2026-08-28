import «Circuits».CircuitConversion

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

-- ─── Generic circuit-to-UFI uncompilation ────────────────────────────

/-- Emit `inputGate` formula nodes indexed by the *position* of the corresponding
    input gate inside the positive
    (`posIds`) / negative (`negIds`) input-id lists, instead of by its
    raw gate id.  Evaluating this formula on the user-facing `inputs`
    list directly recovers `Circuit.eval`'s `initEnv` lookup. -/
def Circuit.toUFIByPos (c : Circuit)
    (fuel : Nat) (k : Nat) : UnboundedFanInFormula :=
  match fuel with
  | 0 => inputGate 0 false
  | fuel' + 1 =>
    if hk : k < c.gates.length then
      match (c.gates[k]'hk).type with
      | GateType.input neg =>
          let posIds := (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id
          let negIds := (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id
          if neg then inputGate (negIds.findIdx (· == k)) true
          else inputGate (posIds.findIdx (· == k)) false
      | GateType.output =>
          match (c.inEdges k).head? with
          | some e => c.toUFIByPos fuel' e.src
          | none   => constant false 0
      | GateType.notGate =>
          match (c.inEdges k).head? with
          | some e => notGate (c.toUFIByPos fuel' e.src)
          | none   => constant false 0
      | GateType.andGate =>
          andGate ((c.inEdges k).map fun e => c.toUFIByPos fuel' e.src)
      | GateType.orGate =>
          orGate ((c.inEdges k).map fun e => c.toUFIByPos fuel' e.src)
    else inputGate 0 false

/-- Fuel-irrelevance for `toUFIByPos`. -/
theorem toUFIByPos_fuel_irrel (c : Circuit)
    (h_topo : ∀ e ∈ c.edges, e.src < e.dst) :
    ∀ k, k < c.gates.length → ∀ fuel₁ fuel₂,
    fuel₁ > k → fuel₂ > k →
    c.toUFIByPos fuel₁ k = c.toUFIByPos fuel₂ k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk fuel₁ fuel₂ hf₁ hf₂
    obtain ⟨f₁, rfl⟩ : ∃ f, fuel₁ = f + 1 := ⟨fuel₁ - 1, by omega⟩
    obtain ⟨f₂, rfl⟩ : ∃ f, fuel₂ = f + 1 := ⟨fuel₂ - 1, by omega⟩
    simp only [Circuit.toUFIByPos, dif_pos hk]
    have pred_info : ∀ e, e ∈ c.inEdges k →
        e.src < k ∧ e.src < c.gates.length := by
      intro e he
      have he_edge : e ∈ c.edges := (List.mem_filter.mp he).1
      have he_dst : e.dst = k := by
        simpa [beq_iff_eq] using (List.mem_filter.mp he).2
      exact ⟨by have := h_topo e he_edge; omega,
             by have := h_topo e he_edge; omega⟩
    split
    · rfl
    · split
      · rename_i e he
        have ⟨hsrc_lt, hsrc_len⟩ := pred_info e (mem_of_head?_some' he)
        exact ih e.src hsrc_lt hsrc_len f₁ f₂ (by omega) (by omega)
      · rfl
    · split
      · rename_i e he
        have ⟨hsrc_lt, hsrc_len⟩ := pred_info e (mem_of_head?_some' he)
        congr 1
        exact ih e.src hsrc_lt hsrc_len f₁ f₂ (by omega) (by omega)
      · rfl
    · congr 1
      apply List.map_congr_left
      intro e he
      have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
      exact ih e.src hsrc_lt hsrc_len f₁ f₂ (by omega) (by omega)
    · congr 1
      apply List.map_congr_left
      intro e he
      have ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
      exact ih e.src hsrc_lt hsrc_len f₁ f₂ (by omega) (by omega)

-- ─── List helper lemmas for find? on zipped Nat lists ───────────────

/-- For a Nodup list `l` of keys with `k ∈ l`, looking up `k` in the
    zipped pair list `l.zip vs` is the same as indexing `vs` by the
    position of `k` in `l`. -/
private lemma find?_zip_eq_getElem?_of_nodup
    (l : List Nat) (vs : List Bool) (k : Nat)
    (hnd : l.Nodup) (hk : k ∈ l) :
    (l.zip vs).find? (fun p => p.1 == k) =
    (vs[l.findIdx (· == k)]?).map (Prod.mk k) := by
  induction l generalizing vs with
  | nil => exact absurd hk (by simp)
  | cons h t ih =>
    cases vs with
    | nil =>
      simp only [List.zip_nil_right, List.find?_nil, List.getElem?_nil,
                 Option.map_none]
    | cons b vs' =>
      simp only [List.zip_cons_cons, List.find?_cons]
      by_cases hhk : h = k
      · subst hhk
        simp [List.findIdx_cons]
      · have hhk_b : (h == k) = false := by simp [hhk]
        simp only [hhk_b, cond_false]
        have hk_t : k ∈ t := by
          rcases List.mem_cons.mp hk with heq | hk_t
          · exact absurd heq.symm hhk
          · exact hk_t
        have hnd_t : t.Nodup := (List.nodup_cons.mp hnd).2
        rw [ih vs' hnd_t hk_t]
        simp [List.findIdx_cons, hhk_b]

/-- If `k` is not in `l`, then `find?` on the zipped pair list returns
    `none`. -/
private lemma find?_zip_eq_none_of_notMem
    (l : List Nat) (vs : List Bool) (k : Nat) (hk : k ∉ l) :
    (l.zip vs).find? (fun p => p.1 == k) = none := by
  induction l generalizing vs with
  | nil => simp
  | cons h t ih =>
    cases vs with
    | nil => simp
    | cons b vs' =>
      simp only [List.zip_cons_cons, List.find?_cons]
      have hhk_b : (h == k) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq; subst heq; exact hk (List.mem_cons_self)
      simp only [hhk_b, cond_false]
      exact ih vs' (fun hkt => hk (List.mem_cons_of_mem _ hkt))

-- ─── Disjointness / Nodup of positive/negative input-id lists ────────

/-- In a well-formed circuit, the positive-input-id list is `Nodup`. -/
private lemma posIds_nodup {c : Circuit} (hwf : c.WellFormed) :
    ((c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id).Nodup := by
  -- `c.gates` is Nodup (since `c.gates.map Gate.id = c.gateIds` is Nodup),
  -- filter preserves Nodup, and Gate.id is injective on c.gates by unique_ids.
  have hgates_nodup : c.gates.Nodup := by
    have := hwf.unique_ids
    exact (List.Nodup.of_map _ this)
  have hfilt_nodup : (c.gates.filter (fun g => g.type == GateType.input false)).Nodup :=
    hgates_nodup.filter _
  apply hfilt_nodup.map_on
  intro a ha b hb hab
  have ha' : a ∈ c.gates := List.mem_of_mem_filter ha
  have hb' : b ∈ c.gates := List.mem_of_mem_filter hb
  obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha'
  obtain ⟨j, hj, hbj⟩ := List.mem_iff_getElem.mp hb'
  have hia : a.id = i := by rw [← hai]; exact hwf.cons_ids i hi
  have hjb : b.id = j := by rw [← hbj]; exact hwf.cons_ids j hj
  have hij : i = j := by rw [hia, hjb] at hab; exact hab
  subst hij
  exact hai.symm.trans hbj

/-- Same for the negative-input-id list. -/
private lemma negIds_nodup {c : Circuit} (hwf : c.WellFormed) :
    ((c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id).Nodup := by
  have hgates_nodup : c.gates.Nodup := by
    have := hwf.unique_ids
    exact (List.Nodup.of_map _ this)
  have hfilt_nodup : (c.gates.filter (fun g => g.type == GateType.input true)).Nodup :=
    hgates_nodup.filter _
  apply hfilt_nodup.map_on
  intro a ha b hb hab
  have ha' : a ∈ c.gates := List.mem_of_mem_filter ha
  have hb' : b ∈ c.gates := List.mem_of_mem_filter hb
  obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha'
  obtain ⟨j, hj, hbj⟩ := List.mem_iff_getElem.mp hb'
  have hia : a.id = i := by rw [← hai]; exact hwf.cons_ids i hi
  have hjb : b.id = j := by rw [← hbj]; exact hwf.cons_ids j hj
  have hij : i = j := by rw [hia, hjb] at hab; exact hab
  subst hij
  exact hai.symm.trans hbj

/-- A gate of type `GateType.input false` has its id in `posIds`. -/
private lemma id_mem_posIds {c : Circuit} {k : Nat} (hk : k < c.gates.length)
    (hwf : c.WellFormed) (htype : (c.gates[k]'hk).type = GateType.input false) :
    k ∈ ((c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id) := by
  simp only [List.mem_map, List.mem_filter]
  refine ⟨c.gates[k]'hk, ⟨List.getElem_mem hk, by rw [htype]; rfl⟩, ?_⟩
  exact hwf.cons_ids k hk

/-- A gate of type `GateType.input true` has its id in `negIds`. -/
private lemma id_mem_negIds {c : Circuit} {k : Nat} (hk : k < c.gates.length)
    (hwf : c.WellFormed) (htype : (c.gates[k]'hk).type = GateType.input true) :
    k ∈ ((c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id) := by
  simp only [List.mem_map, List.mem_filter]
  refine ⟨c.gates[k]'hk, ⟨List.getElem_mem hk, by rw [htype]; rfl⟩, ?_⟩
  exact hwf.cons_ids k hk

/-- A gate of type `GateType.input false` does not have its id in `negIds`. -/
private lemma id_notMem_negIds {c : Circuit} {k : Nat} (hk : k < c.gates.length)
    (hwf : c.WellFormed) (htype : (c.gates[k]'hk).type = GateType.input false) :
    k ∉ ((c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id) := by
  intro hmem
  simp only [List.mem_map, List.mem_filter] at hmem
  obtain ⟨g, ⟨hg_mem, hg_ty⟩, hg_id⟩ := hmem
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg_mem
  have hi_id : g.id = i := by rw [← hgi]; exact hwf.cons_ids i hi
  have hik : i = k := by rw [hi_id] at hg_id; exact hg_id
  subst hik
  rw [hgi] at htype
  rw [htype] at hg_ty
  exact absurd hg_ty (by decide)

/-- A gate of type `GateType.input true` does not have its id in `posIds`. -/
private lemma id_notMem_posIds {c : Circuit} {k : Nat} (hk : k < c.gates.length)
    (hwf : c.WellFormed) (htype : (c.gates[k]'hk).type = GateType.input true) :
    k ∉ ((c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id) := by
  intro hmem
  simp only [List.mem_map, List.mem_filter] at hmem
  obtain ⟨g, ⟨hg_mem, hg_ty⟩, hg_id⟩ := hmem
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg_mem
  have hi_id : g.id = i := by rw [← hgi]; exact hwf.cons_ids i hi
  have hik : i = k := by rw [hi_id] at hg_id; exact hg_id
  subst hik
  rw [hgi] at htype
  rw [htype] at hg_ty
  exact absurd hg_ty (by decide)

/-- The positional `initEnv` used to evaluate a `Circuit` whose
    input wires are addressed by their *position* in the positive /
    negative input-id lists (matching `toUFIByPos`).  For an input gate
    with id `k`, this looks up the position of `k` in `posIds` (resp.
    `negIds`) and returns the input value at that position. -/
def Circuit.byPosEnv (c : Circuit) (inputs : List Bool) : Nat → Bool :=
  let posIds := (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id
  let negIds := (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id
  fun id =>
    match (posIds.zip inputs).find? (fun p => p.1 == id) with
    | some (_, v) => v
    | none =>
      match (negIds.zip inputs).find? (fun p => p.1 == id) with
      | some (_, v) => v
      | none        => false

/-- Correctness of `toUFIByPos`: for any gate `k` in a well-formed circuit,
    structurally evaluating `c` with the positional `byPosEnv` initial
    environment agrees with evaluating the UFI formula produced by
    `toUFIByPos`. -/
theorem toUFIByPos_agrees_with_evalS (c : Circuit) (hwf : c.WellFormed)
    (inputs : List Bool) (hlen : c.inputWidth ≤ inputs.length) :
    ∀ k, k < c.gates.length →
    c.evalS (c.byPosEnv inputs) c.gates.length k =
    ufiFormulaEval (c.toUFIByPos c.gates.length k) inputs := by
  set posIds := (c.gates.filter (fun g => g.type == GateType.input false)).map Gate.id with hpos_ids
  set negIds := (c.gates.filter (fun g => g.type == GateType.input true)).map Gate.id with hneg_ids
  set initEnv : Nat → Bool := c.byPosEnv inputs with hinit_env
  have hinit_env_def : ∀ id, initEnv id =
      match (posIds.zip inputs).find? (fun p => p.1 == id) with
      | some (_, v) => v
      | none =>
        match (negIds.zip inputs).find? (fun p => p.1 == id) with
        | some (_, v) => v
        | none        => false := by
    intro id; rfl
  have h_uniq : ∀ (i j : Nat) (hi : i < c.gates.length) (hj : j < c.gates.length),
      i ≠ j → (c.gates[i]'hi).id ≠ (c.gates[j]'hj).id := by
    intro i j hi hj hij
    rw [hwf.cons_ids i hi, hwf.cons_ids j hj]; exact hij
  have hpos_nd := posIds_nodup hwf
  have hneg_nd := negIds_nodup hwf
  have hneg_len : negIds.length = c.inputWidth := by
    rw [hneg_ids, hwf.has_canonical_input_ids.2, List.length_map, List.length_range]
    rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    have pred_info : ∀ e, e ∈ c.inEdges k →
        e.src < k ∧ e.src < c.gates.length := by
      intro e he
      have he_edge : e ∈ c.edges := (List.mem_filter.mp he).1
      have he_dst : e.dst = k := by
        simpa [beq_iff_eq] using (List.mem_filter.mp he).2
      exact ⟨by have := hwf.topo e he_edge; omega,
             by have := hwf.topo e he_edge; omega⟩
    set N' := c.gates.length - 1 with h_n'_def
    have h_n_eq : c.gates.length = N' + 1 := by omega
    have pred_fuel : ∀ e ∈ c.inEdges k,
        c.toUFIByPos N' e.src = c.toUFIByPos c.gates.length e.src := by
      intro e he
      obtain ⟨_, hsrc_len⟩ := pred_info e he
      exact toUFIByPos_fuel_irrel c hwf.topo e.src hsrc_len N' c.gates.length
        (by omega) (by omega)
    have ih_pred : ∀ e ∈ c.inEdges k,
        c.evalS initEnv c.gates.length e.src =
        ufiFormulaEval (c.toUFIByPos N' e.src) inputs := by
      intro e he
      obtain ⟨hsrc_lt, hsrc_len⟩ := pred_info e he
      rw [ih e.src hsrc_lt hsrc_len, pred_fuel e he]
    by_cases htype : (c.gates[k]'hk).type.isInput = true
    · rw [c.evalS_input initEnv h_uniq hwf.cons_ids k hk htype]
      have ⟨neg, hgt⟩ : ∃ neg, (c.gates[k]'hk).type = GateType.input neg := by
        cases h : (c.gates[k]'hk).type with
        | input neg => exact ⟨neg, rfl⟩
        | _ => simp [h, GateType.isInput] at htype
      have hid := hwf.cons_ids k hk
      conv_rhs => rw [h_n_eq]
      cases neg with
      | false =>
        have h1 : c.evalGate initEnv initEnv (c.gates[k]'hk) = initEnv k := by
          simp [Circuit.evalGate, hgt, hid]
        have h2 : c.toUFIByPos (N' + 1) k = inputGate (posIds.findIdx (· == k)) false := by
          simp [Circuit.toUFIByPos, dif_pos hk, hgt, hpos_ids, hneg_ids]
        rw [h1, h2]
        have hk_pos : k ∈ posIds := id_mem_posIds hk hwf hgt
        have hk_neg : k ∉ negIds := id_notMem_negIds hk hwf hgt
        have hpos_find :=
          find?_zip_eq_getElem?_of_nodup posIds inputs k hpos_nd hk_pos
        have hneg_none :=
          find?_zip_eq_none_of_notMem negIds inputs k hk_neg
        rw [hinit_env_def k, hpos_find, hneg_none]
        simp only [ufiFormulaEval]
        cases hgi : inputs[posIds.findIdx (· == k)]? with
        | none => simp [Option.map]
        | some v => simp [Option.map]
      | true =>
        have h1 : c.evalGate initEnv initEnv (c.gates[k]'hk) = Bool.not (initEnv k) := by
          simp [Circuit.evalGate, hgt, hid]
        have h2 : c.toUFIByPos (N' + 1) k = inputGate (negIds.findIdx (· == k)) true := by
          simp [Circuit.toUFIByPos, dif_pos hk, hgt, hpos_ids, hneg_ids]
        rw [h1, h2]
        have hk_pos : k ∉ posIds := id_notMem_posIds hk hwf hgt
        have hk_neg : k ∈ negIds := id_mem_negIds hk hwf hgt
        have hpos_none :=
          find?_zip_eq_none_of_notMem posIds inputs k hk_pos
        have hneg_find :=
          find?_zip_eq_getElem?_of_nodup negIds inputs k hneg_nd hk_neg
        rw [hinit_env_def k, hpos_none, hneg_find]
        simp only [ufiFormulaEval]
        cases hgi : inputs[negIds.findIdx (· == k)]? with
        | none =>
          have hidx : negIds.findIdx (· == k) < negIds.length :=
            List.findIdx_lt_length.mpr ⟨k, hk_neg, by simp⟩
          have hidx' : negIds.findIdx (· == k) < inputs.length := by
            rw [hneg_len] at hidx
            omega
          rw [List.getElem?_eq_getElem hidx'] at hgi
          contradiction
        | some v => simp [Option.map]
    · rw [c.evalS_fp initEnv h_uniq hwf.cons_ids hwf.topo k hk]
      conv_rhs => rw [h_n_eq]
      simp only [Circuit.toUFIByPos, dif_pos hk]
      have hid := hwf.cons_ids k hk
      split
      · rename_i neg heq
        exfalso; exact htype (by rw [heq]; rfl)
      · rename_i h_out
        unfold Circuit.evalGate
        simp only [h_out, hid]
        cases h_head : (c.inEdges k).head? with
        | none => simp [ufiFormulaEval]
        | some e =>
          simp only [ufiFormulaEval]
          exact ih_pred e (mem_of_head?_some' (by rw [h_head]))
      · rename_i h_not
        unfold Circuit.evalGate
        simp only [h_not, hid]
        cases h_head : (c.inEdges k).head? with
        | none => simp [ufiFormulaEval]
        | some e =>
          simp only [ufiFormulaEval]
          congr 1
          exact ih_pred e (mem_of_head?_some' (by rw [h_head]))
      · rename_i h_and
        unfold Circuit.evalGate
        simp only [h_and, hid]
        rw [ufi_eval_andGate_eq_all, List.map_map]
        have h_eq : (c.inEdges k).map (fun e => c.evalS initEnv c.gates.length e.src) =
                    (c.inEdges k).map ((fun c_ufi => ufiFormulaEval c_ufi inputs) ∘
                      (fun e => c.toUFIByPos N' e.src)) :=
          List.map_congr_left (fun e he => ih_pred e he)
        rw [h_eq]
      · rename_i h_or
        unfold Circuit.evalGate
        simp only [h_or, hid]
        rw [ufi_eval_orGate_eq_any, List.map_map]
        have h_eq : (c.inEdges k).map (fun e => c.evalS initEnv c.gates.length e.src) =
                    (c.inEdges k).map ((fun c_ufi => ufiFormulaEval c_ufi inputs) ∘
                      (fun e => c.toUFIByPos N' e.src)) :=
          List.map_congr_left (fun e he => ih_pred e he)
        rw [h_eq]

end Circuits
