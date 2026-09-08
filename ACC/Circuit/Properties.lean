import Mathlib.Data.List.ProdSigma
import ACC.Circuit.Basic

set_option linter.style.setOption false
set_option linter.flexible false

namespace Circuits

namespace DAG.ACCCircuit

/-! ## General properties of ACC circuits

This file collects structural facts about the DAG representation that are not
specific to any particular conversion.
-/

lemma edge_pair_injective : Function.Injective (fun e : Edge => (e.src, e.dst)) := by
  intro e₁ e₂ h
  cases e₁
  cases e₂
  simp at h
  simp [h.1, h.2]

lemma gate_id_mem_lt_length (c : ACCCircuit) (hwf : c.WellFormed)
    {id : Nat} (hid : id ∈ c.gateIds) : id < c.gates.length := by
  unfold gateIds at hid
  rcases List.mem_map.mp hid with ⟨g, hg, hgid⟩
  rw [List.mem_iff_getElem] at hg
  rcases hg with ⟨k, hk, hg_eq⟩
  subst hg_eq
  rw [← hgid, hwf.cons_ids k hk]
  exact hk

/-- A well-formed finite DAG has at most one edge for each ordered pair of
    gates, so its wire count is bounded by the square of its gate count. -/
lemma edges_length_le_gates_length_sq (c : ACCCircuit) (hwf : c.WellFormed) :
    c.edges.length ≤ c.gates.length * c.gates.length := by
  let edgePairs : List (Nat × Nat) := c.edges.map (fun e => (e.src, e.dst))
  have hnodup : edgePairs.Nodup := hwf.edges_nodup.map edge_pair_injective
  have hsubset :
      edgePairs.toFinset ⊆ (c.gateIds ×ˢ c.gateIds).toFinset := by
    intro p hp
    rw [List.mem_toFinset] at hp ⊢
    rcases List.mem_map.mp hp with ⟨e, he, rfl⟩
    have hclosed := hwf.edges_closed e he
    exact List.mem_product.mpr hclosed
  calc
    c.edges.length = edgePairs.length := by simp [edgePairs]
    _ = edgePairs.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (c.gateIds ×ˢ c.gateIds).toFinset.card := Finset.card_le_card hsubset
    _ = (c.gateIds ×ˢ c.gateIds).length := by
      rw [List.toFinset_card_of_nodup]
      exact List.Nodup.product hwf.unique_ids hwf.unique_ids
    _ = c.gates.length * c.gates.length := by
      simp [gateIds, List.length_product]

private lemma list_length_eq_filter_add_not {α : Type} (p : α → Bool) :
    ∀ xs : List α,
      xs.length = (xs.filter p).length + (xs.filter (fun x => !p x)).length
  | [] => by simp
  | x :: xs => by
      by_cases hp : p x = true
      · simp [hp, list_length_eq_filter_add_not p xs]
        omega
      · have hpfalse : p x = false := by
          cases hpx : p x <;> simp [hpx] at hp ⊢
        simp [hpfalse, list_length_eq_filter_add_not p xs]
        omega

@[simp] private lemma input_false_beq_input_false :
    (ACCGateType.input false == ACCGateType.input false) = true := rfl

@[simp] private lemma input_false_beq_input_true :
    (ACCGateType.input false == ACCGateType.input true) = false := rfl

@[simp] private lemma input_true_beq_input_false :
    (ACCGateType.input true == ACCGateType.input false) = false := rfl

@[simp] private lemma input_true_beq_input_true :
    (ACCGateType.input true == ACCGateType.input true) = true := rfl

@[simp] private lemma output_beq_input_false :
    (ACCGateType.output == ACCGateType.input false) = false := rfl

@[simp] private lemma output_beq_input_true :
    (ACCGateType.output == ACCGateType.input true) = false := rfl

@[simp] private lemma andGate_beq_input_false :
    (ACCGateType.andGate == ACCGateType.input false) = false := rfl

@[simp] private lemma andGate_beq_input_true :
    (ACCGateType.andGate == ACCGateType.input true) = false := rfl

@[simp] private lemma orGate_beq_input_false :
    (ACCGateType.orGate == ACCGateType.input false) = false := rfl

@[simp] private lemma orGate_beq_input_true :
    (ACCGateType.orGate == ACCGateType.input true) = false := rfl

@[simp] private lemma notGate_beq_input_false :
    (ACCGateType.notGate == ACCGateType.input false) = false := rfl

@[simp] private lemma notGate_beq_input_true :
    (ACCGateType.notGate == ACCGateType.input true) = false := rfl

@[simp] private lemma modGate_beq_input_false :
    (ACCGateType.modGate == ACCGateType.input false) = false := rfl

@[simp] private lemma modGate_beq_input_true :
    (ACCGateType.modGate == ACCGateType.input true) = false := rfl

private lemma input_filter_length_eq_positive_add_negative :
    ∀ gs : List ACCGate,
      (gs.filter (fun g => g.type.isInput)).length =
        (gs.filter (fun g => g.type == ACCGateType.input false)).length +
        (gs.filter (fun g => g.type == ACCGateType.input true)).length
  | [] => by simp
  | g :: gs => by
      cases g with
      | mk id type =>
          cases type with
          | input negated =>
              cases negated
              · simp [List.filter, ACCGateType.isInput, Nat.add_assoc, Nat.add_comm]
                change (gs.filter (fun g => g.type.isInput)).length =
                  (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                  (gs.filter (fun g => g.type == ACCGateType.input true)).length
                exact input_filter_length_eq_positive_add_negative gs
              · simp [List.filter, ACCGateType.isInput, Nat.add_comm,
                  Nat.add_left_comm]
                change (gs.filter (fun g => g.type.isInput)).length =
                  (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                  (gs.filter (fun g => g.type == ACCGateType.input true)).length
                exact input_filter_length_eq_positive_add_negative gs
          | output =>
              simp [List.filter, ACCGateType.isInput]
              change (gs.filter (fun g => g.type.isInput)).length =
                (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                (gs.filter (fun g => g.type == ACCGateType.input true)).length
              exact input_filter_length_eq_positive_add_negative gs
          | andGate =>
              simp [List.filter, ACCGateType.isInput]
              change (gs.filter (fun g => g.type.isInput)).length =
                (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                (gs.filter (fun g => g.type == ACCGateType.input true)).length
              exact input_filter_length_eq_positive_add_negative gs
          | orGate =>
              simp [List.filter, ACCGateType.isInput]
              change (gs.filter (fun g => g.type.isInput)).length =
                (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                (gs.filter (fun g => g.type == ACCGateType.input true)).length
              exact input_filter_length_eq_positive_add_negative gs
          | notGate =>
              simp [List.filter, ACCGateType.isInput]
              change (gs.filter (fun g => g.type.isInput)).length =
                (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                (gs.filter (fun g => g.type == ACCGateType.input true)).length
              exact input_filter_length_eq_positive_add_negative gs
          | modGate =>
              simp [List.filter, ACCGateType.isInput]
              change (gs.filter (fun g => g.type.isInput)).length =
                (gs.filter (fun g => g.type == ACCGateType.input false)).length +
                (gs.filter (fun g => g.type == ACCGateType.input true)).length
              exact input_filter_length_eq_positive_add_negative gs

/-- In a well-formed canonical ACC circuit, the total number of gates is
    bounded by the non-input gate count plus the two canonical input blocks. -/
lemma gates_length_le_circuitSize_add_two_mul_inputWidth
    (c : ACCCircuit) (hwf : c.WellFormed) :
    c.gates.length ≤ c.circuitSize + 2 * c.inputWidth := by
  have hpart := list_length_eq_filter_add_not (fun g : ACCGate => g.type.isInput) c.gates
  have hinput := input_filter_length_eq_positive_add_negative c.gates
  have hpos :
      (c.gates.filter (fun g => g.type == ACCGateType.input false)).length =
        c.inputWidth := by
    have := congrArg List.length hwf.has_canonical_input_ids.1
    simpa [positiveInputIds] using this
  have hneg :
      (c.gates.filter (fun g => g.type == ACCGateType.input true)).length =
        c.inputWidth := by
    have := congrArg List.length hwf.has_canonical_input_ids.2
    simpa [negativeInputIds] using this
  unfold circuitSize
  omega

end DAG.ACCCircuit

end Circuits
