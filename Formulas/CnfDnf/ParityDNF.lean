import Formulas.CnfDnf.CnfDnfFamilies
import Formulas.Eval
import Mathlib.Data.List.Perm.Subperm
import Parity.ParityProperties

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.CnfDnf.Families

open Circuits
open Circuits.CnfDnf
open UnboundedFanInFormula

/- ============================================================
   Satisfying assignment for a clause
   ============================================================ -/

/-- The bit value at variable `v` required for the literal `inputGate v negated`
    to evaluate to `true`. -/
def satisfyingBit (negated : Bool) : Bool :=
  match negated with
  | true => false
  | false => true

/-- Build a length-`n` assignment that satisfies all literals in clause `c`:
    each variable mentioned in `c` is set to its satisfying value; variables
    not mentioned in `c` are set to `zero`. -/
def clauseAssignment (c : List (Nat × Bool)) (n : Nat) : List Bool :=
  (List.range n).map fun i =>
    match c.find? (fun p => p.1 == i) with
    | some p => satisfyingBit p.2
    | none => false

/- ============================================================
   Basic properties of `clauseAssignment`
   ============================================================ -/

@[simp] theorem length_clauseAssignment (c : List (Nat × Bool)) (n : Nat) :
    (clauseAssignment c n).length = n := by
  simp [clauseAssignment]

/- ============================================================
   `find?` on nodup variable-keyed lists
   ============================================================ -/

theorem find?_eq_some_of_mem_nodup
    (c : List (Nat × Bool)) (h_nodup : (c.map Prod.fst).Nodup)
    (v : Nat) (b : Bool) (h_mem : (v, b) ∈ c) :
    c.find? (fun p => p.1 == v) = some (v, b) := by
  induction c with
  | nil => cases h_mem
  | cons hd tl ih =>
    rcases hd with ⟨v', b'⟩
    rw [List.map_cons, List.nodup_cons] at h_nodup
    obtain ⟨h_notin, h_nodup_tl⟩ := h_nodup
    rcases List.mem_cons.mp h_mem with h_eq | h_in_tl
    · have hpair := (Prod.mk.injEq _ _ _ _).mp h_eq
      obtain ⟨hv, hb⟩ := hpair
      subst hv; subst hb
      simp [List.find?]
    · have hv_ne : v' ≠ v := by
        intro h
        subst h
        apply h_notin
        exact List.mem_map.mpr ⟨(v', b), h_in_tl, rfl⟩
      have hbeq : (v' == v) = false := by simp [hv_ne]
      simp [List.find?, hbeq]
      exact ih h_nodup_tl h_in_tl

theorem find?_eq_none_of_notMem
    (c : List (Nat × Bool)) (i : Nat) (h : i ∉ c.map Prod.fst) :
    c.find? (fun p => p.1 == i) = none := by
  induction c with
  | nil => simp [List.find?]
  | cons hd tl ih =>
    rcases hd with ⟨v', b'⟩
    rw [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, h_tl⟩ := h
    have hne' : (v' == i) = false := by simp [Ne.symm hne]
    have hpred : ¬ ((fun p : Nat × Bool => p.1 == i) (v', b') = true) := by
      simp [hne']
    rw [List.find?_cons_of_neg (a := (v', b')) (l := tl) hpred]
    exact ih h_tl

/-- At a variable index `v` listed in clause `c` with value `b`, the constructed
    assignment has the satisfying bit. -/
theorem clauseAssignment_getElem_of_mem
    (c : List (Nat × Bool)) (n : Nat)
    (h_nodup : (c.map Prod.fst).Nodup)
    (v : Nat) (b : Bool) (h_mem : (v, b) ∈ c) (h_lt : v < n) :
    (clauseAssignment c n)[v]'(by simp; exact h_lt) = satisfyingBit b := by
  unfold clauseAssignment
  rw [List.getElem_map, List.getElem_range]
  rw [find?_eq_some_of_mem_nodup c h_nodup v b h_mem]

/-- At an index `i` not mentioned by clause `c`, the constructed assignment is `zero`. -/
theorem clauseAssignment_getElem_of_notMem
    (c : List (Nat × Bool)) (n : Nat) (i : Nat)
    (h_not_mem : i ∉ c.map Prod.fst) (h_lt : i < n) :
    (clauseAssignment c n)[i]'(by simp; exact h_lt) = false := by
  unfold clauseAssignment
  rw [List.getElem_map, List.getElem_range]
  rw [find?_eq_none_of_notMem c i h_not_mem]

/- ============================================================
   Evaluation of `inputGate` literals
   ============================================================ -/

theorem ufi_eval_input_lt (inputs : List Bool) (v : Nat) (b : Bool)
    (h : v < inputs.length) :
    ufiFormulaEval (inputGate v b) inputs =
      (if b then Bool.not (inputs[v]'h) else inputs[v]'h) := by
  unfold ufiFormulaEval
  have hg : inputs[v]? = some (inputs[v]'h) := by
    exact List.getElem?_eq_getElem h
  rw [hg]
  cases b <;> simp

theorem ufi_eval_input_satisfying
    (inputs : List Bool) (v : Nat) (b : Bool) (h : v < inputs.length)
    (hbit : inputs[v]'h = satisfyingBit b) :
    ufiFormulaEval (inputGate v b) inputs = true := by
  rw [ufi_eval_input_lt inputs v b h, hbit]
  cases b <;> simp [satisfyingBit, Bool.not]

/-- Bound on `inputGate` variable indices implied by `ufiLargestInput < n`. -/
theorem var_lt_of_input_mem
    (dnf : UnboundedFanInFormula) (n : Nat)
    (h_bound : ufiLargestInput dnf < n)
    (v : Nat) (h_in : v ∈ ufiCollectInputIndices dnf) :
    v < n := by
  have h_le : v ≤ (List.foldr max 0) (ufiCollectInputIndices dnf) :=
    Circuits.adder_foldr_max_ge_of_mem h_in
  exact Nat.lt_of_le_of_lt h_le h_bound

theorem mem_collect_of_input_in_andgate
    (lits : List UnboundedFanInFormula) (v : Nat) (b : Bool)
    (h : inputGate v b ∈ lits) :
    v ∈ ufiCollectInputIndices (andGate lits) := by
  simp [ufiCollectInputIndices]
  refine ⟨inputGate v b, h, ?_⟩
  simp [ufiCollectInputIndices]

theorem mem_collect_of_andgate_in_orgate
    (gates : List UnboundedFanInFormula) (g : UnboundedFanInFormula)
    (hg : g ∈ gates) (v : Nat) (hv : v ∈ ufiCollectInputIndices g) :
    v ∈ ufiCollectInputIndices (orGate gates) := by
  simp [ufiCollectInputIndices]
  exact ⟨g, hg, hv⟩

/- ============================================================
   Connecting `dnfClauses` to the structural decomposition
   ============================================================ -/

/-- When `c ∈ dnfClauses (orGate gates)`, some sub-gate `g ∈ gates` yields `c`. -/
theorem mem_dnfClauses_orGate
    (gates : List UnboundedFanInFormula) (c : List (Nat × Bool))
    (h : c ∈ dnfClauses (orGate gates)) :
    ∃ g ∈ gates,
      c = (match g with
            | andGate lits => lits.filterMap fun lit =>
                match lit with
                | inputGate i b => some (i, b)
                | _ => none
            | _ => []) := by
  simp [dnfClauses] at h
  obtain ⟨g, hg, hgc⟩ := h
  exact ⟨g, hg, hgc.symm⟩

/-- Every `(v, b)` pair in `c` (for `c ∈ dnfClauses`) came from a corresponding
    `inputGate v b` literal in the andGate. -/
theorem input_mem_of_pair_mem_clause
    (gates : List UnboundedFanInFormula) (h_dnf : isDNF (orGate gates) = true)
    (c : List (Nat × Bool)) (h_c : c ∈ dnfClauses (orGate gates))
    (v : Nat) (b : Bool) (h_pair : (v, b) ∈ c) :
    ∃ g ∈ gates, ∃ lits, g = andGate lits ∧ inputGate v b ∈ lits := by
  obtain ⟨g, hg, hgc⟩ := mem_dnfClauses_orGate gates c h_c
  obtain ⟨lits, hglits, h_inputs⟩ := mem_gates_of_dnf gates h_dnf g hg
  refine ⟨g, hg, lits, hglits, ?_⟩
  rw [hglits] at hgc
  rw [hgc] at h_pair
  rw [List.mem_filterMap] at h_pair
  obtain ⟨lit, h_lit_mem, h_lit_eq⟩ := h_pair
  obtain ⟨v', b', rfl⟩ := h_inputs lit h_lit_mem
  simp only at h_lit_eq
  have hopt : (v', b') = (v, b) := Option.some_inj.mp h_lit_eq
  have hvb := (Prod.mk.injEq _ _ _ _).mp hopt
  obtain ⟨hv, hb⟩ := hvb
  subst hv; subst hb
  exact h_lit_mem

theorem var_lt_of_pair_mem_clause
    (dnf : UnboundedFanInFormula) (n : Nat)
    (h_bound : ufiLargestInput dnf < n)
    (h_dnf : isDNF dnf = true)
    (c : List (Nat × Bool)) (h_c : c ∈ dnfClauses dnf)
    (v : Nat) (b : Bool) (h_pair : (v, b) ∈ c) :
    v < n := by
  obtain ⟨gates, rfl⟩ := isDNF_eq_orGate dnf h_dnf
  obtain ⟨g, hg, lits, rfl, h_lit⟩ :=
    input_mem_of_pair_mem_clause gates h_dnf c h_c v b h_pair
  have h1 : v ∈ ufiCollectInputIndices (andGate lits) :=
    mem_collect_of_input_in_andgate lits v b h_lit
  have h2 : v ∈ ufiCollectInputIndices (orGate gates) :=
    mem_collect_of_andgate_in_orgate gates (andGate lits) hg v h1
  exact var_lt_of_input_mem (orGate gates) n h_bound v h2

/- ============================================================
   Evaluating an andGate of literals at a satisfying assignment
   ============================================================ -/

/-- An `andGate` of literals evaluates to `true` when each literal does. -/
theorem ufi_eval_andGate_inputs_eq_one
    (lits : List UnboundedFanInFormula)
    (inputs : List Bool)
    (h_all : ∀ l ∈ lits, ufiFormulaEval l inputs = true) :
    ufiFormulaEval (andGate lits) inputs = true := by
  rw [ufi_eval_andGate_eq_all]
  have hall : (lits.map fun c => ufiFormulaEval c inputs).all (· == true) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨l, hl, hxeq⟩ := hx
    rw [← hxeq, h_all l hl]
    decide
  rw [hall]
  decide

/-- An `orGate` evaluates to `true` when some sub-gate evaluates to `true`. -/
theorem ufi_eval_orGate_eq_one
    (gates : List UnboundedFanInFormula) (inputs : List Bool)
    (g : UnboundedFanInFormula) (hg : g ∈ gates)
    (h_eq : ufiFormulaEval g inputs = true) :
    ufiFormulaEval (orGate gates) inputs = true := by
  rw [ufi_eval_orGate_eq_any]
  have hany : (gates.map fun c => ufiFormulaEval c inputs).any (· == true) = true := by
    rw [List.any_eq_true]
    refine ⟨true, ?_, by decide⟩
    rw [List.mem_map]
    exact ⟨g, hg, h_eq⟩
  rw [hany]
  decide

/-- If an `orGate` evaluates to `true`, one of its sub-gates evaluates to
    `true`. -/
theorem orGate_eval_one_exists (gates : List UnboundedFanInFormula) (inputs : List Bool)
    (h : ufiFormulaEval (orGate gates) inputs = true) :
    ∃ g ∈ gates, ufiFormulaEval g inputs = true := by
  rw [ufi_eval_orGate_eq_any] at h
  simpa [List.any_eq_true] using h

/- ============================================================
   Main theorem
   ============================================================ -/

/-- A proper DNF computing parity, or its complement, must have every variable
    appear in every clause:
    for each clause `c` and each `i < n`, `i` is one of the variables of `c`. -/
theorem proper_dnf_computing_offset_parity_mentions_all_vars
    (n : Nat) (f : UnboundedFanInProperDNF n) (offset : Bool)
    (h_parity : ∀ inputs, inputs.length = n →
      ((ufiFormulaEval f.val inputs = true) ↔
        (Odd (inputs.countP (· == true)) ↔ offset = false))) :
    ∀ c ∈ dnfClauses f.val,
      ∀ i, i < n → i ∈ c.map Prod.fst := by
  intro c h_c i hi
  by_contra h_not_mem
  set dnf := f.val with hdnf
  have h_bound : ufiLargestInput dnf < n := f.property.1
  have h_dnf   : isDNF dnf = true := f.property.2.1
  have h_nodup_all := f.property.2.2.2
  have h_nodup : (c.map Prod.fst).Nodup := h_nodup_all c h_c
  set a := clauseAssignment c n with ha_def
  have ha_len : a.length = n := length_clauseAssignment c n
  set a' := flipAt a i with ha'_def
  have ha'_len : a'.length = n := by
    rw [ha'_def, length_flipAt, ha_len]
  have ha_i : a[i]'(by rw [ha_len]; exact hi) = false :=
    clauseAssignment_getElem_of_notMem c n i h_not_mem hi
  obtain ⟨gates, h_or_eq⟩ := isDNF_eq_orGate dnf h_dnf
  obtain ⟨g, hg, h_c_eq⟩ := mem_dnfClauses_orGate gates c (by rw [← h_or_eq]; exact h_c)
  obtain ⟨lits, h_g_eq, h_inputs⟩ :=
    mem_gates_of_dnf gates (by rw [← h_or_eq]; exact h_dnf) g hg
  rw [h_g_eq] at h_c_eq
  -- Now h_c_eq : c = lits.filterMap (...)
  have h_lits_one_a : ∀ l ∈ lits, ufiFormulaEval l a = true := by
    intro l hl
    obtain ⟨v, b, rfl⟩ := h_inputs l hl
    have h_pair_in : (v, b) ∈ c := by
      rw [h_c_eq]
      rw [List.mem_filterMap]
      exact ⟨inputGate v b, hl, rfl⟩
    have hv_lt_n : v < n :=
      var_lt_of_pair_mem_clause dnf n h_bound h_dnf c h_c v b h_pair_in
    have hv_lt_a : v < a.length := by rw [ha_len]; exact hv_lt_n
    have h_av : a[v]'hv_lt_a = satisfyingBit b :=
      clauseAssignment_getElem_of_mem c n h_nodup v b h_pair_in hv_lt_n
    exact ufi_eval_input_satisfying a v b hv_lt_a h_av
  have h_lits_one_a' : ∀ l ∈ lits, ufiFormulaEval l a' = true := by
    intro l hl
    obtain ⟨v, b, rfl⟩ := h_inputs l hl
    have h_pair_in : (v, b) ∈ c := by
      rw [h_c_eq]
      rw [List.mem_filterMap]
      exact ⟨inputGate v b, hl, rfl⟩
    have hv_lt_n : v < n :=
      var_lt_of_pair_mem_clause dnf n h_bound h_dnf c h_c v b h_pair_in
    have hv_lt_a : v < a.length := by rw [ha_len]; exact hv_lt_n
    have hv_ne_i : v ≠ i := by
      intro h
      subst h
      exact h_not_mem (List.mem_map.mpr ⟨(v, b), h_pair_in, rfl⟩)
    have hv_lt_a' : v < a'.length := by rw [ha'_len]; exact hv_lt_n
    have h_a'v_sat : a'[v]'hv_lt_a' = satisfyingBit b := by
      have hflip : a'[v]'hv_lt_a' = a[v]'hv_lt_a :=
        getElem_flipAt_of_ne a i v hv_lt_a hv_ne_i
      have h_av : a[v]'hv_lt_a = satisfyingBit b :=
        clauseAssignment_getElem_of_mem c n h_nodup v b h_pair_in hv_lt_n
      exact hflip.trans h_av
    exact ufi_eval_input_satisfying a' v b hv_lt_a' h_a'v_sat
  have h_and_a : ufiFormulaEval (andGate lits) a = true :=
    ufi_eval_andGate_inputs_eq_one lits a h_lits_one_a
  have h_and_a' : ufiFormulaEval (andGate lits) a' = true :=
    ufi_eval_andGate_inputs_eq_one lits a' h_lits_one_a'
  have h_dnf_a : ufiFormulaEval dnf a = true := by
    rw [h_or_eq]
    exact ufi_eval_orGate_eq_one gates a (andGate lits)
      (by rw [← h_g_eq]; exact hg) h_and_a
  have h_dnf_a' : ufiFormulaEval dnf a' = true := by
    rw [h_or_eq]
    exact ufi_eval_orGate_eq_one gates a' (andGate lits)
      (by rw [← h_g_eq]; exact hg) h_and_a'
  have h_target_a := (h_parity a ha_len).mp h_dnf_a
  have h_target_a' := (h_parity a' ha'_len).mp h_dnf_a'
  have h_diff : parityBit a' ≠ parityBit a := by
    rw [ha'_def]
    have hi_lt_a : i < a.length := by rw [ha_len]; exact hi
    exact parityBit_flipAt_ne_of_eq_false a i hi_lt_a ha_i
  have hbit : (parityBit a' = true) ↔ ¬ (parityBit a = true) := by
    cases hpa : parityBit a <;> cases hpa' : parityBit a' <;> simp_all
  have hodd : Odd (a'.countP (· == true)) ↔ ¬ Odd (a.countP (· == true)) := by
    rw [odd_countP_iff_parityBit a', odd_countP_iff_parityBit a]
    exact hbit
  rw [hodd] at h_target_a'
  tauto

/-- If a proper DNF computes parity, or its complement, every clause has
    exactly `n` literals. -/
theorem proper_dnf_computing_offset_parity_clause_length
    (n : Nat) (f : UnboundedFanInProperDNF n) (offset : Bool)
    (h_parity : ∀ inputs, inputs.length = n →
      ((ufiFormulaEval f.val inputs = true) ↔
        (Odd (inputs.countP (· == true)) ↔ offset = false))) :
    ∀ c ∈ dnfClauses f.val, c.length = n := by
  intro c h_c
  have h_nodup : (c.map Prod.fst).Nodup := f.property.2.2.2 c h_c
  have h_all : ∀ i, i < n → i ∈ c.map Prod.fst :=
    proper_dnf_computing_offset_parity_mentions_all_vars n f offset h_parity c h_c
  have h_bound : ufiLargestInput f.val < n := f.property.1
  have h_dnf   : isDNF f.val = true := f.property.2.1
  have h_sub : ∀ v, v ∈ (c.map Prod.fst) → v < n := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨⟨v', b'⟩, hp, hveq⟩ := hv
    have heq : v' = v := hveq
    rw [← heq]
    exact var_lt_of_pair_mem_clause f.val n h_bound h_dnf c h_c v' b' hp
  have h1 : (List.range n).Subperm (c.map Prod.fst) := by
    apply List.subperm_of_subset List.nodup_range
    intro v hv
    exact h_all v (List.mem_range.mp hv)
  have h2 : (c.map Prod.fst).Subperm (List.range n) := by
    apply List.subperm_of_subset h_nodup
    intro v hv
    exact List.mem_range.mpr (h_sub v hv)
  have hlen_ge : n ≤ (c.map Prod.fst).length := by
    have hh := h1.length_le
    rwa [List.length_range] at hh
  have hlen_le : (c.map Prod.fst).length ≤ n := by
    have hh := h2.length_le
    rwa [List.length_range] at hh
  have hlen : (c.map Prod.fst).length = n := Nat.le_antisymm hlen_le hlen_ge
  have hmap_len : (c.map Prod.fst).length = c.length := List.length_map _
  omega

/- ============================================================
   Narrow proper DNF versus parity
   ============================================================ -/

/-- A proper DNF whose width is smaller than its number of variables disagrees
    with parity, or with parity's complement, on some input. -/
theorem narrow_dnf_misclassifies_parity
      (n : Nat)
      (g : UnboundedFanInProperDNF n)
      (hgw : dnfWidth g.val < n)
      (offset : Bool) :
  ∃ (inputs : List Bool), inputs.length = n ∧
    ((ufiFormulaEval g.val inputs = true) ≠
      (Odd (inputs.countP (· == true)) ↔ offset = false)) := by
  by_contra h_agrees
  push Not at h_agrees
  have h_parity : ∀ inputs, inputs.length = n →
      ((ufiFormulaEval g.val inputs = true) ↔
        (Odd (inputs.countP (· == true)) ↔ offset = false)) := by
    intro inputs hlen
    exact iff_of_eq (h_agrees inputs hlen)
  have h_lengths :=
    proper_dnf_computing_offset_parity_clause_length n g offset h_parity
  have hn : 0 < n := by omega
  obtain ⟨a, ha_len, ha_target⟩ : ∃ a : List Bool, a.length = n ∧
      (Odd (a.countP (· == true)) ↔ offset = false) := by
    cases offset with
    | false =>
      refine ⟨true :: List.replicate (n - 1) false, ?_, ?_⟩
      · simp only [List.length_cons, List.length_replicate]
        omega
      · rw [List.countP_cons, List.countP_replicate]
        simp
    | true =>
      refine ⟨List.replicate n false, by simp, ?_⟩
      rw [List.countP_replicate]
      simp
  have ha_eval : ufiFormulaEval g.val a = true :=
    (h_parity a ha_len).mpr ha_target
  obtain ⟨c, hc⟩ : ∃ c, c ∈ dnfClauses g.val := by
    obtain ⟨gates, h_or⟩ := isDNF_eq_orGate g.val g.property.2.1
    rw [h_or] at ha_eval
    obtain ⟨gc, hgc_mem, _⟩ := orGate_eval_one_exists gates a ha_eval
    obtain ⟨lits, hgc_lits, _⟩ :=
      mem_gates_of_dnf gates (by rw [← h_or]; exact g.property.2.1) gc hgc_mem
    refine ⟨lits.filterMap (fun lit => match lit with
      | inputGate i b => some (i, b) | _ => none), ?_⟩
    rw [h_or]
    simp only [dnfClauses, List.mem_map]
    refine ⟨gc, hgc_mem, ?_⟩
    rw [hgc_lits]
    rfl
  have hc_width : c.length ≤ dnfWidth g.val :=
    clause_length_le_dnfWidth g.val g.property.2.1 c hc
  rw [h_lengths c hc] at hc_width
  omega

end Circuits.CnfDnf.Families
