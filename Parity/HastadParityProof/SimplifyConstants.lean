/-
  constant absorption after restricted substitution.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.Leveling.SimplifyConstantsCore
import Parity.HastadParityProof.Substitution

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-! ### constant-absorption pass `simplifyConstants`.

    A switching restriction may *kill* an `inputGate` leaf — its restricted
    value is a constant (the dead bit), so the producer substitutes a
    `constant` at that position.  After `substFlatten` such a `constant`
    lands as a direct child of an AND/OR gate (`flattenAndChild` /
    `flattenOrChild` keep a `constant` as a singleton).  This pass folds
    those constants away, restoring `IsConstantFree` and (at level ≤ 2)
    proper CNF/DNF shape, while preserving evaluation.

    Constants are represented canonically by *empty gates*:
    `andGate []` evaluates to `true`, `orGate []` to `false` (see
    `ufiFormulaEval`), and both are `IsConstantFree` (they contain no
    `constant` node).  Because every constant-equivalent subformula folds
    to exactly `andGate []` (true) or `orGate []` (false), the syntactic
    tests `isCanonicalTrue` / `isCanonicalFalse` on already-simplified children suffice
    for absorption.  The pass never emits a `constant` constructor, so
    its output is unconditionally `IsConstantFree`. -/
section SimplifyConstants

/- The pass never emits a `constant` constructor, so its output is
    unconditionally constant-free. -/
mutual

theorem isConstantFree_simplifyConstants :
    ∀ (f : UnboundedFanInFormula), IsConstantFree (simplifyConstants f)
  | inputGate x b => by simp only [simplifyConstants, IsConstantFree]
  | constant b _ => by
      simp only [simplifyConstants]
      cases b <;> simp [IsConstantFree]
  | notGate g => by
      simp only [simplifyConstants, IsConstantFree]
      exact isConstantFree_simplifyConstants g
  | andGate gs => by
      simp only [simplifyConstants]
      split
      · simp [IsConstantFree]
      · simp only [IsConstantFree]
        intro g hg
        rw [List.mem_filter] at hg
        exact isConstantFree_simplifyConstantsList gs g hg.1
  | orGate gs => by
      simp only [simplifyConstants]
      split
      · simp [IsConstantFree]
      · simp only [IsConstantFree]
        intro g hg
        rw [List.mem_filter] at hg
        exact isConstantFree_simplifyConstantsList gs g hg.1

theorem isConstantFree_simplifyConstantsList :
    ∀ (gs : List UnboundedFanInFormula), ∀ g ∈ simplifyConstantsList gs, IsConstantFree g
  | [] => by intro g hg; simp [simplifyConstantsList] at hg
  | g₀ :: gs => by
      intro g hg
      simp only [simplifyConstantsList, List.mem_cons] at hg
      cases hg with
      | inl h => rw [h]; exact isConstantFree_simplifyConstants g₀
      | inr h => exact isConstantFree_simplifyConstantsList gs g h

end

/-- `isCanonicalTrue g` holds exactly when `g` is the canonical true constant. -/
lemma isCanonicalTrue_iff (g : UnboundedFanInFormula) :
    isCanonicalTrue g = true ↔ g = andGate [] := by
  cases g with
  | inputGate x b => simp [isCanonicalTrue]
  | constant b m => simp [isCanonicalTrue]
  | notGate g₀ => simp [isCanonicalTrue]
  | andGate gs => cases gs <;> simp [isCanonicalTrue]
  | orGate gs => simp [isCanonicalTrue]

/-- `isCanonicalFalse g` holds exactly when `g` is the canonical false constant. -/
lemma isCanonicalFalse_iff (g : UnboundedFanInFormula) :
    isCanonicalFalse g = true ↔ g = orGate [] := by
  cases g with
  | inputGate x b => simp [isCanonicalFalse]
  | constant b m => simp [isCanonicalFalse]
  | notGate g₀ => simp [isCanonicalFalse]
  | andGate gs => simp [isCanonicalFalse]
  | orGate gs => cases gs <;> simp [isCanonicalFalse]

lemma eval_andGate_nil (xs : List Bool) :
    ufiFormulaEval (andGate []) xs = true := by simp [ufiFormulaEval]

lemma eval_orGate_nil (xs : List Bool) :
    ufiFormulaEval (orGate []) xs = false := by simp [ufiFormulaEval]

/-- Dropping the canonical-true children does not change `.all (· == one)`
    of the evaluated child list. -/
lemma all_one_filter_isCanonicalTrue (cs : List UnboundedFanInFormula) (xs : List Bool) :
    ((cs.filter (fun g => !isCanonicalTrue g)).map (fun c => ufiFormulaEval c xs)).all (· == true)
      = (cs.map (fun c => ufiFormulaEval c xs)).all (· == true) := by
  induction cs with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : isCanonicalTrue hd = true
    · have hhd : ufiFormulaEval hd xs = true := by
        rw [(isCanonicalTrue_iff hd).mp h, eval_andGate_nil]
      have hfilt : (hd :: tl).filter (fun g => !isCanonicalTrue g)
            = tl.filter (fun g => !isCanonicalTrue g) := by
        rw [List.filter_cons]; simp [h]
      rw [hfilt, ih, List.map_cons, List.all_cons, hhd]; simp
    · have h' : isCanonicalTrue hd = false := by simpa using h
      have hfilt : (hd :: tl).filter (fun g => !isCanonicalTrue g)
            = hd :: tl.filter (fun g => !isCanonicalTrue g) := by
        rw [List.filter_cons]; simp [h']
      rw [hfilt, List.map_cons, List.map_cons, List.all_cons, List.all_cons, ih]

/-- Dropping the canonical-false children does not change `.any (· == one)`
    of the evaluated child list. -/
lemma any_one_filter_isCanonicalFalse (cs : List UnboundedFanInFormula) (xs : List Bool) :
    ((cs.filter (fun g => !isCanonicalFalse g)).map (fun c => ufiFormulaEval c xs)).any (· == true)
      = (cs.map (fun c => ufiFormulaEval c xs)).any (· == true) := by
  induction cs with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : isCanonicalFalse hd = true
    · have hhd : ufiFormulaEval hd xs = false := by
        rw [(isCanonicalFalse_iff hd).mp h, eval_orGate_nil]
      have hfilt : (hd :: tl).filter (fun g => !isCanonicalFalse g)
            = tl.filter (fun g => !isCanonicalFalse g) := by
        rw [List.filter_cons]; simp [h]
      rw [hfilt, ih, List.map_cons, List.any_cons, hhd]; simp
    · have h' : isCanonicalFalse hd = false := by simpa using h
      have hfilt : (hd :: tl).filter (fun g => !isCanonicalFalse g)
            = hd :: tl.filter (fun g => !isCanonicalFalse g) := by
        rw [List.filter_cons]; simp [h']
      rw [hfilt, List.map_cons, List.map_cons, List.any_cons, List.any_cons, ih]

/- The absorption pass preserves evaluation. -/
mutual

theorem simplifyConstants_eval :
    ∀ (f : UnboundedFanInFormula) (xs : List Bool),
      ufiFormulaEval (simplifyConstants f) xs = ufiFormulaEval f xs
  | inputGate x b, xs => by simp only [simplifyConstants]
  | constant b _, xs => by
      simp only [simplifyConstants]
      cases b
      · rw [eval_orGate_nil]; simp [ufiFormulaEval]
      · rw [eval_andGate_nil]; simp [ufiFormulaEval]
  | notGate g, xs => by
      simp only [simplifyConstants, ufiFormulaEval]
      rw [simplifyConstants_eval g]
  | andGate gs, xs => by
      have hmap : (simplifyConstantsList gs).map (fun c => ufiFormulaEval c xs)
                    = gs.map (fun c => ufiFormulaEval c xs) :=
        simplifyConstantsList_eval gs xs
      simp only [simplifyConstants]
      by_cases h : (simplifyConstantsList gs).any isCanonicalFalse = true
      · obtain ⟨c, hc, hc_f⟩ := List.any_eq_true.mp h
        have hc₀ : ufiFormulaEval c xs = false := by
          rw [(isCanonicalFalse_iff c).mp hc_f, eval_orGate_nil]
        have hmem : false ∈ gs.map (fun c => ufiFormulaEval c xs) := by
          rw [← hmap]; exact hc₀ ▸ List.mem_map_of_mem hc
        have hnall : ¬ ((gs.map (fun c => ufiFormulaEval c xs)).all (· == true) = true) := by
          rw [List.all_eq_true]; intro hall; have := hall false hmem; simp at this
        rw [if_pos h, eval_orGate_nil, ufi_eval_andGate_eq_all, if_neg hnall]
      · rw [if_neg h, ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all,
            all_one_filter_isCanonicalTrue, hmap]
  | orGate gs, xs => by
      have hmap : (simplifyConstantsList gs).map (fun c => ufiFormulaEval c xs)
                    = gs.map (fun c => ufiFormulaEval c xs) :=
        simplifyConstantsList_eval gs xs
      simp only [simplifyConstants]
      by_cases h : (simplifyConstantsList gs).any isCanonicalTrue = true
      · obtain ⟨c, hc, hc_t⟩ := List.any_eq_true.mp h
        have hc₁ : ufiFormulaEval c xs = true := by
          rw [(isCanonicalTrue_iff c).mp hc_t, eval_andGate_nil]
        have hmem : true ∈ gs.map (fun c => ufiFormulaEval c xs) := by
          rw [← hmap]; exact hc₁ ▸ List.mem_map_of_mem hc
        have hany : (gs.map (fun c => ufiFormulaEval c xs)).any (· == true) = true := by
          rw [List.any_eq_true]; exact ⟨true, hmem, by simp⟩
        rw [if_pos h, eval_andGate_nil, ufi_eval_orGate_eq_any, if_pos hany]
      · rw [if_neg h, ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any,
            any_one_filter_isCanonicalFalse, hmap]

theorem simplifyConstantsList_eval :
    ∀ (gs : List UnboundedFanInFormula) (xs : List Bool),
      (simplifyConstantsList gs).map (fun c => ufiFormulaEval c xs)
        = gs.map (fun c => ufiFormulaEval c xs)
  | [], xs => by simp [simplifyConstantsList]
  | g₀ :: gs, xs => by
      simp only [simplifyConstantsList, List.map_cons]
      rw [simplifyConstants_eval g₀ xs, simplifyConstantsList_eval gs xs]

end

/- An `inputGate` literal is never one of the canonical constant gates. -/
lemma isCanonicalTrue_eq_false_of_input {x : UnboundedFanInFormula}
    (h : isInput x = true) : isCanonicalTrue x = false := by
  cases x with
  | inputGate a b => simp [isCanonicalTrue]
  | constant a b => simp [isInput] at h
  | notGate a => simp [isInput] at h
  | andGate a => simp [isInput] at h
  | orGate a => simp [isInput] at h

lemma isCanonicalFalse_eq_false_of_input {x : UnboundedFanInFormula}
    (h : isInput x = true) : isCanonicalFalse x = false := by
  cases x with
  | inputGate a b => simp [isCanonicalFalse]
  | constant a b => simp [isInput] at h
  | notGate a => simp [isInput] at h
  | andGate a => simp [isInput] at h
  | orGate a => simp [isInput] at h

/- The pass is the identity on `inputGate` leaves. -/
lemma simplifyConstants_input_id {g : UnboundedFanInFormula}
    (h : isInput g = true) : simplifyConstants g = g := by
  cases g with
  | inputGate a b => simp [simplifyConstants]
  | constant a b => simp [isInput] at h
  | notGate a => simp [isInput] at h
  | andGate a => simp [isInput] at h
  | orGate a => simp [isInput] at h

/- The list pass is the identity on a list of `inputGate` leaves. -/
lemma simplifyConstantsList_inputs_id :
    ∀ (gs : List UnboundedFanInFormula), gs.all isInput = true →
      simplifyConstantsList gs = gs
  | [], _ => by simp [simplifyConstantsList]
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      simp only [simplifyConstantsList]
      rw [simplifyConstants_input_id h.1, simplifyConstantsList_inputs_id xs h.2]

/- A list of `inputGate` leaves contains no canonical-true gate. -/
lemma any_isCanonicalTrue_eq_false_of_inputs :
    ∀ (gs : List UnboundedFanInFormula), gs.all isInput = true → gs.any isCanonicalTrue = false
  | [], _ => by simp
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      simp [List.any_cons, isCanonicalTrue_eq_false_of_input h.1,
        any_isCanonicalTrue_eq_false_of_inputs xs h.2]

lemma any_isCanonicalFalse_eq_false_of_inputs :
    ∀ (gs : List UnboundedFanInFormula), gs.all isInput = true → gs.any isCanonicalFalse = false
  | [], _ => by simp
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      simp [List.any_cons, isCanonicalFalse_eq_false_of_input h.1,
        any_isCanonicalFalse_eq_false_of_inputs xs h.2]

/- Filtering out canonical-false gates from a list of `inputGate` leaves is a no-op. -/
lemma filter_not_isCanonicalFalse_id_of_inputs :
    ∀ (gs : List UnboundedFanInFormula), gs.all isInput = true →
      gs.filter (fun g => !isCanonicalFalse g) = gs
  | [], _ => by simp
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [List.filter_cons]
      simp [isCanonicalFalse_eq_false_of_input h.1, filter_not_isCanonicalFalse_id_of_inputs xs h.2]

lemma filter_not_isCanonicalTrue_id_of_inputs :
    ∀ (gs : List UnboundedFanInFormula), gs.all isInput = true →
      gs.filter (fun g => !isCanonicalTrue g) = gs
  | [], _ => by simp
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [List.filter_cons]
      simp [isCanonicalTrue_eq_false_of_input h.1, filter_not_isCanonicalTrue_id_of_inputs xs h.2]

/- The pass is the identity on a proper CNF clause `orGate [inputs…]`. -/
lemma simplifyConstants_or_inputs_id {g : UnboundedFanInFormula}
    (h : isOrOfInputsOnly g = true) : simplifyConstants g = g := by
  cases g with
  | inputGate a b => simp [isOrOfInputsOnly] at h
  | constant a b => simp [isOrOfInputsOnly] at h
  | notGate a => simp [isOrOfInputsOnly] at h
  | andGate a => simp [isOrOfInputsOnly] at h
  | orGate lits =>
      have hlits : lits.all isInput = true := by
        simpa [isOrOfInputsOnly] using h
      simp only [simplifyConstants]
      rw [simplifyConstantsList_inputs_id lits hlits,
          any_isCanonicalTrue_eq_false_of_inputs lits hlits,
          filter_not_isCanonicalFalse_id_of_inputs lits hlits]
      simp

/- The pass is the identity on a proper DNF clause `andGate [inputs…]`. -/
lemma simplifyConstants_and_inputs_id {g : UnboundedFanInFormula}
    (h : isAndOfInputsOnly g = true) : simplifyConstants g = g := by
  cases g with
  | inputGate a b => simp [isAndOfInputsOnly] at h
  | constant a b => simp [isAndOfInputsOnly] at h
  | notGate a => simp [isAndOfInputsOnly] at h
  | orGate a => simp [isAndOfInputsOnly] at h
  | andGate lits =>
      have hlits : lits.all isInput = true := by
        simpa [isAndOfInputsOnly] using h
      simp only [simplifyConstants]
      rw [simplifyConstantsList_inputs_id lits hlits,
          any_isCanonicalFalse_eq_false_of_inputs lits hlits,
          filter_not_isCanonicalTrue_id_of_inputs lits hlits]
      simp

/- The list pass is the identity on a list of proper CNF clauses. -/
lemma simplifyConstantsList_or_inputs_id :
    ∀ (gs : List UnboundedFanInFormula), gs.all isOrOfInputsOnly = true →
      simplifyConstantsList gs = gs
  | [], _ => by simp [simplifyConstantsList]
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      simp only [simplifyConstantsList]
      rw [simplifyConstants_or_inputs_id h.1, simplifyConstantsList_or_inputs_id xs h.2]

lemma simplifyConstantsList_and_inputs_id :
    ∀ (gs : List UnboundedFanInFormula), gs.all isAndOfInputsOnly = true →
      simplifyConstantsList gs = gs
  | [], _ => by simp [simplifyConstantsList]
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      simp only [simplifyConstantsList]
      rw [simplifyConstants_and_inputs_id h.1, simplifyConstantsList_and_inputs_id xs h.2]

/- `simplifyConstantsList` is the pointwise map of `simplifyConstants`. -/
lemma simplifyConstantsList_eq_map (gs : List UnboundedFanInFormula) :
    simplifyConstantsList gs = gs.map simplifyConstants := by
  induction gs with
  | nil => simp [simplifyConstantsList]
  | cons g gs ih => simp [simplifyConstantsList, ih]

/- The canonical empty gates are proper at every level. -/
lemma hasProperBottomsAt_orGate_nil (lvl : Nat) :
    HasProperBottomsAt (orGate []) lvl := by
  unfold HasProperBottomsAt
  by_cases hl : lvl ≤ 2
  · rw [if_pos hl]
    refine ⟨by simp [isDNF], ?_, ?_⟩ <;> simp [dnfClauses]
  · rw [if_neg hl]
    intro g hg; simp at hg

lemma hasProperBottomsAt_andGate_nil (lvl : Nat) :
    HasProperBottomsAt (andGate []) lvl := by
  unfold HasProperBottomsAt
  by_cases hl : lvl ≤ 2
  · rw [if_pos hl]
    refine ⟨by simp [isCNF], ?_, ?_⟩ <;> simp [cnfClauses]
  · rw [if_neg hl]
    intro g hg; simp at hg

/- The absorption pass preserves `HasProperBottomsAt`.  A proper CNF/DNF
    bottom (level ≤ 2) is left essentially unchanged (its input literals
    have no constants to fold); folding higher up only collapses gates to
    the canonical empty gates (proper at any level) or drops children. -/
mutual

theorem hasProperBottomsAt_simplifyConstants :
    ∀ (f : UnboundedFanInFormula) (lvl : Nat),
      HasProperBottomsAt f lvl → HasProperBottomsAt (simplifyConstants f) lvl
  | inputGate x b, lvl, h => by simp only [simplifyConstants]; exact h
  | constant b m, lvl, _ => by
      simp only [simplifyConstants]
      cases b
      · exact hasProperBottomsAt_orGate_nil lvl
      · exact hasProperBottomsAt_andGate_nil lvl
  | notGate g, lvl, h => by
      unfold HasProperBottomsAt at h; exact h.elim
  | andGate gs, lvl, h => by
      by_cases hl : lvl ≤ 2
      · unfold HasProperBottomsAt at h
        rw [if_pos hl] at h
        have hcnf : isCNF (andGate gs) = true := h.1
        have hall : gs.all isOrOfInputsOnly = true := by
          simpa [isCNF] using hcnf
        have hid : simplifyConstantsList gs = gs :=
          simplifyConstantsList_or_inputs_id gs hall
        simp only [simplifyConstants]
        rw [hid]
        by_cases hf : gs.any isCanonicalFalse = true
        · rw [if_pos hf]; exact hasProperBottomsAt_orGate_nil lvl
        · rw [if_neg hf]
          have hfilt : gs.filter (fun g => !isCanonicalTrue g) = gs := by
            rw [List.all_eq_true] at hall
            apply List.filter_eq_self.mpr
            intro x hx
            have hxt : isCanonicalTrue x = false := by
              have hor := hall x hx
              cases x with
              | orGate l => simp [isCanonicalTrue]
              | inputGate a b => simp [isOrOfInputsOnly] at hor
              | constant a b => simp [isOrOfInputsOnly] at hor
              | notGate a => simp [isOrOfInputsOnly] at hor
              | andGate a => simp [isOrOfInputsOnly] at hor
            simp [hxt]
          rw [hfilt]
          unfold HasProperBottomsAt
          rw [if_pos hl]
          exact h
      · unfold HasProperBottomsAt at h
        rw [if_neg hl] at h
        simp only [simplifyConstants]
        by_cases hf : (simplifyConstantsList gs).any isCanonicalFalse = true
        · rw [if_pos hf]; exact hasProperBottomsAt_orGate_nil lvl
        · rw [if_neg hf]
          unfold HasProperBottomsAt
          rw [if_neg hl]
          intro g hg
          rw [List.mem_filter] at hg
          exact hasProperBottomsAt_simplifyConstantsList gs (lvl - 1) h g hg.1
  | orGate gs, lvl, h => by
      by_cases hl : lvl ≤ 2
      · unfold HasProperBottomsAt at h
        rw [if_pos hl] at h
        have hdnf : isDNF (orGate gs) = true := h.1
        have hall : gs.all isAndOfInputsOnly = true := by
          simpa [isDNF] using hdnf
        have hid : simplifyConstantsList gs = gs :=
          simplifyConstantsList_and_inputs_id gs hall
        simp only [simplifyConstants]
        rw [hid]
        by_cases hf : gs.any isCanonicalTrue = true
        · rw [if_pos hf]; exact hasProperBottomsAt_andGate_nil lvl
        · rw [if_neg hf]
          have hfilt : gs.filter (fun g => !isCanonicalFalse g) = gs := by
            rw [List.all_eq_true] at hall
            apply List.filter_eq_self.mpr
            intro x hx
            have hxf : isCanonicalFalse x = false := by
              have hand := hall x hx
              cases x with
              | andGate l => simp [isCanonicalFalse]
              | inputGate a b => simp [isAndOfInputsOnly] at hand
              | constant a b => simp [isAndOfInputsOnly] at hand
              | notGate a => simp [isAndOfInputsOnly] at hand
              | orGate a => simp [isAndOfInputsOnly] at hand
            simp [hxf]
          rw [hfilt]
          unfold HasProperBottomsAt
          rw [if_pos hl]
          exact h
      · unfold HasProperBottomsAt at h
        rw [if_neg hl] at h
        simp only [simplifyConstants]
        by_cases hf : (simplifyConstantsList gs).any isCanonicalTrue = true
        · rw [if_pos hf]; exact hasProperBottomsAt_andGate_nil lvl
        · rw [if_neg hf]
          unfold HasProperBottomsAt
          rw [if_neg hl]
          intro g hg
          rw [List.mem_filter] at hg
          exact hasProperBottomsAt_simplifyConstantsList gs (lvl - 1) h g hg.1

theorem hasProperBottomsAt_simplifyConstantsList :
    ∀ (gs : List UnboundedFanInFormula) (lvl : Nat),
      (∀ g ∈ gs, HasProperBottomsAt g lvl) →
      (∀ g ∈ simplifyConstantsList gs, HasProperBottomsAt g lvl)
  | [], lvl, _ => by intro g hg; simp [simplifyConstantsList] at hg
  | g₀ :: gs, lvl, h => by
      intro g hg
      simp only [simplifyConstantsList, List.mem_cons] at hg
      rcases hg with he | hmem
      · rw [he]
        exact hasProperBottomsAt_simplifyConstants g₀ lvl (h g₀ (by simp))
      · exact hasProperBottomsAt_simplifyConstantsList gs lvl
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) g hmem

end

/- Filtering a list never increases the summed value of a `Nat`-valued map. -/
lemma sum_map_filter_le {α : Type*} (p : α → Bool) (fn : α → Nat) :
    ∀ (l : List α), ((l.filter p).map fn).sum ≤ (l.map fn).sum
  | [] => by simp
  | x :: xs => by
      have ih := sum_map_filter_le p fn xs
      rw [List.filter_cons]
      by_cases hx : p x = true
      · rw [if_pos hx]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [if_neg hx]
        simp only [List.map_cons, List.sum_cons]
        omega

/- Every input index surviving the absorption pass was already present. -/
mutual

theorem simplifyConstants_collect_subset :
    ∀ (f : UnboundedFanInFormula) (i : Nat),
      i ∈ ufiCollectInputIndices (simplifyConstants f) →
      i ∈ ufiCollectInputIndices f
  | inputGate x b, i, hi => hi
  | constant b m, i, hi => by
      simp only [simplifyConstants] at hi
      cases b <;> simp [ufiCollectInputIndices] at hi
  | notGate g, i, hi => by
      simp only [simplifyConstants, ufiCollectInputIndices] at hi ⊢
      exact simplifyConstants_collect_subset g i hi
  | andGate gs, i, hi => by
      simp only [simplifyConstants] at hi
      split at hi
      · simp [ufiCollectInputIndices] at hi
      · simp only [ufiCollectInputIndices] at hi ⊢
        rw [List.mem_flatMap] at hi
        obtain ⟨g, hg, hig⟩ := hi
        have hgcs : g ∈ simplifyConstantsList gs := List.mem_of_mem_filter hg
        apply simplifyConstantsList_collect_subset gs i
        rw [List.mem_flatMap]
        exact ⟨g, hgcs, hig⟩
  | orGate gs, i, hi => by
      simp only [simplifyConstants] at hi
      split at hi
      · simp [ufiCollectInputIndices] at hi
      · simp only [ufiCollectInputIndices] at hi ⊢
        rw [List.mem_flatMap] at hi
        obtain ⟨g, hg, hig⟩ := hi
        have hgcs : g ∈ simplifyConstantsList gs := List.mem_of_mem_filter hg
        apply simplifyConstantsList_collect_subset gs i
        rw [List.mem_flatMap]
        exact ⟨g, hgcs, hig⟩

theorem simplifyConstantsList_collect_subset :
    ∀ (gs : List UnboundedFanInFormula) (i : Nat),
      i ∈ (simplifyConstantsList gs).flatMap ufiCollectInputIndices →
      i ∈ gs.flatMap ufiCollectInputIndices
  | [], i, hi => by
      simp [simplifyConstantsList] at hi
  | g₀ :: gs, i, hi => by
      simp only [simplifyConstantsList, List.flatMap_cons, List.mem_append] at hi ⊢
      rcases hi with h | h
      · exact Or.inl (simplifyConstants_collect_subset g₀ i h)
      · exact Or.inr (simplifyConstantsList_collect_subset gs i h)

end

/- If every element of a `Nat` list is `≤ b`, so is its maximum. -/
lemma foldr_max_le_of_all_le {l : List Nat} {b : Nat}
    (h : ∀ i ∈ l, i ≤ b) : (List.foldr max 0) l ≤ b := by
  induction l with
  | nil => simp [List.foldr_nil]
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact max_le (h x (by simp)) (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

/- The absorption pass does not raise the largest input index bound. -/
lemma simplifyConstants_ufiLargestInput_lt {f : UnboundedFanInFormula} {m : Nat}
    (h : ufiLargestInput f < m) : ufiLargestInput (simplifyConstants f) < m := by
  unfold ufiLargestInput at h ⊢
  have hle : (List.foldr max 0) (ufiCollectInputIndices (simplifyConstants f))
      ≤ (List.foldr max 0) (ufiCollectInputIndices f) := by
    apply foldr_max_le_of_all_le
    intro i hi
    exact mem_le_foldr_max (simplifyConstants_collect_subset f i hi)
  omega

/- The absorption pass never increases the circuit size (folding only
    drops or shrinks children; a `constant` and an empty gate both have
    circuit size `1`). -/
mutual

theorem simplifyConstants_ufiFormulaCircuitSize_le :
    ∀ (f : UnboundedFanInFormula),
      ufiFormulaCircuitSize (simplifyConstants f) ≤ ufiFormulaCircuitSize f
  | inputGate x b => by simp [simplifyConstants]
  | constant b m => by
      simp only [simplifyConstants]
      cases b <;> simp [ufiFormulaCircuitSize]
  | notGate g => by
      simp only [simplifyConstants, ufiFormulaCircuitSize]
      have := simplifyConstants_ufiFormulaCircuitSize_le g; omega
  | andGate gs => by
      simp only [simplifyConstants]
      split
      · simp only [ufiFormulaCircuitSize, List.map_nil, List.sum_nil]; omega
      · simp only [ufiFormulaCircuitSize, Nat.add_comm]
        have h₁ := sum_map_filter_le (fun g => !isCanonicalTrue g) ufiFormulaCircuitSize
          (simplifyConstantsList gs)
        have h₂ := simplifyConstantsList_ufiFormulaCircuitSize_sum_le gs
        omega
  | orGate gs => by
      simp only [simplifyConstants]
      split
      · simp only [ufiFormulaCircuitSize, List.map_nil, List.sum_nil]; omega
      · simp only [ufiFormulaCircuitSize, Nat.add_comm]
        have h₁ := sum_map_filter_le (fun g => !isCanonicalFalse g) ufiFormulaCircuitSize
          (simplifyConstantsList gs)
        have h₂ := simplifyConstantsList_ufiFormulaCircuitSize_sum_le gs
        omega

theorem simplifyConstantsList_ufiFormulaCircuitSize_sum_le :
    ∀ (gs : List UnboundedFanInFormula),
      ((simplifyConstantsList gs).map ufiFormulaCircuitSize).sum
        ≤ (gs.map ufiFormulaCircuitSize).sum
  | [] => by simp [simplifyConstantsList]
  | g₀ :: gs => by
      simp only [simplifyConstantsList, List.map_cons, List.sum_cons]
      have h₁ := simplifyConstants_ufiFormulaCircuitSize_le g₀
      have h₂ := simplifyConstantsList_ufiFormulaCircuitSize_sum_le gs
      omega

end

/- constant absorption does not increase the number of gates still visible to
   the switching process.  Below-level gates are deliberately opaque to this
   measure, exactly as in `switchingGateBudget`. -/
mutual

theorem simplifyConstants_switchingGateBudget_le :
    ∀ (lvl : Nat) (f : UnboundedFanInFormula),
      switchingGateBudget lvl (simplifyConstants f) ≤ switchingGateBudget lvl f
  | _, inputGate x b => by simp [simplifyConstants, switchingGateBudget]
  | _, constant b m => by
      cases b <;> simp [simplifyConstants, switchingGateBudget]
  | lvl, notGate g => by
      simp only [simplifyConstants, switchingGateBudget]
      exact Nat.add_le_add_right (simplifyConstants_switchingGateBudget_le lvl g) 1
  | lvl, andGate [] => by
      simp [simplifyConstants, simplifyConstantsList, switchingGateBudget]
  | lvl, andGate (g :: gs) => by
      simp only [simplifyConstants]
      split
      · simp [switchingGateBudget]
      · by_cases hl : lvl ≤ 2
        · cases hf : (simplifyConstantsList (g :: gs)).filter (fun x => !isCanonicalTrue x) with
          | nil => simp [switchingGateBudget]
          | cons x xs => simp [switchingGateBudget, hl]
        · cases hf : (simplifyConstantsList (g :: gs)).filter (fun x => !isCanonicalTrue x) with
          | nil => simp [switchingGateBudget]
          | cons x xs =>
              simp only [switchingGateBudget, if_neg hl, List.map_cons, List.sum_cons]
              apply Nat.add_le_add_right
              have hfilter := sum_map_filter_le (fun x => !isCanonicalTrue x)
                (switchingGateBudget (lvl - 1)) (simplifyConstantsList (g :: gs))
              rw [hf] at hfilter
              exact le_trans hfilter
                (simplifyConstantsList_switchingGateBudget_sum_le (lvl - 1) (g :: gs))
  | lvl, orGate [] => by
      simp [simplifyConstants, simplifyConstantsList, switchingGateBudget]
  | lvl, orGate (g :: gs) => by
      simp only [simplifyConstants]
      split
      · simp [switchingGateBudget]
      · by_cases hl : lvl ≤ 2
        · cases hf : (simplifyConstantsList (g :: gs)).filter (fun x => !isCanonicalFalse x) with
          | nil => simp [switchingGateBudget]
          | cons x xs => simp [switchingGateBudget, hl]
        · cases hf : (simplifyConstantsList (g :: gs)).filter (fun x => !isCanonicalFalse x) with
          | nil => simp [switchingGateBudget]
          | cons x xs =>
              simp only [switchingGateBudget, if_neg hl, List.map_cons, List.sum_cons]
              apply Nat.add_le_add_right
              have hfilter := sum_map_filter_le (fun x => !isCanonicalFalse x)
                (switchingGateBudget (lvl - 1)) (simplifyConstantsList (g :: gs))
              rw [hf] at hfilter
              exact le_trans hfilter
                (simplifyConstantsList_switchingGateBudget_sum_le (lvl - 1) (g :: gs))

theorem simplifyConstantsList_switchingGateBudget_sum_le :
    ∀ (lvl : Nat) (gs : List UnboundedFanInFormula),
      ((simplifyConstantsList gs).map (switchingGateBudget lvl)).sum ≤
        (gs.map (switchingGateBudget lvl)).sum
  | _, [] => by simp [simplifyConstantsList]
  | lvl, g :: gs => by
      simp only [simplifyConstantsList, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (simplifyConstants_switchingGateBudget_le lvl g)
        (simplifyConstantsList_switchingGateBudget_sum_le lvl gs)

end

/- A formula with no `notGate` anywhere.  Both `substFlatten` outputs and
    any `IsAlternatingAndLeveledAt` circuit satisfy this, and it is exactly
    the hypothesis under which the absorption pass does not increase depth. -/
def IsNotGateFree : UnboundedFanInFormula → Prop
  | inputGate _ _    => True
  | constant _ _ => True
  | notGate _    => False
  | andGate gs   => ∀ x ∈ gs, IsNotGateFree x
  | orGate gs    => ∀ x ∈ gs, IsNotGateFree x

/- Disjunctive depth invariant for the absorption pass.  For a `notGate`-free
    formula, `simplifyConstants` either collapses to an empty gate (depth `1`)
    or does not increase depth.  Surviving children of a gate are provably not
    empty gates (the filter removes `isCanonicalTrue` and the else-branch excludes
    `isCanonicalFalse`), so they fall in the depth-`≤` case. -/
mutual

theorem simplifyConstants_eq_empty_or_depth_le :
    ∀ (f : UnboundedFanInFormula), IsNotGateFree f →
      (simplifyConstants f = andGate [] ∨ simplifyConstants f = orGate []) ∨
      ufiFormulaDepth (simplifyConstants f) ≤ ufiFormulaDepth f
  | inputGate x b, _ => Or.inr (by simp [simplifyConstants])
  | constant b m, _ => by
      simp only [simplifyConstants]
      cases b
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)
  | notGate g, hnn => by simp only [IsNotGateFree] at hnn
  | andGate gs, hnn => by
      simp only [IsNotGateFree] at hnn
      simp only [simplifyConstants]
      split
      · exact Or.inl (Or.inr rfl)
      · rename_i hbranch
        refine Or.inr ?_
        simp only [ufiFormulaDepth]
        have hmono :
            (List.foldr max 0) (((simplifyConstantsList gs).filter (fun g => !isCanonicalTrue g)).map
                ufiFormulaDepth)
              ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) := by
          apply foldr_max_le_of_all_le
          intro dpt hd
          rw [List.mem_map] at hd
          obtain ⟨h, hhfilter, rfl⟩ := hd
          have hmemcs : h ∈ simplifyConstantsList gs := List.mem_of_mem_filter hhfilter
          have hnot_true : isCanonicalTrue h = false := by
            simpa using List.of_mem_filter hhfilter
          have hnot_false : isCanonicalFalse h = false := by
            rcases Bool.eq_false_or_eq_true (isCanonicalFalse h) with h_f | h_f
            · exact absurd (List.any_eq_true.mpr ⟨h, hmemcs, h_f⟩) hbranch
            · exact h_f
          have hcomp := simplifyConstantsList_eq_empty_or_depth_le gs hnn h hmemcs
          rcases hcomp with hempty | hle
          · exfalso
            rcases hempty with he | he
            · rw [he] at hnot_true; simp [isCanonicalTrue] at hnot_true
            · rw [he] at hnot_false; simp [isCanonicalFalse] at hnot_false
          · exact hle
        omega
  | orGate gs, hnn => by
      simp only [IsNotGateFree] at hnn
      simp only [simplifyConstants]
      split
      · exact Or.inl (Or.inl rfl)
      · rename_i hbranch
        refine Or.inr ?_
        simp only [ufiFormulaDepth]
        have hmono :
            (List.foldr max 0) (((simplifyConstantsList gs).filter (fun g => !isCanonicalFalse g)).map
                ufiFormulaDepth)
              ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) := by
          apply foldr_max_le_of_all_le
          intro dpt hd
          rw [List.mem_map] at hd
          obtain ⟨h, hhfilter, rfl⟩ := hd
          have hmemcs : h ∈ simplifyConstantsList gs := List.mem_of_mem_filter hhfilter
          have hnot_false : isCanonicalFalse h = false := by
            simpa using List.of_mem_filter hhfilter
          have hnot_true : isCanonicalTrue h = false := by
            rcases Bool.eq_false_or_eq_true (isCanonicalTrue h) with h_t | h_t
            · exact absurd (List.any_eq_true.mpr ⟨h, hmemcs, h_t⟩) hbranch
            · exact h_t
          have hcomp := simplifyConstantsList_eq_empty_or_depth_le gs hnn h hmemcs
          rcases hcomp with hempty | hle
          · exfalso
            rcases hempty with he | he
            · rw [he] at hnot_true; simp [isCanonicalTrue] at hnot_true
            · rw [he] at hnot_false; simp [isCanonicalFalse] at hnot_false
          · exact hle
        omega

theorem simplifyConstantsList_eq_empty_or_depth_le :
    ∀ (gs : List UnboundedFanInFormula), (∀ g ∈ gs, IsNotGateFree g) →
      ∀ h ∈ simplifyConstantsList gs,
        (h = andGate [] ∨ h = orGate []) ∨
        ufiFormulaDepth h ≤ (List.foldr max 0) (gs.map ufiFormulaDepth)
  | [], _, h, hmem => by simp [simplifyConstantsList] at hmem
  | g₀ :: gs, hnn, h, hmem => by
      simp only [simplifyConstantsList_eq_map, List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · have hd := simplifyConstants_eq_empty_or_depth_le g₀ (hnn g₀ (by simp))
        rcases hd with hempty | hle
        · exact Or.inl hempty
        · refine Or.inr ?_
          have hle₂ : ufiFormulaDepth g₀ ≤ (List.foldr max 0) ((g₀ :: gs).map ufiFormulaDepth) := by
            simp only [List.map_cons, List.foldr_cons]
            exact le_max_left _ _
          exact le_trans hle hle₂
      · have hd := simplifyConstantsList_eq_empty_or_depth_le gs
          (fun g hg => hnn g (List.mem_cons_of_mem _ hg)) h
          (by rw [simplifyConstantsList_eq_map]; exact hmem)
        rcases hd with hempty | hle
        · exact Or.inl hempty
        · refine Or.inr ?_
          have hle₂ : (List.foldr max 0) (gs.map ufiFormulaDepth)
              ≤ (List.foldr max 0) ((g₀ :: gs).map ufiFormulaDepth) := by
            simp only [List.map_cons, List.foldr_cons]
            exact le_max_right _ _
          exact le_trans hle hle₂

end

/- A formula has **no empty interior And/orGate**: every `andGate`/`orGate`
    node has a non-empty child list.  (`inputGate`/`constant` leaves and the
    recursion through `notGate` are unconstrained.)  This is the structural
    cleanliness invariant established by `simplifyConstants` away from the
    root: empty gates produced at non-root positions are absorbed by their
    parent (filtered out as `isCanonicalTrue`, or triggering the parent's collapse
    as `isCanonicalFalse`). -/
def HasNoEmptyAndOrGate : UnboundedFanInFormula → Prop
  | inputGate _ _    => True
  | constant _ _ => True
  | notGate g    => HasNoEmptyAndOrGate g
  | andGate gs   => gs ≠ [] ∧ ∀ g ∈ gs, HasNoEmptyAndOrGate g
  | orGate gs    => gs ≠ [] ∧ ∀ g ∈ gs, HasNoEmptyAndOrGate g

mutual

/-- The extracted skeleton contains exactly the still-active structural gates;
    its ordinary gate count is bounded by the switching budget of the source.
    `HasNoEmptyAndOrGate` excludes semantic-constant empty gates in interior positions. -/
theorem extractBottomLayer_skeleton_size_le_switchingGateBudget :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      HasNoEmptyAndOrGate f →
      ufiFormulaCircuitSize (extractBottomLayer lvl start f).2.1 ≤
        switchingGateBudget lvl f
  | _, _, inputGate _ _, _ => by simp [extractBottomLayer, ufiFormulaCircuitSize,
      switchingGateBudget]
  | _, _, constant _ _, _ => by simp [extractBottomLayer, ufiFormulaCircuitSize,
      switchingGateBudget]
  | _, _, notGate _, _ => by simp [extractBottomLayer, ufiFormulaCircuitSize,
      switchingGateBudget]
  | lvl, start, andGate gates, hne => by
      simp only [HasNoEmptyAndOrGate] at hne
      by_cases hl : lvl ≤ 2
      · simp [extractBottomLayer, ufiFormulaCircuitSize, hl]
      · have hgates : gates ≠ [] := (by simpa [HasNoEmptyAndOrGate] using hne.1)
        cases gates with
        | nil => exact absurd rfl hgates
        | cons g gs =>
            simp only [extractBottomLayer, if_neg hl, switchingGateBudget,
              ufiFormulaCircuitSize]
            apply Nat.add_le_add_right
            exact extractBottomLayerList_skeleton_size_le_switchingGateBudget (lvl - 1) start
              (g :: gs) (by simpa [HasNoEmptyAndOrGate] using hne.2)
  | lvl, start, orGate gates, hne => by
      simp only [HasNoEmptyAndOrGate] at hne
      by_cases hl : lvl ≤ 2
      · simp [extractBottomLayer, ufiFormulaCircuitSize, hl]
      · have hgates : gates ≠ [] := (by simpa [HasNoEmptyAndOrGate] using hne.1)
        cases gates with
        | nil => exact absurd rfl hgates
        | cons g gs =>
            simp only [extractBottomLayer, if_neg hl, switchingGateBudget,
              ufiFormulaCircuitSize]
            apply Nat.add_le_add_right
            exact extractBottomLayerList_skeleton_size_le_switchingGateBudget (lvl - 1) start
              (g :: gs) (by simpa [HasNoEmptyAndOrGate] using hne.2)

theorem extractBottomLayerList_skeleton_size_le_switchingGateBudget :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      (∀ g ∈ gates, HasNoEmptyAndOrGate g) →
      ((extractBottomLayerList lvl start gates).2.1.map
        ufiFormulaCircuitSize).sum ≤
        (gates.map (switchingGateBudget lvl)).sum
  | _, _, [], _ => by simp [extractBottomLayerList]
  | lvl, start, g :: gs, hne => by
      simp only [extractBottomLayerList, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (extractBottomLayer_skeleton_size_le_switchingGateBudget lvl start g
          (hne g (by simp)))
        (extractBottomLayerList_skeleton_size_le_switchingGateBudget lvl
          (extractBottomLayer lvl start g).2.2 gs
          (fun x hx => hne x (by simp [hx])))

end

/- **Empty-gate cleanup (the count-bound linchpin).**  For a `notGate`-free
    input, `simplifyConstants f` is either one of the canonical empty gates
    (a fully-collapsed root) or has no empty interior And/orGate at all.
    Surviving children of a non-collapsed gate are provably non-empty: the
    filter drops `isCanonicalTrue` (= `andGate []`) children and the else-branch
    excludes any `isCanonicalFalse` (= `orGate []`) child.  Mirrors
    `simplifyConstants_eq_empty_or_depth_le`. -/
mutual

theorem hasNoEmptyAndOrGate_simplifyConstants :
    ∀ (f : UnboundedFanInFormula), IsNotGateFree f →
      (simplifyConstants f = andGate [] ∨ simplifyConstants f = orGate []) ∨
      HasNoEmptyAndOrGate (simplifyConstants f)
  | inputGate x b, _ => Or.inr (by simp [simplifyConstants, HasNoEmptyAndOrGate])
  | constant b m, _ => by
      simp only [simplifyConstants]
      cases b
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)
  | notGate g, hnn => by simp only [IsNotGateFree] at hnn
  | andGate gs, hnn => by
      simp only [IsNotGateFree] at hnn
      simp only [simplifyConstants]
      split
      · exact Or.inl (Or.inr rfl)
      · rename_i hbranch
        by_cases hempty : (simplifyConstantsList gs).filter (fun g => !isCanonicalTrue g) = []
        · rw [hempty]; exact Or.inl (Or.inl rfl)
        · refine Or.inr ?_
          simp only [HasNoEmptyAndOrGate]
          refine ⟨hempty, ?_⟩
          intro h hhfilter
          have hmemcs : h ∈ simplifyConstantsList gs := List.mem_of_mem_filter hhfilter
          have hnot_true : isCanonicalTrue h = false := by
            simpa using List.of_mem_filter hhfilter
          have hnot_false : isCanonicalFalse h = false := by
            rcases Bool.eq_false_or_eq_true (isCanonicalFalse h) with h_f | h_f
            · exact absurd (List.any_eq_true.mpr ⟨h, hmemcs, h_f⟩) hbranch
            · exact h_f
          have hcomp := hasNoEmptyAndOrGate_simplifyConstantsList gs hnn h hmemcs
          rcases hcomp with hempty_g | hne
          · exfalso
            rcases hempty_g with he | he
            · rw [he] at hnot_true; simp [isCanonicalTrue] at hnot_true
            · rw [he] at hnot_false; simp [isCanonicalFalse] at hnot_false
          · exact hne
  | orGate gs, hnn => by
      simp only [IsNotGateFree] at hnn
      simp only [simplifyConstants]
      split
      · exact Or.inl (Or.inl rfl)
      · rename_i hbranch
        by_cases hempty : (simplifyConstantsList gs).filter (fun g => !isCanonicalFalse g) = []
        · rw [hempty]; exact Or.inl (Or.inr rfl)
        · refine Or.inr ?_
          simp only [HasNoEmptyAndOrGate]
          refine ⟨hempty, ?_⟩
          intro h hhfilter
          have hmemcs : h ∈ simplifyConstantsList gs := List.mem_of_mem_filter hhfilter
          have hnot_false : isCanonicalFalse h = false := by
            simpa using List.of_mem_filter hhfilter
          have hnot_true : isCanonicalTrue h = false := by
            rcases Bool.eq_false_or_eq_true (isCanonicalTrue h) with h_t | h_t
            · exact absurd (List.any_eq_true.mpr ⟨h, hmemcs, h_t⟩) hbranch
            · exact h_t
          have hcomp := hasNoEmptyAndOrGate_simplifyConstantsList gs hnn h hmemcs
          rcases hcomp with hempty_g | hne
          · exfalso
            rcases hempty_g with he | he
            · rw [he] at hnot_true; simp [isCanonicalTrue] at hnot_true
            · rw [he] at hnot_false; simp [isCanonicalFalse] at hnot_false
          · exact hne

theorem hasNoEmptyAndOrGate_simplifyConstantsList :
    ∀ (gs : List UnboundedFanInFormula), (∀ g ∈ gs, IsNotGateFree g) →
      ∀ h ∈ simplifyConstantsList gs,
        (h = andGate [] ∨ h = orGate []) ∨ HasNoEmptyAndOrGate h
  | [], _, h, hmem => by simp [simplifyConstantsList] at hmem
  | g₀ :: gs, hnn, h, hmem => by
      simp only [simplifyConstantsList_eq_map, List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hasNoEmptyAndOrGate_simplifyConstants g₀ (hnn g₀ (by simp))
      · exact hasNoEmptyAndOrGate_simplifyConstantsList gs
          (fun g hg => hnn g (List.mem_cons_of_mem _ hg)) h
          (by rw [simplifyConstantsList_eq_map]; exact hmem)

end

/- **Threadable cleanliness invariant.**  A formula is `IsCleanFormula` when it
    is either a fully-collapsed canonical empty gate (`andGate []`/`orGate []`)
    or has no empty interior And/orGate (`HasNoEmptyAndOrGate`).  This is exactly the
    output shape of `simplifyConstants` on a `notGate`-free input
    (`hasNoEmptyAndOrGate_simplifyConstants`), so it is preserved across switching
    rounds and can be carried as a hypothesis through the depth recursion. -/
def IsCleanFormula (g : UnboundedFanInFormula) : Prop :=
  (g = andGate [] ∨ g = orGate []) ∨ HasNoEmptyAndOrGate g

/- `simplifyConstants` always produces a `IsCleanFormula` from a `notGate`-free
    input. -/
theorem isCleanFormula_simplifyConstants (f : UnboundedFanInFormula) (hnn : IsNotGateFree f) :
    IsCleanFormula (simplifyConstants f) :=
  hasNoEmptyAndOrGate_simplifyConstants f hnn

/- A proper CNF (an `andGate` of `orGate`s of `inputGate`s) is `notGate`-free. -/
lemma isNotGateFree_of_isCNF {f : UnboundedFanInFormula} (h : isCNF f = true) : IsNotGateFree f := by
  cases f with
  | inputGate x b => simp only [IsNotGateFree]
  | constant b m => simp [isCNF] at h
  | notGate g => simp [isCNF] at h
  | andGate gs =>
      simp only [IsNotGateFree]
      intro x hx
      simp only [isCNF, List.all_eq_true] at h
      have hx' := h x hx
      cases x with
      | orGate ls =>
          simp only [IsNotGateFree]
          intro y hy
          simp only [isOrOfInputsOnly, List.all_eq_true] at hx'
          have hy' := hx' y hy
          cases y with
          | inputGate a c => simp only [IsNotGateFree]
          | constant a c => simp [isInput] at hy'
          | notGate g => simp [isInput] at hy'
          | andGate gz => simp [isInput] at hy'
          | orGate gz => simp [isInput] at hy'
      | inputGate a c => simp [isOrOfInputsOnly] at hx'
      | constant a c => simp [isOrOfInputsOnly] at hx'
      | notGate g => simp [isOrOfInputsOnly] at hx'
      | andGate gz => simp [isOrOfInputsOnly] at hx'
  | orGate gs => simp [isCNF] at h

/- A proper DNF (an `orGate` of `andGate`s of `inputGate`s) is `notGate`-free. -/
lemma isNotGateFree_of_isDNF {f : UnboundedFanInFormula} (h : isDNF f = true) : IsNotGateFree f := by
  cases f with
  | inputGate x b => simp only [IsNotGateFree]
  | constant b m => simp [isDNF] at h
  | notGate g => simp [isDNF] at h
  | orGate gs =>
      simp only [IsNotGateFree]
      intro x hx
      simp only [isDNF, List.all_eq_true] at h
      have hx' := h x hx
      cases x with
      | andGate ls =>
          simp only [IsNotGateFree]
          intro y hy
          simp only [isAndOfInputsOnly, List.all_eq_true] at hx'
          have hy' := hx' y hy
          cases y with
          | inputGate a c => simp only [IsNotGateFree]
          | constant a c => simp [isInput] at hy'
          | notGate g => simp [isInput] at hy'
          | andGate gz => simp [isInput] at hy'
          | orGate gz => simp [isInput] at hy'
      | inputGate a c => simp [isAndOfInputsOnly] at hx'
      | constant a c => simp [isAndOfInputsOnly] at hx'
      | notGate g => simp [isAndOfInputsOnly] at hx'
      | orGate gz => simp [isAndOfInputsOnly] at hx'
  | andGate gs => simp [isDNF] at h

/- The `extractBottomLayer` skeleton is always `notGate`-free: every
    non-And/Or formula (including any `notGate`) is replaced by an `inputGate`
    placeholder, and the surviving And/Or structure recurses. -/
mutual

theorem isNotGateFree_extractBottomLayer_skeleton :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      IsNotGateFree (extractBottomLayer lvl start f).2.1
  | _, _, .inputGate _ _ => by simp only [extractBottomLayer, IsNotGateFree]
  | _, _, .constant _ _ => by simp only [extractBottomLayer, IsNotGateFree]
  | _, _, .notGate _ => by simp only [extractBottomLayer, IsNotGateFree]
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp only [IsNotGateFree]
      · simp only
        unfold IsNotGateFree
        exact isNotGateFree_extractBottomLayerList_skeleton (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp only [IsNotGateFree]
      · simp only
        unfold IsNotGateFree
        exact isNotGateFree_extractBottomLayerList_skeleton (lvl - 1) start gates

theorem isNotGateFree_extractBottomLayerList_skeleton :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      ∀ x ∈ (extractBottomLayerList lvl start gs).2.1, IsNotGateFree x
  | _, _, [] => by unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · exact isNotGateFree_extractBottomLayer_skeleton lvl start g
      · exact isNotGateFree_extractBottomLayerList_skeleton lvl
          (extractBottomLayer lvl start g).2.2 gs x hx

end

/- A strictly-assigned-leveled formula has no `notGate` nodes (the
   `notGate` clause of `IsAlternatingAndLeveledAt` is `False`). -/
mutual

theorem isNotGateFree_of_strictly_leveled :
    ∀ (f : UnboundedFanInFormula) (n : Nat),
      IsAlternatingAndLeveledAt f n → IsNotGateFree f
  | .inputGate _ _, _, _ => by simp only [IsNotGateFree]
  | .constant _ _, _, _ => by simp only [IsNotGateFree]
  | .notGate _, _, h => by
      simp only [IsAlternatingAndLeveledAt] at h
  | .andGate gs, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
      simp only [IsNotGateFree]
      exact isNotGateFree_of_strictly_leveled_list gs (n - 1) h.2.2
  | .orGate gs, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
      simp only [IsNotGateFree]
      exact isNotGateFree_of_strictly_leveled_list gs (n - 1) h.2.2

theorem isNotGateFree_of_strictly_leveled_list :
    ∀ (gs : List UnboundedFanInFormula) (n : Nat),
      (∀ g ∈ gs, IsAlternatingAndLeveledAt g n) →
      ∀ x ∈ gs, IsNotGateFree x
  | [], _, _ => by simp
  | g :: gs, n, h => by
      intro x hx
      rcases List.mem_cons.mp hx with heq | hx
      · subst x
        exact isNotGateFree_of_strictly_leveled g n (h g (by simp))
      · exact isNotGateFree_of_strictly_leveled_list gs n
          (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) x hx

end

/- The extracted top skeleton is `constant`-free: every produced node is
   either an `andGate`/`orGate` (recursing on the surviving structure) or an
   `inputGate` placeholder.  No `constant` ever appears, unconditionally. -/
mutual

theorem isConstantFree_extractBottomLayer_skeleton :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      IsConstantFree (extractBottomLayer lvl start f).2.1
  | _, _, .inputGate _ _ => by simp only [extractBottomLayer, IsConstantFree]
  | _, _, .constant _ _ => by simp only [extractBottomLayer, IsConstantFree]
  | _, _, .notGate _ => by simp only [extractBottomLayer, IsConstantFree]
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp only [IsConstantFree]
      · simp only
        unfold IsConstantFree
        exact isConstantFree_extractBottomLayerList_skeleton (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp only [IsConstantFree]
      · simp only
        unfold IsConstantFree
        exact isConstantFree_extractBottomLayerList_skeleton (lvl - 1) start gates

theorem isConstantFree_extractBottomLayerList_skeleton :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      ∀ x ∈ (extractBottomLayerList lvl start gs).2.1, IsConstantFree x
  | _, _, [] => by unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · exact isConstantFree_extractBottomLayer_skeleton lvl start g
      · exact isConstantFree_extractBottomLayerList_skeleton lvl
          (extractBottomLayer lvl start g).2.2 gs x hx

end

/- `HasNoEmptyAndOrGate` is preserved by the top-skeleton extraction: above level 2
   each surviving And/orGate keeps a non-empty (length-preserved) child list,
   and bottoms become `inputGate` placeholders. -/
mutual

theorem hasNoEmptyAndOrGate_extractBottomLayer_skeleton :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      HasNoEmptyAndOrGate f → HasNoEmptyAndOrGate (extractBottomLayer lvl start f).2.1
  | _, _, .inputGate _ _ => by intro _; simp only [extractBottomLayer, HasNoEmptyAndOrGate]
  | _, _, .constant _ _ => by intro _; simp only [extractBottomLayer, HasNoEmptyAndOrGate]
  | _, _, .notGate _ => by intro _; simp only [extractBottomLayer, HasNoEmptyAndOrGate]
  | lvl, start, .andGate gates => by
      intro hne
      unfold extractBottomLayer
      split_ifs with h
      · simp only [HasNoEmptyAndOrGate]
      · simp only
        unfold HasNoEmptyAndOrGate at hne ⊢
        obtain ⟨hgne, hch⟩ := hne
        refine ⟨?_, hasNoEmptyAndOrGate_extractBottomLayerList_skeleton (lvl - 1) start gates hch⟩
        cases gates with
        | nil => exact absurd rfl hgne
        | cons g₀ gs₀ => unfold extractBottomLayerList; simp
  | lvl, start, .orGate gates => by
      intro hne
      unfold extractBottomLayer
      split_ifs with h
      · simp only [HasNoEmptyAndOrGate]
      · simp only
        unfold HasNoEmptyAndOrGate at hne ⊢
        obtain ⟨hgne, hch⟩ := hne
        refine ⟨?_, hasNoEmptyAndOrGate_extractBottomLayerList_skeleton (lvl - 1) start gates hch⟩
        cases gates with
        | nil => exact absurd rfl hgne
        | cons g₀ gs₀ => unfold extractBottomLayerList; simp

theorem hasNoEmptyAndOrGate_extractBottomLayerList_skeleton :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      (∀ g ∈ gs, HasNoEmptyAndOrGate g) →
      ∀ x ∈ (extractBottomLayerList lvl start gs).2.1, HasNoEmptyAndOrGate x
  | _, _, [], _ => by unfold extractBottomLayerList; simp
  | lvl, start, g :: gs, hch => by
      unfold extractBottomLayerList
      simp only [List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · exact hasNoEmptyAndOrGate_extractBottomLayer_skeleton lvl start g (hch g (List.mem_cons_self))
      · exact hasNoEmptyAndOrGate_extractBottomLayerList_skeleton lvl
          (extractBottomLayer lvl start g).2.2 gs
          (fun g' hg' => hch g' (List.mem_cons_of_mem _ hg')) x hx

end

/- `flattenAndChild`/`flattenOrChild` preserve `IsNotGateFree`: unwrapping a top
    gate keeps every produced child `notGate`-free. -/
lemma isNotGateFree_of_mem_flattenAndChild {y : UnboundedFanInFormula} (h : IsNotGateFree y) :
    ∀ x ∈ flattenAndChild y, IsNotGateFree x := by
  cases y with
  | inputGate i b =>
      intro x hx; simp only [flattenAndChild, List.mem_singleton] at hx; subst hx; exact h
  | constant b m =>
      intro x hx; simp only [flattenAndChild, List.mem_singleton] at hx; subst hx; exact h
  | notGate g => simp only [IsNotGateFree] at h
  | orGate gs =>
      intro x hx; simp only [flattenAndChild, List.mem_singleton] at hx; subst hx; exact h
  | andGate inner =>
      intro x hx
      simp only [flattenAndChild] at hx
      simp only [IsNotGateFree] at h
      exact h x hx

lemma isNotGateFree_of_mem_flattenOrChild {y : UnboundedFanInFormula} (h : IsNotGateFree y) :
    ∀ x ∈ flattenOrChild y, IsNotGateFree x := by
  cases y with
  | inputGate i b =>
      intro x hx; simp only [flattenOrChild, List.mem_singleton] at hx; subst hx; exact h
  | constant b m =>
      intro x hx; simp only [flattenOrChild, List.mem_singleton] at hx; subst hx; exact h
  | notGate g => simp only [IsNotGateFree] at h
  | andGate gs =>
      intro x hx; simp only [flattenOrChild, List.mem_singleton] at hx; subst hx; exact h
  | orGate inner =>
      intro x hx
      simp only [flattenOrChild] at hx
      simp only [IsNotGateFree] at h
      exact h x hx

/- `substFlatten` preserves `IsNotGateFree`: substituting `notGate`-free forms into a
    `notGate`-free skeleton (and flattening) yields a `notGate`-free formula.
    Used to discharge `IsNotGateFree circuit'_raw` for the absorption-pass depth bound. -/
lemma isNotGateFree_substFlatten (sub : Nat → UnboundedFanInFormula)
    (hsub : ∀ i, IsNotGateFree (sub i)) :
    ∀ (f : UnboundedFanInFormula), IsNotGateFree f → IsNotGateFree (substFlatten sub f) := by
  intro f
  induction f using UnboundedFanInFormula.induction with
  | input i b => intro _; simp only [substFlatten]; exact hsub i
  | const b m => intro _; simp only [substFlatten, IsNotGateFree]
  | notg g ih => intro h; simp only [IsNotGateFree] at h
  | andg gs ih =>
      intro h
      simp only [IsNotGateFree] at h
      rw [substFlatten_and]
      simp only [IsNotGateFree]
      intro x hx
      rw [List.mem_flatMap] at hx
      obtain ⟨gc, hgc, hxc⟩ := hx
      exact isNotGateFree_of_mem_flattenAndChild (ih gc hgc (h gc hgc)) x hxc
  | org gs ih =>
      intro h
      simp only [IsNotGateFree] at h
      rw [substFlatten_or]
      simp only [IsNotGateFree]
      intro x hx
      rw [List.mem_flatMap] at hx
      obtain ⟨gc, hgc, hxc⟩ := hx
      exact isNotGateFree_of_mem_flattenOrChild (ih gc hgc (h gc hgc)) x hxc

/- Shape lemmas: a nonempty `andGate`/`orGate` output of the absorption
    pass can only arise from an `andGate`/`orGate` input.  (Constants and
    annihilator collapses produce only *empty* gates.) -/
lemma exists_eq_andGate_of_simplifyConstants_eq_andGate {g : UnboundedFanInFormula}
    {ls : List UnboundedFanInFormula}
    (h : simplifyConstants g = andGate ls) (hne : ls ≠ []) :
    ∃ inner, g = andGate inner := by
  cases g with
  | inputGate x b => simp only [simplifyConstants] at h; exact absurd h (by simp)
  | constant b m =>
      simp only [simplifyConstants] at h
      cases b
      · exact absurd h (by simp)
      · injection h with h'; exact absurd h'.symm hne
  | notGate g' => simp only [simplifyConstants] at h; exact absurd h (by simp)
  | andGate inner => exact ⟨inner, rfl⟩
  | orGate gs' =>
      simp only [simplifyConstants] at h
      split at h
      · injection h with h'; exact absurd h'.symm hne
      · exact absurd h (by simp)

lemma exists_eq_orGate_of_simplifyConstants_eq_orGate {g : UnboundedFanInFormula}
    {ls : List UnboundedFanInFormula}
    (h : simplifyConstants g = orGate ls) (hne : ls ≠ []) :
    ∃ inner, g = orGate inner := by
  cases g with
  | inputGate x b => simp only [simplifyConstants] at h; exact absurd h (by simp)
  | constant b m =>
      simp only [simplifyConstants] at h
      cases b
      · injection h with h'; exact absurd h'.symm hne
      · exact absurd h (by simp)
  | notGate g' => simp only [simplifyConstants] at h; exact absurd h (by simp)
  | andGate gs' =>
      simp only [simplifyConstants] at h
      split at h
      · injection h with h'; exact absurd h'.symm hne
      · exact absurd h (by simp)
  | orGate inner => exact ⟨inner, rfl⟩

/- The absorption pass preserves strict assigned-leveling.  In the fully
    simplified output an empty gate can appear only at the root; every
    interior parent either filters its identity children or collapses on an
    annihilator, so surviving children are never empty gates and the
    no-consecutive-same-type invariant is maintained. -/
mutual

theorem isAlternatingAndLeveledAt_simplifyConstants :
    ∀ (f : UnboundedFanInFormula) (n : Nat),
      IsAlternatingAndLeveledAt f n →
      IsAlternatingAndLeveledAt (simplifyConstants f) n
  | inputGate x b, n, _ => by simp [simplifyConstants, IsAlternatingAndLeveledAt]
  | constant b m, n, _ => by
      simp only [simplifyConstants]
      cases b <;> simp [IsAlternatingAndLeveledAt]
  | notGate g, n, h => by simp only [IsAlternatingAndLeveledAt] at h
  | andGate gs, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      simp only [simplifyConstants]
      split
      · simp [IsAlternatingAndLeveledAt]
      · rename_i hbranch
        simp only [IsAlternatingAndLeveledAt]
        refine ⟨?_, ?_, ?_⟩
        · intro h_child hh inner hcontra
          have hmemcs : h_child ∈ simplifyConstantsList gs := List.mem_of_mem_filter hh
          have hnot_true : isCanonicalTrue h_child = false := by simpa using List.of_mem_filter hh
          rw [simplifyConstantsList_eq_map, List.mem_map] at hmemcs
          obtain ⟨g₀, hg₀, hg₀eq⟩ := hmemcs
          have hinner_ne : inner ≠ [] := by
            rintro rfl; rw [hcontra] at hnot_true; simp [isCanonicalTrue] at hnot_true
          obtain ⟨inner', hg₀and⟩ :=
            exists_eq_andGate_of_simplifyConstants_eq_andGate (hg₀eq.trans hcontra) hinner_ne
          exact (h₁ g₀ hg₀ inner') hg₀and
        · intro h_child hh hand
          have hmemcs : h_child ∈ simplifyConstantsList gs := List.mem_of_mem_filter hh
          have hnot_true : isCanonicalTrue h_child = false := by simpa using List.of_mem_filter hh
          have hnot_false : isCanonicalFalse h_child = false := by
            rcases Bool.eq_false_or_eq_true (isCanonicalFalse h_child) with h_f | h_f
            · exact absurd (List.any_eq_true.mpr ⟨h_child, hmemcs, h_f⟩) hbranch
            · exact h_f
          rw [simplifyConstantsList_eq_map, List.mem_map] at hmemcs
          obtain ⟨g₀, hg₀, hg₀eq⟩ := hmemcs
          have hg₀andor : IsAndOr g₀ := by
            cases h_child with
            | inputGate x b => simp [IsAndOr] at hand
            | constant b m => simp [IsAndOr] at hand
            | notGate g' => simp [IsAndOr] at hand
            | andGate ls =>
                have hls_ne : ls ≠ [] := by
                  rintro rfl; simp [isCanonicalTrue] at hnot_true
                obtain ⟨inner', hg₀and⟩ := exists_eq_andGate_of_simplifyConstants_eq_andGate hg₀eq hls_ne
                rw [hg₀and]; simp [IsAndOr]
            | orGate ls =>
                have hls_ne : ls ≠ [] := by
                  rintro rfl; simp [isCanonicalFalse] at hnot_false
                obtain ⟨inner', hg₀or⟩ := exists_eq_orGate_of_simplifyConstants_eq_orGate hg₀eq hls_ne
                rw [hg₀or]; simp [IsAndOr]
          exact h₂ g₀ hg₀ hg₀andor
        · intro h_child hh
          have hmemcs : h_child ∈ simplifyConstantsList gs := List.mem_of_mem_filter hh
          exact isAlternatingAndLeveledAt_simplifyConstantsList gs (n - 1) h₃ h_child hmemcs
  | orGate gs, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      simp only [simplifyConstants]
      split
      · simp [IsAlternatingAndLeveledAt]
      · rename_i hbranch
        simp only [IsAlternatingAndLeveledAt]
        refine ⟨?_, ?_, ?_⟩
        · intro h_child hh inner hcontra
          have hmemcs : h_child ∈ simplifyConstantsList gs := List.mem_of_mem_filter hh
          have hnot_false : isCanonicalFalse h_child = false := by simpa using List.of_mem_filter hh
          rw [simplifyConstantsList_eq_map, List.mem_map] at hmemcs
          obtain ⟨g₀, hg₀, hg₀eq⟩ := hmemcs
          have hinner_ne : inner ≠ [] := by
            rintro rfl; rw [hcontra] at hnot_false; simp [isCanonicalFalse] at hnot_false
          obtain ⟨inner', hg₀or⟩ :=
            exists_eq_orGate_of_simplifyConstants_eq_orGate (hg₀eq.trans hcontra) hinner_ne
          exact (h₁ g₀ hg₀ inner') hg₀or
        · intro h_child hh hand
          have hmemcs : h_child ∈ simplifyConstantsList gs := List.mem_of_mem_filter hh
          have hnot_false : isCanonicalFalse h_child = false := by simpa using List.of_mem_filter hh
          have hnot_true : isCanonicalTrue h_child = false := by
            rcases Bool.eq_false_or_eq_true (isCanonicalTrue h_child) with h_t | h_t
            · exact absurd (List.any_eq_true.mpr ⟨h_child, hmemcs, h_t⟩) hbranch
            · exact h_t
          rw [simplifyConstantsList_eq_map, List.mem_map] at hmemcs
          obtain ⟨g₀, hg₀, hg₀eq⟩ := hmemcs
          have hg₀andor : IsAndOr g₀ := by
            cases h_child with
            | inputGate x b => simp [IsAndOr] at hand
            | constant b m => simp [IsAndOr] at hand
            | notGate g' => simp [IsAndOr] at hand
            | andGate ls =>
                have hls_ne : ls ≠ [] := by
                  rintro rfl; simp [isCanonicalTrue] at hnot_true
                obtain ⟨inner', hg₀and⟩ := exists_eq_andGate_of_simplifyConstants_eq_andGate hg₀eq hls_ne
                rw [hg₀and]; simp [IsAndOr]
            | orGate ls =>
                have hls_ne : ls ≠ [] := by
                  rintro rfl; simp [isCanonicalFalse] at hnot_false
                obtain ⟨inner', hg₀or⟩ := exists_eq_orGate_of_simplifyConstants_eq_orGate hg₀eq hls_ne
                rw [hg₀or]; simp [IsAndOr]
          exact h₂ g₀ hg₀ hg₀andor
        · intro h_child hh
          have hmemcs : h_child ∈ simplifyConstantsList gs := List.mem_of_mem_filter hh
          exact isAlternatingAndLeveledAt_simplifyConstantsList gs (n - 1) h₃ h_child hmemcs

theorem isAlternatingAndLeveledAt_simplifyConstantsList :
    ∀ (gs : List UnboundedFanInFormula) (n : Nat),
      (∀ g ∈ gs, IsAlternatingAndLeveledAt g n) →
      ∀ h ∈ simplifyConstantsList gs, IsAlternatingAndLeveledAt h n
  | [], n, _, h, hmem => by simp [simplifyConstantsList] at hmem
  | g₀ :: gs, n, hall, h, hmem => by
      rw [simplifyConstantsList_eq_map, List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact isAlternatingAndLeveledAt_simplifyConstants g₀ n (hall g₀ (by simp))
      · exact isAlternatingAndLeveledAt_simplifyConstantsList gs n
          (fun g hg => hall g (List.mem_cons_of_mem _ hg)) h
          (by rw [simplifyConstantsList_eq_map]; exact hmem)

end

/-! ### `HasProperBottomsWithConstants`: proper-leveled tolerating `constant` bottom children.

    After substituting *killed* leaves with `constant deadbit` into the
    extracted skeleton, the splice-base gate has the shape
    `andGate [orGate [inputs…], …, constant b m, …]` (constants land as
    direct gate children — `flattenAndChild (constant b m) = [constant b m]`).
    This is *not* `HasProperBottomsAt` (a `constant` child breaks `isCNF`).  But
    after `simplifyConstants` it *is*: a `constant false` collapses the AND to
    `orGate []` (proper, vacuous DNF); a `constant one` is dropped, leaving the
    proper clauses.  `HasProperBottomsWithConstants` is exactly the relaxed invariant that
    `substFlatten` produces and that `simplifyConstants` upgrades to
    `HasProperBottomsAt`. -/
def HasProperBottomsWithConstants : UnboundedFanInFormula → Nat → Prop
  | .inputGate _ _, _ => True
  | .constant _ _, _ => True
  | .notGate _, _ => False
  | .andGate gates, lvl =>
      if lvl ≤ 2 then
        ∀ g ∈ gates,
          (isOrOfInputsOnly g = true ∧
            (∀ c ∈ Circuits.CnfDnf.cnfClauses (.andGate [g]), c ≠ []) ∧
            (∀ c ∈ Circuits.CnfDnf.cnfClauses (.andGate [g]), (c.map Prod.fst).Nodup))
          ∨ (∃ b m, g = .constant b m)
      else
        ∀ g ∈ gates, HasProperBottomsWithConstants g (lvl - 1)
  | .orGate gates, lvl =>
      if lvl ≤ 2 then
        ∀ g ∈ gates,
          (isAndOfInputsOnly g = true ∧
            (∀ c ∈ Circuits.CnfDnf.dnfClauses (.orGate [g]), c ≠ []) ∧
            (∀ c ∈ Circuits.CnfDnf.dnfClauses (.orGate [g]), (c.map Prod.fst).Nodup))
          ∨ (∃ b m, g = .constant b m)
      else
        ∀ g ∈ gates, HasProperBottomsWithConstants g (lvl - 1)

/- Relating per-child clause data to whole-gate `cnfClauses`/`dnfClauses`:
    each clause of `andGate gs` is the clause of some child `andGate [g]`. -/
lemma exists_mem_of_mem_cnfClauses_andGate {gs : List UnboundedFanInFormula}
    {c : List (Nat × Bool)} (hc : c ∈ Circuits.CnfDnf.cnfClauses (andGate gs)) :
    ∃ g ∈ gs, c ∈ Circuits.CnfDnf.cnfClauses (andGate [g]) := by
  simp only [Circuits.CnfDnf.cnfClauses, List.mem_map] at hc
  obtain ⟨g, hg, hceq⟩ := hc
  refine ⟨g, hg, ?_⟩
  simp only [Circuits.CnfDnf.cnfClauses, List.map_cons, List.map_nil, List.mem_singleton]
  exact hceq.symm

lemma exists_mem_of_mem_dnfClauses_orGate {gs : List UnboundedFanInFormula}
    {c : List (Nat × Bool)} (hc : c ∈ Circuits.CnfDnf.dnfClauses (orGate gs)) :
    ∃ g ∈ gs, c ∈ Circuits.CnfDnf.dnfClauses (orGate [g]) := by
  simp only [Circuits.CnfDnf.dnfClauses, List.mem_map] at hc
  obtain ⟨g, hg, hceq⟩ := hc
  refine ⟨g, hg, ?_⟩
  simp only [Circuits.CnfDnf.dnfClauses, List.map_cons, List.map_nil, List.mem_singleton]
  exact hceq.symm

/- **Base-case absorption (CNF side).**  At the splice base, every child of an
    `andGate` is either a nonempty proper clause `orGate [inputs…]` or a
    `constant`.  `simplifyConstants` either collapses on a `constant false`
    (→ `orGate []`, proper) or drops every `constant one` (→ `andGate []`) and
    keeps the proper clauses, giving a proper CNF. -/
lemma hasProperBottomsAt_simplifyConstants_andGate (gates : List UnboundedFanInFormula)
    (hchild : ∀ g ∈ gates,
      (isOrOfInputsOnly g = true ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (andGate [g]), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (andGate [g]), (c.map Prod.fst).Nodup))
      ∨ (∃ b m, g = constant b m)) (lvl : Nat) (hl : lvl ≤ 2) :
    HasProperBottomsAt (simplifyConstants (andGate gates)) lvl := by
  simp only [simplifyConstants]
  by_cases hf : (simplifyConstantsList gates).any isCanonicalFalse = true
  · rw [if_pos hf]; exact hasProperBottomsAt_orGate_nil lvl
  · rw [if_neg hf]
    -- Every surviving filtered element is a proper clause carrying its conditions.
    have hsurv : ∀ g ∈ (simplifyConstantsList gates).filter (fun g => !isCanonicalTrue g),
        isOrOfInputsOnly g = true ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (andGate [g]), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (andGate [g]), (c.map Prod.fst).Nodup) := by
      intro g hg
      rw [List.mem_filter] at hg
      obtain ⟨hgmem, hgnt⟩ := hg
      rw [simplifyConstantsList_eq_map, List.mem_map] at hgmem
      obtain ⟨g₀, hg₀, hg₀eq⟩ := hgmem
      rcases hchild g₀ hg₀ with ⟨hor₀, hne₀, hnd₀⟩ | ⟨b, m, hbm⟩
      · rw [simplifyConstants_or_inputs_id hor₀] at hg₀eq
        subst hg₀eq; exact ⟨hor₀, hne₀, hnd₀⟩
      · exfalso
        subst hbm
        cases b with
        | false =>
            have hfalse : isCanonicalFalse g = true := by rw [← hg₀eq]; simp [simplifyConstants, isCanonicalFalse]
            refine hf (List.any_eq_true.mpr ⟨g, ?_, hfalse⟩)
            rw [simplifyConstantsList_eq_map, ← hg₀eq]
            exact List.mem_map_of_mem hg₀
        | true =>
            have hxt : isCanonicalTrue g = true := by rw [← hg₀eq]; simp [simplifyConstants, isCanonicalTrue]
            rw [hxt] at hgnt; simp at hgnt
    have hcnf : isCNF (andGate ((simplifyConstantsList gates).filter (fun g => !isCanonicalTrue g)))
        = true := by
      simp only [isCNF, List.all_eq_true]; exact fun x hx => (hsurv x hx).1
    unfold HasProperBottomsAt
    rw [if_pos hl]
    refine ⟨hcnf, ?_, ?_⟩
    · intro c hc
      obtain ⟨g, hg, hcg⟩ := exists_mem_of_mem_cnfClauses_andGate hc
      exact (hsurv g hg).2.1 c hcg
    · intro c hc
      obtain ⟨g, hg, hcg⟩ := exists_mem_of_mem_cnfClauses_andGate hc
      exact (hsurv g hg).2.2 c hcg

/- **Base-case absorption (DNF side).**  Dual of `hasProperBottomsAt_simplifyConstants_andGate`. -/
lemma hasProperBottomsAt_simplifyConstants_orGate (gates : List UnboundedFanInFormula)
    (hchild : ∀ g ∈ gates,
      (isAndOfInputsOnly g = true ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (orGate [g]), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (orGate [g]), (c.map Prod.fst).Nodup))
      ∨ (∃ b m, g = constant b m)) (lvl : Nat) (hl : lvl ≤ 2) :
    HasProperBottomsAt (simplifyConstants (orGate gates)) lvl := by
  simp only [simplifyConstants]
  by_cases hf : (simplifyConstantsList gates).any isCanonicalTrue = true
  · rw [if_pos hf]; exact hasProperBottomsAt_andGate_nil lvl
  · rw [if_neg hf]
    have hsurv : ∀ g ∈ (simplifyConstantsList gates).filter (fun g => !isCanonicalFalse g),
        isAndOfInputsOnly g = true ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (orGate [g]), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (orGate [g]), (c.map Prod.fst).Nodup) := by
      intro g hg
      rw [List.mem_filter] at hg
      obtain ⟨hgmem, hgnf⟩ := hg
      rw [simplifyConstantsList_eq_map, List.mem_map] at hgmem
      obtain ⟨g₀, hg₀, hg₀eq⟩ := hgmem
      rcases hchild g₀ hg₀ with ⟨hand₀, hne₀, hnd₀⟩ | ⟨b, m, hbm⟩
      · rw [simplifyConstants_and_inputs_id hand₀] at hg₀eq
        subst hg₀eq; exact ⟨hand₀, hne₀, hnd₀⟩
      · exfalso
        subst hbm
        cases b with
        | true =>
            have htrue : isCanonicalTrue g = true := by rw [← hg₀eq]; simp [simplifyConstants, isCanonicalTrue]
            refine hf (List.any_eq_true.mpr ⟨g, ?_, htrue⟩)
            rw [simplifyConstantsList_eq_map, ← hg₀eq]
            exact List.mem_map_of_mem hg₀
        | false =>
            have hxf : isCanonicalFalse g = true := by rw [← hg₀eq]; simp [simplifyConstants, isCanonicalFalse]
            rw [hxf] at hgnf; simp at hgnf
    have hdnf : isDNF (orGate ((simplifyConstantsList gates).filter (fun g => !isCanonicalFalse g)))
        = true := by
      simp only [isDNF, List.all_eq_true]; exact fun x hx => (hsurv x hx).1
    unfold HasProperBottomsAt
    rw [if_pos hl]
    refine ⟨hdnf, ?_, ?_⟩
    · intro c hc
      obtain ⟨g, hg, hcg⟩ := exists_mem_of_mem_dnfClauses_orGate hc
      exact (hsurv g hg).2.1 c hcg
    · intro c hc
      obtain ⟨g, hg, hcg⟩ := exists_mem_of_mem_dnfClauses_orGate hc
      exact (hsurv g hg).2.2 c hcg

/- **The absorption pass upgrades `HasProperBottomsWithConstants` to `HasProperBottomsAt`.**
    At the splice base the relaxed (constant-tolerant) invariant collapses to a
    genuine proper CNF/DNF; above the base, `simplifyConstants` recurses
    structurally and a `constant` child is always proper. -/
mutual

theorem hasProperBottomsAt_simplifyConstants_of_hasProperBottomsWithConstants :
    ∀ (f : UnboundedFanInFormula) (lvl : Nat),
      HasProperBottomsWithConstants f lvl → HasProperBottomsAt (simplifyConstants f) lvl
  | inputGate x b, lvl, _ => by simp only [simplifyConstants]; simp [HasProperBottomsAt]
  | constant b m, lvl, _ => by
      simp only [simplifyConstants]
      cases b
      · exact hasProperBottomsAt_orGate_nil lvl
      · exact hasProperBottomsAt_andGate_nil lvl
  | notGate g, lvl, h => by simp only [HasProperBottomsWithConstants] at h
  | andGate gs, lvl, h => by
      by_cases hl : lvl ≤ 2
      · simp only [HasProperBottomsWithConstants, if_pos hl] at h
        exact hasProperBottomsAt_simplifyConstants_andGate gs h lvl hl
      · simp only [HasProperBottomsWithConstants, if_neg hl] at h
        simp only [simplifyConstants]
        by_cases hf : (simplifyConstantsList gs).any isCanonicalFalse = true
        · rw [if_pos hf]; exact hasProperBottomsAt_orGate_nil lvl
        · rw [if_neg hf]
          unfold HasProperBottomsAt
          rw [if_neg hl]
          intro g hg
          rw [List.mem_filter] at hg
          exact hasProperBottomsAt_simplifyConstantsList_of_hasProperBottomsWithConstants gs (lvl - 1) h g hg.1
  | orGate gs, lvl, h => by
      by_cases hl : lvl ≤ 2
      · simp only [HasProperBottomsWithConstants, if_pos hl] at h
        exact hasProperBottomsAt_simplifyConstants_orGate gs h lvl hl
      · simp only [HasProperBottomsWithConstants, if_neg hl] at h
        simp only [simplifyConstants]
        by_cases hf : (simplifyConstantsList gs).any isCanonicalTrue = true
        · rw [if_pos hf]; exact hasProperBottomsAt_andGate_nil lvl
        · rw [if_neg hf]
          unfold HasProperBottomsAt
          rw [if_neg hl]
          intro g hg
          rw [List.mem_filter] at hg
          exact hasProperBottomsAt_simplifyConstantsList_of_hasProperBottomsWithConstants gs (lvl - 1) h g hg.1

theorem hasProperBottomsAt_simplifyConstantsList_of_hasProperBottomsWithConstants :
    ∀ (gs : List UnboundedFanInFormula) (lvl : Nat),
      (∀ g ∈ gs, HasProperBottomsWithConstants g lvl) →
      (∀ g ∈ simplifyConstantsList gs, HasProperBottomsAt g lvl)
  | [], lvl, _ => by intro g hg; simp [simplifyConstantsList] at hg
  | g₀ :: gs, lvl, h => by
      intro g hg
      simp only [simplifyConstantsList, List.mem_cons] at hg
      rcases hg with he | hmem
      · rw [he]; exact hasProperBottomsAt_simplifyConstants_of_hasProperBottomsWithConstants g₀ lvl (h g₀ (by simp))
      · exact hasProperBottomsAt_simplifyConstantsList_of_hasProperBottomsWithConstants gs lvl
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) g hmem

end

/-! ### constant-tolerant readiness and its `substFlatten` producer.

    At the splice base, each placeholder
    `inputGate i b` may substitute either to a matching-polarity proper CNF/DNF *or*
    to a `constant` (a killed leaf).  After flattening, the proper subs spread
    their clauses while constants land as direct gate children — exactly the
    `HasProperBottomsWithConstants` shape. -/
def IsProperSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula) :
    UnboundedFanInFormula → Nat → Prop
  | inputGate _ _, _ => True
  | constant _ _, _ => True
  | notGate _, _ => False
  | andGate gs, n =>
      if n ≤ 1 then
        ∀ g ∈ gs, ∃ i b, g = inputGate i b ∧
          ((isCNF (sub i) = true ∧
            (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), c ≠ []) ∧
            (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), (c.map Prod.fst).Nodup))
           ∨ (∃ bb m, sub i = constant bb m))
      else
        (∀ g ∈ gs, IsProperSubstitutionReadyWithConstants sub g (n - 1)) ∧
        (∀ gs', andGate gs' ∉ gs) ∧
        (∀ i b, inputGate i b ∈ gs →
          (∃ x d, sub i = inputGate x d) ∨ (∃ bb m, sub i = constant bb m))
  | orGate gs, n =>
      if n ≤ 1 then
        ∀ g ∈ gs, ∃ i b, g = inputGate i b ∧
          ((isDNF (sub i) = true ∧
            (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), c ≠ []) ∧
            (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), (c.map Prod.fst).Nodup))
           ∨ (∃ bb m, sub i = constant bb m))
      else
        (∀ g ∈ gs, IsProperSubstitutionReadyWithConstants sub g (n - 1)) ∧
        (∀ gs', orGate gs' ∉ gs) ∧
        (∀ i b, inputGate i b ∈ gs →
          (∃ x d, sub i = inputGate x d) ∨ (∃ bb m, sub i = constant bb m))

/- **constant-tolerant `IsProperSubstitutionReadyWithConstants → IsSubstitutionReady` downgrade.**
   The splice-base case tolerates
   a `constant` substitution (a killed leaf), which is non-`andGate`/`orGate`
   and strictly leveled at any level, hence lands in the second `IsSubstitutionReady`
   disjunct.  Lets the existing `isAlternatingAndLeveledAt_substFlatten` consume the
   relaxed readiness invariant. -/
lemma isSubstitutionReady_of_isProperSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula)
    (g : UnboundedFanInFormula) :
    ∀ n, IsProperSubstitutionReadyWithConstants sub g n → IsSubstitutionReady sub g n := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => intro n _; simp only [IsSubstitutionReady]
  | const b m => intro n _; simp only [IsSubstitutionReady]
  | notg g ih => intro n h; simp only [IsProperSubstitutionReadyWithConstants] at h
  | andg gs ih =>
    intro n hpsr
    by_cases hn : n ≤ 1
    · simp only [IsProperSubstitutionReadyWithConstants, if_pos hn] at hpsr
      simp only [IsSubstitutionReady]
      refine ⟨?_, ?_⟩
      · intro i b hmem
        obtain ⟨i', b', heq, hdisj⟩ := hpsr (inputGate i b) hmem
        injection heq with hii hbb
        subst hii
        rcases hdisj with ⟨hcnf, -, -⟩ | ⟨bb, m, hbm⟩
        · exact Or.inl ⟨exists_eq_andGate_of_isCNF (sub i) hcnf,
            isAlternatingAndLeveledAt_of_isCNF (sub i) hcnf (n + 1) (by omega)⟩
        · refine Or.inr ⟨fun cl => ?_, ?_⟩
          · rw [hbm]; simp
          · rw [hbm]; simp only [IsAlternatingAndLeveledAt]
      · intro g hg
        obtain ⟨i, b, rfl, -⟩ := hpsr g hg
        simp only [IsSubstitutionReady]
    · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hpsr
      obtain ⟨hrec, _, hleaf⟩ := hpsr
      simp only [IsSubstitutionReady]
      refine ⟨?_, ?_⟩
      · intro i b hmem
        refine Or.inr ?_
        rcases hleaf i b hmem with ⟨x, dd, hxd⟩ | ⟨bb, m, hbm⟩
        · refine ⟨fun cl => ?_, ?_⟩
          · rw [hxd]; simp
          · rw [hxd]; simp only [IsAlternatingAndLeveledAt]
        · refine ⟨fun cl => ?_, ?_⟩
          · rw [hbm]; simp
          · rw [hbm]; simp only [IsAlternatingAndLeveledAt]
      · intro g hg
        exact ih g hg (n - 1) (hrec g hg)
  | org gs ih =>
    intro n hpsr
    by_cases hn : n ≤ 1
    · simp only [IsProperSubstitutionReadyWithConstants, if_pos hn] at hpsr
      simp only [IsSubstitutionReady]
      refine ⟨?_, ?_⟩
      · intro i b hmem
        obtain ⟨i', b', heq, hdisj⟩ := hpsr (inputGate i b) hmem
        injection heq with hii hbb
        subst hii
        rcases hdisj with ⟨hdnf, -, -⟩ | ⟨bb, m, hbm⟩
        · exact Or.inl ⟨exists_eq_orGate_of_isDNF (sub i) hdnf,
            isAlternatingAndLeveledAt_of_isDNF (sub i) hdnf (n + 1) (by omega)⟩
        · refine Or.inr ⟨fun cl => ?_, ?_⟩
          · rw [hbm]; simp
          · rw [hbm]; simp only [IsAlternatingAndLeveledAt]
      · intro g hg
        obtain ⟨i, b, rfl, -⟩ := hpsr g hg
        simp only [IsSubstitutionReady]
    · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hpsr
      obtain ⟨hrec, _, hleaf⟩ := hpsr
      simp only [IsSubstitutionReady]
      refine ⟨?_, ?_⟩
      · intro i b hmem
        refine Or.inr ?_
        rcases hleaf i b hmem with ⟨x, dd, hxd⟩ | ⟨bb, m, hbm⟩
        · refine ⟨fun cl => ?_, ?_⟩
          · rw [hxd]; simp
          · rw [hxd]; simp only [IsAlternatingAndLeveledAt]
        · refine ⟨fun cl => ?_, ?_⟩
          · rw [hbm]; simp
          · rw [hbm]; simp only [IsAlternatingAndLeveledAt]
      · intro g hg
        exact ih g hg (n - 1) (hrec g hg)

/- Base producer (CNF side): every produced child of the splice-base `andGate`
    is either a proper input-OR clause (from a proper-CNF sub) or a `constant`. -/
lemma hasProperBottomsWithConstants_substFlatten_cnf_child (sub : Nat → UnboundedFanInFormula)
    (gs : List UnboundedFanInFormula)
    (hgs : ∀ g ∈ gs, ∃ i b, g = inputGate i b ∧
      ((isCNF (sub i) = true ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), (c.map Prod.fst).Nodup))
       ∨ (∃ bb m, sub i = constant bb m)))
    (c : UnboundedFanInFormula)
    (hc : c ∈ gs.flatMap (fun g => flattenAndChild (substFlatten sub g))) :
    (isOrOfInputsOnly c = true ∧
      (∀ cl ∈ Circuits.CnfDnf.cnfClauses (andGate [c]), cl ≠ []) ∧
      (∀ cl ∈ Circuits.CnfDnf.cnfClauses (andGate [c]), (cl.map Prod.fst).Nodup))
    ∨ (∃ b m, c = constant b m) := by
  rw [List.mem_flatMap] at hc
  obtain ⟨gc, hgc, hcc⟩ := hc
  obtain ⟨i, b, rfl, hsub⟩ := hgs gc hgc
  rw [substFlatten] at hcc
  rcases hsub with ⟨hcnf, hne, hnd⟩ | ⟨bb, m, hbm⟩
  · -- proper-CNF sub: c is one of its clauses (an input-OR), inheriting conditions
    left
    refine ⟨isCNF_proper_flatten (sub i) hcnf c hcc, ?_, ?_⟩
    · intro cl hcl
      -- cl is the single clause of andGate [c]; it is a clause of (sub i)
      obtain ⟨inner, hinner⟩ := exists_eq_andGate_of_isCNF (sub i) hcnf
      rw [hinner] at hcc
      simp only [flattenAndChild] at hcc
      have hcl_sub : cl ∈ Circuits.CnfDnf.cnfClauses (sub i) := by
        rw [hinner]
        simp only [Circuits.CnfDnf.cnfClauses, List.mem_map]
        simp only [Circuits.CnfDnf.cnfClauses, List.map_cons, List.map_nil,
          List.mem_singleton] at hcl
        exact ⟨c, hcc, hcl.symm⟩
      exact hne cl hcl_sub
    · intro cl hcl
      obtain ⟨inner, hinner⟩ := exists_eq_andGate_of_isCNF (sub i) hcnf
      rw [hinner] at hcc
      simp only [flattenAndChild] at hcc
      have hcl_sub : cl ∈ Circuits.CnfDnf.cnfClauses (sub i) := by
        rw [hinner]
        simp only [Circuits.CnfDnf.cnfClauses, List.mem_map]
        simp only [Circuits.CnfDnf.cnfClauses, List.map_cons, List.map_nil,
          List.mem_singleton] at hcl
        exact ⟨c, hcc, hcl.symm⟩
      exact hnd cl hcl_sub
  · -- constant sub: c is that constant
    right
    rw [hbm] at hcc
    simp only [flattenAndChild, List.mem_singleton] at hcc
    exact ⟨bb, m, hcc⟩

/- Base producer (DNF side): dual of `hasProperBottomsWithConstants_substFlatten_cnf_child`. -/
lemma hasProperBottomsWithConstants_substFlatten_dnf_child (sub : Nat → UnboundedFanInFormula)
    (gs : List UnboundedFanInFormula)
    (hgs : ∀ g ∈ gs, ∃ i b, g = inputGate i b ∧
      ((isDNF (sub i) = true ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), (c.map Prod.fst).Nodup))
       ∨ (∃ bb m, sub i = constant bb m)))
    (c : UnboundedFanInFormula)
    (hc : c ∈ gs.flatMap (fun g => flattenOrChild (substFlatten sub g))) :
    (isAndOfInputsOnly c = true ∧
      (∀ cl ∈ Circuits.CnfDnf.dnfClauses (orGate [c]), cl ≠ []) ∧
      (∀ cl ∈ Circuits.CnfDnf.dnfClauses (orGate [c]), (cl.map Prod.fst).Nodup))
    ∨ (∃ b m, c = constant b m) := by
  rw [List.mem_flatMap] at hc
  obtain ⟨gc, hgc, hcc⟩ := hc
  obtain ⟨i, b, rfl, hsub⟩ := hgs gc hgc
  rw [substFlatten] at hcc
  rcases hsub with ⟨hdnf, hne, hnd⟩ | ⟨bb, m, hbm⟩
  · left
    refine ⟨isDNF_proper_flatten (sub i) hdnf c hcc, ?_, ?_⟩
    · intro cl hcl
      obtain ⟨inner, hinner⟩ := exists_eq_orGate_of_isDNF (sub i) hdnf
      rw [hinner] at hcc
      simp only [flattenOrChild] at hcc
      have hcl_sub : cl ∈ Circuits.CnfDnf.dnfClauses (sub i) := by
        rw [hinner]
        simp only [Circuits.CnfDnf.dnfClauses, List.mem_map]
        simp only [Circuits.CnfDnf.dnfClauses, List.map_cons, List.map_nil,
          List.mem_singleton] at hcl
        exact ⟨c, hcc, hcl.symm⟩
      exact hne cl hcl_sub
    · intro cl hcl
      obtain ⟨inner, hinner⟩ := exists_eq_orGate_of_isDNF (sub i) hdnf
      rw [hinner] at hcc
      simp only [flattenOrChild] at hcc
      have hcl_sub : cl ∈ Circuits.CnfDnf.dnfClauses (sub i) := by
        rw [hinner]
        simp only [Circuits.CnfDnf.dnfClauses, List.mem_map]
        simp only [Circuits.CnfDnf.dnfClauses, List.map_cons, List.map_nil,
          List.mem_singleton] at hcl
        exact ⟨c, hcc, hcl.symm⟩
      exact hnd cl hcl_sub
  · right
    rw [hbm] at hcc
    simp only [flattenOrChild, List.mem_singleton] at hcc
    exact ⟨bb, m, hcc⟩

/- **constant-tolerant `substFlatten` producer.** Produces the relaxed
    `HasProperBottomsWithConstants` invariant from
    `IsProperSubstitutionReadyWithConstants`: at the splice base, killed leaves
    (substituted to `constant`) land as direct gate children and are tolerated;
    above the base the alternation argument is unchanged. -/
lemma hasProperBottomsWithConstants_substFlatten (sub : Nat → UnboundedFanInFormula)
    (g : UnboundedFanInFormula) :
    ∀ n, IsAndOr g → IsProperSubstitutionReadyWithConstants sub g n →
      HasProperBottomsWithConstants (substFlatten sub g) (n + 1) := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | const b m => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | notg g ih => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | andg gs ih =>
    intro n _ hsub
    by_cases hn : n ≤ 1
    · simp only [IsProperSubstitutionReadyWithConstants, if_pos hn] at hsub
      rw [substFlatten_and]
      simp only [HasProperBottomsWithConstants, if_pos (show n + 1 ≤ 2 by omega)]
      intro c hc
      exact hasProperBottomsWithConstants_substFlatten_cnf_child sub gs hsub c hc
    · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hsub
      obtain ⟨hrec, hnoand, hleaf⟩ := hsub
      rw [substFlatten_and]
      simp only [HasProperBottomsWithConstants, if_neg (show ¬ (n + 1 ≤ 2) by omega)]
      intro child hchild
      rw [Nat.add_sub_cancel]
      rw [List.mem_flatMap] at hchild
      obtain ⟨g', hg', hcc⟩ := hchild
      cases g' with
      | inputGate i b =>
        rcases hleaf i b hg' with ⟨x, d, hsi⟩ | ⟨bb, m, hsi⟩
        · have he : substFlatten sub (inputGate i b) = inputGate x d := by rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenAndChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomsWithConstants]
        · have he : substFlatten sub (inputGate i b) = constant bb m := by
            rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenAndChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomsWithConstants]
      | constant b m =>
        simp only [substFlatten, flattenAndChild, List.mem_singleton] at hcc
        subst hcc; simp only [HasProperBottomsWithConstants]
      | notGate g₀ => have hf := hrec (notGate g₀) hg'; simp only [IsProperSubstitutionReadyWithConstants] at hf
      | andGate gs' => exact absurd hg' (hnoand gs')
      | orGate gs' =>
        have hih := ih (orGate gs') hg' (n - 1) (by simp [IsAndOr]) (hrec _ hg')
        rw [show n - 1 + 1 = n by omega, substFlatten_or] at hih
        rw [substFlatten_or] at hcc
        simp only [flattenAndChild, List.mem_singleton] at hcc
        subst hcc
        exact hih
  | org gs ih =>
    intro n _ hsub
    by_cases hn : n ≤ 1
    · simp only [IsProperSubstitutionReadyWithConstants, if_pos hn] at hsub
      rw [substFlatten_or]
      simp only [HasProperBottomsWithConstants, if_pos (show n + 1 ≤ 2 by omega)]
      intro c hc
      exact hasProperBottomsWithConstants_substFlatten_dnf_child sub gs hsub c hc
    · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hsub
      obtain ⟨hrec, hnoor, hleaf⟩ := hsub
      rw [substFlatten_or]
      simp only [HasProperBottomsWithConstants, if_neg (show ¬ (n + 1 ≤ 2) by omega)]
      intro child hchild
      rw [Nat.add_sub_cancel]
      rw [List.mem_flatMap] at hchild
      obtain ⟨g', hg', hcc⟩ := hchild
      cases g' with
      | inputGate i b =>
        rcases hleaf i b hg' with ⟨x, d, hsi⟩ | ⟨bb, m, hsi⟩
        · have he : substFlatten sub (inputGate i b) = inputGate x d := by rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenOrChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomsWithConstants]
        · have he : substFlatten sub (inputGate i b) = constant bb m := by
            rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenOrChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomsWithConstants]
      | constant b m =>
        simp only [substFlatten, flattenOrChild, List.mem_singleton] at hcc
        subst hcc; simp only [HasProperBottomsWithConstants]
      | notGate g₀ => have hf := hrec (notGate g₀) hg'; simp only [IsProperSubstitutionReadyWithConstants] at hf
      | orGate gs' => exact absurd hg' (hnoor gs')
      | andGate gs' =>
        have hih := ih (andGate gs') hg' (n - 1) (by simp [IsAndOr]) (hrec _ hg')
        rw [show n - 1 + 1 = n by omega, substFlatten_and] at hih
        rw [substFlatten_and] at hcc
        simp only [flattenOrChild, List.mem_singleton] at hcc
        subst hcc
        exact hih

/- **Composed proper-leveling brick.**  Substituting (with `constant`-killed
    leaves) into an alternating skeleton and then running the absorption pass
    yields a genuine `HasProperBottomsAt` formula.  This is the proper-leveling
    output obligation of `exists_switching_depth_reduction` for `circuit' = simplifyConstants
    (substFlatten sub top)`. -/
lemma simplifyConstants_hasProperBottomsAt_substFlatten
    (sub : Nat → UnboundedFanInFormula) (g : UnboundedFanInFormula) (n : Nat)
    (h_and_or : IsAndOr g) (h_ready : IsProperSubstitutionReadyWithConstants sub g n) :
    HasProperBottomsAt (simplifyConstants (substFlatten sub g)) (n + 1) :=
  hasProperBottomsAt_simplifyConstants_of_hasProperBottomsWithConstants (substFlatten sub g) (n + 1)
    (hasProperBottomsWithConstants_substFlatten sub g n h_and_or h_ready)

/-! ### Extraction readiness and its bridge to
    `IsProperSubstitutionReadyWithConstants`.

    The splice-base placeholder condition accepts
    `IsSubstitutionProperFormOrConstant` (a matching-polarity proper CNF/DNF *or* a `constant`,
    modelling a restriction-killed bottom).  The above-splice `IsSubstitutionLeaf`
    condition already tolerates `constant`, so it is reused verbatim. -/
def IsSubstitutionProperFormOrConstant (sub : Nat → UnboundedFanInFormula)
    (needCnf : Bool) (i : Nat) : Prop :=
  IsSubstitutionProperForm sub needCnf i ∨ (∃ b m, sub i = constant b m)

mutual

def IsExtractionSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula) :
    Nat → Nat → UnboundedFanInFormula → Prop
  | lvl, start, .andGate gates =>
      if lvl ≤ 2 then True
      else if lvl ≤ 3 then IsExtractionBaseListSubstitutionReadyWithConstants sub true start gates
      else IsExtractionRecursiveListSubstitutionReadyWithConstants sub (lvl - 1) start gates
  | lvl, start, .orGate gates =>
      if lvl ≤ 2 then True
      else if lvl ≤ 3 then IsExtractionBaseListSubstitutionReadyWithConstants sub false start gates
      else IsExtractionRecursiveListSubstitutionReadyWithConstants sub (lvl - 1) start gates
  | _, _, _ => True

def IsExtractionBaseListSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula)
    (needCnf : Bool) : Nat → List UnboundedFanInFormula → Prop
  | _, [] => True
  | start, g :: gs =>
      IsSubstitutionProperFormOrConstant sub needCnf start ∧
      IsExtractionBaseListSubstitutionReadyWithConstants sub needCnf
        (extractBottomLayer 2 start g).2.2 gs

def IsExtractionRecursiveListSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula) :
    Nat → Nat → List UnboundedFanInFormula → Prop
  | _, _, [] => True
  | lvl, start, g :: gs =>
      (match g with
       | .andGate _ => IsExtractionSubstitutionReadyWithConstants sub lvl start g
       | .orGate _ => IsExtractionSubstitutionReadyWithConstants sub lvl start g
       | _ => IsSubstitutionLeaf sub start) ∧
      IsExtractionRecursiveListSubstitutionReadyWithConstants sub lvl
        (extractBottomLayer lvl start g).2.2 gs

end

/- **Base-list bridge.** Every extracted base placeholder has a proper-form
    or constant substitution. -/
lemma exists_input_isSubstitutionProperFormOrConstant_of_mem_extractBottomLayerList_base
    (sub : Nat → UnboundedFanInFormula) (needCnf : Bool) :
    ∀ (start : Nat) (gates : List UnboundedFanInFormula),
      IsExtractionBaseListSubstitutionReadyWithConstants sub needCnf start gates →
      ∀ g ∈ (extractBottomLayerList 2 start gates).2.1,
        ∃ i, g = inputGate i false ∧ IsSubstitutionProperFormOrConstant sub needCnf i
  | _, [], _ => by
      intro g hg
      unfold extractBottomLayerList at hg
      simp at hg
  | start, g₀ :: gs, hsr => by
      intro g hg
      unfold IsExtractionBaseListSubstitutionReadyWithConstants at hsr
      obtain ⟨hhead, htail⟩ := hsr
      unfold extractBottomLayerList at hg
      simp only [List.mem_cons] at hg
      rw [extractBottomLayer_two_top] at hg
      rw [extractBottomLayer_two_next] at hg htail
      rcases hg with hg | hg
      · exact ⟨start, hg, hhead⟩
      · exact exists_input_isSubstitutionProperFormOrConstant_of_mem_extractBottomLayerList_base sub needCnf (start + 1) gs htail g hg

/- **Main extraction-readiness bridge**, mutual with its recurse-list companion,
    producing `IsProperSubstitutionReadyWithConstants`. -/
mutual

theorem isProperSubstitutionReadyWithConstants_extractBottomLayer
    (sub : Nat → UnboundedFanInFormula) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      IsAlternatingAndLeveledAt f lvl →
      HasProperBottomsAt f lvl →
      IsExtractionSubstitutionReadyWithConstants sub lvl start f →
      IsProperSubstitutionReadyWithConstants sub (extractBottomLayer lvl start f).2.1 (lvl - 2)
  | lvl, start, .inputGate i b, _, _, _ => by
      have h : (extractBottomLayer lvl start (.inputGate i b)).2.1 = inputGate start false := rfl
      rw [h]; simp only [IsProperSubstitutionReadyWithConstants]
  | lvl, start, .constant b m, _, _, _ => by
      have h : (extractBottomLayer lvl start (.constant b m)).2.1 = inputGate start false := rfl
      rw [h]; simp only [IsProperSubstitutionReadyWithConstants]
  | lvl, start, .notGate g, _, hpl, _ => by
      simp only [HasProperBottomsAt] at hpl
  | lvl, start, .andGate gates, hsl, hpl, hsr => by
      by_cases hle : lvl ≤ 2
      · have h : (extractBottomLayer lvl start (.andGate gates)).2.1 = inputGate start false := by
          simp [extractBottomLayer, hle]
        rw [h]; simp only [IsProperSubstitutionReadyWithConstants]
      · have htop : (extractBottomLayer lvl start (.andGate gates)).2.1
            = .andGate (extractBottomLayerList (lvl - 1) start gates).2.1 := by
          simp [extractBottomLayer, hle]
        rw [htop]
        by_cases hle₃ : lvl ≤ 3
        · have hlvl₃ : lvl = 3 := by omega
          subst hlvl₃
          simp only [IsProperSubstitutionReadyWithConstants, Nat.le_refl, if_true]
          intro g hg
          have hsrb : IsExtractionBaseListSubstitutionReadyWithConstants sub true start gates := by
            unfold IsExtractionSubstitutionReadyWithConstants at hsr
            simpa using hsr
          obtain ⟨i, hgi, hspfc⟩ :=
            exists_input_isSubstitutionProperFormOrConstant_of_mem_extractBottomLayerList_base sub true start gates hsrb g hg
          refine ⟨i, false, hgi, ?_⟩
          rcases hspfc with hspf | hconst
          · unfold IsSubstitutionProperForm at hspf
            simp only [if_true] at hspf
            obtain ⟨hc, hne, hnd⟩ := hspf
            exact Or.inl ⟨hc, hne, hnd⟩
          · exact Or.inr hconst
        · have hlvl₄ : 4 ≤ lvl := by omega
          have hsl' := hsl
          simp only [IsAlternatingAndLeveledAt] at hsl'
          obtain ⟨_, _, hsl_ch⟩ := hsl'
          have hpl' := hpl
          unfold HasProperBottomsAt at hpl'
          simp only [if_neg hle] at hpl'
          have hsrr : IsExtractionRecursiveListSubstitutionReadyWithConstants sub (lvl - 1) start gates := by
            unfold IsExtractionSubstitutionReadyWithConstants at hsr
            simp only [if_neg hle, if_neg hle₃] at hsr
            exact hsr
          have hrec :=
            isProperSubstitutionReadyWithConstants_extractBottomLayerList sub (lvl - 1) start gates
              (by omega) hsl_ch hpl' hsrr
          obtain ⟨hrec_psr, hrec_leaf⟩ := hrec
          have hsl_top :=
            isAlternatingAndLeveledAt_extractBottomLayer_top lvl start (.andGate gates) hsl
          rw [htop] at hsl_top
          simp only [IsAlternatingAndLeveledAt] at hsl_top
          obtain ⟨hno, _, _⟩ := hsl_top
          simp only [IsProperSubstitutionReadyWithConstants, if_neg (show ¬ (lvl - 2 ≤ 1) by omega)]
          refine ⟨?_, ?_, ?_⟩
          · intro g hg
            have := hrec_psr g hg
            rwa [show (lvl - 1) - 2 = lvl - 2 - 1 by omega] at this
          · intro gs' hmem
            exact hno (.andGate gs') hmem gs' rfl
          · intro i b hmem
            have := hrec_leaf i b hmem
            unfold IsSubstitutionLeaf at this
            exact this
  | lvl, start, .orGate gates, hsl, hpl, hsr => by
      by_cases hle : lvl ≤ 2
      · have h : (extractBottomLayer lvl start (.orGate gates)).2.1 = inputGate start false := by
          simp [extractBottomLayer, hle]
        rw [h]; simp only [IsProperSubstitutionReadyWithConstants]
      · have htop : (extractBottomLayer lvl start (.orGate gates)).2.1
            = .orGate (extractBottomLayerList (lvl - 1) start gates).2.1 := by
          simp [extractBottomLayer, hle]
        rw [htop]
        by_cases hle₃ : lvl ≤ 3
        · have hlvl₃ : lvl = 3 := by omega
          subst hlvl₃
          simp only [IsProperSubstitutionReadyWithConstants, Nat.le_refl, if_true]
          intro g hg
          have hsrb : IsExtractionBaseListSubstitutionReadyWithConstants sub false start gates := by
            unfold IsExtractionSubstitutionReadyWithConstants at hsr
            simpa using hsr
          obtain ⟨i, hgi, hspfc⟩ :=
            exists_input_isSubstitutionProperFormOrConstant_of_mem_extractBottomLayerList_base sub false start gates hsrb g hg
          refine ⟨i, false, hgi, ?_⟩
          rcases hspfc with hspf | hconst
          · unfold IsSubstitutionProperForm at hspf
            simp only [Bool.false_eq_true, if_false] at hspf
            obtain ⟨hc, hne, hnd⟩ := hspf
            exact Or.inl ⟨hc, hne, hnd⟩
          · exact Or.inr hconst
        · have hlvl₄ : 4 ≤ lvl := by omega
          have hsl' := hsl
          simp only [IsAlternatingAndLeveledAt] at hsl'
          obtain ⟨_, _, hsl_ch⟩ := hsl'
          have hpl' := hpl
          unfold HasProperBottomsAt at hpl'
          simp only [if_neg hle] at hpl'
          have hsrr : IsExtractionRecursiveListSubstitutionReadyWithConstants sub (lvl - 1) start gates := by
            unfold IsExtractionSubstitutionReadyWithConstants at hsr
            simp only [if_neg hle, if_neg hle₃] at hsr
            exact hsr
          have hrec :=
            isProperSubstitutionReadyWithConstants_extractBottomLayerList sub (lvl - 1) start gates
              (by omega) hsl_ch hpl' hsrr
          obtain ⟨hrec_psr, hrec_leaf⟩ := hrec
          have hsl_top :=
            isAlternatingAndLeveledAt_extractBottomLayer_top lvl start (.orGate gates) hsl
          rw [htop] at hsl_top
          simp only [IsAlternatingAndLeveledAt] at hsl_top
          obtain ⟨hno, _, _⟩ := hsl_top
          simp only [IsProperSubstitutionReadyWithConstants, if_neg (show ¬ (lvl - 2 ≤ 1) by omega)]
          refine ⟨?_, ?_, ?_⟩
          · intro g hg
            have := hrec_psr g hg
            rwa [show (lvl - 1) - 2 = lvl - 2 - 1 by omega] at this
          · intro gs' hmem
            exact hno (.orGate gs') hmem gs' rfl
          · intro i b hmem
            have := hrec_leaf i b hmem
            unfold IsSubstitutionLeaf at this
            exact this

theorem isProperSubstitutionReadyWithConstants_extractBottomLayerList
    (sub : Nat → UnboundedFanInFormula) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      3 ≤ lvl →
      (∀ g ∈ gates, IsAlternatingAndLeveledAt g lvl) →
      (∀ g ∈ gates, HasProperBottomsAt g lvl) →
      IsExtractionRecursiveListSubstitutionReadyWithConstants sub lvl start gates →
      (∀ g' ∈ (extractBottomLayerList lvl start gates).2.1,
          IsProperSubstitutionReadyWithConstants sub g' (lvl - 2)) ∧
      (∀ i b, inputGate i b ∈ (extractBottomLayerList lvl start gates).2.1 →
          IsSubstitutionLeaf sub i)
  | lvl, start, [], _, _, _, _ => by
      constructor
      · intro g' hg'; unfold extractBottomLayerList at hg'; simp at hg'
      · intro i b hg'; unfold extractBottomLayerList at hg'; simp at hg'
  | lvl, start, g₀ :: gs, hlvl, hsl, hpl, hsr => by
      unfold IsExtractionRecursiveListSubstitutionReadyWithConstants at hsr
      obtain ⟨hhead, htail⟩ := hsr
      have htop : (extractBottomLayerList lvl start (g₀ :: gs)).2.1
          = (extractBottomLayer lvl start g₀).2.1 ::
            (extractBottomLayerList lvl (extractBottomLayer lvl start g₀).2.2 gs).2.1 := rfl
      have hsl₀ : IsAlternatingAndLeveledAt g₀ lvl :=
        hsl g₀ (by simp)
      have hpl₀ : HasProperBottomsAt g₀ lvl := hpl g₀ (by simp)
      have hnle : ¬ lvl ≤ 2 := by omega
      have h_head :
          IsProperSubstitutionReadyWithConstants sub (extractBottomLayer lvl start g₀).2.1 (lvl - 2) ∧
          (∀ i b, (extractBottomLayer lvl start g₀).2.1 = inputGate i b → IsSubstitutionLeaf sub i) := by
        cases g₀ with
        | inputGate x d =>
          refine ⟨?_, ?_⟩
          · have h : (extractBottomLayer lvl start (inputGate x d)).2.1 = inputGate start false := rfl
            rw [h]; simp only [IsProperSubstitutionReadyWithConstants]
          · intro i b heq
            have h : (extractBottomLayer lvl start (inputGate x d)).2.1 = inputGate start false := rfl
            rw [h] at heq; injection heq with hi _; subst hi
            exact hhead
        | constant x d =>
          refine ⟨?_, ?_⟩
          · have h : (extractBottomLayer lvl start (constant x d)).2.1 = inputGate start false := rfl
            rw [h]; simp only [IsProperSubstitutionReadyWithConstants]
          · intro i b heq
            have h : (extractBottomLayer lvl start (constant x d)).2.1 = inputGate start false := rfl
            rw [h] at heq; injection heq with hi _; subst hi
            exact hhead
        | notGate g => simp only [HasProperBottomsAt] at hpl₀
        | andGate gs' =>
          have hand : (extractBottomLayer lvl start (andGate gs')).2.1
              = andGate (extractBottomLayerList (lvl - 1) start gs').2.1 := by
            simp [extractBottomLayer, hnle]
          refine ⟨?_, ?_⟩
          · exact isProperSubstitutionReadyWithConstants_extractBottomLayer sub lvl start (andGate gs') hsl₀ hpl₀ hhead
          · intro i b heq; rw [hand] at heq; simp at heq
        | orGate gs' =>
          have hor : (extractBottomLayer lvl start (orGate gs')).2.1
              = orGate (extractBottomLayerList (lvl - 1) start gs').2.1 := by
            simp [extractBottomLayer, hnle]
          refine ⟨?_, ?_⟩
          · exact isProperSubstitutionReadyWithConstants_extractBottomLayer sub lvl start (orGate gs') hsl₀ hpl₀ hhead
          · intro i b heq; rw [hor] at heq; simp at heq
      have hsl_tail : ∀ g ∈ gs, IsAlternatingAndLeveledAt g lvl :=
        fun g hg => hsl g (by simp [hg])
      have hpl_tail : ∀ g ∈ gs, HasProperBottomsAt g lvl :=
        fun g hg => hpl g (by simp [hg])
      have hrec :=
        isProperSubstitutionReadyWithConstants_extractBottomLayerList sub lvl
          (extractBottomLayer lvl start g₀).2.2 gs hlvl hsl_tail hpl_tail htail
      obtain ⟨hrec_psr, hrec_leaf⟩ := hrec
      refine ⟨?_, ?_⟩
      · intro g' hg'
        rw [htop] at hg'
        rcases List.mem_cons.mp hg' with h | h
        · rw [h]; exact h_head.1
        · exact hrec_psr g' h
      · intro i b hib
        rw [htop] at hib
        rcases List.mem_cons.mp hib with h | h
        · exact h_head.2 i b h.symm
        · exact hrec_leaf i b h

end

/- **Leveling consumer.** Composes the
    `IsExtractionSubstitutionReadyWithConstants → IsProperSubstitutionReadyWithConstants` bridge with the producer +
    absorption brick `simplifyConstants_hasProperBottomsAt_substFlatten`,
    yielding `HasProperBottomsAt` of the simplified flattened skeleton. -/
lemma hasProperBottomsAt_simplifyConstants_substFlatten_extractBottomLayer
    (sub : Nat → UnboundedFanInFormula) (d : Nat) (hd : 2 ≤ d)
    (circuit : UnboundedFanInFormula)
    (h_and_or : IsAndOr circuit)
    (h_strict : IsAlternatingAndLeveledAt circuit (d + 1))
    (h_proper : HasProperBottomsAt circuit (d + 1))
    (h_ready_c : IsExtractionSubstitutionReadyWithConstants sub (d + 1) 0 circuit) :
    HasProperBottomsAt
      (simplifyConstants (substFlatten sub (extractBottomLayer (d + 1) 0 circuit).2.1)) d := by
  have hle : ¬ (d + 1) ≤ 2 := by omega
  have h_and_or_top : IsAndOr (extractBottomLayer (d + 1) 0 circuit).2.1 :=
    isAndOr_extractBottomLayer_top (d + 1) 0 circuit hle h_and_or
  have hpsr_c : IsProperSubstitutionReadyWithConstants sub (extractBottomLayer (d + 1) 0 circuit).2.1 ((d + 1) - 2) :=
    isProperSubstitutionReadyWithConstants_extractBottomLayer sub (d + 1) 0 circuit h_strict h_proper h_ready_c
  have hpl := simplifyConstants_hasProperBottomsAt_substFlatten sub
      (extractBottomLayer (d + 1) 0 circuit).2.1 ((d + 1) - 2) h_and_or_top hpsr_c
  rw [show (d + 1) - 2 + 1 = d by omega] at hpl
  exact hpl

end SimplifyConstants

end Circuits.HastadParity
