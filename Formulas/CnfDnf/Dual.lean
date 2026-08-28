/-
  De Morgan duality for unbounded-fan-in CNF and DNF formulas.

  This module is part of the Håstad parity lower-bound proof.
-/

import Formulas.CnfDnf.CnfDnfBasic
import Formulas.Eval
import Formulas.Properties

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open UnboundedFanInFormula

set_option linter.style.longLine false

/- Literal / clause / CNF De Morgan duals.  `negLit` flips an input's
   polarity; `dualClause` turns an OR-of-literals into an
   AND-of-negated-literals; `cnfDual` turns an AND-of-clauses into an
   OR-of-dual-clauses. -/
def negLit : UnboundedFanInFormula → UnboundedFanInFormula
  | .inputGate i b => .inputGate i (!b)
  | g => g

def dualClause : UnboundedFanInFormula → UnboundedFanInFormula
  | .orGate lits => .andGate (lits.map negLit)
  | g => g

def cnfDual : UnboundedFanInFormula → UnboundedFanInFormula
  | .andGate clauses => .orGate (clauses.map dualClause)
  | g => g

lemma isInput_negLit (l : UnboundedFanInFormula) :
    isInput (negLit l) = isInput l := by
  cases l <;> rfl

lemma eval_input_neg (i : Nat) (b : Bool) (xs : List Bool)
    (hi : i < xs.length) :
    ufiFormulaEval (UnboundedFanInFormula.inputGate i (!b)) xs
      = not (ufiFormulaEval (UnboundedFanInFormula.inputGate i b) xs) := by
  unfold ufiFormulaEval
  rw [List.getElem?_eq_getElem hi]
  cases b <;> cases xs[i] <;> rfl

lemma negLit_eval (l : UnboundedFanInFormula) (xs : List Bool)
    (hl : isInput l = true)
    (h_range : ∀ i ∈ ufiCollectInputIndices l, i < xs.length) :
    ufiFormulaEval (negLit l) xs = not (ufiFormulaEval l xs) := by
  cases l with
  | inputGate i b =>
      apply eval_input_neg i b xs
      exact h_range i (by simp [ufiCollectInputIndices])
  | constant b m => exact absurd hl (by simp [isInput])
  | notGate g => exact absurd hl (by simp [isInput])
  | andGate gs => exact absurd hl (by simp [isInput])
  | orGate gs => exact absurd hl (by simp [isInput])

lemma all_map_not_eq_one (cs : List Bool) :
    ((cs.map not).all (· == true)) = !(cs.any (· == true)) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    cases c with
    | false =>
      have heq₁ : (not false == true) = true := by decide
      have heq₂ : (false == true) = false := by decide
      simp only [List.map_cons, List.all_cons, List.any_cons, heq₁, heq₂, ih]
      simp
    | true =>
      have heq₁ : (not true == true) = false := by decide
      have heq₂ : (true == true) = true := by decide
      simp only [List.map_cons, List.all_cons, List.any_cons, heq₁, heq₂]
      simp

lemma any_map_not_eq_one (cs : List Bool) :
    ((cs.map not).any (· == true)) = !(cs.all (· == true)) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    cases c with
    | false =>
      have heq₁ : (not false == true) = true := by decide
      have heq₂ : (false == true) = false := by decide
      simp only [List.map_cons, List.any_cons, List.all_cons, heq₁, heq₂]
      simp
    | true =>
      have heq₁ : (not true == true) = false := by decide
      have heq₂ : (true == true) = true := by decide
      simp only [List.map_cons, List.any_cons, List.all_cons, heq₁, heq₂, ih]
      simp

lemma if_not_eq (p : Bool) :
    (if !p then true else false) = not (if p then true else false) := by
  cases p <;> rfl

lemma dualClause_eval (c : UnboundedFanInFormula) (xs : List Bool)
    (hc : isOrOfInputsOnly c = true)
    (h_range : ∀ i ∈ ufiCollectInputIndices c, i < xs.length) :
    ufiFormulaEval (dualClause c) xs = not (ufiFormulaEval c xs) := by
  cases c with
  | orGate lits =>
    simp only [isOrOfInputsOnly] at hc
    have hmap : ((lits.map negLit).map (fun t => ufiFormulaEval t xs))
        = (lits.map (fun t => ufiFormulaEval t xs)).map not := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro l hl
      have hli : isInput l = true := List.all_eq_true.mp hc l hl
      apply negLit_eval l xs hli
      intro i hi
      apply h_range i
      simp only [ufiCollectInputIndices]
      exact List.mem_flatMap.mpr ⟨l, hl, hi⟩
    change ufiFormulaEval (UnboundedFanInFormula.andGate (lits.map negLit)) xs
       = not (ufiFormulaEval (UnboundedFanInFormula.orGate lits) xs)
    rw [ufi_eval_andGate_eq_all, ufi_eval_orGate_eq_any, hmap, all_map_not_eq_one]
    exact if_not_eq _
  | inputGate i b => exact absurd hc (by simp [isOrOfInputsOnly])
  | constant b m => exact absurd hc (by simp [isOrOfInputsOnly])
  | notGate g => exact absurd hc (by simp [isOrOfInputsOnly])
  | andGate gs => exact absurd hc (by simp [isOrOfInputsOnly])

lemma cnfDual_eval (cnf : UnboundedFanInFormula) (xs : List Bool)
    (hcnf : isCNF cnf = true)
    (h_range : ∀ i ∈ ufiCollectInputIndices cnf, i < xs.length) :
    ufiFormulaEval (cnfDual cnf) xs = not (ufiFormulaEval cnf xs) := by
  cases cnf with
  | andGate clauses =>
    simp only [isCNF] at hcnf
    have hmap : ((clauses.map dualClause).map (fun t => ufiFormulaEval t xs))
        = (clauses.map (fun t => ufiFormulaEval t xs)).map not := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro c hc
      have hco : isOrOfInputsOnly c = true := List.all_eq_true.mp hcnf c hc
      apply dualClause_eval c xs hco
      intro i hi
      apply h_range i
      simp only [ufiCollectInputIndices]
      exact List.mem_flatMap.mpr ⟨c, hc, hi⟩
    change ufiFormulaEval
        (UnboundedFanInFormula.orGate (clauses.map dualClause)) xs
       = not (ufiFormulaEval (UnboundedFanInFormula.andGate clauses) xs)
    rw [ufi_eval_orGate_eq_any, ufi_eval_andGate_eq_all, hmap, any_map_not_eq_one]
    exact if_not_eq _
  | inputGate i b => exact absurd hcnf (by simp [isCNF])
  | constant b m => exact absurd hcnf (by simp [isCNF])
  | notGate g => exact absurd hcnf (by simp [isCNF])
  | orGate gs => exact absurd hcnf (by simp [isCNF])

lemma cnfDual_width (cnf : UnboundedFanInFormula) (hcnf : isCNF cnf = true) :
    dnfWidth (cnfDual cnf) = cnfWidth cnf := by
  cases cnf with
  | andGate clauses =>
    simp only [isCNF] at hcnf
    change dnfWidth (UnboundedFanInFormula.orGate (clauses.map dualClause))
         = cnfWidth (UnboundedFanInFormula.andGate clauses)
    simp only [dnfWidth, cnfWidth]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    have hco : isOrOfInputsOnly c = true := List.all_eq_true.mp hcnf c hc
    cases c with
    | orGate lits =>
      simp only [Function.comp_apply, dualClause, List.length_map]
    | inputGate i b => exact absurd hco (by simp [isOrOfInputsOnly])
    | constant b m => exact absurd hco (by simp [isOrOfInputsOnly])
    | notGate g => exact absurd hco (by simp [isOrOfInputsOnly])
    | andGate gs => exact absurd hco (by simp [isOrOfInputsOnly])
  | inputGate i b => exact absurd hcnf (by simp [isCNF])
  | constant b m => exact absurd hcnf (by simp [isCNF])
  | notGate g => exact absurd hcnf (by simp [isCNF])
  | orGate gs => exact absurd hcnf (by simp [isCNF])

lemma isDNF_cnfDual (cnf : UnboundedFanInFormula) (hcnf : isCNF cnf = true) :
    isDNF (cnfDual cnf) = true := by
  cases cnf with
  | andGate clauses =>
    simp only [isCNF] at hcnf
    change isDNF (UnboundedFanInFormula.orGate (clauses.map dualClause)) = true
    simp only [isDNF]
    apply List.all_eq_true.mpr
    intro dc hdc
    rw [List.mem_map] at hdc
    obtain ⟨c, hc, rfl⟩ := hdc
    have hco : isOrOfInputsOnly c = true := List.all_eq_true.mp hcnf c hc
    cases c with
    | orGate lits =>
      simp only [isOrOfInputsOnly] at hco
      change isAndOfInputsOnly
          (UnboundedFanInFormula.andGate (lits.map negLit)) = true
      simp only [isAndOfInputsOnly]
      apply List.all_eq_true.mpr
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [isInput_negLit]
      exact List.all_eq_true.mp hco y hy
    | inputGate i b => exact absurd hco (by simp [isOrOfInputsOnly])
    | constant b m => exact absurd hco (by simp [isOrOfInputsOnly])
    | notGate g => exact absurd hco (by simp [isOrOfInputsOnly])
    | andGate gs => exact absurd hco (by simp [isOrOfInputsOnly])
  | inputGate i b => exact absurd hcnf (by simp [isCNF])
  | constant b m => exact absurd hcnf (by simp [isCNF])
  | notGate g => exact absurd hcnf (by simp [isCNF])
  | orGate gs => exact absurd hcnf (by simp [isCNF])

lemma negLit_collect (l : UnboundedFanInFormula) :
    ufiCollectInputIndices (negLit l) = ufiCollectInputIndices l := by
  cases l <;> simp only [negLit, ufiCollectInputIndices]

lemma flatMap_map_negLit_collect (lits : List UnboundedFanInFormula) :
    (lits.map negLit).flatMap ufiCollectInputIndices
      = lits.flatMap ufiCollectInputIndices := by
  induction lits with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.flatMap_cons, negLit_collect hd, ih]

lemma dualClause_collect (c : UnboundedFanInFormula) :
    ufiCollectInputIndices (dualClause c) = ufiCollectInputIndices c := by
  cases c with
  | orGate lits =>
    simp only [dualClause, ufiCollectInputIndices]
    exact flatMap_map_negLit_collect lits
  | inputGate i b => rfl
  | constant b m => rfl
  | notGate g => rfl
  | andGate gs => rfl

lemma cnfDual_collect (cnf : UnboundedFanInFormula) :
    ufiCollectInputIndices (cnfDual cnf) = ufiCollectInputIndices cnf := by
  cases cnf with
  | andGate clauses =>
    simp only [cnfDual, ufiCollectInputIndices]
    induction clauses with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.flatMap_cons, dualClause_collect hd, ih]
  | inputGate i b => rfl
  | constant b m => rfl
  | notGate g => rfl
  | orGate gs => rfl

lemma cnfDual_ufiLargestInput (cnf : UnboundedFanInFormula) :
    ufiLargestInput (cnfDual cnf) = ufiLargestInput cnf := by
  unfold ufiLargestInput
  rw [cnfDual_collect]

lemma filterMap_negLit_eq (lits : List UnboundedFanInFormula)
    (h : lits.all isInput = true) :
    (lits.map negLit).filterMap
        (fun lit => match lit with
          | UnboundedFanInFormula.inputGate i b => some (i, b)
          | _ => none)
      = (lits.filterMap
          (fun lit => match lit with
            | UnboundedFanInFormula.inputGate i b => some (i, b)
            | _ => none)).map (fun p => (p.1, !p.2)) := by
  induction lits with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hhd, htl⟩ := h
    cases hd with
    | inputGate i b => simp [negLit, ih htl]
    | constant b m => exact absurd hhd (by simp [isInput])
    | notGate g => exact absurd hhd (by simp [isInput])
    | andGate gs => exact absurd hhd (by simp [isInput])
    | orGate gs => exact absurd hhd (by simp [isInput])

lemma cnfDual_clauses (cnf : UnboundedFanInFormula) (hcnf : isCNF cnf = true) :
    dnfClauses (cnfDual cnf)
      = (cnfClauses cnf).map (fun cc => cc.map (fun p => (p.1, !p.2))) := by
  cases cnf with
  | andGate clauses =>
    simp only [isCNF] at hcnf
    change dnfClauses (UnboundedFanInFormula.orGate (clauses.map dualClause))
         = (cnfClauses (UnboundedFanInFormula.andGate clauses)).map
             (fun cc => cc.map (fun p => (p.1, !p.2)))
    simp only [dnfClauses, cnfClauses, List.map_map]
    apply List.map_congr_left
    intro c hc
    have hco : isOrOfInputsOnly c = true := List.all_eq_true.mp hcnf c hc
    cases c with
    | orGate lits =>
      simp only [isOrOfInputsOnly] at hco
      exact filterMap_negLit_eq lits hco
    | inputGate i b => exact absurd hco (by simp [isOrOfInputsOnly])
    | constant b m => exact absurd hco (by simp [isOrOfInputsOnly])
    | notGate g => exact absurd hco (by simp [isOrOfInputsOnly])
    | andGate gs => exact absurd hco (by simp [isOrOfInputsOnly])
  | inputGate i b => exact absurd hcnf (by simp [isCNF])
  | constant b m => exact absurd hcnf (by simp [isCNF])
  | notGate g => exact absurd hcnf (by simp [isCNF])
  | orGate gs => exact absurd hcnf (by simp [isCNF])

/- ===================================================================
   DNF De Morgan dual and `decisionTreeToCNF`.

   `dnfDual` turns an OR-of-AND (DNF) into an AND-of-OR (CNF) computing
   the negation, mirroring `cnfDual`.  Composing it with the
   negated-tree DNF yields `decisionTreeToCNF`: the CNF that a
   shallow decision tree collapses to.  This is the "switch" direction
   (DNF→CNF) needed so a bottom DNF can merge with an AND layer above
   it, reducing depth by one.
   =================================================================== -/

def dualAndClause : UnboundedFanInFormula → UnboundedFanInFormula
  | .andGate lits => .orGate (lits.map negLit)
  | g => g

def dnfDual : UnboundedFanInFormula → UnboundedFanInFormula
  | .orGate clauses => .andGate (clauses.map dualAndClause)
  | g => g

lemma dualAndClause_eval (c : UnboundedFanInFormula) (xs : List Bool)
    (hc : isAndOfInputsOnly c = true)
    (h_range : ∀ i ∈ ufiCollectInputIndices c, i < xs.length) :
    ufiFormulaEval (dualAndClause c) xs = not (ufiFormulaEval c xs) := by
  cases c with
  | andGate lits =>
    simp only [isAndOfInputsOnly] at hc
    have hmap : ((lits.map negLit).map (fun t => ufiFormulaEval t xs))
        = (lits.map (fun t => ufiFormulaEval t xs)).map not := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro l hl
      have hli : isInput l = true := List.all_eq_true.mp hc l hl
      apply negLit_eval l xs hli
      intro i hi
      apply h_range i
      simp only [ufiCollectInputIndices]
      exact List.mem_flatMap.mpr ⟨l, hl, hi⟩
    change ufiFormulaEval (UnboundedFanInFormula.orGate (lits.map negLit)) xs
       = not (ufiFormulaEval (UnboundedFanInFormula.andGate lits) xs)
    rw [ufi_eval_orGate_eq_any, ufi_eval_andGate_eq_all, hmap, any_map_not_eq_one]
    exact if_not_eq _
  | inputGate i b => exact absurd hc (by simp [isAndOfInputsOnly])
  | constant b m => exact absurd hc (by simp [isAndOfInputsOnly])
  | notGate g => exact absurd hc (by simp [isAndOfInputsOnly])
  | orGate gs => exact absurd hc (by simp [isAndOfInputsOnly])

lemma dnfDual_eval (dnf : UnboundedFanInFormula) (xs : List Bool)
    (hdnf : isDNF dnf = true)
    (h_range : ∀ i ∈ ufiCollectInputIndices dnf, i < xs.length) :
    ufiFormulaEval (dnfDual dnf) xs = not (ufiFormulaEval dnf xs) := by
  cases dnf with
  | orGate clauses =>
    simp only [isDNF] at hdnf
    have hmap : ((clauses.map dualAndClause).map (fun t => ufiFormulaEval t xs))
        = (clauses.map (fun t => ufiFormulaEval t xs)).map not := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro c hc
      have hco : isAndOfInputsOnly c = true := List.all_eq_true.mp hdnf c hc
      apply dualAndClause_eval c xs hco
      intro i hi
      apply h_range i
      simp only [ufiCollectInputIndices]
      exact List.mem_flatMap.mpr ⟨c, hc, hi⟩
    change ufiFormulaEval
        (UnboundedFanInFormula.andGate (clauses.map dualAndClause)) xs
       = not (ufiFormulaEval (UnboundedFanInFormula.orGate clauses) xs)
    rw [ufi_eval_andGate_eq_all, ufi_eval_orGate_eq_any, hmap, all_map_not_eq_one]
    exact if_not_eq _
  | inputGate i b => exact absurd hdnf (by simp [isDNF])
  | constant b m => exact absurd hdnf (by simp [isDNF])
  | notGate g => exact absurd hdnf (by simp [isDNF])
  | andGate gs => exact absurd hdnf (by simp [isDNF])

lemma isCNF_dnfDual (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true) :
    isCNF (dnfDual dnf) = true := by
  cases dnf with
  | orGate clauses =>
    simp only [isDNF] at hdnf
    change isCNF (UnboundedFanInFormula.andGate (clauses.map dualAndClause)) = true
    simp only [isCNF]
    apply List.all_eq_true.mpr
    intro dc hdc
    rw [List.mem_map] at hdc
    obtain ⟨c, hc, rfl⟩ := hdc
    have hco : isAndOfInputsOnly c = true := List.all_eq_true.mp hdnf c hc
    cases c with
    | andGate lits =>
      simp only [isAndOfInputsOnly] at hco
      change isOrOfInputsOnly (UnboundedFanInFormula.orGate (lits.map negLit)) = true
      simp only [isOrOfInputsOnly]
      apply List.all_eq_true.mpr
      intro l hl
      rw [List.mem_map] at hl
      obtain ⟨l₀, hl₀, rfl⟩ := hl
      have hl0i : isInput l₀ = true := List.all_eq_true.mp hco l₀ hl₀
      rw [isInput_negLit]; exact hl0i
    | inputGate i b => exact absurd hco (by simp [isAndOfInputsOnly])
    | constant b m => exact absurd hco (by simp [isAndOfInputsOnly])
    | notGate g => exact absurd hco (by simp [isAndOfInputsOnly])
    | orGate gs => exact absurd hco (by simp [isAndOfInputsOnly])
  | inputGate i b => exact absurd hdnf (by simp [isDNF])
  | constant b m => exact absurd hdnf (by simp [isDNF])
  | notGate g => exact absurd hdnf (by simp [isDNF])
  | andGate gs => exact absurd hdnf (by simp [isDNF])

lemma dnfDual_width (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true) :
    cnfWidth (dnfDual dnf) = dnfWidth dnf := by
  cases dnf with
  | orGate clauses =>
    simp only [isDNF] at hdnf
    change cnfWidth (UnboundedFanInFormula.andGate (clauses.map dualAndClause))
         = dnfWidth (UnboundedFanInFormula.orGate clauses)
    simp only [cnfWidth, dnfWidth]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    have hco : isAndOfInputsOnly c = true := List.all_eq_true.mp hdnf c hc
    cases c with
    | andGate lits =>
      simp only [Function.comp_apply, dualAndClause, List.length_map]
    | inputGate i b => exact absurd hco (by simp [isAndOfInputsOnly])
    | constant b m => exact absurd hco (by simp [isAndOfInputsOnly])
    | notGate g => exact absurd hco (by simp [isAndOfInputsOnly])
    | orGate gs => exact absurd hco (by simp [isAndOfInputsOnly])
  | inputGate i b => exact absurd hdnf (by simp [isDNF])
  | constant b m => exact absurd hdnf (by simp [isDNF])
  | notGate g => exact absurd hdnf (by simp [isDNF])
  | andGate gs => exact absurd hdnf (by simp [isDNF])

lemma dualAndClause_collect (c : UnboundedFanInFormula) :
    ufiCollectInputIndices (dualAndClause c) = ufiCollectInputIndices c := by
  cases c with
  | andGate lits =>
    simp only [dualAndClause, ufiCollectInputIndices]
    exact flatMap_map_negLit_collect lits
  | inputGate i b => rfl
  | constant b m => rfl
  | notGate g => rfl
  | orGate gs => rfl

lemma dnfDual_collect (dnf : UnboundedFanInFormula) :
    ufiCollectInputIndices (dnfDual dnf) = ufiCollectInputIndices dnf := by
  cases dnf with
  | orGate clauses =>
    simp only [dnfDual, ufiCollectInputIndices]
    induction clauses with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.flatMap_cons, dualAndClause_collect hd, ih]
  | inputGate i b => rfl
  | constant b m => rfl
  | notGate g => rfl
  | andGate gs => rfl

end Circuits.HastadParity
