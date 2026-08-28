import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import Formulas.CnfDnf.CnfDnfBasic
import Formulas.CnfDnf.CnfDnfFamilies
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Circuits.CnfDnf.Restrictions
open Circuits.CnfDnf.Families

/-- A rational-valued switching parameter strictly between zero and one. -/
def OpenUnitIntervalQ := { x : ℚ // 0 < x ∧ x < 1 }

/-- Finite sets of variable indices below `n`. -/
def BoundedFinset (n : Nat) := { S : Finset Nat // S ⊆ Finset.range n }

def RandomRestrictionVars (σ : OpenUnitIntervalQ) (n : Nat) :=
{
  liveVars : BoundedFinset n //
  liveVars.val.card = Nat.ceil (σ.val * (n : ℚ))
}

structure AssignedRandomRestriction (σ : OpenUnitIntervalQ) (n : Nat) where
  starAssignment : RandomRestrictionVars σ n
  varAssignments : List Bool
  non_starred_vars_fully_assigned : starAssignment.val.val.card + varAssignments.length = n

open UnboundedFanInFormula

/-- Apply a restriction to a single literal. Live variables are kept;
    dead variables are replaced by their assigned constant value. -/
private def restrictLiteral (asgn : Nat → Option Bool)
    (lit : UnboundedFanInFormula) : UnboundedFanInFormula :=
  match lit with
  | inputGate i negated =>
    match asgn i with
    | none => inputGate i negated
    | some b => constant (if negated then Bool.not b else b) 0
  | c => c

/-- Apply a restriction to an AND term. Returns `none` if any literal evaluates to false
    (the term is killed). Otherwise returns the term with only live literals remaining. -/
private def restrictTerm (asgn : Nat → Option Bool)
    (term : UnboundedFanInFormula) : Option UnboundedFanInFormula :=
  match term with
  | andGate lits =>
    let applied := lits.map (restrictLiteral asgn)
    if applied.any (fun l => match l with | constant false _ => true | _ => false) then
      none
    else
      some (andGate (applied.filter (fun l => match l with | constant _ _ => false | _ => true)))
  | c => some c

/-- Apply a restriction to a DNF: restrict each term and collect the surviving ones. -/
private def restrictDNF (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula) : UnboundedFanInFormula :=
  match dnf with
  | orGate terms => orGate (terms.filterMap (restrictTerm asgn))
  | c => c

private theorem restrictLiteral_preserves_or_becomes_constant (asgn : Nat → Option Bool)
    (lit : UnboundedFanInFormula) (h : isInput lit = true) :
    isInput (restrictLiteral asgn lit) = true
    ∨ ∃ b n, restrictLiteral asgn lit = constant b n := by
  match lit with
  | inputGate i negated =>
    simp only [restrictLiteral]
    match hasgn : asgn i with
    | none => left; simp [isInput]
    | some b => right; exact ⟨if negated then Bool.not b else b, 0, rfl⟩

private def isNotConstant (l : UnboundedFanInFormula) : Bool :=
  match l with | constant _ _ => false | _ => true

private theorem filter_map_restrict_all_inputs (asgn : Nat → Option Bool)
    (lits : List UnboundedFanInFormula) (h : lits.all isInput = true) :
    ((lits.map (restrictLiteral asgn)).filter isNotConstant).all isInput = true := by
  induction lits with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hhd, htl⟩ := h
    simp only [List.map_cons, List.filter_cons]
    have ih_tl := ih htl
    have hlit := restrictLiteral_preserves_or_becomes_constant asgn hd hhd
    rcases hlit with hinp | ⟨b, n, hconst⟩
    · -- restrictLiteral kept it as an inputGate
      simp only [isNotConstant]
      match heq : restrictLiteral asgn hd with
      | inputGate _ _ =>
        simp only [ite_true, List.all_cons, Bool.and_eq_true]
        exact ⟨by rw [heq] at hinp; exact hinp, ih_tl⟩
      | constant _ _ => rw [heq] at hinp; simp [isInput] at hinp
      | notGate _ => rw [heq] at hinp; simp [isInput] at hinp
      | andGate _ => rw [heq] at hinp; simp [isInput] at hinp
      | orGate _ => rw [heq] at hinp; simp [isInput] at hinp
    · -- restrictLiteral turned it into a constant
      rw [hconst]
      simp only [isNotConstant]
      exact ih_tl

private theorem restrictTerm_preserves_and_inputs (asgn : Nat → Option Bool)
    (term : UnboundedFanInFormula) (h : Circuits.CnfDnf.isAndOfInputsOnly term = true) :
    ∀ t, restrictTerm asgn term = some t →
      Circuits.CnfDnf.isAndOfInputsOnly t = true := by
  intro t ht
  match term with
  | andGate lits =>
    simp only [restrictTerm] at ht
    split at ht
    · simp at ht
    · next hneg =>
      simp only [Option.some.injEq] at ht
      rw [← ht]
      simp only [Circuits.CnfDnf.isAndOfInputsOnly]
      simp only [Circuits.CnfDnf.isAndOfInputsOnly] at h
      exact filter_map_restrict_all_inputs asgn lits h

theorem restrictDNF_preserves_dnf
    (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula)
    (h : isDNF dnf) :
    isDNF (restrictDNF asgn dnf) := by
  match dnf with
  | orGate terms =>
    simp only [restrictDNF, isDNF]
    simp only [isDNF] at h
    induction terms with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hhd, htl⟩ := h
      have ih_tl := ih htl
      simp only [List.filterMap_cons]
      split
      · exact ih_tl
      · next t ht =>
        simp only [List.all_cons, Bool.and_eq_true]
        constructor
        · exact restrictTerm_preserves_and_inputs asgn hd hhd t ht
        · exact ih_tl

private theorem restrictLiteral_input_indices_subset (asgn : Nat → Option Bool)
    (lit : UnboundedFanInFormula) :
    ufiCollectInputIndices (restrictLiteral asgn lit) ⊆
    ufiCollectInputIndices lit := by
  match lit with
  | inputGate i negated =>
    simp only [restrictLiteral]
    match asgn i with
    | none => exact List.Subset.refl _
    | some _ => simp [ufiCollectInputIndices]
  | constant _ _ => simp [restrictLiteral]
  | notGate _ => simp [restrictLiteral]
  | andGate _ => simp [restrictLiteral]
  | orGate _ => simp [restrictLiteral]

private theorem restrictTerm_input_indices_subset (asgn : Nat → Option Bool)
    (term : UnboundedFanInFormula) (t : UnboundedFanInFormula)
    (ht : restrictTerm asgn term = some t) :
    ufiCollectInputIndices t ⊆ ufiCollectInputIndices term := by
  match term with
  | andGate lits =>
    simp only [restrictTerm] at ht
    split at ht
    · simp at ht
    · simp only [Option.some.injEq] at ht
      rw [← ht]
      simp only [ufiCollectInputIndices]
      intro x hx
      rw [List.mem_flatMap] at hx ⊢
      obtain ⟨lit', hlit'_mem, hx_in⟩ := hx
      rw [List.mem_filter] at hlit'_mem
      obtain ⟨hlit'_map, _⟩ := hlit'_mem
      rw [List.mem_map] at hlit'_map
      obtain ⟨orig, horig_mem, heq⟩ := hlit'_map
      exact ⟨orig, horig_mem, restrictLiteral_input_indices_subset asgn orig (heq ▸ hx_in)⟩
  | inputGate _ _ =>
    simp only [restrictTerm] at ht
    have := Option.some.inj ht.symm; subst this; exact List.Subset.refl _
  | constant _ _ =>
    simp only [restrictTerm] at ht
    have := Option.some.inj ht.symm; subst this; exact List.Subset.refl _
  | notGate _ =>
    simp only [restrictTerm] at ht
    have := Option.some.inj ht.symm; subst this; exact List.Subset.refl _
  | orGate _ =>
    simp only [restrictTerm] at ht
    have := Option.some.inj ht.symm; subst this; exact List.Subset.refl _

private theorem restrictDNF_input_indices_subset (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula) :
    ufiCollectInputIndices (restrictDNF asgn dnf) ⊆
    ufiCollectInputIndices dnf := by
  match dnf with
  | orGate terms =>
    simp only [restrictDNF, ufiCollectInputIndices]
    intro x hx
    rw [List.mem_flatMap] at hx ⊢
    obtain ⟨t, ht_mem, hx_in⟩ := hx
    rw [List.mem_filterMap] at ht_mem
    obtain ⟨orig, horig_mem, horig_eq⟩ := ht_mem
    exact ⟨orig, horig_mem,
           restrictTerm_input_indices_subset asgn orig t horig_eq hx_in⟩
  | inputGate _ _ => simp [restrictDNF]
  | constant _ _ => simp [restrictDNF]
  | notGate _ => simp [restrictDNF]
  | andGate _ => simp [restrictDNF]

private theorem restrictLiteral_only_live (asgn : Nat → Option Bool)
    (lit : UnboundedFanInFormula) (h : isInput lit = true) :
    ∀ i ∈ ufiCollectInputIndices (restrictLiteral asgn lit), asgn i = none := by
  match lit with
  | inputGate idx negated =>
    simp only [restrictLiteral]
    match hasgn : asgn idx with
    | none =>
      simp only [ufiCollectInputIndices]
      intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; exact hasgn
    | some _ =>
      intro i hi
      simp [ufiCollectInputIndices] at hi
  | constant _ _ => simp [isInput] at h
  | notGate _ => simp [isInput] at h
  | andGate _ => simp [isInput] at h
  | orGate _ => simp [isInput] at h

private theorem restrictTerm_only_live (asgn : Nat → Option Bool)
    (term : UnboundedFanInFormula) (h : isAndOfInputsOnly term = true)
    (t : UnboundedFanInFormula) (ht : restrictTerm asgn term = some t) :
    ∀ i ∈ ufiCollectInputIndices t, asgn i = none := by
  match term with
  | andGate lits =>
    simp only [restrictTerm] at ht
    split at ht
    · simp at ht
    · simp only [Option.some.injEq] at ht
      rw [← ht]
      simp only [ufiCollectInputIndices]
      intro i hi
      rw [List.mem_flatMap] at hi
      obtain ⟨rlit, hrlit_mem, hi_in⟩ := hi
      rw [List.mem_filter] at hrlit_mem
      obtain ⟨hrlit_map, _⟩ := hrlit_mem
      rw [List.mem_map] at hrlit_map
      obtain ⟨orig, horig_mem, heq⟩ := hrlit_map
      simp only [isAndOfInputsOnly] at h
      rw [← heq] at hi_in
      have horig_input := List.all_eq_true.mp h orig horig_mem
      exact restrictLiteral_only_live asgn orig horig_input i hi_in
  | inputGate _ _ => simp [isAndOfInputsOnly] at h
  | constant _ _ => simp [isAndOfInputsOnly] at h
  | notGate _ => simp [isAndOfInputsOnly] at h
  | orGate _ => simp [isAndOfInputsOnly] at h

/-- After applying a restriction to a DNF, all remaining input indices are live variables
    (i.e., variables where the assignment returns `none`). -/
theorem restrictDNF_preserves_liveVars_in_assignment
    (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula)
    (h : isDNF dnf) :
    ∀ i ∈ ufiCollectInputIndices (restrictDNF asgn dnf), asgn i = none := by
  match dnf with
  | orGate terms =>
    simp only [restrictDNF, ufiCollectInputIndices]
    intro i hi
    rw [List.mem_flatMap] at hi
    obtain ⟨t, ht_mem, hi_in⟩ := hi
    rw [List.mem_filterMap] at ht_mem
    obtain ⟨orig, horig_mem, horig_eq⟩ := ht_mem
    simp only [isDNF] at h
    have horig_and := List.all_eq_true.mp h orig horig_mem
    exact restrictTerm_only_live asgn orig horig_and t horig_eq i hi_in
  | inputGate _ _ => simp [isDNF] at h
  | constant _ _ => simp [isDNF] at h
  | notGate _ => simp [isDNF] at h
  | andGate _ => simp [isDNF] at h

/-- The unique inputs of the restricted DNF are a subset of the original DNF's
    live (starred) inputs: each remaining input was in the original and has
    `asgn i = none`. Equality does not hold in general because killed terms
    remove their live inputs as well. -/
theorem restrictDNF_preserves_valid_inputs
    (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula)
    (h : isDNF dnf) :
    ∀ i ∈ ufiUniqueInputs (restrictDNF asgn dnf),
      i ∈ ufiUniqueInputs dnf ∧ asgn i = none := by
  intro i hi
  simp only [ufiUniqueInputs, List.mem_dedup] at hi ⊢
  exact ⟨restrictDNF_input_indices_subset asgn dnf hi,
         restrictDNF_preserves_liveVars_in_assignment asgn dnf h i hi⟩

-- Let s = Nat.ceil (σ.val * (n : ℚ))

lemma ceil_sigma_n_le (σ : OpenUnitIntervalQ) (n : Nat) :
    Nat.ceil (σ.val * (n : ℚ)) ≤ n := by
  rw [Nat.ceil_le]
  have h1 : σ.val < 1 := σ.2.2
  have h2 : (0 : ℚ) ≤ ↑n := by positivity
  nlinarith

end Circuits.CnfDnf.Restrictions
