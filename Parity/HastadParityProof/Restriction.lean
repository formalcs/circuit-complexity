/-
  Restriction/rekey infrastructure and density-parametric round zero.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.DepthReduction
import Parity.FaninReductionBridge

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

section RestrictRekeyInfra
open UnboundedFanInFormula

/- **Leaf-level restriction-and-rekey operator.**

    `ufiRestrictRekey asgn φ` rewrites every `inputGate i b` leaf:
    * if `asgn i = some bit` (the variable is *dead*, fixed to `bit`)
      it becomes the literal-value `constant`;
    * if `asgn i = none` (the variable is *live*) it becomes
      `inputGate (φ i) b`, relabelled by `φ`.
    Gates are mapped recursively; the gate tree is otherwise untouched,
    so structural invariants (leveling, depth, circuit size) are preserved
    verbatim and only the bottom CNF/DNF shape needs a follow-up
    `simplifyConstants` pass to absorb the freshly introduced constants. -/
def ufiRestrictRekey (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    UnboundedFanInFormula → UnboundedFanInFormula
  | UnboundedFanInFormula.inputGate i b =>
      match asgn i with
      | none => UnboundedFanInFormula.inputGate (φ i) b
      | some bit =>
          UnboundedFanInFormula.constant (if b then Bool.not bit else bit) 0
  | UnboundedFanInFormula.constant b lbl => UnboundedFanInFormula.constant b lbl
  | UnboundedFanInFormula.notGate g =>
      UnboundedFanInFormula.notGate (ufiRestrictRekey asgn φ g)
  | UnboundedFanInFormula.andGate gs =>
      UnboundedFanInFormula.andGate (gs.map (ufiRestrictRekey asgn φ))
  | UnboundedFanInFormula.orGate gs =>
      UnboundedFanInFormula.orGate (gs.map (ufiRestrictRekey asgn φ))

/-- Restriction and rekeying preserve the active switching-gate topology.
    Inputs and constants both have zero budget; AND/OR emptiness and all
    remaining structural gates are preserved exactly. -/
theorem ufiRestrictRekey_switchingGateBudget
    (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lvl : Nat) (formula : UnboundedFanInFormula),
      switchingGateBudget lvl (ufiRestrictRekey asgn φ formula) =
        switchingGateBudget lvl formula
  | _, .inputGate i b => by
      simp only [ufiRestrictRekey]
      cases asgn i <;> simp [switchingGateBudget]
  | _, .constant b m => by simp [ufiRestrictRekey, switchingGateBudget]
  | lvl, .notGate g => by
      simp [ufiRestrictRekey, switchingGateBudget,
        ufiRestrictRekey_switchingGateBudget asgn φ lvl g]
  | lvl, .andGate [] => by simp [ufiRestrictRekey, switchingGateBudget]
  | lvl, .andGate (g :: gs) => by
      simp only [ufiRestrictRekey, List.map_cons, switchingGateBudget]
      by_cases hl : lvl ≤ 2
      · simp [hl]
      · simp only [if_neg hl, List.map_map]
        simp only [List.sum_cons]
        rw [ufiRestrictRekey_switchingGateBudget asgn φ (lvl - 1) g]
        have hmap : List.map (switchingGateBudget (lvl - 1) ∘
              ufiRestrictRekey asgn φ) gs =
            List.map (switchingGateBudget (lvl - 1)) gs := by
          apply List.map_congr_left
          intro child hmem
          exact ufiRestrictRekey_switchingGateBudget asgn φ (lvl - 1) child
        rw [hmap]
  | lvl, .orGate [] => by simp [ufiRestrictRekey, switchingGateBudget]
  | lvl, .orGate (g :: gs) => by
      simp only [ufiRestrictRekey, List.map_cons, switchingGateBudget]
      by_cases hl : lvl ≤ 2
      · simp [hl]
      · simp only [if_neg hl, List.map_map]
        simp only [List.sum_cons]
        rw [ufiRestrictRekey_switchingGateBudget asgn φ (lvl - 1) g]
        have hmap : List.map (switchingGateBudget (lvl - 1) ∘
              ufiRestrictRekey asgn φ) gs =
            List.map (switchingGateBudget (lvl - 1)) gs := by
          apply List.map_congr_left
          intro child hmem
          exact ufiRestrictRekey_switchingGateBudget asgn φ (lvl - 1) child
        rw [hmap]

/- Restriction-and-rekey preserves the syntactic depth (leaves stay depth 0). -/
theorem ufiRestrictRekey_depth (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) →
      ufiFormulaDepth (ufiRestrictRekey asgn φ formula) = ufiFormulaDepth formula
  | UnboundedFanInFormula.inputGate i b => by
      simp only [ufiRestrictRekey]; cases asgn i <;> simp [ufiFormulaDepth]
  | UnboundedFanInFormula.constant b lbl => by
      simp [ufiRestrictRekey, ufiFormulaDepth]
  | UnboundedFanInFormula.notGate sub => by
      simp only [ufiRestrictRekey, ufiFormulaDepth]
      rw [ufiRestrictRekey_depth asgn φ sub]
  | UnboundedFanInFormula.andGate gates => by
      simp only [ufiRestrictRekey, ufiFormulaDepth, List.map_map]
      have hmap : List.map (ufiFormulaDepth ∘ ufiRestrictRekey asgn φ) gates
          = List.map ufiFormulaDepth gates :=
        List.map_congr_left (fun g _ => ufiRestrictRekey_depth asgn φ g)
      rw [hmap]
  | UnboundedFanInFormula.orGate gates => by
      simp only [ufiRestrictRekey, ufiFormulaDepth, List.map_map]
      have hmap : List.map (ufiFormulaDepth ∘ ufiRestrictRekey asgn φ) gates
          = List.map ufiFormulaDepth gates :=
        List.map_congr_left (fun g _ => ufiRestrictRekey_depth asgn φ g)
      rw [hmap]

/- Restriction-and-rekey preserves `IsNotGateFree`. -/
theorem isNotGateFree_ufiRestrictRekey (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) → IsNotGateFree formula →
      IsNotGateFree (ufiRestrictRekey asgn φ formula)
  | UnboundedFanInFormula.inputGate i b, _ => by
      simp only [ufiRestrictRekey]; cases asgn i <;> simp [IsNotGateFree]
  | UnboundedFanInFormula.constant b lbl, _ => by
      simp [ufiRestrictRekey, IsNotGateFree]
  | UnboundedFanInFormula.notGate sub, h => by
      simp only [IsNotGateFree] at h
  | UnboundedFanInFormula.andGate gates, h => by
      simp only [IsNotGateFree] at h
      simp only [ufiRestrictRekey, IsNotGateFree, List.mem_map, forall_exists_index,
        and_imp]
      rintro x g hg rfl
      exact isNotGateFree_ufiRestrictRekey asgn φ g (h g hg)
  | UnboundedFanInFormula.orGate gates, h => by
      simp only [IsNotGateFree] at h
      simp only [ufiRestrictRekey, IsNotGateFree, List.mem_map, forall_exists_index,
        and_imp]
      rintro x g hg rfl
      exact isNotGateFree_ufiRestrictRekey asgn φ g (h g hg)

/- If a rekeyed gate is an `andGate`, the original was an `andGate`. -/
lemma ufiRestrictRekey_not_andGate (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (g : UnboundedFanInFormula) (h : ∀ inner, g ≠ UnboundedFanInFormula.andGate inner) :
    ∀ inner, ufiRestrictRekey asgn φ g ≠ UnboundedFanInFormula.andGate inner := by
  cases g with
  | inputGate i b => intro inner; simp only [ufiRestrictRekey]; cases asgn i <;> simp
  | constant b m => intro inner; simp [ufiRestrictRekey]
  | notGate s => intro inner; simp [ufiRestrictRekey]
  | andGate gs => exact absurd rfl (h gs)
  | orGate gs => intro inner; simp [ufiRestrictRekey]

lemma ufiRestrictRekey_not_orGate (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (g : UnboundedFanInFormula) (h : ∀ inner, g ≠ UnboundedFanInFormula.orGate inner) :
    ∀ inner, ufiRestrictRekey asgn φ g ≠ UnboundedFanInFormula.orGate inner := by
  cases g with
  | inputGate i b => intro inner; simp only [ufiRestrictRekey]; cases asgn i <;> simp
  | constant b m => intro inner; simp [ufiRestrictRekey]
  | notGate s => intro inner; simp [ufiRestrictRekey]
  | andGate gs => intro inner; simp [ufiRestrictRekey]
  | orGate gs => exact absurd rfl (h gs)

/- If a rekeyed gate is an And/Or, the original was an And/Or. -/
lemma isAndOr_of_ufiRestrictRekey (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (g : UnboundedFanInFormula) (h : IsAndOr (ufiRestrictRekey asgn φ g)) : IsAndOr g := by
  cases g with
  | inputGate i b =>
      cases hasgn : asgn i with
      | none => simp only [ufiRestrictRekey, hasgn, IsAndOr] at h
      | some bit => simp only [ufiRestrictRekey, hasgn, IsAndOr] at h
  | constant b m => simp [ufiRestrictRekey, IsAndOr] at h
  | notGate s => simp [ufiRestrictRekey, IsAndOr] at h
  | andGate gs => simp [IsAndOr]
  | orGate gs => simp [IsAndOr]

/- Restriction-and-rekey preserves `IsAlternatingAndLeveledAt` (the gate
    tree is structurally unchanged; leaves are leveled at any level). -/
theorem isAlternatingAndLeveledAt_ufiRestrictRekey (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) → (n : Nat) →
      IsAlternatingAndLeveledAt formula n →
      IsAlternatingAndLeveledAt (ufiRestrictRekey asgn φ formula) n
  | UnboundedFanInFormula.inputGate i b, n, _ => by
      simp only [ufiRestrictRekey]; cases asgn i <;> simp [IsAlternatingAndLeveledAt]
  | UnboundedFanInFormula.constant b lbl, n, _ => by
      simp [ufiRestrictRekey, IsAlternatingAndLeveledAt]
  | UnboundedFanInFormula.notGate sub, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
  | UnboundedFanInFormula.andGate gates, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      simp only [ufiRestrictRekey, IsAlternatingAndLeveledAt]
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg' inner
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact ufiRestrictRekey_not_andGate asgn φ g (h₁ g hg) inner
      · intro g' hg' h_ao
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact h₂ g hg (isAndOr_of_ufiRestrictRekey asgn φ g h_ao)
      · intro g' hg'
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact isAlternatingAndLeveledAt_ufiRestrictRekey asgn φ g (n - 1) (h₃ g hg)
  | UnboundedFanInFormula.orGate gates, n, h => by
      simp only [IsAlternatingAndLeveledAt] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      simp only [ufiRestrictRekey, IsAlternatingAndLeveledAt]
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg' inner
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact ufiRestrictRekey_not_orGate asgn φ g (h₁ g hg) inner
      · intro g' hg' h_ao
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact h₂ g hg (isAndOr_of_ufiRestrictRekey asgn φ g h_ao)
      · intro g' hg'
        rw [List.mem_map] at hg'
        obtain ⟨g, hg, rfl⟩ := hg'
        exact isAlternatingAndLeveledAt_ufiRestrictRekey asgn φ g (n - 1) (h₃ g hg)

/- Every input index surviving in the rekeyed formula is `φ i` for some
    *live* index `i` of the original. -/
theorem ufiRestrictRekey_collect_mem (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) →
      ∀ x ∈ ufiCollectInputIndices (ufiRestrictRekey asgn φ formula),
        ∃ i ∈ ufiCollectInputIndices formula, asgn i = none ∧ φ i = x
  | UnboundedFanInFormula.inputGate i b => by
      intro x hx
      cases hasgn : asgn i with
      | none =>
          simp only [ufiRestrictRekey, hasgn, ufiCollectInputIndices,
            List.mem_singleton] at hx
          exact ⟨i, by simp [ufiCollectInputIndices], hasgn, hx.symm⟩
      | some bit =>
          simp only [ufiRestrictRekey, hasgn, ufiCollectInputIndices,
            List.not_mem_nil] at hx
  | UnboundedFanInFormula.constant b lbl => by
      intro x hx
      simp only [ufiRestrictRekey, ufiCollectInputIndices, List.not_mem_nil] at hx
  | UnboundedFanInFormula.notGate sub => by
      intro x hx
      simp only [ufiRestrictRekey, ufiCollectInputIndices] at hx
      obtain ⟨i, hi, hasgn, hφ⟩ := ufiRestrictRekey_collect_mem asgn φ sub x hx
      exact ⟨i, by simp only [ufiCollectInputIndices]; exact hi, hasgn, hφ⟩
  | UnboundedFanInFormula.andGate gates => by
      intro x hx
      simp only [ufiRestrictRekey, ufiCollectInputIndices, List.mem_flatMap,
        List.mem_map] at hx
      obtain ⟨g', ⟨g, hg, rfl⟩, hxg⟩ := hx
      obtain ⟨i, hi, hasgn, hφ⟩ := ufiRestrictRekey_collect_mem asgn φ g x hxg
      refine ⟨i, ?_, hasgn, hφ⟩
      simp only [ufiCollectInputIndices, List.mem_flatMap]
      exact ⟨g, hg, hi⟩
  | UnboundedFanInFormula.orGate gates => by
      intro x hx
      simp only [ufiRestrictRekey, ufiCollectInputIndices, List.mem_flatMap,
        List.mem_map] at hx
      obtain ⟨g', ⟨g, hg, rfl⟩, hxg⟩ := hx
      obtain ⟨i, hi, hasgn, hφ⟩ := ufiRestrictRekey_collect_mem asgn φ g x hxg
      refine ⟨i, ?_, hasgn, hφ⟩
      simp only [ufiCollectInputIndices, List.mem_flatMap]
      exact ⟨g, hg, hi⟩

/- The largest surviving input index is `< m` provided `φ` maps every live
    index of the formula below `m`. -/
lemma ufiRestrictRekey_ufiLargestInput_lt
    (asgn : Nat → Option Bool) (φ : Nat → Nat) (formula : UnboundedFanInFormula) (m : Nat)
    (hbound : ∀ i ∈ ufiCollectInputIndices formula, asgn i = none → φ i < m)
    (hpos : 0 < m) :
    ufiLargestInput (ufiRestrictRekey asgn φ formula) < m := by
  unfold ufiLargestInput
  apply ProperizeProto.foldr_max_lt_of_forall_lt hpos
  intro x hx
  obtain ⟨i, hi, hasgn, rfl⟩ := ufiRestrictRekey_collect_mem asgn φ formula x hx
  exact hbound i hi hasgn

/- **Eval composition for the restriction-and-rekey operator.**

    If at every input index `i` of `formula` the original assignment `xs`
    matches the prescribed restriction (a live index reads through `φ`, a
    dead index reads the fixed bit), the formula and its rekeyed image
    evaluate identically. -/
theorem ufiRestrictRekey_eval (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) → (xs ys : List Bool) →
      (∀ i ∈ ufiCollectInputIndices formula,
        (match asgn i with
         | none => xs[i]? = ys[(φ i)]? | some bit => xs[i]? = some bit)) →
      ufiFormulaEval formula xs
        = ufiFormulaEval (ufiRestrictRekey asgn φ formula) ys
  | UnboundedFanInFormula.inputGate i b, xs, ys, h => by
      have hi : i ∈ ufiCollectInputIndices (UnboundedFanInFormula.inputGate i b) := by
        simp [ufiCollectInputIndices]
      have heq := h i hi
      cases hasgn : asgn i with
      | none =>
          rw [hasgn] at heq
          simp only [ufiRestrictRekey, hasgn]
          unfold ufiFormulaEval
          rw [heq]
      | some bit =>
          rw [hasgn] at heq
          simp only [ufiRestrictRekey, hasgn]
          unfold ufiFormulaEval
          rw [heq]
          cases b <;> rfl
  | UnboundedFanInFormula.constant b lbl, xs, ys, _ => by
      simp [ufiRestrictRekey, ufiFormulaEval]
  | UnboundedFanInFormula.notGate sub, xs, ys, h => by
      have h_sub : ∀ i ∈ ufiCollectInputIndices sub,
          (match asgn i with
           | none => xs[i]? = ys[(φ i)]? | some bit => xs[i]? = some bit) := by
        intro i hi
        exact h i (by simp only [ufiCollectInputIndices]; exact hi)
      have ih := ufiRestrictRekey_eval asgn φ sub xs ys h_sub
      simp only [ufiRestrictRekey, ufiFormulaEval, ih]
  | UnboundedFanInFormula.andGate gates, xs, ys, h => by
      simp only [ufiRestrictRekey]
      rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all]
      have hmap : (gates.map fun c => ufiFormulaEval c xs) =
          ((gates.map (ufiRestrictRekey asgn φ)).map fun c => ufiFormulaEval c ys) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro g hg
        have h_sub : ∀ i ∈ ufiCollectInputIndices g,
            (match asgn i with
             | none => xs[i]? = ys[(φ i)]? | some bit => xs[i]? = some bit) := by
          intro i hi
          apply h
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨g, hg, hi⟩
        exact ufiRestrictRekey_eval asgn φ g xs ys h_sub
      rw [hmap]
  | UnboundedFanInFormula.orGate gates, xs, ys, h => by
      simp only [ufiRestrictRekey]
      rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any]
      have hmap : (gates.map fun c => ufiFormulaEval c xs) =
          ((gates.map (ufiRestrictRekey asgn φ)).map fun c => ufiFormulaEval c ys) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro g hg
        have h_sub : ∀ i ∈ ufiCollectInputIndices g,
            (match asgn i with
             | none => xs[i]? = ys[(φ i)]? | some bit => xs[i]? = some bit) := by
          intro i hi
          apply h
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨g, hg, hi⟩
        exact ufiRestrictRekey_eval asgn φ g xs ys h_sub
      rw [hmap]

end RestrictRekeyInfra

section RestrictRekeyProper
open UnboundedFanInFormula

/- For a pure-input clause list, after restriction+simplification, and in the
   branch where no literal became the *true* constant `andGate []`, every
   surviving child is an `inputGate`, and the collected indices of those survivors
   are exactly the φ-images of the *live* original indices (dead indices are
   dropped). -/
lemma ufiRestrictRekey_orGate_filtered
    (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lits : List UnboundedFanInFormula),
      lits.all isInput = true →
      (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalTrue = false →
      (((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
          (fun g => !isCanonicalFalse g)).all isInput = true)
      ∧ ufiCollectInputIndices
          (orGate ((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
            (fun g => !isCanonicalFalse g)))
        = (ufiCollectInputIndices (orGate lits)).filterMap
            (fun i => match asgn i with | none => some (φ i) | some _ => none)
  | [], _, _ => by
      constructor
      · simp [List.filter_nil]
      · simp [ufiCollectInputIndices]
  | l :: ls, hall, hno_t => by
      rw [List.all_cons, Bool.and_eq_true] at hall
      have hl : isInput l = true := hall.1
      -- l is an input
      cases l with
      | constant a b => simp [isInput] at hl
      | notGate a => simp [isInput] at hl
      | andGate a => simp [isInput] at hl
      | orGate a => simp [isInput] at hl
      | inputGate i b =>
          simp only [List.map_cons, List.any_cons, Bool.or_eq_false_iff] at hno_t
          have ihres := ufiRestrictRekey_orGate_filtered asgn φ ls hall.2 hno_t.2
          cases hasgn : asgn i with
          | none =>
              -- live: child survives as `inputGate (φ i) b`
              have hhead : simplifyConstants (ufiRestrictRekey asgn φ (inputGate i b))
                  = inputGate (φ i) b := by
                simp only [ufiRestrictRekey, hasgn, simplifyConstants]
              constructor
              · simp only [List.map_cons, hhead, List.filter_cons]
                rw [if_pos (by simp [isCanonicalFalse])]
                rw [List.all_cons, Bool.and_eq_true]
                exact ⟨by simp [isInput], ihres.1⟩
              · have ih₂ := ihres.2
                simp only [List.map_cons, hhead, List.filter_cons]
                rw [if_pos (by simp [isCanonicalFalse])]
                simp only [ufiCollectInputIndices, List.flatMap_cons,
                  List.filterMap_cons, List.singleton_append, hasgn] at ih₂ ⊢
                rw [ih₂]
          | some bit =>
              -- dead: child becomes a constant; in the `no-true` branch it is `orGate []`
              set cval : Bool := (if b then Bool.not bit else bit) with hcval
              have hhead₀ : ufiRestrictRekey asgn φ (inputGate i b)
                  = constant cval 0 := by
                simp only [ufiRestrictRekey, hasgn, hcval]
              cases hc : cval with
              | true =>
                  exfalso
                  have : simplifyConstants (ufiRestrictRekey asgn φ (inputGate i b))
                      = andGate [] := by
                    rw [hhead₀, hc]; simp only [simplifyConstants]
                  rw [this] at hno_t
                  simp [isCanonicalTrue] at hno_t
              | false =>
                  have hhead : simplifyConstants (ufiRestrictRekey asgn φ (inputGate i b))
                      = orGate [] := by
                    rw [hhead₀, hc]; simp only [simplifyConstants]
                  constructor
                  · simp only [List.map_cons, hhead, List.filter_cons]
                    rw [if_neg (by simp [isCanonicalFalse])]
                    exact ihres.1
                  · have ih₂ := ihres.2
                    simp only [List.map_cons, hhead, List.filter_cons]
                    rw [if_neg (by simp [isCanonicalFalse])]
                    simp only [ufiCollectInputIndices, List.flatMap_cons,
                      List.filterMap_cons, List.singleton_append, hasgn] at ih₂ ⊢
                    rw [ih₂]

/- DNF-side mirror of `ufiRestrictRekey_orGate_filtered`: for a pure-input AND clause, in
   the branch where no literal became the *false* constant `orGate []`, every
   surviving child is an `inputGate`, and the collected indices are the φ-images of
   the live original indices. -/
lemma ufiRestrictRekey_andGate_filtered
    (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lits : List UnboundedFanInFormula),
      lits.all isInput = true →
      (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalFalse = false →
      (((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
          (fun g => !isCanonicalTrue g)).all isInput = true)
      ∧ ufiCollectInputIndices
          (andGate ((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
            (fun g => !isCanonicalTrue g)))
        = (ufiCollectInputIndices (andGate lits)).filterMap
            (fun i => match asgn i with | none => some (φ i) | some _ => none)
  | [], _, _ => by
      constructor
      · simp [List.filter_nil]
      · simp [ufiCollectInputIndices]
  | l :: ls, hall, hno_f => by
      rw [List.all_cons, Bool.and_eq_true] at hall
      have hl : isInput l = true := hall.1
      cases l with
      | constant a b => simp [isInput] at hl
      | notGate a => simp [isInput] at hl
      | andGate a => simp [isInput] at hl
      | orGate a => simp [isInput] at hl
      | inputGate i b =>
          simp only [List.map_cons, List.any_cons, Bool.or_eq_false_iff] at hno_f
          have ihres := ufiRestrictRekey_andGate_filtered asgn φ ls hall.2 hno_f.2
          cases hasgn : asgn i with
          | none =>
              have hhead : simplifyConstants (ufiRestrictRekey asgn φ (inputGate i b))
                  = inputGate (φ i) b := by
                simp only [ufiRestrictRekey, hasgn, simplifyConstants]
              constructor
              · simp only [List.map_cons, hhead, List.filter_cons]
                rw [if_pos (by simp [isCanonicalTrue])]
                rw [List.all_cons, Bool.and_eq_true]
                exact ⟨by simp [isInput], ihres.1⟩
              · have ih₂ := ihres.2
                simp only [List.map_cons, hhead, List.filter_cons]
                rw [if_pos (by simp [isCanonicalTrue])]
                simp only [ufiCollectInputIndices, List.flatMap_cons,
                  List.filterMap_cons, List.singleton_append, hasgn] at ih₂ ⊢
                rw [ih₂]
          | some bit =>
              set cval : Bool := (if b then Bool.not bit else bit) with hcval
              have hhead₀ : ufiRestrictRekey asgn φ (inputGate i b)
                  = constant cval 0 := by
                simp only [ufiRestrictRekey, hasgn, hcval]
              cases hc : cval with
              | false =>
                  exfalso
                  have : simplifyConstants (ufiRestrictRekey asgn φ (inputGate i b))
                      = orGate [] := by
                    rw [hhead₀, hc]; simp only [simplifyConstants]
                  rw [this] at hno_f
                  simp [isCanonicalFalse] at hno_f
              | true =>
                  have hhead : simplifyConstants (ufiRestrictRekey asgn φ (inputGate i b))
                      = andGate [] := by
                    rw [hhead₀, hc]; simp only [simplifyConstants]
                  constructor
                  · simp only [List.map_cons, hhead, List.filter_cons]
                    rw [if_neg (by simp [isCanonicalTrue])]
                    exact ihres.1
                  · have ih₂ := ihres.2
                    simp only [List.map_cons, hhead, List.filter_cons]
                    rw [if_neg (by simp [isCanonicalTrue])]
                    simp only [ufiCollectInputIndices, List.flatMap_cons,
                      List.filterMap_cons, List.singleton_append, hasgn] at ih₂ ⊢
                    rw [ih₂]

/- The variable indices of a pure-input clause's CNF/DNF literal list coincide
   with the formula's collected input indices. -/
lemma clause_fst_eq_collect
    (f : UnboundedFanInFormula → Option (Nat × Bool))
    (hf : ∀ i b, f (inputGate i b) = some (i, b)) :
    ∀ (ls : List UnboundedFanInFormula), ls.all isInput = true →
      (ls.filterMap f).map Prod.fst = ls.flatMap ufiCollectInputIndices
  | [], _ => by simp []
  | l :: ls, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          rw [List.filterMap_cons, hf i b]
          simp only [List.map_cons, List.flatMap_cons,
            ufiCollectInputIndices, List.singleton_append]
          rw [clause_fst_eq_collect f hf ls h.2]

/- The φ-image of a Nodup index list under the live-only remap is again Nodup
   (using that φ is injective on the live indices). -/
lemma nodup_filterMap_live_rekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (hφ : ∀ i j, asgn i = none → asgn j = none → φ i = φ j → i = j)
    {l : List Nat} (hl : l.Nodup) :
    (l.filterMap (fun i => match asgn i with | none => some (φ i) | some _ => none)).Nodup := by
  refine List.Nodup.filterMap ?_ hl
  intro a a' x ha ha'
  have ha₂ : asgn a = none ∧ φ a = x := by
    cases hh : asgn a with
    | none => simp only [hh, Option.mem_def, Option.some.injEq] at ha; exact ⟨rfl, ha⟩
    | some v => simp [hh] at ha
  have ha'2 : asgn a' = none ∧ φ a' = x := by
    cases hh : asgn a' with
    | none => simp only [hh, Option.mem_def, Option.some.injEq] at ha'; exact ⟨rfl, ha'⟩
    | some v => simp [hh] at ha'
  exact hφ a a' ha₂.1 ha'2.1 (ha₂.2.trans ha'2.2.symm)

/- A surviving CNF clause after restriction+simplification is a non-empty,
   pure-input OR gate whose variables are Nodup. -/
lemma exists_cnf_survivor_ufiRestrictRekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (hφ : ∀ i j, asgn i = none → asgn j = none → φ i = φ j → i = j)
    (g : UnboundedFanInFormula)
    (hg : isOrOfInputsOnly g = true)
    (hnod : (ufiCollectInputIndices g).Nodup)
    (hnot_t : isCanonicalTrue (simplifyConstants (ufiRestrictRekey asgn φ g)) = false)
    (hnot_f : isCanonicalFalse (simplifyConstants (ufiRestrictRekey asgn φ g)) = false) :
    ∃ ls, simplifyConstants (ufiRestrictRekey asgn φ g) = orGate ls
          ∧ ls.all isInput = true
          ∧ ls ≠ []
          ∧ (ufiCollectInputIndices (orGate ls)).Nodup := by
  cases g with
  | inputGate a b => simp [isOrOfInputsOnly] at hg
  | constant a b => simp [isOrOfInputsOnly] at hg
  | notGate a => simp [isOrOfInputsOnly] at hg
  | andGate a => simp [isOrOfInputsOnly] at hg
  | orGate lits =>
      have hlits : lits.all isInput = true := by simpa [isOrOfInputsOnly] using hg
      have hsimp : simplifyConstants (ufiRestrictRekey asgn φ (orGate lits))
          = (if (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalTrue
             then andGate []
             else orGate ((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
                    (fun g => !isCanonicalFalse g))) := by
        simp only [ufiRestrictRekey, simplifyConstants, simplifyConstantsList_eq_map,
          List.map_map, Function.comp_def]
      by_cases hany : (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalTrue = true
      · exfalso
        rw [hsimp, if_pos hany] at hnot_t
        simp [isCanonicalTrue] at hnot_t
      · have hany' : (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalTrue = false := by
          simpa using hany
        have hres : simplifyConstants (ufiRestrictRekey asgn φ (orGate lits))
            = orGate ((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
                (fun g => !isCanonicalFalse g)) := by
          rw [hsimp, if_neg hany]
        obtain ⟨hallinp, hcollect⟩ := ufiRestrictRekey_orGate_filtered asgn φ lits hlits hany'
        refine ⟨_, hres, hallinp, ?_, ?_⟩
        · intro hnil
          rw [hres, hnil] at hnot_f
          simp [isCanonicalFalse] at hnot_f
        · rw [hcollect]
          exact nodup_filterMap_live_rekey asgn φ hφ hnod

/- DNF mirror: a surviving DNF clause is a non-empty, pure-input AND gate whose
   variables are Nodup. -/
lemma exists_dnf_survivor_ufiRestrictRekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (hφ : ∀ i j, asgn i = none → asgn j = none → φ i = φ j → i = j)
    (g : UnboundedFanInFormula)
    (hg : isAndOfInputsOnly g = true)
    (hnod : (ufiCollectInputIndices g).Nodup)
    (hnot_t : isCanonicalTrue (simplifyConstants (ufiRestrictRekey asgn φ g)) = false)
    (hnot_f : isCanonicalFalse (simplifyConstants (ufiRestrictRekey asgn φ g)) = false) :
    ∃ ls, simplifyConstants (ufiRestrictRekey asgn φ g) = andGate ls
          ∧ ls.all isInput = true
          ∧ ls ≠ []
          ∧ (ufiCollectInputIndices (andGate ls)).Nodup := by
  cases g with
  | inputGate a b => simp [isAndOfInputsOnly] at hg
  | constant a b => simp [isAndOfInputsOnly] at hg
  | notGate a => simp [isAndOfInputsOnly] at hg
  | orGate a => simp [isAndOfInputsOnly] at hg
  | andGate lits =>
      have hlits : lits.all isInput = true := by simpa [isAndOfInputsOnly] using hg
      have hsimp : simplifyConstants (ufiRestrictRekey asgn φ (andGate lits))
          = (if (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalFalse
             then orGate []
             else andGate ((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
                    (fun g => !isCanonicalTrue g))) := by
        simp only [ufiRestrictRekey, simplifyConstants, simplifyConstantsList_eq_map,
          List.map_map, Function.comp_def]
      by_cases hany : (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalFalse = true
      · exfalso
        rw [hsimp, if_pos hany] at hnot_f
        simp [isCanonicalFalse] at hnot_f
      · have hany' : (lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).any isCanonicalFalse = false := by
          simpa using hany
        have hres : simplifyConstants (ufiRestrictRekey asgn φ (andGate lits))
            = andGate ((lits.map (fun l => simplifyConstants (ufiRestrictRekey asgn φ l))).filter
                (fun g => !isCanonicalTrue g)) := by
          rw [hsimp, if_neg hany]
        obtain ⟨hallinp, hcollect⟩ := ufiRestrictRekey_andGate_filtered asgn φ lits hlits hany'
        refine ⟨_, hres, hallinp, ?_, ?_⟩
        · intro hnil
          rw [hres, hnil] at hnot_t
          simp [isCanonicalTrue] at hnot_t
        · rw [hcollect]
          exact nodup_filterMap_live_rekey asgn φ hφ hnod

/- A non-empty pure-input gate has a non-empty collected index list. -/
lemma flatMap_collect_ne_nil :
    ∀ (ls : List UnboundedFanInFormula), ls.all isInput = true → ls ≠ [] →
      ls.flatMap ufiCollectInputIndices ≠ []
  | [], _, hne => by exact absurd rfl hne
  | x :: xs, hinp, _ => by
      rw [List.all_cons, Bool.and_eq_true] at hinp
      cases x with
      | inputGate i b => simp [ufiCollectInputIndices, List.flatMap_cons]
      | constant a b => simp [isInput] at hinp
      | notGate a => simp [isInput] at hinp
      | andGate a => simp [isInput] at hinp
      | orGate a => simp [isInput] at hinp

/- **Restriction+simplification preserves `HasProperBottomsAt`.**  Given a proper
   leveled formula `f` and a remap `φ` injective on the live coordinates, the
   restricted-and-simplified formula `simplifyConstants (ufiRestrictRekey …)`
   is again proper at the same level.  The bottom (level ≤ 2) case is the heart:
   each CNF/DNF clause loses its dead literals, satisfied clauses vanish, and the
   surviving clauses remain pure-input with Nodup variables; higher levels recurse
   structurally (folding only collapses to canonical empty gates or drops
   children). -/
mutual
theorem hasProperBottomsAt_simplifyConstants_ufiRestrictRekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (hφ : ∀ i j, asgn i = none → asgn j = none → φ i = φ j → i = j) :
    ∀ (f : UnboundedFanInFormula) (lvl : Nat),
      HasProperBottomsAt f lvl →
      HasProperBottomsAt (simplifyConstants (ufiRestrictRekey asgn φ f)) lvl
  | inputGate x b, lvl, _ => by
      cases hasgn : asgn x with
      | none =>
          have hh : simplifyConstants (ufiRestrictRekey asgn φ (inputGate x b)) = inputGate (φ x) b := by
            simp only [ufiRestrictRekey, hasgn, simplifyConstants]
          rw [hh]; simp only [HasProperBottomsAt]
      | some bit =>
          have h₀ : ufiRestrictRekey asgn φ (inputGate x b)
              = constant (if b then Bool.not bit else bit) 0 := by
            simp only [ufiRestrictRekey, hasgn]
          cases hc : (if b then Bool.not bit else bit) with
          | false =>
              have hh : simplifyConstants (ufiRestrictRekey asgn φ (inputGate x b)) = orGate [] := by
                rw [h₀, hc]; simp only [simplifyConstants]
              rw [hh]; exact hasProperBottomsAt_orGate_nil lvl
          | true =>
              have hh : simplifyConstants (ufiRestrictRekey asgn φ (inputGate x b)) = andGate [] := by
                rw [h₀, hc]; simp only [simplifyConstants]
              rw [hh]; exact hasProperBottomsAt_andGate_nil lvl
  | constant b m, lvl, _ => by
      cases b with
      | false =>
          have hh : simplifyConstants (ufiRestrictRekey asgn φ (constant false m)) = orGate [] := by
            simp only [ufiRestrictRekey, simplifyConstants]
          rw [hh]; exact hasProperBottomsAt_orGate_nil lvl
      | true =>
          have hh : simplifyConstants (ufiRestrictRekey asgn φ (constant true m)) = andGate [] := by
            simp only [ufiRestrictRekey, simplifyConstants]
          rw [hh]; exact hasProperBottomsAt_andGate_nil lvl
  | notGate g, lvl, h => by
      unfold HasProperBottomsAt at h; exact h.elim
  | andGate gs, lvl, h => by
      have htop : simplifyConstants (ufiRestrictRekey asgn φ (andGate gs))
          = (if (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse
             then orGate []
             else andGate ((gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter
                    (fun g => !isCanonicalTrue g))) := by
        simp only [ufiRestrictRekey, simplifyConstants, simplifyConstantsList_eq_map,
          List.map_map, Function.comp_def]
      by_cases hl : lvl ≤ 2
      · unfold HasProperBottomsAt at h; rw [if_pos hl] at h
        have hcnf : gs.all isOrOfInputsOnly = true := by simpa [isCNF] using h.1
        have hisor : ∀ g ∈ gs, isOrOfInputsOnly g = true := by
          intro g hg; rw [List.all_eq_true] at hcnf; exact hcnf g hg
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse = true
        · rw [htop, if_pos hany]; exact hasProperBottomsAt_orGate_nil lvl
        · have hanyf : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse = false := by
            simpa using hany
          have key : ∀ g', g' ∈ (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter (fun g => !isCanonicalTrue g) →
              ∃ ls, g' = orGate ls ∧ ls.all isInput = true ∧ ls ≠ [] ∧ (ufiCollectInputIndices (orGate ls)).Nodup := by
            intro g' hg'
            rw [List.mem_filter] at hg'
            obtain ⟨hg'cs, hg't⟩ := hg'
            have hg'incs := hg'cs
            rw [List.mem_map] at hg'cs
            obtain ⟨g, hg, hgeq⟩ := hg'cs
            have hor := hisor g hg
            have hg'f : isCanonicalFalse g' = false := by
              by_contra h_f
              have h_ft : isCanonicalFalse g' = true := by simpa using h_f
              have hc₂ : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse = true :=
                List.any_eq_true.2 ⟨g', hg'incs, h_ft⟩
              rw [hc₂] at hanyf; exact absurd hanyf (by simp)
            have hg'tf : isCanonicalTrue g' = false := by simpa using hg't
            cases g with
            | inputGate a b => simp [isOrOfInputsOnly] at hor
            | constant a b => simp [isOrOfInputsOnly] at hor
            | notGate a => simp [isOrOfInputsOnly] at hor
            | andGate a => simp [isOrOfInputsOnly] at hor
            | orGate lits =>
                have hlits : lits.all isInput = true := by simpa [isOrOfInputsOnly] using hor
                have hmem : (lits.filterMap (fun lit => match lit with | inputGate i b => some (i, b) | _ => none))
                    ∈ Circuits.CnfDnf.cnfClauses (andGate gs) := by
                  unfold Circuits.CnfDnf.cnfClauses
                  rw [List.mem_map]
                  exact ⟨orGate lits, hg, rfl⟩
                have hnd := h.2.2 _ hmem
                rw [clause_fst_eq_collect (fun lit => match lit with | inputGate i b => some (i, b) | _ => none) (fun _ _ => rfl) lits hlits] at hnd
                have hcollnod : (ufiCollectInputIndices (orGate lits)).Nodup := by
                  simpa [ufiCollectInputIndices] using hnd
                have hsv := exists_cnf_survivor_ufiRestrictRekey asgn φ hφ (orGate lits) hor hcollnod
                  (by rw [hgeq]; exact hg'tf) (by rw [hgeq]; exact hg'f)
                obtain ⟨ls, hls₁, hls₂, hls₃, hls₄⟩ := hsv
                exact ⟨ls, by rw [← hgeq]; exact hls₁, hls₂, hls₃, hls₄⟩
          rw [htop, if_neg hany]
          unfold HasProperBottomsAt; rw [if_pos hl]
          refine ⟨?_, ?_, ?_⟩
          · simp only [isCNF]
            rw [List.all_eq_true]
            intro g' hg'
            obtain ⟨ls, hgls, hlsinp, _, _⟩ := key g' hg'
            rw [hgls]; simpa [isOrOfInputsOnly] using hlsinp
          · intro c hc
            unfold Circuits.CnfDnf.cnfClauses at hc
            rw [List.mem_map] at hc
            obtain ⟨g', hg', hceq⟩ := hc
            obtain ⟨ls, hgls, hlsinp, hlsne, _⟩ := key g' hg'
            subst hgls
            dsimp only at hceq
            have hcmap : c.map Prod.fst = ls.flatMap ufiCollectInputIndices := by
              rw [← hceq]
              refine clause_fst_eq_collect _ ?_ ls hlsinp
              intro i b; rfl
            intro hcnil
            rw [hcnil] at hcmap
            simp only [List.map_nil] at hcmap
            exact flatMap_collect_ne_nil ls hlsinp hlsne hcmap.symm
          · intro c hc
            unfold Circuits.CnfDnf.cnfClauses at hc
            rw [List.mem_map] at hc
            obtain ⟨g', hg', hceq⟩ := hc
            obtain ⟨ls, hgls, hlsinp, _, hlsnod⟩ := key g' hg'
            subst hgls
            dsimp only at hceq
            have hcmap : c.map Prod.fst = ls.flatMap ufiCollectInputIndices := by
              rw [← hceq]
              refine clause_fst_eq_collect _ ?_ ls hlsinp
              intro i b; rfl
            rw [hcmap]
            simpa [ufiCollectInputIndices] using hlsnod
      · unfold HasProperBottomsAt at h; rw [if_neg hl] at h
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse = true
        · rw [htop, if_pos hany]; exact hasProperBottomsAt_orGate_nil lvl
        · rw [htop, if_neg hany]
          unfold HasProperBottomsAt; rw [if_neg hl]
          intro g' hg'
          rw [List.mem_filter] at hg'
          exact hasProperBottomsAt_of_mem_simplifyConstantsList_ufiRestrictRekey asgn φ hφ gs (lvl - 1) h g' hg'.1
  | orGate gs, lvl, h => by
      have htop : simplifyConstants (ufiRestrictRekey asgn φ (orGate gs))
          = (if (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue
             then andGate []
             else orGate ((gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter
                    (fun g => !isCanonicalFalse g))) := by
        simp only [ufiRestrictRekey, simplifyConstants, simplifyConstantsList_eq_map,
          List.map_map, Function.comp_def]
      by_cases hl : lvl ≤ 2
      · unfold HasProperBottomsAt at h; rw [if_pos hl] at h
        have hdnf : gs.all isAndOfInputsOnly = true := by simpa [isDNF] using h.1
        have hisand : ∀ g ∈ gs, isAndOfInputsOnly g = true := by
          intro g hg; rw [List.all_eq_true] at hdnf; exact hdnf g hg
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue = true
        · rw [htop, if_pos hany]; exact hasProperBottomsAt_andGate_nil lvl
        · have hanyf : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue = false := by
            simpa using hany
          have key : ∀ g', g' ∈ (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter (fun g => !isCanonicalFalse g) →
              ∃ ls, g' = andGate ls ∧ ls.all isInput = true ∧ ls ≠ [] ∧ (ufiCollectInputIndices (andGate ls)).Nodup := by
            intro g' hg'
            rw [List.mem_filter] at hg'
            obtain ⟨hg'cs, hg'f⟩ := hg'
            have hg'incs := hg'cs
            rw [List.mem_map] at hg'cs
            obtain ⟨g, hg, hgeq⟩ := hg'cs
            have hand := hisand g hg
            have hg't : isCanonicalTrue g' = false := by
              by_contra h_t
              have h_tt : isCanonicalTrue g' = true := by simpa using h_t
              have hc₂ : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue = true :=
                List.any_eq_true.2 ⟨g', hg'incs, h_tt⟩
              rw [hc₂] at hanyf; exact absurd hanyf (by simp)
            have hg'ff : isCanonicalFalse g' = false := by simpa using hg'f
            cases g with
            | inputGate a b => simp [isAndOfInputsOnly] at hand
            | constant a b => simp [isAndOfInputsOnly] at hand
            | notGate a => simp [isAndOfInputsOnly] at hand
            | orGate a => simp [isAndOfInputsOnly] at hand
            | andGate lits =>
                have hlits : lits.all isInput = true := by simpa [isAndOfInputsOnly] using hand
                have hmem : (lits.filterMap (fun lit => match lit with | inputGate i b => some (i, b) | _ => none))
                    ∈ Circuits.CnfDnf.dnfClauses (orGate gs) := by
                  unfold Circuits.CnfDnf.dnfClauses
                  rw [List.mem_map]
                  exact ⟨andGate lits, hg, rfl⟩
                have hnd := h.2.2 _ hmem
                rw [clause_fst_eq_collect (fun lit => match lit with | inputGate i b => some (i, b) | _ => none) (fun _ _ => rfl) lits hlits] at hnd
                have hcollnod : (ufiCollectInputIndices (andGate lits)).Nodup := by
                  simpa [ufiCollectInputIndices] using hnd
                have hsv := exists_dnf_survivor_ufiRestrictRekey asgn φ hφ (andGate lits) hand hcollnod
                  (by rw [hgeq]; exact hg't) (by rw [hgeq]; exact hg'ff)
                obtain ⟨ls, hls₁, hls₂, hls₃, hls₄⟩ := hsv
                exact ⟨ls, by rw [← hgeq]; exact hls₁, hls₂, hls₃, hls₄⟩
          rw [htop, if_neg hany]
          unfold HasProperBottomsAt; rw [if_pos hl]
          refine ⟨?_, ?_, ?_⟩
          · simp only [isDNF]
            rw [List.all_eq_true]
            intro g' hg'
            obtain ⟨ls, hgls, hlsinp, _, _⟩ := key g' hg'
            rw [hgls]; simpa [isAndOfInputsOnly] using hlsinp
          · intro c hc
            unfold Circuits.CnfDnf.dnfClauses at hc
            rw [List.mem_map] at hc
            obtain ⟨g', hg', hceq⟩ := hc
            obtain ⟨ls, hgls, hlsinp, hlsne, _⟩ := key g' hg'
            subst hgls
            dsimp only at hceq
            have hcmap : c.map Prod.fst = ls.flatMap ufiCollectInputIndices := by
              rw [← hceq]
              refine clause_fst_eq_collect _ ?_ ls hlsinp
              intro i b; rfl
            intro hcnil
            rw [hcnil] at hcmap
            simp only [List.map_nil] at hcmap
            exact flatMap_collect_ne_nil ls hlsinp hlsne hcmap.symm
          · intro c hc
            unfold Circuits.CnfDnf.dnfClauses at hc
            rw [List.mem_map] at hc
            obtain ⟨g', hg', hceq⟩ := hc
            obtain ⟨ls, hgls, hlsinp, _, hlsnod⟩ := key g' hg'
            subst hgls
            dsimp only at hceq
            have hcmap : c.map Prod.fst = ls.flatMap ufiCollectInputIndices := by
              rw [← hceq]
              refine clause_fst_eq_collect _ ?_ ls hlsinp
              intro i b; rfl
            rw [hcmap]
            simpa [ufiCollectInputIndices] using hlsnod
      · unfold HasProperBottomsAt at h; rw [if_neg hl] at h
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue = true
        · rw [htop, if_pos hany]; exact hasProperBottomsAt_andGate_nil lvl
        · rw [htop, if_neg hany]
          unfold HasProperBottomsAt; rw [if_neg hl]
          intro g' hg'
          rw [List.mem_filter] at hg'
          exact hasProperBottomsAt_of_mem_simplifyConstantsList_ufiRestrictRekey asgn φ hφ gs (lvl - 1) h g' hg'.1

theorem hasProperBottomsAt_of_mem_simplifyConstantsList_ufiRestrictRekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (hφ : ∀ i j, asgn i = none → asgn j = none → φ i = φ j → i = j) :
    ∀ (gs : List UnboundedFanInFormula) (lvl : Nat),
      (∀ g ∈ gs, HasProperBottomsAt g lvl) →
      ∀ x ∈ gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g)),
        HasProperBottomsAt x lvl
  | [], lvl, _ => by intro x hx; simp at hx
  | g₀ :: gs, lvl, h => by
      intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with he | hmem
      · subst he
        exact hasProperBottomsAt_simplifyConstants_ufiRestrictRekey asgn φ hφ g₀ lvl (h g₀ (by simp))
      · exact hasProperBottomsAt_of_mem_simplifyConstantsList_ufiRestrictRekey asgn φ hφ gs lvl
          (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hmem
end

/- **Kill-condition agreement.**  For an all-input clause `lits`, the
   `simplifyConstants ∘ ufiRestrictRekey` pipeline produces a falsified
   (`orGate []`) literal exactly when the keystone's `simpleRestrictLiteral`
   pipeline produces a falsified (`constant false`) literal. -/
lemma ufiRestrictRekey_kill_agree (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lits : List UnboundedFanInFormula), lits.all isInput = true →
      ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse
      = (lits.map (simpleRestrictLiteral asgn)).any
          (fun l => match l with | constant false _ => true | _ => false)
  | [], _ => by simp
  | l :: ls, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          simp only [List.map_cons, List.any_cons]
          cases hasgn : asgn i with
          | none =>
              simp only [ufiRestrictRekey, hasgn, simplifyConstants, isCanonicalFalse,
                simpleRestrictLiteral, Bool.false_or]
              exact ufiRestrictRekey_kill_agree asgn φ ls h.2
          | some bit =>
              cases hsat : (if b then Bool.not bit else bit) with
              | false =>
                  simp only [ufiRestrictRekey, hasgn, hsat, simplifyConstants, isCanonicalFalse,
                    simpleRestrictLiteral, Bool.true_or]
              | true =>
                  simp only [ufiRestrictRekey, hasgn, hsat, simplifyConstants, isCanonicalFalse,
                    simpleRestrictLiteral, Bool.false_or]
                  exact ufiRestrictRekey_kill_agree asgn φ ls h.2

/- **Live-count agreement.**  When no literal is falsified, the number of
   surviving literals (after `simplifyConstants ∘ ufiRestrictRekey`) equals
   the number of surviving literals after `simpleRestrictLiteral`.  Both count
   the live (unassigned) inputs. -/
lemma ufiRestrictRekey_live_count_eq (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lits : List UnboundedFanInFormula), lits.all isInput = true →
      ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse = false →
      (((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
          (fun g => !isCanonicalTrue g)).length
      = ((lits.map (simpleRestrictLiteral asgn)).filter
          (fun l => match l with | constant _ _ => false | _ => true)).length
  | [], _, _ => by simp
  | l :: ls, h, hnokill => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          cases hasgn : asgn i with
          | none =>
              simp only [List.map_cons, List.any_cons, ufiRestrictRekey, hasgn,
                simplifyConstants, isCanonicalFalse, Bool.false_or] at hnokill
              have ih := ufiRestrictRekey_live_count_eq asgn φ ls h.2 hnokill
              simp only [List.map_cons, List.filter_cons, ufiRestrictRekey, hasgn,
                simplifyConstants, isCanonicalTrue, simpleRestrictLiteral, Bool.not_false,
                if_true, List.length_cons] at ih ⊢
              omega
          | some bit =>
              cases hsat : (if b then Bool.not bit else bit) with
              | false =>
                  simp only [List.map_cons, List.any_cons, ufiRestrictRekey, hasgn, hsat,
                    simplifyConstants, isCanonicalFalse, Bool.true_or] at hnokill
                  exact absurd hnokill (by decide)
              | true =>
                  simp only [List.map_cons, List.any_cons, ufiRestrictRekey, hasgn, hsat,
                    simplifyConstants, isCanonicalFalse, Bool.false_or] at hnokill
                  simp only [List.map_cons, List.filter_cons, ufiRestrictRekey, hasgn, hsat,
                    simplifyConstants, isCanonicalTrue, simpleRestrictLiteral, Bool.not_true]
                  exact ufiRestrictRekey_live_count_eq asgn φ ls h.2 hnokill

/- **Per-term survival agreement.**  When the `simplifyConstants ∘ rekey`
   restriction of an all-input clause survives as `andGate survivors`, the keystone's
   `simpleRestrictTerm` also survives as `some (andGate survivors')` with the same
   number of surviving literals. -/
lemma exists_term_survivor_ufiRestrictRekey (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (lits : List UnboundedFanInFormula) (hlits : lits.all isInput = true)
    (survivors : List UnboundedFanInFormula)
    (hsimp : simplifyConstants (ufiRestrictRekey asgn φ (andGate lits)) = andGate survivors) :
    ∃ survivors', simpleRestrictTerm asgn (andGate lits) = some (andGate survivors')
        ∧ survivors.length = survivors'.length := by
  have hrekey : ufiRestrictRekey asgn φ (andGate lits)
      = andGate (lits.map (ufiRestrictRekey asgn φ)) := by
    simp only [ufiRestrictRekey]
  rw [hrekey] at hsimp
  rw [show simplifyConstants (andGate (lits.map (ufiRestrictRekey asgn φ)))
        = (if ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse
           then orGate []
           else andGate (((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
                  (fun g => !isCanonicalTrue g)))
        from by simp only [simplifyConstants, simplifyConstantsList_eq_map]] at hsimp
  by_cases hany : ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse = true
  · rw [if_pos hany] at hsimp; exact absurd hsimp (by simp)
  · have hnokill : ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse
        = false := by simpa using hany
    rw [if_neg hany] at hsimp
    have h_survivors : survivors = ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
        (fun g => !isCanonicalTrue g) := by
      injection hsimp with h_survivors'; exact h_survivors'.symm
    have hkill := ufiRestrictRekey_kill_agree asgn φ lits hlits
    have happlied : (lits.map (simpleRestrictLiteral asgn)).any
        (fun l => match l with | constant false _ => true | _ => false) = false := by
      rw [← hkill]; exact hnokill
    refine ⟨(lits.map (simpleRestrictLiteral asgn)).filter
      (fun l => match l with | constant _ _ => false | _ => true), ?_, ?_⟩
    · simp only [simpleRestrictTerm]
      split_ifs with hc
      · exact absurd (hc.symm.trans happlied) (by decide)
      · rfl
    · rw [h_survivors]; exact ufiRestrictRekey_live_count_eq asgn φ lits hlits hnokill

/- **DNF width bridge.**  The `simplifyConstants ∘ ufiRestrictRekey` restriction
   never makes a DNF wider than the keystone's `simpleRestrictDNF` restriction
   (with the same assignment).  This connects the project-native restriction
   operator to the banked Round-0 keystone, whose conclusion bounds
   `dnfWidth (simpleRestrictDNF asgn _)`. -/
lemma ufiRestrictRekey_dnfWidth_le (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (terms : List UnboundedFanInFormula) (hterms : terms.all isAndOfInputsOnly = true) :
    dnfWidth (simplifyConstants (ufiRestrictRekey asgn φ (orGate terms)))
      ≤ dnfWidth (simpleRestrictDNF asgn (orGate terms)) := by
  have hrekey : ufiRestrictRekey asgn φ (orGate terms)
      = orGate (terms.map (ufiRestrictRekey asgn φ)) := by
    simp only [ufiRestrictRekey]
  rw [hrekey]
  rw [show simplifyConstants (orGate (terms.map (ufiRestrictRekey asgn φ)))
        = (if ((terms.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue
           then andGate []
           else orGate (((terms.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
                  (fun g => !isCanonicalFalse g)))
        from by simp only [simplifyConstants, simplifyConstantsList_eq_map]]
  by_cases hany : ((terms.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue = true
  · rw [if_pos hany]; simp [dnfWidth]
  · rw [if_neg hany]
    -- Width of the surviving orGate is bounded by every surviving clause's
    -- length, each of which equals a surviving `simpleRestrictTerm` clause.
    apply Lists.ListLemmas.foldl_max_le_of_forall
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨g, hgmem, hxeq⟩ := hx
    rw [List.mem_filter] at hgmem
    obtain ⟨hgcs, _⟩ := hgmem
    rw [List.mem_map] at hgcs
    obtain ⟨rg, hrgmem, hgeq⟩ := hgcs
    rw [List.mem_map] at hrgmem
    obtain ⟨term, htermmem, hrgeq⟩ := hrgmem
    -- `term` is an all-input andGate; its rekey-simplify survived as `g`.
    have htermin : isAndOfInputsOnly term = true := by
      have := List.all_eq_true.mp hterms term htermmem
      exact this
    obtain ⟨lits, hlitseq⟩ : ∃ lits, term = andGate lits := by
      cases term with
      | andGate lits => exact ⟨lits, rfl⟩
      | _ => simp [isAndOfInputsOnly] at htermin
    subst hlitseq
    have hlits : lits.all isInput = true := by
      simpa [isAndOfInputsOnly] using htermin
    -- `g = simplifyConstants (rekey (andGate lits))`; `x` is its clause length.
    cases hg' : g with
    | andGate Lg =>
        have hsimp : simplifyConstants (ufiRestrictRekey asgn φ (andGate lits)) = andGate Lg := by
          rw [← hrgeq] at hgeq; rw [hgeq, hg']
        obtain ⟨L', hrestrict, hlen⟩ := exists_term_survivor_ufiRestrictRekey asgn φ lits hlits Lg hsimp
        -- `x = Lg.length = L'.length`; the surviving clause `andGate L'` is a
        -- member of the restricted DNF, so its length is ≤ the dnfWidth.
        have hxval : x = Lg.length := by rw [← hxeq, hg']
        rw [hxval, hlen]
        apply Lists.ListLemmas.mem_le_foldl_max
        rw [List.mem_map]
        refine ⟨andGate L', ?_, rfl⟩
        show andGate L' ∈ terms.filterMap (simpleRestrictTerm asgn)
        rw [List.mem_filterMap]
        exact ⟨andGate lits, htermmem, hrestrict⟩
    | _ =>
        -- A non-andGate survivor contributes width 0.
        have hxval : x = 0 := by rw [← hxeq, hg']
        omega

/- ════════════════════════════════════════════════════════════════════════
   CNF (AND-rooted bottom) width bridge — exact dual of the DNF bridge above.
   The keystone is DNF-only, so CNF bottoms are bridged here against a local
   keystone-style restriction `simpleRestrictCNF` (dual of
   `simpleRestrictDNF`).  A clause `orGate lits` is *satisfied* (and dropped)
   when some literal becomes the constant `true`; otherwise the live literals
   survive.  ════════════════════════════════════════════════════════════════ -/

/- Restrict a single CNF clause (OR of literals). Returns `none` when the
   clause is satisfied (some literal becomes `true`); otherwise the surviving
   (live) literals. -/
def simpleRestrictClause (asgn : Nat → Option Bool)
    (clause : UnboundedFanInFormula) : Option UnboundedFanInFormula :=
  match clause with
  | orGate lits =>
      let applied := lits.map (simpleRestrictLiteral asgn)
      if applied.any (fun l => match l with | constant true _ => true | _ => false) then
        none
      else
        some (orGate (applied.filter (fun l => match l with | constant _ _ => false | _ => true)))
  | c => some c

/- Restrict a CNF (AND of clauses) under an assignment.  Satisfied clauses are
   dropped (dual of `simpleRestrictDNF`). -/
def simpleRestrictCNF (asgn : Nat → Option Bool)
    (cnf : UnboundedFanInFormula) : UnboundedFanInFormula :=
  match cnf with
  | andGate clauses => andGate (clauses.filterMap (simpleRestrictClause asgn))
  | c => c

/- **Satisfaction-condition agreement** (dual of `ufiRestrictRekey_kill_agree`).  For an
   all-input clause, the `simplifyConstants ∘ ufiRestrictRekey` pipeline
   produces a satisfied (`andGate []`) literal exactly when the keystone-style
   `simpleRestrictLiteral` pipeline produces a `constant true` literal. -/
lemma ufiRestrictRekey_satisfaction_agree (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lits : List UnboundedFanInFormula), lits.all isInput = true →
      ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue
      = (lits.map (simpleRestrictLiteral asgn)).any
          (fun l => match l with | constant true _ => true | _ => false)
  | [], _ => by simp
  | l :: ls, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          simp only [List.map_cons, List.any_cons]
          cases hasgn : asgn i with
          | none =>
              simp only [ufiRestrictRekey, hasgn, simplifyConstants, isCanonicalTrue,
                simpleRestrictLiteral, Bool.false_or]
              exact ufiRestrictRekey_satisfaction_agree asgn φ ls h.2
          | some bit =>
              cases hsat : (if b then Bool.not bit else bit) with
              | false =>
                  simp only [ufiRestrictRekey, hasgn, hsat, simplifyConstants, isCanonicalTrue,
                    simpleRestrictLiteral, Bool.false_or]
                  exact ufiRestrictRekey_satisfaction_agree asgn φ ls h.2
              | true =>
                  simp only [ufiRestrictRekey, hasgn, hsat, simplifyConstants, isCanonicalTrue,
                    simpleRestrictLiteral, Bool.true_or]

/- **Live-count agreement (CNF)** (dual of `ufiRestrictRekey_live_count_eq`).  When no
   literal satisfies the clause, the number of surviving literals after
   `simplifyConstants ∘ ufiRestrictRekey` equals the number after
   `simpleRestrictLiteral`. -/
lemma ufiRestrictRekey_cnf_live_count_eq (asgn : Nat → Option Bool) (φ : Nat → Nat) :
    ∀ (lits : List UnboundedFanInFormula), lits.all isInput = true →
      ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue = false →
      (((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
          (fun g => !isCanonicalFalse g)).length
      = ((lits.map (simpleRestrictLiteral asgn)).filter
          (fun l => match l with | constant _ _ => false | _ => true)).length
  | [], _, _ => by simp
  | l :: ls, h, hnosat => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          cases hasgn : asgn i with
          | none =>
              simp only [List.map_cons, List.any_cons, ufiRestrictRekey, hasgn,
                simplifyConstants, isCanonicalTrue, Bool.false_or] at hnosat
              have ih := ufiRestrictRekey_cnf_live_count_eq asgn φ ls h.2 hnosat
              simp only [List.map_cons, List.filter_cons, ufiRestrictRekey, hasgn,
                simplifyConstants, isCanonicalFalse, simpleRestrictLiteral, Bool.not_false,
                if_true, List.length_cons] at ih ⊢
              omega
          | some bit =>
              cases hsat : (if b then Bool.not bit else bit) with
              | true =>
                  simp only [List.map_cons, List.any_cons, ufiRestrictRekey, hasgn, hsat,
                    simplifyConstants, isCanonicalTrue, Bool.true_or] at hnosat
                  exact absurd hnosat (by decide)
              | false =>
                  simp only [List.map_cons, List.any_cons, ufiRestrictRekey, hasgn, hsat,
                    simplifyConstants, isCanonicalTrue, Bool.false_or] at hnosat
                  simp only [List.map_cons, List.filter_cons, ufiRestrictRekey, hasgn, hsat,
                    simplifyConstants, isCanonicalFalse, simpleRestrictLiteral, Bool.not_true]
                  exact ufiRestrictRekey_cnf_live_count_eq asgn φ ls h.2 hnosat

/- **Per-clause survival agreement (CNF)** (dual of `exists_term_survivor_ufiRestrictRekey`).
   When the `simplifyConstants ∘ rekey` restriction of an all-input clause
   survives as `orGate survivors`, the keystone-style `simpleRestrictClause` also
   survives as `some (orGate survivors')` with the same number of surviving literals. -/
lemma exists_clause_survivor_ufiRestrictRekey (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (lits : List UnboundedFanInFormula) (hlits : lits.all isInput = true)
    (survivors : List UnboundedFanInFormula)
    (hsimp : simplifyConstants (ufiRestrictRekey asgn φ (orGate lits)) = orGate survivors) :
    ∃ survivors', simpleRestrictClause asgn (orGate lits) = some (orGate survivors')
        ∧ survivors.length = survivors'.length := by
  have hrekey : ufiRestrictRekey asgn φ (orGate lits)
      = orGate (lits.map (ufiRestrictRekey asgn φ)) := by
    simp only [ufiRestrictRekey]
  rw [hrekey] at hsimp
  rw [show simplifyConstants (orGate (lits.map (ufiRestrictRekey asgn φ)))
        = (if ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue
           then andGate []
           else orGate (((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
                  (fun g => !isCanonicalFalse g)))
        from by simp only [simplifyConstants, simplifyConstantsList_eq_map]] at hsimp
  by_cases hany : ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue = true
  · rw [if_pos hany] at hsimp; exact absurd hsimp (by simp)
  · have hnosat : ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalTrue
        = false := by simpa using hany
    rw [if_neg hany] at hsimp
    have h_survivors : survivors = ((lits.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
        (fun g => !isCanonicalFalse g) := by
      injection hsimp with h_survivors'; exact h_survivors'.symm
    have hsat := ufiRestrictRekey_satisfaction_agree asgn φ lits hlits
    have happlied : (lits.map (simpleRestrictLiteral asgn)).any
        (fun l => match l with | constant true _ => true | _ => false) = false := by
      rw [← hsat]; exact hnosat
    refine ⟨(lits.map (simpleRestrictLiteral asgn)).filter
      (fun l => match l with | constant _ _ => false | _ => true), ?_, ?_⟩
    · simp only [simpleRestrictClause]
      split_ifs with hc
      · exact absurd (hc.symm.trans happlied) (by decide)
      · rfl
    · rw [h_survivors]; exact ufiRestrictRekey_cnf_live_count_eq asgn φ lits hlits hnosat

/- **CNF width bridge** (dual of `ufiRestrictRekey_dnfWidth_le`).  The
   `simplifyConstants ∘ ufiRestrictRekey` restriction never makes a CNF wider
   than the keystone-style `simpleRestrictCNF` restriction. -/
lemma ufiRestrictRekey_cnfWidth_le (asgn : Nat → Option Bool) (φ : Nat → Nat)
    (clauses : List UnboundedFanInFormula) (hclauses : clauses.all isOrOfInputsOnly = true) :
    cnfWidth (simplifyConstants (ufiRestrictRekey asgn φ (andGate clauses)))
      ≤ cnfWidth (simpleRestrictCNF asgn (andGate clauses)) := by
  have hrekey : ufiRestrictRekey asgn φ (andGate clauses)
      = andGate (clauses.map (ufiRestrictRekey asgn φ)) := by
    simp only [ufiRestrictRekey]
  rw [hrekey]
  rw [show simplifyConstants (andGate (clauses.map (ufiRestrictRekey asgn φ)))
        = (if ((clauses.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse
           then orGate []
           else andGate (((clauses.map (ufiRestrictRekey asgn φ)).map simplifyConstants).filter
                  (fun g => !isCanonicalTrue g)))
        from by simp only [simplifyConstants, simplifyConstantsList_eq_map]]
  by_cases hany : ((clauses.map (ufiRestrictRekey asgn φ)).map simplifyConstants).any isCanonicalFalse = true
  · rw [if_pos hany]; simp [cnfWidth]
  · rw [if_neg hany]
    apply Lists.ListLemmas.foldl_max_le_of_forall
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨g, hgmem, hxeq⟩ := hx
    rw [List.mem_filter] at hgmem
    obtain ⟨hgcs, _⟩ := hgmem
    rw [List.mem_map] at hgcs
    obtain ⟨rg, hrgmem, hgeq⟩ := hgcs
    rw [List.mem_map] at hrgmem
    obtain ⟨clause, hclausemem, hrgeq⟩ := hrgmem
    have hclausein : isOrOfInputsOnly clause = true :=
      List.all_eq_true.mp hclauses clause hclausemem
    obtain ⟨lits, hlitseq⟩ : ∃ lits, clause = orGate lits := by
      cases clause with
      | orGate lits => exact ⟨lits, rfl⟩
      | _ => simp [isOrOfInputsOnly] at hclausein
    subst hlitseq
    have hlits : lits.all isInput = true := by
      simpa [isOrOfInputsOnly] using hclausein
    cases hg' : g with
    | orGate Lg =>
        have hsimp : simplifyConstants (ufiRestrictRekey asgn φ (orGate lits)) = orGate Lg := by
          rw [← hrgeq] at hgeq; rw [hgeq, hg']
        obtain ⟨L', hrestrict, hlen⟩ := exists_clause_survivor_ufiRestrictRekey asgn φ lits hlits Lg hsimp
        have hxval : x = Lg.length := by rw [← hxeq, hg']
        rw [hxval, hlen]
        apply Lists.ListLemmas.mem_le_foldl_max
        rw [List.mem_map]
        refine ⟨orGate L', ?_, rfl⟩
        show orGate L' ∈ clauses.filterMap (simpleRestrictClause asgn)
        rw [List.mem_filterMap]
        exact ⟨orGate lits, hclausemem, hrestrict⟩
    | _ =>
        have hxval : x = 0 := by rw [← hxeq, hg']
        omega

/- ════════════════════════════════════════════════════════════════════════
   Restriction+simplification preserves the `HasProperBottomWidthLE` invariant.
   Mirrors `hasProperBottomsAt_simplifyConstants_ufiRestrictRekey`: at the bottom level the
   restricted clause/term widths are bounded via the DNF/CNF width bridges,
   while internal levels recurse on the surviving (non-collapsed) children.

   The hypothesis is carried by `HasRestrictionBottomWidthLE`, the keystone-style
   image of `HasProperBottomWidthLE`: every depth-≤2 bottom of the *original*
   formula has `simpleRestrictDNF`/`simpleRestrictCNF` width `≤ t`.
   ════════════════════════════════════════════════════════════════════════ -/
def HasRestrictionBottomWidthLE (asgn : Nat → Option Bool) :
    UnboundedFanInFormula → Nat → Nat → Prop
  | inputGate _ _, _, _ => True
  | constant _ _, _, _ => True
  | notGate _, _, _ => False
  | andGate clauses, lvl, t =>
      if lvl ≤ 2 then cnfWidth (simpleRestrictCNF asgn (andGate clauses)) ≤ t
      else ∀ g ∈ clauses, HasRestrictionBottomWidthLE asgn g (lvl - 1) t
  | orGate terms, lvl, t =>
      if lvl ≤ 2 then dnfWidth (simpleRestrictDNF asgn (orGate terms)) ≤ t
      else ∀ g ∈ terms, HasRestrictionBottomWidthLE asgn g (lvl - 1) t

mutual
theorem hasProperBottomWidthLE_simplifyConstants_ufiRestrictRekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat) (t : Nat) :
    ∀ (f : UnboundedFanInFormula) (lvl : Nat),
      HasProperBottomsAt f lvl →
      HasRestrictionBottomWidthLE asgn f lvl t →
      HasProperBottomWidthLE (simplifyConstants (ufiRestrictRekey asgn φ f)) lvl t
  | inputGate x b, lvl, _, _ => by
      cases hasgn : asgn x with
      | none =>
          have hh : simplifyConstants (ufiRestrictRekey asgn φ (inputGate x b)) = inputGate (φ x) b := by
            simp only [ufiRestrictRekey, hasgn, simplifyConstants]
          rw [hh]; simp only [HasProperBottomWidthLE]
      | some bit =>
          have h₀ : ufiRestrictRekey asgn φ (inputGate x b)
              = constant (if b then Bool.not bit else bit) 0 := by
            simp only [ufiRestrictRekey, hasgn]
          cases hc : (if b then Bool.not bit else bit) with
          | false =>
              have hh : simplifyConstants (ufiRestrictRekey asgn φ (inputGate x b)) = orGate [] := by
                rw [h₀, hc]; simp only [simplifyConstants]
              rw [hh]; exact hasProperBottomWidthLE_orGate_nil lvl t
          | true =>
              have hh : simplifyConstants (ufiRestrictRekey asgn φ (inputGate x b)) = andGate [] := by
                rw [h₀, hc]; simp only [simplifyConstants]
              rw [hh]; exact hasProperBottomWidthLE_andGate_nil lvl t
  | constant b m, lvl, _, _ => by
      cases b with
      | false =>
          have hh : simplifyConstants (ufiRestrictRekey asgn φ (constant false m)) = orGate [] := by
            simp only [ufiRestrictRekey, simplifyConstants]
          rw [hh]; exact hasProperBottomWidthLE_orGate_nil lvl t
      | true =>
          have hh : simplifyConstants (ufiRestrictRekey asgn φ (constant true m)) = andGate [] := by
            simp only [ufiRestrictRekey, simplifyConstants]
          rw [hh]; exact hasProperBottomWidthLE_andGate_nil lvl t
  | notGate g, lvl, h, _ => by
      unfold HasProperBottomsAt at h; exact h.elim
  | andGate gs, lvl, hproper, hrbw => by
      have htop : simplifyConstants (ufiRestrictRekey asgn φ (andGate gs))
          = (if (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse
             then orGate []
             else andGate ((gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter
                    (fun g => !isCanonicalTrue g))) := by
        simp only [ufiRestrictRekey, simplifyConstants, simplifyConstantsList_eq_map,
          List.map_map, Function.comp_def]
      by_cases hl : lvl ≤ 2
      · have hcnf : gs.all isOrOfInputsOnly = true := by
          unfold HasProperBottomsAt at hproper; rw [if_pos hl] at hproper
          simpa [isCNF] using hproper.1
        have hwidth : cnfWidth (simpleRestrictCNF asgn (andGate gs)) ≤ t := by
          unfold HasRestrictionBottomWidthLE at hrbw; rw [if_pos hl] at hrbw; exact hrbw
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse = true
        · rw [htop, if_pos hany]; exact hasProperBottomWidthLE_orGate_nil lvl t
        · have hresult : simplifyConstants (ufiRestrictRekey asgn φ (andGate gs))
              = andGate ((gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter
                    (fun g => !isCanonicalTrue g)) := by rw [htop, if_neg hany]
          rw [hresult]
          unfold HasProperBottomWidthLE; rw [if_pos hl]
          rw [← hresult]
          calc cnfWidth (simplifyConstants (ufiRestrictRekey asgn φ (andGate gs)))
              ≤ cnfWidth (simpleRestrictCNF asgn (andGate gs)) :=
                ufiRestrictRekey_cnfWidth_le asgn φ gs hcnf
            _ ≤ t := hwidth
      · have hpchildren : ∀ g ∈ gs, HasProperBottomsAt g (lvl - 1) := by
          unfold HasProperBottomsAt at hproper; rw [if_neg hl] at hproper; exact hproper
        have hrchildren : ∀ g ∈ gs, HasRestrictionBottomWidthLE asgn g (lvl - 1) t := by
          unfold HasRestrictionBottomWidthLE at hrbw; rw [if_neg hl] at hrbw; exact hrbw
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalFalse = true
        · rw [htop, if_pos hany]; exact hasProperBottomWidthLE_orGate_nil lvl t
        · rw [htop, if_neg hany]
          unfold HasProperBottomWidthLE; rw [if_neg hl]
          intro g' hg'
          rw [List.mem_filter] at hg'
          exact hasProperBottomWidthLE_of_mem_simplifyConstantsList_ufiRestrictRekey asgn φ t gs (lvl - 1)
            hpchildren hrchildren g' hg'.1
  | orGate gs, lvl, hproper, hrbw => by
      have htop : simplifyConstants (ufiRestrictRekey asgn φ (orGate gs))
          = (if (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue
             then andGate []
             else orGate ((gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter
                    (fun g => !isCanonicalFalse g))) := by
        simp only [ufiRestrictRekey, simplifyConstants, simplifyConstantsList_eq_map,
          List.map_map, Function.comp_def]
      by_cases hl : lvl ≤ 2
      · have hdnf : gs.all isAndOfInputsOnly = true := by
          unfold HasProperBottomsAt at hproper; rw [if_pos hl] at hproper
          simpa [isDNF] using hproper.1
        have hwidth : dnfWidth (simpleRestrictDNF asgn (orGate gs)) ≤ t := by
          unfold HasRestrictionBottomWidthLE at hrbw; rw [if_pos hl] at hrbw; exact hrbw
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue = true
        · rw [htop, if_pos hany]; exact hasProperBottomWidthLE_andGate_nil lvl t
        · have hresult : simplifyConstants (ufiRestrictRekey asgn φ (orGate gs))
              = orGate ((gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).filter
                    (fun g => !isCanonicalFalse g)) := by rw [htop, if_neg hany]
          rw [hresult]
          unfold HasProperBottomWidthLE; rw [if_pos hl]
          rw [← hresult]
          calc dnfWidth (simplifyConstants (ufiRestrictRekey asgn φ (orGate gs)))
              ≤ dnfWidth (simpleRestrictDNF asgn (orGate gs)) :=
                ufiRestrictRekey_dnfWidth_le asgn φ gs hdnf
            _ ≤ t := hwidth
      · have hpchildren : ∀ g ∈ gs, HasProperBottomsAt g (lvl - 1) := by
          unfold HasProperBottomsAt at hproper; rw [if_neg hl] at hproper; exact hproper
        have hrchildren : ∀ g ∈ gs, HasRestrictionBottomWidthLE asgn g (lvl - 1) t := by
          unfold HasRestrictionBottomWidthLE at hrbw; rw [if_neg hl] at hrbw; exact hrbw
        by_cases hany : (gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g))).any isCanonicalTrue = true
        · rw [htop, if_pos hany]; exact hasProperBottomWidthLE_andGate_nil lvl t
        · rw [htop, if_neg hany]
          unfold HasProperBottomWidthLE; rw [if_neg hl]
          intro g' hg'
          rw [List.mem_filter] at hg'
          exact hasProperBottomWidthLE_of_mem_simplifyConstantsList_ufiRestrictRekey asgn φ t gs (lvl - 1)
            hpchildren hrchildren g' hg'.1

theorem hasProperBottomWidthLE_of_mem_simplifyConstantsList_ufiRestrictRekey
    (asgn : Nat → Option Bool) (φ : Nat → Nat) (t : Nat) :
    ∀ (gs : List UnboundedFanInFormula) (lvl : Nat),
      (∀ g ∈ gs, HasProperBottomsAt g lvl) →
      (∀ g ∈ gs, HasRestrictionBottomWidthLE asgn g lvl t) →
      ∀ x ∈ gs.map (fun g => simplifyConstants (ufiRestrictRekey asgn φ g)),
        HasProperBottomWidthLE x lvl t
  | [], _, _, _ => by intro x hx; simp at hx
  | g₀ :: gs, lvl, hp, hr => by
      intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with he | hmem
      · subst he
        exact hasProperBottomWidthLE_simplifyConstants_ufiRestrictRekey asgn φ t g₀ lvl
          (hp g₀ (by simp)) (hr g₀ (by simp))
      · exact hasProperBottomWidthLE_of_mem_simplifyConstantsList_ufiRestrictRekey asgn φ t gs lvl
          (fun g hg => hp g (List.mem_cons_of_mem _ hg))
          (fun g hg => hr g (List.mem_cons_of_mem _ hg)) x hmem
end

/- ════════════════════════════════════════════════════════════════════════
   CNF↔DNF dual-commutation of the keystone-style restriction.

   The keystone bounds DNF widths only.  A CNF bottom `andGate clauses` is
   bridged by dualising (`cnfDual`) to a DNF and observing that the CNF
   restriction width equals the DNF restriction width of the dual.  This is
   self-contained: it never mentions `ufiRestrictRekey`/`simplifyConstants`.
   Per literal, `simpleRestrictLiteral asgn (negLit l)` is the De Morgan
   negation of `simpleRestrictLiteral asgn l`, so a clause is *satisfied*
   (dropped) exactly when its dual term is *killed*, and the surviving live
   literals coincide. ════════════════════════════════════════════════════════ -/

lemma simpleRestrictLiteral_dual_any_eq (asgn : Nat → Option Bool) :
    ∀ (lits : List UnboundedFanInFormula), lits.all isInput = true →
      ((lits.map negLit).map (simpleRestrictLiteral asgn)).any
          (fun l => match l with | constant false _ => true | _ => false)
      = (lits.map (simpleRestrictLiteral asgn)).any
          (fun l => match l with | constant true _ => true | _ => false)
  | [], _ => rfl
  | l :: ls, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          simp only [List.map_cons, List.any_cons, negLit]
          rw [simpleRestrictLiteral_dual_any_eq asgn ls h.2]
          cases hasgn : asgn i with
          | none => simp [simpleRestrictLiteral, hasgn]
          | some v => cases b <;> cases v <;> simp [simpleRestrictLiteral, hasgn, Bool.not]

lemma simpleRestrictLiteral_dual_filter_length_eq (asgn : Nat → Option Bool) :
    ∀ (lits : List UnboundedFanInFormula), lits.all isInput = true →
      (((lits.map negLit).map (simpleRestrictLiteral asgn)).filter
          (fun l => match l with | constant _ _ => false | _ => true)).length
      = ((lits.map (simpleRestrictLiteral asgn)).filter
          (fun l => match l with | constant _ _ => false | _ => true)).length
  | [], _ => rfl
  | l :: ls, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      cases l with
      | constant a b => simp [isInput] at h
      | notGate a => simp [isInput] at h
      | andGate a => simp [isInput] at h
      | orGate a => simp [isInput] at h
      | inputGate i b =>
          have ih := simpleRestrictLiteral_dual_filter_length_eq asgn ls h.2
          cases hasgn : asgn i with
          | none =>
              simp [List.map_cons, negLit, simpleRestrictLiteral, hasgn] at ih ⊢
              omega
          | some v =>
              simp [List.map_cons, negLit, simpleRestrictLiteral, hasgn] at ih ⊢
              omega

/- Per-clause: the CNF-restricted clause and its dual DNF-restricted term either
   both vanish, or both survive with equal live-literal count. -/
lemma simpleRestrictClause_dual_map (asgn : Nat → Option Bool)
    (lits : List UnboundedFanInFormula) (hlits : lits.all isInput = true) :
    (simpleRestrictClause asgn (orGate lits)).map
        (fun g => match g with | orGate l => l.length | _ => 0)
      = (simpleRestrictTerm asgn (dualClause (orGate lits))).map
        (fun g => match g with | andGate l => l.length | _ => 0) := by
  have hany := simpleRestrictLiteral_dual_any_eq asgn lits hlits
  have hlen := simpleRestrictLiteral_dual_filter_length_eq asgn lits hlits
  simp only [simpleRestrictClause, dualClause, simpleRestrictTerm]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (hany.trans h₁) h₂
  · exact absurd (hany.symm.trans h₂) h₁
  · simp only [Option.map_some]; exact congrArg some hlen.symm

lemma filterMap_clause_dual_eq (asgn : Nat → Option Bool) :
    ∀ (clauses : List UnboundedFanInFormula), clauses.all isOrOfInputsOnly = true →
      clauses.filterMap (fun c => (simpleRestrictClause asgn c).map
          (fun g => match g with | orGate l => l.length | _ => 0))
      = clauses.filterMap (fun c => (simpleRestrictTerm asgn (dualClause c)).map
          (fun g => match g with | andGate l => l.length | _ => 0))
  | [], _ => rfl
  | c :: rest, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨lits, rfl⟩ : ∃ lits, c = orGate lits := by
        cases c with
        | orGate lits => exact ⟨lits, rfl⟩
        | _ => simp [isOrOfInputsOnly] at h
      have hlits : lits.all isInput = true := by simpa [isOrOfInputsOnly] using h.1
      simp only [List.filterMap_cons]
      rw [simpleRestrictClause_dual_map asgn lits hlits, filterMap_clause_dual_eq asgn rest h.2]

/- **CNF dual-commutation (width).**  The keystone-style CNF restriction width of
   `andGate clauses` equals the DNF restriction width of its De Morgan dual. -/
lemma simpleRestrictCNF_dual_width (asgn : Nat → Option Bool)
    (clauses : List UnboundedFanInFormula) (hclauses : clauses.all isOrOfInputsOnly = true) :
    cnfWidth (simpleRestrictCNF asgn (andGate clauses))
      = dnfWidth (simpleRestrictDNF asgn (cnfDual (andGate clauses))) := by
  simp only [simpleRestrictCNF, cnfDual, simpleRestrictDNF, cnfWidth, dnfWidth,
    List.map_filterMap, List.filterMap_map, Function.comp_def]
  exact congrArg (List.foldl max 0) (filterMap_clause_dual_eq asgn clauses hclauses)

/- ════════════════════════════════════════════════════════════════════════
   Bridging extracted bottoms to `HasRestrictionBottomWidthLE`.

   `extractBottomLayer` descends through internal levels with *exactly* the
   same `lvl ≤ 2` recursion as `HasRestrictionBottomWidthLE`.  Hence a per-bottom
   restricted width bound (`HasRestrictedBottomWidthLE`) on every gate of the
   extracted bottom layer lifts to `HasRestrictionBottomWidthLE` on the whole
   formula.  This is the structural converse of
   `extractBottomLayer_bottoms_fanIn_le` and feeds the keystone's per-DNF
   width bounds into `hasProperBottomWidthLE_simplifyConstants_ufiRestrictRekey`. ══════════ -/

def HasRestrictedBottomWidthLE (asgn : Nat → Option Bool) :
    UnboundedFanInFormula → Nat → Prop
  | andGate clauses, t => cnfWidth (simpleRestrictCNF asgn (andGate clauses)) ≤ t
  | orGate terms, t => dnfWidth (simpleRestrictDNF asgn (orGate terms)) ≤ t
  | _, _ => True

mutual
theorem hasRestrictionBottomWidthLE_of_extracted
    (asgn : Nat → Option Bool) (t : Nat) :
    ∀ (f : UnboundedFanInFormula) (lvl start : Nat),
      HasProperBottomsAt f lvl →
      (∀ g ∈ (extractBottomLayer lvl start f).1, HasRestrictedBottomWidthLE asgn g t) →
      HasRestrictionBottomWidthLE asgn f lvl t
  | inputGate x b, _, _, _, _ => by simp only [HasRestrictionBottomWidthLE]
  | constant b m, _, _, _, _ => by simp only [HasRestrictionBottomWidthLE]
  | notGate g, lvl, start, hproper, _ => by
      unfold HasProperBottomsAt at hproper; exact hproper.elim
  | andGate gs, lvl, start, hproper, hbot => by
      unfold HasRestrictionBottomWidthLE
      by_cases hl : lvl ≤ 2
      · rw [if_pos hl]
        have hb₁ : (extractBottomLayer lvl start (andGate gs)).1 = [andGate gs] := by
          simp only [extractBottomLayer]; rw [if_pos hl]
        have hmem := hbot (andGate gs) (by rw [hb₁]; simp)
        simpa [HasRestrictedBottomWidthLE] using hmem
      · rw [if_neg hl]
        have hp' : ∀ g ∈ gs, HasProperBottomsAt g (lvl - 1) := by
          unfold HasProperBottomsAt at hproper; rw [if_neg hl] at hproper; exact hproper
        have hbl : (extractBottomLayer lvl start (andGate gs)).1
            = (extractBottomLayerList (lvl - 1) start gs).1 := by
          simp only [extractBottomLayer]; rw [if_neg hl]
        exact hasRestrictionBottomWidthLE_of_extracted_list asgn t gs (lvl - 1) start hp'
          (fun x hx => hbot x (by rw [hbl]; exact hx))
  | orGate gs, lvl, start, hproper, hbot => by
      unfold HasRestrictionBottomWidthLE
      by_cases hl : lvl ≤ 2
      · rw [if_pos hl]
        have hb₁ : (extractBottomLayer lvl start (orGate gs)).1 = [orGate gs] := by
          simp only [extractBottomLayer]; rw [if_pos hl]
        have hmem := hbot (orGate gs) (by rw [hb₁]; simp)
        simpa [HasRestrictedBottomWidthLE] using hmem
      · rw [if_neg hl]
        have hp' : ∀ g ∈ gs, HasProperBottomsAt g (lvl - 1) := by
          unfold HasProperBottomsAt at hproper; rw [if_neg hl] at hproper; exact hproper
        have hbl : (extractBottomLayer lvl start (orGate gs)).1
            = (extractBottomLayerList (lvl - 1) start gs).1 := by
          simp only [extractBottomLayer]; rw [if_neg hl]
        exact hasRestrictionBottomWidthLE_of_extracted_list asgn t gs (lvl - 1) start hp'
          (fun x hx => hbot x (by rw [hbl]; exact hx))

theorem hasRestrictionBottomWidthLE_of_extracted_list
    (asgn : Nat → Option Bool) (t : Nat) :
    ∀ (gs : List UnboundedFanInFormula) (lvl start : Nat),
      (∀ g ∈ gs, HasProperBottomsAt g lvl) →
      (∀ x ∈ (extractBottomLayerList lvl start gs).1, HasRestrictedBottomWidthLE asgn x t) →
      ∀ g ∈ gs, HasRestrictionBottomWidthLE asgn g lvl t
  | [], _, _, _, _ => by intro g hg; simp at hg
  | g₀ :: gs, lvl, start, hp, hbot => by
      have hsplit : (extractBottomLayerList lvl start (g₀ :: gs)).1
          = (extractBottomLayer lvl start g₀).1
            ++ (extractBottomLayerList lvl (extractBottomLayer lvl start g₀).2.2 gs).1 := by
        simp only [extractBottomLayerList]
      intro g hg
      rcases List.mem_cons.mp hg with heq | hmem
      · subst g
        exact hasRestrictionBottomWidthLE_of_extracted asgn t g₀ lvl start
          (hp g₀ List.mem_cons_self)
          (fun x hx => hbot x (by rw [hsplit]; exact List.mem_append_left _ hx))
      · exact hasRestrictionBottomWidthLE_of_extracted_list asgn t gs lvl
          (extractBottomLayer lvl start g₀).2.2
          (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
          (fun x hx => hbot x (by rw [hsplit]; exact List.mem_append_right _ hx))
          g hmem
end

/- ════════════════════════════════════════════════════════════════════════
   Per-bottom translation: keystone DNF width bound → `HasRestrictedBottomWidthLE`.

   The Round-0 bound controls DNF restriction widths. Each extracted bottom
   is dualised to a DNF via `toBottomDNF`
   (an `orGate` stays put; an `andGate` CNF becomes its De Morgan dual); the
   restricted DNF width of that dual then matches the bottom's own restricted
   width (`dnfWidth`/`cnfWidth` via `simpleRestrictCNF_dual_width`). ═════ -/

def toBottomDNF : UnboundedFanInFormula → UnboundedFanInFormula
  | orGate terms => orGate terms
  | andGate clauses => cnfDual (andGate clauses)
  | _ => orGate []

lemma hasRestrictedBottomWidthLE_of_bound (asgn : Nat → Option Bool) (t : Nat)
    (g : UnboundedFanInFormula)
    (hcnf : ∀ clauses, g = andGate clauses → clauses.all isOrOfInputsOnly = true)
    (hbound : dnfWidth (simpleRestrictDNF asgn (toBottomDNF g)) ≤ t) :
    HasRestrictedBottomWidthLE asgn g t := by
  cases g with
  | inputGate x b => simp only [HasRestrictedBottomWidthLE]
  | constant b m => simp only [HasRestrictedBottomWidthLE]
  | notGate g => simp only [HasRestrictedBottomWidthLE]
  | orGate terms =>
      simp only [HasRestrictedBottomWidthLE]
      simpa only [toBottomDNF] using hbound
  | andGate clauses =>
      simp only [HasRestrictedBottomWidthLE]
      rw [simpleRestrictCNF_dual_width asgn clauses (hcnf clauses rfl)]
      simpa only [toBottomDNF] using hbound

/- Combined: per-bottom keystone DNF bounds (after dualisation) lift to the
   whole-formula `HasRestrictionBottomWidthLE` invariant via the extraction bridge. -/
lemma hasRestrictionBottomWidthLE_of_bottom_bounds (asgn : Nat → Option Bool) (t : Nat)
    (f : UnboundedFanInFormula) (lvl : Nat)
    (hproper : HasProperBottomsAt f lvl)
    (hcnf : ∀ g ∈ (extractBottomLayer lvl 0 f).1, ∀ clauses, g = andGate clauses →
        clauses.all isOrOfInputsOnly = true)
    (hbound : ∀ g ∈ (extractBottomLayer lvl 0 f).1,
        dnfWidth (simpleRestrictDNF asgn (toBottomDNF g)) ≤ t) :
    HasRestrictionBottomWidthLE asgn f lvl t :=
  hasRestrictionBottomWidthLE_of_extracted asgn t f lvl 0 hproper
    (fun g hg => hasRestrictedBottomWidthLE_of_bound asgn t g (hcnf g hg) (hbound g hg))

/- Shape facts about a proper bottom (`HasProperBottomsAt g 2`) consumed by
   the per-bottom bridge: the dualised bottom is a DNF, and a CNF bottom's clauses are
   OR-of-inputs. -/
lemma all_isOrOfInputsOnly_of_hasProperBottomsAt_andGate (g : UnboundedFanInFormula)
    (hp : HasProperBottomsAt g 2) :
    ∀ clauses, g = andGate clauses → clauses.all isOrOfInputsOnly = true := by
  intro clauses hgc
  subst hgc
  unfold HasProperBottomsAt at hp; rw [if_pos (le_refl 2)] at hp
  simpa [isCNF] using hp.1

lemma isDNF_toBottomDNF (g : UnboundedFanInFormula)
    (hp : HasProperBottomsAt g 2) : isDNF (toBottomDNF g) = true := by
  cases g with
  | inputGate x b => simp [toBottomDNF, isDNF]
  | constant b m => simp [toBottomDNF, isDNF]
  | notGate g => unfold HasProperBottomsAt at hp; exact hp.elim
  | orGate terms =>
      unfold HasProperBottomsAt at hp; rw [if_pos (le_refl 2)] at hp
      simpa only [toBottomDNF] using hp.1
  | andGate clauses =>
      unfold HasProperBottomsAt at hp; rw [if_pos (le_refl 2)] at hp
      simp only [toBottomDNF]
      exact isDNF_cnfDual (andGate clauses) hp.1

/- Every clause variable of a DNF appears among its collected input indices. -/
lemma dnf_clause_var_mem_collect (d : UnboundedFanInFormula)
    (hdnf : isDNF d = true) :
    ∀ c ∈ Circuits.CnfDnf.dnfClauses d, ∀ p ∈ c,
      p.1 ∈ ufiCollectInputIndices d := by
  cases d with
  | inputGate a b => simp [isDNF] at hdnf
  | constant a b => simp [isDNF] at hdnf
  | notGate g => simp [isDNF] at hdnf
  | andGate gs => simp [isDNF] at hdnf
  | orGate gates =>
      simp only [isDNF] at hdnf
      intro c hc p hp
      simp only [Circuits.CnfDnf.dnfClauses, List.mem_map] at hc
      obtain ⟨gate, hgate, rfl⟩ := hc
      have hgand : isAndOfInputsOnly gate = true := List.all_eq_true.mp hdnf gate hgate
      cases gate with
      | inputGate a b => simp [isAndOfInputsOnly] at hgand
      | constant a b => simp [isAndOfInputsOnly] at hgand
      | notGate g => simp [isAndOfInputsOnly] at hgand
      | orGate g => simp [isAndOfInputsOnly] at hgand
      | andGate lits =>
          simp only [isAndOfInputsOnly] at hgand
          have hfst : (lits.filterMap
                (fun lit => match lit with | inputGate i b => some (i, b) | _ => none)).map Prod.fst
              = lits.flatMap ufiCollectInputIndices :=
            clause_fst_eq_collect _ (fun i b => rfl) lits hgand
          have hp₁ : p.1 ∈ lits.flatMap ufiCollectInputIndices := by
            rw [← hfst]; exact List.mem_map_of_mem hp
          change p.1 ∈ ufiCollectInputIndices (orGate gates)
          simp only [ufiCollectInputIndices]
          exact List.mem_flatMap.mpr ⟨andGate lits, hgate,
            by simp only [ufiCollectInputIndices]; exact hp₁⟩

/- `var < n` for the dualised bottom DNF, from `HasProperBottomsAt g 2` and a bound
   on the bottom's collected inputs. -/
lemma toBottomDNF_clause_var_lt (g : UnboundedFanInFormula) (n : Nat)
    (hp : HasProperBottomsAt g 2)
    (hlt : ∀ x ∈ ufiCollectInputIndices g, x < n) :
    ∀ c ∈ Circuits.CnfDnf.dnfClauses (toBottomDNF g), ∀ p ∈ c, p.1 < n := by
  intro c hc p hp'
  have hmem : p.1 ∈ ufiCollectInputIndices (toBottomDNF g) :=
    dnf_clause_var_mem_collect (toBottomDNF g) (isDNF_toBottomDNF g hp) c hc p hp'
  apply hlt
  cases g with
  | inputGate x b => simp only [toBottomDNF, ufiCollectInputIndices, List.flatMap_nil,
      List.not_mem_nil] at hmem
  | constant b m => simp only [toBottomDNF, ufiCollectInputIndices, List.flatMap_nil,
      List.not_mem_nil] at hmem
  | notGate g => unfold HasProperBottomsAt at hp; exact hp.elim
  | orGate terms => simpa only [toBottomDNF] using hmem
  | andGate clauses =>
      rw [show toBottomDNF (andGate clauses) = cnfDual (andGate clauses) from rfl] at hmem
      rwa [cnfDual_collect] at hmem

/- Nodup of the variable list of each dualised bottom DNF clause. -/
lemma toBottomDNF_clause_nodup (g : UnboundedFanInFormula)
    (hp : HasProperBottomsAt g 2) :
    ∀ c ∈ Circuits.CnfDnf.dnfClauses (toBottomDNF g), (c.map Prod.fst).Nodup := by
  cases g with
  | inputGate x b => intro c hc; simp [toBottomDNF, Circuits.CnfDnf.dnfClauses] at hc
  | constant b m => intro c hc; simp [toBottomDNF, Circuits.CnfDnf.dnfClauses] at hc
  | notGate g => unfold HasProperBottomsAt at hp; exact hp.elim
  | orGate terms =>
      unfold HasProperBottomsAt at hp; rw [if_pos (le_refl 2)] at hp
      simpa only [toBottomDNF] using hp.2.2
  | andGate clauses =>
      unfold HasProperBottomsAt at hp; rw [if_pos (le_refl 2)] at hp
      have hcnf : (clauses.all isOrOfInputsOnly) = true := by simpa [isCNF] using hp.1
      have hnd := hp.2.2
      intro c hc
      rw [show toBottomDNF (andGate clauses) = cnfDual (andGate clauses) from rfl] at hc
      change c ∈ Circuits.CnfDnf.dnfClauses
        (UnboundedFanInFormula.orGate (clauses.map dualClause)) at hc
      simp only [Circuits.CnfDnf.dnfClauses, List.mem_map] at hc
      obtain ⟨gate, hgate, rfl⟩ := hc
      obtain ⟨c', hc', rfl⟩ := hgate
      have hc'or : isOrOfInputsOnly c' = true := List.all_eq_true.mp hcnf c' hc'
      cases c' with
      | inputGate a b => simp [isOrOfInputsOnly] at hc'or
      | constant a b => simp [isOrOfInputsOnly] at hc'or
      | notGate g => simp [isOrOfInputsOnly] at hc'or
      | andGate g => simp [isOrOfInputsOnly] at hc'or
      | orGate lits =>
          simp only [isOrOfInputsOnly] at hc'or
          -- dual DNF clause fst = lits.flatMap collect = original CNF clause fst (Nodup)
          have hdual : dualClause (orGate lits) = andGate (lits.map negLit) := rfl
          rw [hdual]
          change (((lits.map negLit).filterMap
              (fun lit => match lit with | inputGate i b => some (i, b) | _ => none)).map
              Prod.fst).Nodup
          have hfstdual : ((lits.map negLit).filterMap
                (fun lit => match lit with | inputGate i b => some (i, b) | _ => none)).map Prod.fst
              = (lits.map negLit).flatMap ufiCollectInputIndices := by
            refine clause_fst_eq_collect _ (fun i b => rfl) (lits.map negLit) ?_
            rw [List.all_eq_true]; intro x hx
            rw [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
            rw [isInput_negLit]; exact List.all_eq_true.mp hc'or y hy
          have hfstcnf : (lits.filterMap
                (fun lit => match lit with | inputGate i b => some (i, b) | _ => none)).map Prod.fst
              = lits.flatMap ufiCollectInputIndices :=
            clause_fst_eq_collect _ (fun i b => rfl) lits hc'or
          -- the original CNF clause for `orGate lits`
          have hcnfclause : (lits.filterMap
                (fun lit => match lit with | inputGate i b => some (i, b) | _ => none))
              ∈ Circuits.CnfDnf.cnfClauses (andGate clauses) := by
            simp only [Circuits.CnfDnf.cnfClauses, List.mem_map]
            exact ⟨orGate lits, hc', rfl⟩
          have hndclause := hnd _ hcnfclause
          rw [hfstcnf] at hndclause
          rw [hfstdual, flatMap_map_negLit_collect]
          exact hndclause

end RestrictRekeyProper

open UnboundedFanInFormula in
/- **Round-0 eval composition.** With the live/dead split produced by
   `exists_assembled_restriction`, evaluating the original formula on the
   assembled input equals evaluating its restrict-and-rekeyed image
   (rekey `φ i = rank of i in live₀`) on the live bits. The dead-side
   faithfulness is supplied by `exists_assembled_restriction`; the live
   side is `assembleInput_at_live`. -/
lemma round_zero_restrict_rekey_eval
    {n : Nat} {σ : OpenUnitIntervalQ} (ρ : AssignedRandomRestriction σ n)
    (live₀ : List Nat) (dead₀ : List Bool)
    (h_live_lt : ∀ v ∈ live₀, v < n)
    (h_live_nodup : live₀.Nodup)
    (h_card : dead₀.length + live₀.length = n)
    (h_live_eq : (live₀ : Multiset Nat) = ρ.starAssignment.val.val.val)
    (h_faithful : ∀ (liveBits : List Bool), liveBits.length = live₀.length →
        ∀ i b, randomRestrictionToMap n σ ρ i = some b →
          (assembleInput n live₀ liveBits dead₀)[i]? = some b)
    (φ : Nat → Nat)
    (hφrank : ∀ i j, live₀.findIdx? (· = i) = some j → φ i = j)
    (f : UnboundedFanInFormula) (hf : ufiLargestInput f < n)
    (liveBits : List Bool) (h_lb : liveBits.length = live₀.length) :
    ufiFormulaEval f (assembleInput n live₀ liveBits dead₀) =
      ufiFormulaEval
        (ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ f) liveBits := by
  apply ufiRestrictRekey_eval
  intro i hi
  have hi_lt : i < n := by
    have hle := mem_le_foldr_max hi
    unfold ufiLargestInput at hf
    omega
  have hmem_iff : i ∈ live₀ ↔ i ∈ ρ.starAssignment.val.val := by
    rw [← Multiset.mem_coe, h_live_eq, Finset.mem_val]
  have h_len : live₀.length = ρ.starAssignment.val.val.card := by
    have hc := congrArg Multiset.card h_live_eq
    simpa [Multiset.coe_card] using hc
  by_cases hmem : i ∈ live₀
  · -- live coordinate: restriction map is `none`, read through `φ`
    have hmem_set : i ∈ ρ.starAssignment.val.val := hmem_iff.mp hmem
    have h_none : randomRestrictionToMap n σ ρ i = none := by
      unfold randomRestrictionToMap mkAssignment
      rw [if_pos hmem_set]
    rw [h_none]
    rcases List.mem_iff_get.mp hmem with ⟨⟨j, hjlt⟩, hj_eq⟩
    have hj_get : live₀[j] = i := by simpa using hj_eq
    have hfind : live₀.findIdx? (· = i) = some j := by
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨hjlt, by simpa using hj_get, ?_⟩
      intro m hmj
      simp only [decide_eq_true_eq]
      intro hm_eq
      exact (Nat.ne_of_lt hmj)
        (List.Nodup.getElem_inj_iff h_live_nodup |>.mp (hm_eq.trans hj_get.symm))
    change (assembleInput n live₀ liveBits dead₀)[i]?
        = liveBits[φ i]?
    rw [hφrank i j hfind]
    exact assembleInput_at_live n live₀ liveBits dead₀ h_lb h_live_lt i hmem j hfind
  · -- dead coordinate: restriction map is `some b`, faithfully assembled
    have hmem_set : i ∉ ρ.starAssignment.val.val := fun h => hmem (hmem_iff.mpr h)
    have hcard_lt : (Finset.range i \ ρ.starAssignment.val.val).card < dead₀.length := by
      have h_sub : Finset.range i \ ρ.starAssignment.val.val
            ⊆ Finset.range n \ ρ.starAssignment.val.val :=
        Finset.sdiff_subset_sdiff (Finset.range_mono (le_of_lt hi_lt)) Finset.Subset.rfl
      have hi_in : i ∈ Finset.range n \ ρ.starAssignment.val.val :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hi_lt, hmem_set⟩
      have hi_notin : i ∉ Finset.range i \ ρ.starAssignment.val.val := by
        intro h
        exact absurd (Finset.mem_range.mp (Finset.mem_sdiff.mp h).1) (lt_irrefl i)
      have hssub : Finset.range i \ ρ.starAssignment.val.val
            ⊂ Finset.range n \ ρ.starAssignment.val.val :=
        ⟨h_sub, fun h => hi_notin (h hi_in)⟩
      have hcard_lt' := Finset.card_lt_card hssub
      have h_rn_eq : (Finset.range n \ ρ.starAssignment.val.val).card
            = n - ρ.starAssignment.val.val.card := by
        rw [Finset.card_sdiff_of_subset ρ.starAssignment.val.property,
            Finset.card_range]
      omega
    obtain ⟨b, hb⟩ : ∃ b, randomRestrictionToMap n σ ρ i = some b := by
      have hidx : (Finset.range i \ ρ.starAssignment.val.val).card
          < ρ.varAssignments.length := by
        have hlen_eq : dead₀.length = ρ.varAssignments.length := by
          have hns := ρ.non_starred_vars_fully_assigned
          omega
        rw [← hlen_eq]; exact hcard_lt
      refine ⟨ρ.varAssignments[(Finset.range i \ ρ.starAssignment.val.val).card], ?_⟩
      unfold randomRestrictionToMap mkAssignment
      rw [if_neg hmem_set, List.getElem?_eq_getElem hidx]
    rw [hb]
    exact h_faithful liveBits h_lb i b hb

/- ════════════════ Round-0 structural counting bounds ════════════════ -/

/- Generic monotonicity of a mapped `Nat`-sum. -/
lemma round_zero_list_sum_map_le {α : Type*} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/- The total circuit size of the extracted bottom layer never exceeds the
   circuit size of the whole formula (the bottoms are disjoint subtrees). -/
mutual
theorem extractBottomLayer_sum_ufiFormulaCircuitSize_le :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ((extractBottomLayer lvl start f).1.map ufiFormulaCircuitSize).sum
        ≤ ufiFormulaCircuitSize f
  | _, _, .inputGate _ _ => by unfold extractBottomLayer; simp
  | _, _, .constant _ _ => by unfold extractBottomLayer; simp
  | _, _, .notGate g => by unfold extractBottomLayer; simp
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp
      · simp only
        have hsum := extractBottomLayerList_sum_ufiFormulaCircuitSize_le (lvl - 1) start gates
        have hnc : ufiFormulaCircuitSize (UnboundedFanInFormula.andGate gates) =
            1 + (gates.map ufiFormulaCircuitSize).sum := by
          simp only [ufiFormulaCircuitSize, Nat.add_comm]
        omega
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp
      · simp only
        have hsum := extractBottomLayerList_sum_ufiFormulaCircuitSize_le (lvl - 1) start gates
        have hnc : ufiFormulaCircuitSize (UnboundedFanInFormula.orGate gates) =
            1 + (gates.map ufiFormulaCircuitSize).sum := by
          simp only [ufiFormulaCircuitSize, Nat.add_comm]
        omega

theorem extractBottomLayerList_sum_ufiFormulaCircuitSize_le :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      ((extractBottomLayerList lvl start gs).1.map ufiFormulaCircuitSize).sum
        ≤ (gs.map ufiFormulaCircuitSize).sum
  | _, _, [] => by unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      have h₁ := extractBottomLayer_sum_ufiFormulaCircuitSize_le lvl start g
      have h₂ := extractBottomLayerList_sum_ufiFormulaCircuitSize_le lvl
                  (extractBottomLayer lvl start g).2.2 gs
      omega
end

/- The number of clauses of a bottom's dualised DNF never exceeds that bottom's
   circuit size. -/
lemma toBottomDNF_dnfClauses_length_le (g : UnboundedFanInFormula)
    (hp : HasProperBottomsAt g 2) :
    (Circuits.CnfDnf.dnfClauses (toBottomDNF g)).length ≤ ufiFormulaCircuitSize g := by
  have hd := isDNF_toBottomDNF g hp
  have hs := ProperizeProto.dnfSize_le_circuit_size (toBottomDNF g) hd
  cases g with
  | inputGate x b => simp [toBottomDNF, Circuits.CnfDnf.dnfClauses]
  | constant b m => simp [toBottomDNF, Circuits.CnfDnf.dnfClauses]
  | notGate g => simp [HasProperBottomsAt] at hp
  | orGate terms => simpa [toBottomDNF, Circuits.CnfDnf.dnfClauses, dnfSize] using hs
  | andGate clauses =>
      unfold HasProperBottomsAt at hp
      rw [if_pos (le_refl 2)] at hp
      have hc := ProperizeProto.cnfSize_le_circuit_size
        (UnboundedFanInFormula.andGate clauses) hp.1
      rw [show toBottomDNF (UnboundedFanInFormula.andGate clauses) =
          cnfDual (UnboundedFanInFormula.andGate clauses) from rfl,
        cnfDual_clauses (UnboundedFanInFormula.andGate clauses) hp.1, List.length_map]
      simpa [cnfSize, cnfClauses] using hc

/- The number of wide clauses across the bottom-DNF list never exceeds the
   formula's circuit size. -/
lemma round_zero_wideClauses_le_ufiFormulaCircuitSize (t d : Nat) (circuit : UnboundedFanInFormula)
    (hproper : HasProperBottomsAt circuit d) :
    (FaninReduction.wideClauses t
        ((extractBottomLayer d 0 circuit).1.map toBottomDNF)).length
      ≤ ufiFormulaCircuitSize circuit := by
  set bottoms := (extractBottomLayer d 0 circuit).1 with hb
  have hbottom_proper := hasProperBottomsAt_of_mem_extractBottomLayer d 0 circuit hproper
  -- filter never increases length
  have h₁ : (FaninReduction.wideClauses t (bottoms.map toBottomDNF)).length
      ≤ ((bottoms.map toBottomDNF).flatMap Circuits.CnfDnf.dnfClauses).length := by
    unfold FaninReduction.wideClauses
    exact List.length_filter_le _ _
  -- flatMap length = sum of per-DNF clause counts
  have h₂ : ((bottoms.map toBottomDNF).flatMap Circuits.CnfDnf.dnfClauses).length
      = (bottoms.map (fun g => (Circuits.CnfDnf.dnfClauses (toBottomDNF g)).length)).sum := by
    have hgen : ∀ (l : List UnboundedFanInFormula),
        ((l.map toBottomDNF).flatMap Circuits.CnfDnf.dnfClauses).length
          = (l.map (fun g => (Circuits.CnfDnf.dnfClauses (toBottomDNF g)).length)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih =>
          simp only [List.map_cons, List.flatMap_cons, List.length_append,
            List.sum_cons, ih]
    exact hgen bottoms
  -- pointwise clause-count ≤ circuit-size
  have h₃ : (bottoms.map (fun g => (Circuits.CnfDnf.dnfClauses (toBottomDNF g)).length)).sum
      ≤ (bottoms.map ufiFormulaCircuitSize).sum :=
    round_zero_list_sum_map_le bottoms _ _ (fun g hg =>
      toBottomDNF_dnfClauses_length_le g (hbottom_proper g (hb ▸ hg)))
  -- bottoms' circuit-size sum ≤ whole circuit size
  have h₄ : (bottoms.map ufiFormulaCircuitSize).sum ≤ ufiFormulaCircuitSize circuit := by
    rw [hb]; exact extractBottomLayer_sum_ufiFormulaCircuitSize_le d 0 circuit
  omega

/-- **Round-0 fan-in reduction (preprocessing).**

    A general AC⁰ formula may have arbitrarily wide bottom AND/OR gates, so it
    need not initially satisfy `HasBottomFanInLE d _ t`. Round 0 applies one
    restriction before the uniform switching rounds and rebuilds the formula
    so that every surviving bottom gate has fan-in at most `t`.

    The density-dependent arithmetic is isolated in
    `FaninReduction.RoundZeroCalibration q n s`. A calibration supplies a
    legal restriction density retaining exactly `s` variables and proves that
    a literal survives with probability at most `q`. The concrete one-fifth,
    one-third, and two-fifths instances live in the corresponding
    `Parity.FaninReduction` and `Parity.HastadParityProof.Restriction` modules.

    The remaining hypotheses are the three quantitative budgets used by the
    structural proof:

    * `hcount_m` makes the first-moment bound for width-`> t` clauses less than
      one;
    * `h_bot_m` bounds the reconstructed formula's bottom switching-gate budget
      by `2^t`; and
    * `h_thresh_m` reserves enough of the `s` live variables for the later
      iterated switching collapse.

    The proof extracts the original bottom layer, converts each proper bottom
    to a DNF, and bounds the number of wide clauses by the circuit size. It
    then uses the calibration to obtain a project restriction killing every
    wide clause. That restriction is materialized as `live₀` and `dead₀`,
    applied to the entire formula, and the live coordinates are rekeyed to
    `[0, live₀.length)`. After simplifying constants, the proof packages the
    result as a `SwitchingRoundState` and establishes:

    * exact live-set cardinality `live₀.length = s`;
    * preservation of evaluation through `assembleInput`;
    * a leveled formula whose subtype already carries its input bound, together
      with constant-freeness, cleanliness, bottom fan-in at most `t`, and
      bottom budget below `2^t`; and
    * the live-variable threshold required by the subsequent switching rounds.

    Thus this theorem contains only density-neutral structural plumbing; the
    public calibrated wrappers merely instantiate `q`, `s`, and `cal`. -/
lemma exists_round_zero_fanIn_reduced_of_parameters_core
        {c k d n t s : Nat}
        (q : ℚ)
        (hd : 1 ≤ d)
        (h_two_le_t : 2 ≤ t)
        (hcount_m : (((c * n ^ k : ℕ) : ℚ) * q ^ (t + 1) < 1))
        (h_bot_m : c * n ^ k < 2 ^ t)
        (h_thresh_m : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ s)
        (cal : FaninReduction.RoundZeroCalibration q n s)
        (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k d) :
  ∃ (live₀ : List Nat)
    (_h_live₀_lt : ∀ v ∈ live₀, v < n)
    (_h_live₀_nodup : live₀.Nodup)
    (dead₀ : List Bool)
    (c' k' : Nat)
    (state : SwitchingRoundState live₀.length c' k' d t)
    (_h_thresh : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ live₀.length),
    ∀ (liveBits : List Bool), liveBits.length = live₀.length →
      ufiFormulaEval formula.val (assembleInput n live₀ liveBits dead₀) =
      ufiFormulaEval state.circuit.val liveBits := by
  have h_inputs_bound : ufiLargestInput formula.val < n := formula.property.1
  have h_proper : HasProperBottomsAt formula.val d :=
    Circuits.Leveling.isProperlyLeveled_imp_proper _ _ formula.property.2.2.2.2
  -- The bottom layer of `formula` and its per-bottom dualised DNFs.
  set bottoms := (extractBottomLayer d 0 formula.val).1 with hbottoms
  set dnfs := bottoms.map toBottomDNF with hdnfs
  -- Shape facts of each bottom (`HasProperBottomsAt _ 2`) and var-bounds.
  have hbottom_proper := hasProperBottomsAt_of_mem_extractBottomLayer d 0 formula.val h_proper
  have hbottom_var : ∀ g ∈ bottoms, ∀ x ∈ ufiCollectInputIndices g, x < n := by
    intro g hg x hx
    have hsub := extractBottomLayer_bottoms_collect_subset d 0 formula.val g hg x hx
    have hle := mem_le_foldr_max hsub
    have hlarge : ufiLargestInput formula.val < n := h_inputs_bound
    unfold ufiLargestInput at hlarge; omega
  -- Keystone hypotheses on the dualised bottom DNFs.
  have hdnf : ∀ dd ∈ dnfs, isDNF dd = true := by
    intro dd hdd; rw [hdnfs] at hdd
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hdd
    exact isDNF_toBottomDNF g (hbottom_proper g hg)
  have hnd : ∀ dd ∈ dnfs, ∀ c' ∈ Circuits.CnfDnf.dnfClauses dd,
      (c'.map Prod.fst).Nodup := by
    intro dd hdd; rw [hdnfs] at hdd
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hdd
    exact toBottomDNF_clause_nodup g (hbottom_proper g hg)
  have hvar : ∀ dd ∈ dnfs, ∀ c' ∈ Circuits.CnfDnf.dnfClauses dd,
      ∀ p ∈ c', p.1 < n := by
    intro dd hdd; rw [hdnfs] at hdd
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hdd
    exact toBottomDNF_clause_var_lt g n (hbottom_proper g hg) (hbottom_var g hg)
  -- The wide-clause first-moment budget `(#wideClauses)·q^(t+1) < 1`.
  have hwc_le : (FaninReduction.wideClauses t dnfs).length ≤ c * n ^ k := by
    have h := round_zero_wideClauses_le_ufiFormulaCircuitSize t d formula.val h_proper
    exact le_trans h formula.property.2.2.1
  have hcount : ((FaninReduction.wideClauses t dnfs).length : ℚ) * q ^ (t + 1) < 1 := by
    have hcast : ((FaninReduction.wideClauses t dnfs).length : ℚ) ≤ ((c * n ^ k : ℕ) : ℚ) := by
      exact_mod_cast hwc_le
    have hpos : (0 : ℚ) ≤ q ^ (t + 1) :=
      pow_nonneg (le_of_lt cal.q_pos) _
    calc ((FaninReduction.wideClauses t dnfs).length : ℚ) * q ^ (t + 1)
        ≤ ((c * n ^ k : ℕ) : ℚ) * q ^ (t + 1) :=
          mul_le_mul_of_nonneg_right hcast hpos
      _ < 1 := hcount_m
  -- Apply the banked Round-0 keystone: a restriction killing all wide bottoms.
  obtain ⟨σ, ρ, hcard, hwidth⟩ :=
    cal.exists_restriction_width_le_card t dnfs hdnf hnd hvar hcount
  -- Materialise the restriction as an `assembleInput` map on `live₀`/`dead₀`.
  obtain ⟨live₀, h_live_lt, h_live_nodup, dead₀, h_card, h_live_eq, h_faithful⟩ :=
    exists_assembled_restriction ρ
  have h_faithful' :
      ∀ (liveBits : List Bool), liveBits.length = live₀.length →
        ∀ i b, randomRestrictionToMap n σ ρ i = some b →
          (assembleInput n live₀ liveBits dead₀)[i]? = some b := by
    simpa [randomRestrictionToMap] using h_faithful
  -- `live₀` has exactly `s` coordinates.
  have h_live_len : live₀.length = s := by
    have hc := congrArg Multiset.card h_live_eq
    rw [Multiset.coe_card] at hc
    rw [hc]; exact hcard
  have hpos_len : 0 < live₀.length := by
    rw [h_live_len]
    have : 0 < (20 * t) ^ (d - 2) * (20 * t * (t + 1)) := by positivity
    omega
  -- Rank function for the live coordinates (default `i` keeps it injective
  -- on the whole `asgn = none` set, including out-of-range indices).
  set φ : Nat → Nat := fun i => (live₀.findIdx? (· = i)).getD i with hφdef
  -- Canonical rank witness for each live index.
  have h_rank_witness : ∀ i ∈ live₀,
      ∃ j, live₀.findIdx? (· = i) = some j ∧ j < live₀.length := by
    intro i hi_live
    rcases List.mem_iff_get.mp hi_live with ⟨⟨j, hjlt⟩, hj_eq⟩
    have hj_get : live₀[j] = i := by simpa using hj_eq
    refine ⟨j, ?_, hjlt⟩
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hjlt, by simpa using hj_get, ?_⟩
    intro k hkj
    simp only [decide_eq_true_eq]
    intro hk_eq
    have heq_get : live₀[k]'(lt_trans hkj hjlt) = live₀[j] := by rw [hk_eq, hj_get]
    exact (Nat.ne_of_lt hkj) (List.Nodup.getElem_inj_iff h_live_nodup |>.mp heq_get)
  -- `φ` agrees with the rank on live indices.
  have hφrank : ∀ i j, live₀.findIdx? (· = i) = some j → φ i = j := by
    intro i j h; rw [hφdef]; simp [h]
  -- `asgn = none` at `i < n` forces `i ∈ live₀`.
  have h_none_mem : ∀ i, i < n → randomRestrictionToMap n σ ρ i = none → i ∈ live₀ := by
    intro i hi_lt hnone
    have hmk : mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = none := hnone
    have hin : i ∈ ρ.starAssignment.val.val :=
      mkAssignment_none_imp_mem ρ.starAssignment.val.val ρ.varAssignments n
        ρ.starAssignment.val.property ρ.non_starred_vars_fully_assigned i hi_lt hmk
    have hmem : i ∈ (live₀ : Multiset Nat) := by
      rw [h_live_eq]; exact Finset.mem_val.mpr hin
    exact Multiset.mem_coe.mp hmem
  -- Global injectivity of `φ` on the `asgn = none` set.
  have hφinj : ∀ i j, randomRestrictionToMap n σ ρ i = none →
      randomRestrictionToMap n σ ρ j = none → φ i = φ j → i = j := by
    intro i j hi hj hij
    have h_len_le_n : live₀.length ≤ n := by rw [h_live_len]; omega
    by_cases hil : i ∈ live₀
    · obtain ⟨ri, hri_eq, hri_lt⟩ := h_rank_witness i hil
      have hφi : φ i = ri := by rw [hφdef]; simp [hri_eq]
      by_cases hjl : j ∈ live₀
      · obtain ⟨rj, hrj_eq, hrj_lt⟩ := h_rank_witness j hjl
        have hφj : φ j = rj := by rw [hφdef]; simp [hrj_eq]
        have hrij : ri = rj := by rw [hφi, hφj] at hij; exact hij
        have hgi : live₀[ri]'hri_lt = i := by
          simpa using (List.findIdx?_eq_some_iff_getElem.mp hri_eq).2.1
        have hgj : live₀[rj]'hrj_lt = j := by
          simpa using (List.findIdx?_eq_some_iff_getElem.mp hrj_eq).2.1
        rw [← hgi, ← hgj]; congr 1
      · exfalso
        have hjnone : live₀.findIdx? (· = j) = none := by
          rcases hf : live₀.findIdx? (· = j) with _ | r
          · rfl
          · exfalso
            obtain ⟨hrlt, hget, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            have hjmem : live₀[r]'hrlt = j := by simpa using hget
            exact hjl (hjmem ▸ List.getElem_mem hrlt)
        have hφj : φ j = j := by rw [hφdef]; simp [hjnone]
        have hjge : n ≤ j := by
          by_contra hlt; push Not at hlt
          exact hjl (h_none_mem j hlt hj)
        rw [hφi, hφj] at hij; omega
    · by_cases hjl : j ∈ live₀
      · exfalso
        have hinone : live₀.findIdx? (· = i) = none := by
          rcases hf : live₀.findIdx? (· = i) with _ | r
          · rfl
          · exfalso
            obtain ⟨hrlt, hget, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            have himem : live₀[r]'hrlt = i := by simpa using hget
            exact hil (himem ▸ List.getElem_mem hrlt)
        have hφi : φ i = i := by rw [hφdef]; simp [hinone]
        obtain ⟨rj, hrj_eq, hrj_lt⟩ := h_rank_witness j hjl
        have hφj : φ j = rj := by rw [hφdef]; simp [hrj_eq]
        have hige : n ≤ i := by
          by_contra hlt; push Not at hlt
          exact hil (h_none_mem i hlt hi)
        rw [hφi, hφj] at hij; omega
      · have hinone : live₀.findIdx? (· = i) = none := by
          rcases hf : live₀.findIdx? (· = i) with _ | r
          · rfl
          · exfalso
            obtain ⟨hrlt, hget, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            have himem : live₀[r]'hrlt = i := by simpa using hget
            exact hil (himem ▸ List.getElem_mem hrlt)
        have hjnone : live₀.findIdx? (· = j) = none := by
          rcases hf : live₀.findIdx? (· = j) with _ | r
          · rfl
          · exfalso
            obtain ⟨hrlt, hget, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
            have hjmem : live₀[r]'hrlt = j := by simpa using hget
            exact hjl (hjmem ▸ List.getElem_mem hrlt)
        have hφi : φ i = i := by rw [hφdef]; simp [hinone]
        have hφj : φ j = j := by rw [hφdef]; simp [hjnone]
        rw [hφi, hφj] at hij; exact hij
  -- The rebuilt Round-0 formula.
  set c₀Val : UnboundedFanInFormula :=
    simplifyConstants (ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ formula.val)
    with h_c₀
  -- Useful structural facts on `formula`.
  have hstrict : IsAlternatingAndLeveledAt formula.val d :=
    Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2
  have hnn_circ : IsNotGateFree formula.val := isNotGateFree_of_strictly_leveled formula.val d hstrict
  have hnn_rk : IsNotGateFree (ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ formula.val) :=
    isNotGateFree_ufiRestrictRekey _ φ formula.val hnn_circ
  -- inputGate-bound on `c₀Val`.
  have hrk_ib : ufiLargestInput
      (ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ formula.val) < live₀.length := by
    apply ufiRestrictRekey_ufiLargestInput_lt _ φ formula.val live₀.length _ hpos_len
    intro i hi hnone
    have hi_lt : i < n := by
      have hle := mem_le_foldr_max hi
      have hlarge : ufiLargestInput formula.val < n := h_inputs_bound
      unfold ufiLargestInput at hlarge; omega
    obtain ⟨j, hj_eq, hjlt⟩ := h_rank_witness i (h_none_mem i hi_lt hnone)
    rw [hφrank i j hj_eq]; exact hjlt
  have h_c_ib : ufiLargestInput c₀Val < live₀.length :=
    simplifyConstants_ufiLargestInput_lt hrk_ib
  -- Eval composition: `formula ∘ assemble = c₀Val`.
  have h_c_eval : ∀ (liveBits : List Bool), liveBits.length = live₀.length →
      ufiFormulaEval formula.val (assembleInput n live₀ liveBits dead₀) =
      ufiFormulaEval c₀Val liveBits := by
    intro liveBits hlb
    rw [round_zero_restrict_rekey_eval ρ live₀ dead₀ h_live_lt h_live_nodup h_card
          h_live_eq h_faithful' φ hφrank formula.val h_inputs_bound liveBits hlb]
    exact (simplifyConstants_eval _ liveBits).symm
  -- Depth bound.
  have h_c_depth : ufiFormulaDepth c₀Val ≤ d := by
    rcases simplifyConstants_eq_empty_or_depth_le
        (ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ formula.val) hnn_rk
      with hempty | hle
    · have heq : ufiFormulaDepth c₀Val = 1 := by
        rcases hempty with he | he <;> rw [h_c₀, he] <;> simp [ufiFormulaDepth, List.foldr_nil]
      omega
    · rw [ufiRestrictRekey_depth] at hle
      exact le_trans (by rw [h_c₀]; exact hle) formula.property.2.1
  -- The downstream switching invariant is the active-gate budget, not this
  -- carrier's polynomial coefficient.  Package the finite rebuilt formula
  -- with its exact size as a degree-zero polynomial.
  have h_c_size : ufiFormulaCircuitSize c₀Val ≤
      ufiFormulaCircuitSize c₀Val * live₀.length ^ 0 := by simp
  -- Strict-leveled / proper / constant-free / clean preservation.
  have h_c_strict : IsAlternatingAndLeveledAt c₀Val d := by
    rw [h_c₀]
    exact isAlternatingAndLeveledAt_simplifyConstants _ d
      (isAlternatingAndLeveledAt_ufiRestrictRekey _ φ formula.val d hstrict)
  have h_c_proper : HasProperBottomsAt c₀Val d := by
    rw [h_c₀]
    exact hasProperBottomsAt_simplifyConstants_ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ hφinj
      formula.val d h_proper
  have h_c_cf : IsConstantFree c₀Val := by rw [h_c₀]; exact isConstantFree_simplifyConstants _
  have h_c_clean : IsCleanFormula c₀Val := by
    rw [h_c₀]; exact isCleanFormula_simplifyConstants _ hnn_rk
  -- Bottom fan-in `≤ t` on `c₀Val`.
  have hcnf : ∀ g ∈ (extractBottomLayer d 0 formula.val).1, ∀ clauses,
      g = UnboundedFanInFormula.andGate clauses →
      clauses.all isOrOfInputsOnly = true :=
    fun g hg => all_isOrOfInputsOnly_of_hasProperBottomsAt_andGate g (hbottom_proper g hg)
  have hbound : ∀ g ∈ (extractBottomLayer d 0 formula.val).1,
      dnfWidth (simpleRestrictDNF (randomRestrictionToMap n σ ρ) (toBottomDNF g)) ≤ t := by
    intro g hg
    exact hwidth (toBottomDNF g) (by rw [hdnfs]; exact List.mem_map.mpr ⟨g, hg, rfl⟩)
  have h_rbw : HasRestrictionBottomWidthLE (randomRestrictionToMap n σ ρ) formula.val d t :=
    hasRestrictionBottomWidthLE_of_bottom_bounds (randomRestrictionToMap n σ ρ) t formula.val d
      h_proper hcnf hbound
  have h_pbw : HasProperBottomWidthLE c₀Val d t := by
    rw [h_c₀]
    exact hasProperBottomWidthLE_simplifyConstants_ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ t
      formula.val d h_proper h_rbw
  have h_c_bfi : HasBottomFanInLE d c₀Val t :=
    extractBottomLayer_bottoms_fanIn_le t (by omega) d 0 c₀Val h_pbw
  -- Bottom count `< 2^t`.
  have h_c_bot : switchingGateBudget d c₀Val < 2 ^ t := by
    have hsimp := simplifyConstants_switchingGateBudget_le d
      (ufiRestrictRekey (randomRestrictionToMap n σ ρ) φ formula.val)
    rw [← h_c₀] at hsimp
    have hrk := ufiRestrictRekey_switchingGateBudget
      (randomRestrictionToMap n σ ρ) φ d formula.val
    rw [hrk] at hsimp
    exact lt_of_le_of_lt hsimp
      (lt_of_le_of_lt (switchingGateBudget_le_ufiFormulaCircuitSize d formula.val)
        (lt_of_le_of_lt formula.property.2.2.1 h_bot_m))
  -- Iterated-switching threshold.
  have h_c_thresh : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ live₀.length := by
    rw [h_live_len]; exact h_thresh_m
  -- Package the result.
  exact ⟨live₀, h_live_lt, h_live_nodup, dead₀,
    ufiFormulaCircuitSize c₀Val, 0,
    ⟨⟨c₀Val, h_c_ib, h_c_depth, h_c_size, hd,
        Circuits.Leveling.isProperlyLeveled_of_strict_proper _ _ h_c_strict h_c_proper⟩,
      h_c_cf, h_c_clean, h_c_bfi, h_c_bot⟩,
    h_c_thresh, h_c_eval⟩

/-- Density-neutral composition of calibrated Round 0 with the iterated
switching collapse. -/
lemma exists_good_restriction_reduces_ac0_to_narrow_dnf_of_parameters_core
      {c k d n t s : Nat}
      (q : ℚ)
      (hd : 1 ≤ d)
      (ht : 2 ≤ t)
      (hcount_m : (((c * n ^ k : ℕ) : ℚ) * q ^ (t + 1) < 1))
      (h_bot_m : c * n ^ k < 2 ^ t)
      (h_thresh_m : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ s)
      (cal : FaninReduction.RoundZeroCalibration q n s)
      (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k d) :
  ∃ (live : List Nat)
    (deadBits : List Bool)
    (_h_live_lt : ∀ v ∈ live, v < n)
    (_h_live_nodup : live.Nodup)
    (_h_card : deadBits.length + live.length = n)
    (g : UnboundedFanInProperDNF live.length),
    dnfWidth g.val < live.length ∧
    ∀ (liveBits : List Bool), liveBits.length = live.length →
      ufiFormulaEval formula.val
          (assembleInput n live liveBits deadBits) =
      ufiFormulaEval g.val liveBits := by
  -- Compose Round-0 fan-in reduction (producing a complete switching state)
  -- with the state-consuming iterated switching depth-collapse lemma.
  -- Round 0 restricts to the calibrated number of live variables.
  obtain ⟨live₀, h_live₀_lt, h_live₀_nodup, dead₀,
          c', k', state, h_thresh, h_eval₀⟩ :=
    exists_round_zero_fanIn_reduced_of_parameters_core
      q hd ht hcount_m h_bot_m h_thresh_m cal formula
  -- Iterated switching collapse from the fan-in-reduced round state.
  obtain ⟨live₁, h_live₁_lt, h_live₁_nodup, h_live₁_big,
          dead₁, w, hw, g, hgw, h_eval₁⟩ :=
    exists_iterated_switching_depth_collapse hd state ht h_thresh
  -- Compose the two restrictions into one on the original `n`.
  obtain ⟨live, h_live_lt, h_live_nodup, deadBits,
          h_card, h_len_eq, h_assemble⟩ :=
    exists_composed_collapse n live₀ h_live₀_lt h_live₀_nodup
      dead₀ live₁ h_live₁_lt h_live₁_nodup
      dead₁
  have h_live_pos : 0 < live.length := by rw [h_len_eq]; omega
  have hg_bound : ufiLargestInput g.val < live.length := by
    rw [h_len_eq]
    exact g.property.1
  obtain ⟨hdnf', hne', hnd', hbnd', heval'⟩ :=
    ProperizeProto.properize_narrow_dnf live.length h_live_pos g.val g.property.2 hg_bound
  let g' : UnboundedFanInProperDNF live.length :=
    ⟨ProperizeProto.properizeDNF g.val, hbnd', hdnf', hne', hnd'⟩
  refine ⟨live, deadBits, h_live_lt, h_live_nodup, h_card, g', ?_, ?_⟩
  · change dnfWidth (ProperizeProto.properizeDNF g.val) < live.length
    have hle := ProperizeProto.properizeDNF_width_le g.val g.property.2
    have hgw' : dnfWidth g.val < live.length := by
      rw [h_len_eq]
      exact lt_of_le_of_lt hgw hw
    omega
  · intro liveBits h_len
    -- Eval chain: original eval on `assemble n live liveBits dead`
    --   = original on `assemble n live₀ (assemble live₀.length live₁
    --     liveBits dead₁) dead₀`            (h_assemble)
    --   = c₀ on `assemble live₀.length live₁ liveBits dead₁`  (h_eval₀)
    --   = g on liveBits                       (h_eval₁).
    have hlb₁ : liveBits.length = live₁.length := by rw [h_len, h_len_eq]
    rw [h_assemble liveBits hlb₁]
    rw [h_eval₀ (assembleInput live₀.length live₁ liveBits dead₁)
          (length_assembleInput live₀.length live₁ liveBits dead₁)]
    exact (h_eval₁ liveBits hlb₁).trans (heval' liveBits h_len).symm

end Circuits.HastadParity
