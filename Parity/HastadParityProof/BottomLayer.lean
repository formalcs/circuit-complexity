/-
  Bottom-layer extraction and active-frontier accounting.

  This module is part of the Håstad parity lower-bound proof.
-/

import Formulas.Basic
import Formulas.Eval
import Formulas.CircuitFamilies
import Formulas.CnfDnf.CnfDnfBasic
import Formulas.CnfDnf.CnfDnfFamilies
import Formulas.CnfDnf.SwitchingLemmaBasic
import Formulas.CnfDnf.SwitchingLemma
import Formulas.CnfDnf.ParityDNF
import Parity.ParityProperties
import Parity.Properize
import Parity.Leveling.ProperBottoms
import Parity.Leveling.SimplifyConstantsCore
import Formulas.UFITransformations
import Lists.ListLemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Find

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

inductive BottomFormula (n : Nat) : Type
  | dnf (f : UnboundedFanInProperDNF n) : BottomFormula n
  | cnf (f : UnboundedFanInProperCNF n) : BottomFormula n

def BottomFormula.polarity {n : Nat} : BottomFormula n → Bool
  | .dnf _ => true
  | .cnf _ => false

def BottomFormula.toUFI {n : Nat} : BottomFormula n → UnboundedFanInFormula
  | .dnf f => f.val
  | .cnf f => f.val

def BottomFormula.width {n : Nat} : BottomFormula n → Nat
  | .dnf f => dnfWidth f.val
  | .cnf f => cnfWidth f.val

/-! ### Bottom-layer extraction helpers for `extractBottomLayer`.

    These helpers walk a strictly-leveled UFI formula and split it into
    its top depth-`(d-1)` skeleton (with placeholder `inputGate`s) and its
    bottom depth-≤-`2` subformulas (each wrapped as a `BottomFormula n`).
-/

/- Walk a UFI formula at level `lvl`, extracting subformulas at
    level ≤ 2 as "bottom" leaves and replacing each with a fresh
    placeholder `inputGate start false`.  Threaded `start` index increments
    per extracted leaf, so placeholder indices are unique.

    Returns the extracted bottoms, the skeleton, and the next unused index.
    Because Lean
    parses `A × B × C` as the right-associated product `A × (B × C)`, the
    three result components are accessed as follows:

    * `.1` contains the bottom subformulas in left-to-right order;
    * `.2.1` is the top skeleton in which every
      extracted bottom has been replaced by a fresh positive `inputGate`;
    * `.2.2` is the first unused placeholder index after the traversal,
      equal to `start + (extractBottomLayer lvl start f).1.length`.

    For non-AND/OR formulas (e.g., bare `inputGate` or `constant`) found
    above level 2, treats them as already-bottom leaves. -/
mutual

def extractBottomLayer :
    Nat → Nat → UnboundedFanInFormula →
    List UnboundedFanInFormula × UnboundedFanInFormula × Nat
  | lvl, start, .andGate gates =>
      if lvl ≤ 2 then
        ([.andGate gates], .inputGate start false, start + 1)
      else
        let r := extractBottomLayerList (lvl - 1) start gates
        (r.1, .andGate r.2.1, r.2.2)
  | lvl, start, .orGate gates =>
      if lvl ≤ 2 then
        ([.orGate gates], .inputGate start false, start + 1)
      else
        let r := extractBottomLayerList (lvl - 1) start gates
        (r.1, .orGate r.2.1, r.2.2)
  | _, start, other =>
      ([other], .inputGate start false, start + 1)

def extractBottomLayerList :
    Nat → Nat → List UnboundedFanInFormula →
    List UnboundedFanInFormula × List UnboundedFanInFormula × Nat
  | _, start, [] => ([], [], start)
  | lvl, start, g :: gs =>
      let r₁ := extractBottomLayer lvl start g
      let r₂ := extractBottomLayerList lvl r₁.2.2 gs
      (r₁.1 ++ r₂.1, r₁.2.1 :: r₂.2.1, r₂.2.2)

end

/-! ### Gate budget for the active switching frontier

`extractBottomLayer` is a semantic decomposition, so its raw list also
contains bare input leaves.  Those leaves need rekeying when a restriction is
applied, but they are not gates and must not be charged to the union bound.

`switchingGateBudget lvl f` counts the nonconstant gates in the part of `f`
visible down to level `2`, charging a nonempty bottom AND/OR subformula once
and not looking inside it.  Empty AND/OR gates and `constant` constructors are
semantic constants, so they consume no switching budget. -/
def IsSwitchingGate : UnboundedFanInFormula → Prop
  | .andGate (_ :: _) => True
  | .orGate (_ :: _) => True
  | _ => False

instance : DecidablePred IsSwitchingGate
  | .andGate [] | .orGate [] | .inputGate _ _ | .constant _ _ | .notGate _ =>
      isFalse (by simp [IsSwitchingGate])
  | .andGate (_ :: _) | .orGate (_ :: _) => isTrue (by simp [IsSwitchingGate])

@[simp] theorem decide_isSwitchingGate :
    ∀ f, decide (IsSwitchingGate f) =
      match f with
      | .andGate (_ :: _) | .orGate (_ :: _) => true
      | _ => false
  | .inputGate _ _ => rfl
  | .constant _ _ => rfl
  | .notGate _ => rfl
  | .andGate [] => rfl
  | .andGate (_ :: _) => rfl
  | .orGate [] => rfl
  | .orGate (_ :: _) => rfl

/-- Package a genuine extracted switching gate as a polarity-tagged bottom.

    The caller must show that `g` is a nonempty
    AND/OR gate, that its inputs fit in the ambient arity, and that the
    depth-two properness invariant holds.  Those certificates select the
    CNF/DNF branch directly, and the resulting `BottomFormula` is
    structurally the original gate. -/
def switchingGateBottom (n : Nat) (g : UnboundedFanInFormula)
    (h_gate : IsSwitchingGate g) (h_inputs : ufiLargestInput g < n)
    (h_proper : HasProperBottomsAt g 2) : BottomFormula n := by
  cases g with
  | inputGate i b => simp [IsSwitchingGate] at h_gate
  | constant b label => simp [IsSwitchingGate] at h_gate
  | notGate g => simp [IsSwitchingGate] at h_gate
  | andGate gates =>
      have hp : IsProperCNF (.andGate gates) := by
        simpa only [HasProperBottomsAt, if_pos (by omega : 2 ≤ 2), IsProperCNF]
          using h_proper
      exact .cnf ⟨.andGate gates, h_inputs, hp⟩
  | orGate gates =>
      have hp : IsProperDNF (.orGate gates) := by
        simpa only [HasProperBottomsAt, if_pos (by omega : 2 ≤ 2), IsProperDNF]
          using h_proper
      exact .dnf ⟨.orGate gates, h_inputs, hp⟩

/-- The proof-directed switching-gate constructor changes only the type: its
    underlying UFI formula is definitionally the gate supplied by the caller. -/
@[simp] theorem switchingGateBottom_toUFI
    (n : Nat) (g : UnboundedFanInFormula)
    (h_gate : IsSwitchingGate g) (h_inputs : ufiLargestInput g < n)
    (h_proper : HasProperBottomsAt g 2) :
    (switchingGateBottom n g h_gate h_inputs h_proper).toUFI = g := by
  cases g <;>
    simp [switchingGateBottom, IsSwitchingGate, BottomFormula.toUFI] at h_gate ⊢

def switchingGateBudget : Nat → UnboundedFanInFormula → Nat
  | _, .inputGate _ _ => 0
  | _, .constant _ _ => 0
  | lvl, .notGate g => switchingGateBudget lvl g + 1
  | _, .andGate [] => 0
  | _, .orGate [] => 0
  | lvl, .andGate gates =>
      if lvl ≤ 2 then 1
      else (gates.map (switchingGateBudget (lvl - 1))).sum + 1
  | lvl, .orGate gates =>
      if lvl ≤ 2 then 1
      else (gates.map (switchingGateBudget (lvl - 1))).sum + 1

/-- The active switching-gate budget is bounded by ordinary circuit size. -/
theorem switchingGateBudget_le_ufiFormulaCircuitSize :
    ∀ (lvl : Nat) (f : UnboundedFanInFormula),
      switchingGateBudget lvl f ≤ ufiFormulaCircuitSize f
  | _, .inputGate _ _ => by simp [switchingGateBudget, ufiFormulaCircuitSize]
  | _, .constant _ _ => by simp [switchingGateBudget, ufiFormulaCircuitSize]
  | lvl, .notGate g => by
      simp only [switchingGateBudget, ufiFormulaCircuitSize]
      exact Nat.add_le_add_right (switchingGateBudget_le_ufiFormulaCircuitSize lvl g) 1
  | lvl, .andGate [] => by simp [switchingGateBudget, ufiFormulaCircuitSize]
  | lvl, .andGate (g :: gates) => by
      simp only [switchingGateBudget, ufiFormulaCircuitSize]
      split_ifs with h
      · omega
      · apply Nat.add_le_add_right
        apply List.sum_le_sum
        intro x hx
        exact switchingGateBudget_le_ufiFormulaCircuitSize (lvl - 1) x
  | lvl, .orGate [] => by simp [switchingGateBudget, ufiFormulaCircuitSize]
  | lvl, .orGate (g :: gates) => by
      simp only [switchingGateBudget, ufiFormulaCircuitSize]
      split_ifs with h
      · omega
      · apply Nat.add_le_add_right
        apply List.sum_le_sum
        intro x hx
        exact switchingGateBudget_le_ufiFormulaCircuitSize (lvl - 1) x

/-- Only genuine AND/OR members of the semantic bottom extraction consume
    switching-lemma union-bound budget. -/
def extractedBottomGates (lvl start : Nat)
    (f : UnboundedFanInFormula) : List UnboundedFanInFormula :=
  (extractBottomLayer lvl start f).1.filter IsSwitchingGate

mutual

theorem extractedBottomGates_length_le_budget :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      (extractedBottomGates lvl start f).length ≤ switchingGateBudget lvl f
  | _, _, .inputGate _ _ => by
      simp [extractedBottomGates, extractBottomLayer, switchingGateBudget,
        decide_isSwitchingGate]
  | _, _, .constant _ _ => by
      simp [extractedBottomGates, extractBottomLayer, switchingGateBudget,
        decide_isSwitchingGate]
  | lvl, start, .notGate g => by
      simp [extractedBottomGates, extractBottomLayer, switchingGateBudget,
        decide_isSwitchingGate]
  | lvl, start, .andGate [] => by
      by_cases h : lvl ≤ 2 <;>
        simp [extractedBottomGates, extractBottomLayer, extractBottomLayerList,
          switchingGateBudget, decide_isSwitchingGate, h]
  | lvl, start, .andGate (g :: gates) => by
      simp only [extractedBottomGates, extractBottomLayer, switchingGateBudget]
      by_cases h : lvl ≤ 2
      · simp [h, decide_isSwitchingGate]
      · simp only [if_neg h]
        exact le_trans
          (extractedBottomGates_list_length_le_budget (lvl - 1) start (g :: gates))
          (Nat.le_add_right _ 1)
  | lvl, start, .orGate [] => by
      by_cases h : lvl ≤ 2 <;>
        simp [extractedBottomGates, extractBottomLayer, extractBottomLayerList,
          switchingGateBudget, decide_isSwitchingGate, h]
  | lvl, start, .orGate (g :: gates) => by
      simp only [extractedBottomGates, extractBottomLayer, switchingGateBudget]
      by_cases h : lvl ≤ 2
      · simp [h, decide_isSwitchingGate]
      · simp only [if_neg h]
        exact le_trans
          (extractedBottomGates_list_length_le_budget (lvl - 1) start (g :: gates))
          (Nat.le_add_right _ 1)

theorem extractedBottomGates_list_length_le_budget :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      ((extractBottomLayerList lvl start gates).1.filter
        IsSwitchingGate).length ≤
        (gates.map (switchingGateBudget lvl)).sum
  | _, _, [] => by simp [extractBottomLayerList]
  | lvl, start, g :: gs => by
      simp only [extractBottomLayerList, List.filter_append, List.length_append,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (by simpa [extractedBottomGates] using
          extractedBottomGates_length_le_budget lvl start g)
        (extractedBottomGates_list_length_le_budget lvl
          (extractBottomLayer lvl start g).2.2 gs)

end

/-! `IsConstantFree` is required by the strict bottom-layer substitution
    contract because `HasProperBottomsAt` treats a bare `constant` as
    vacuously proper.  The shared `buildFormsWith` recursion handles the
    following splice cases:

    * a depth-≤2 AND/OR bottom is replaced by the requested-polarity proper
      form supplied by `exists_bottom_sub_proper_for_polarity`;
    * an `inputGate` at the splice base is represented by
      `litToProperCNF`/`litToProperDNF`;
    * an `inputGate` above the splice remains a bare rekeyed input.

    It also preserves a source `constant` explicitly.  constant-tolerant
    readiness accepts that result and lets the common `simplifyConstants`
    boundary absorb it.  The strict predicate `IsSubstitutionProperForm`,
    however, accepts only a polarity-matching proper CNF/DNF and has no bare
    constant alternative.  Therefore its proofs must make the `constant`
    branch unreachable: `HasProperBottomsAt` rules out `notGate`, while
    `IsConstantFree` rules out `constant`. -/

/- Every bottom extracted from a constant-free formula is itself
    constant-free.  In particular none of the extracted bottoms is a bare
    `constant`, so the producer's `sub` map only ever has to represent
    proper AND/OR gates and `inputGate` literals. -/
mutual
theorem isConstantFree_of_mem_extractBottomLayer :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      IsConstantFree f →
      ∀ g ∈ (extractBottomLayer lvl start f).1, IsConstantFree g
  | lvl, start, .andGate gates, h_cf => by
      simp only [IsConstantFree] at h_cf
      unfold extractBottomLayer
      split_ifs with h
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg; simp only [IsConstantFree]; exact h_cf
      · simp only
        exact isConstantFree_of_mem_extractBottomLayerList (lvl - 1) start gates h_cf
  | lvl, start, .orGate gates, h_cf => by
      simp only [IsConstantFree] at h_cf
      unfold extractBottomLayer
      split_ifs with h
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg; simp only [IsConstantFree]; exact h_cf
      · simp only
        exact isConstantFree_of_mem_extractBottomLayerList (lvl - 1) start gates h_cf
  | _, start, .inputGate x b, h_cf => by
      unfold extractBottomLayer
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg; exact h_cf
  | _, _, .constant b m, h_cf => by
      simp only [IsConstantFree] at h_cf
  | _, start, .notGate g₀, h_cf => by
      unfold extractBottomLayer
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg; exact h_cf

theorem isConstantFree_of_mem_extractBottomLayerList :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      (∀ g ∈ gates, IsConstantFree g) →
      ∀ g ∈ (extractBottomLayerList lvl start gates).1, IsConstantFree g
  | _, _, [], _ => by
      unfold extractBottomLayerList
      intro g hg
      simp only [List.not_mem_nil] at hg
  | lvl, start, g₀ :: gs, h_cf => by
      unfold extractBottomLayerList
      intro g hg
      rw [List.mem_append] at hg
      cases hg with
      | inl h =>
          exact isConstantFree_of_mem_extractBottomLayer lvl start g₀
            (h_cf g₀ (by simp)) g h
      | inr h =>
          exact isConstantFree_of_mem_extractBottomLayerList lvl
            (extractBottomLayer lvl start g₀).2.2 gs
            (fun g' hg' => h_cf g' (List.mem_cons_of_mem g₀ hg')) g h
end

/-! ### Auxiliary lemmas about `extractBottomLayer`. -/

/- **Index threading.**  The third component of `extractBottomLayer`'s
    output is exactly `start + length-of-extracted`. -/
mutual

theorem extractBottomLayer_next_index :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      (extractBottomLayer lvl start f).2.2 =
      start + (extractBottomLayer lvl start f).1.length
  | _, _, .inputGate _ _ => by unfold extractBottomLayer; simp
  | _, _, .constant _ _ => by unfold extractBottomLayer; simp
  | _, _, .notGate _ => by unfold extractBottomLayer; simp
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp
      · simp only
        exact extractBottomLayerList_next_index (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp
      · simp only
        exact extractBottomLayerList_next_index (lvl - 1) start gates

theorem extractBottomLayerList_next_index :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      (extractBottomLayerList lvl start gs).2.2 =
      start + (extractBottomLayerList lvl start gs).1.length
  | _, _, [] => by unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.length_append]
      have h₁ := extractBottomLayer_next_index lvl start g
      have h₂ := extractBottomLayerList_next_index lvl
                  (extractBottomLayer lvl start g).2.2 gs
      omega

end

/- **Placeholder indices.** The resulting skeleton collects exactly the
    placeholder input indices `[start, start+1, ..., start + length - 1]`. -/
mutual

theorem extractBottomLayer_collect_eq :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ufiCollectInputIndices (extractBottomLayer lvl start f).2.1 =
      List.range' start (extractBottomLayer lvl start f).1.length
  | _, _, .inputGate _ _ => by
      unfold extractBottomLayer ufiCollectInputIndices
      simp
  | _, _, .constant _ _ => by
      unfold extractBottomLayer ufiCollectInputIndices
      simp
  | _, _, .notGate _ => by
      unfold extractBottomLayer ufiCollectInputIndices
      simp
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp [ufiCollectInputIndices]
      · simp only
        unfold ufiCollectInputIndices
        exact extractBottomLayerList_flatMap_collect_eq (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp [ufiCollectInputIndices]
      · simp only
        unfold ufiCollectInputIndices
        exact extractBottomLayerList_flatMap_collect_eq (lvl - 1) start gates

theorem extractBottomLayerList_flatMap_collect_eq :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      (extractBottomLayerList lvl start gs).2.1.flatMap
        ufiCollectInputIndices =
      List.range' start (extractBottomLayerList lvl start gs).1.length
  | _, _, [] => by
      unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.flatMap_cons, List.length_append]
      rw [extractBottomLayer_collect_eq lvl start g,
          extractBottomLayer_next_index lvl start g,
          extractBottomLayerList_flatMap_collect_eq lvl
            (start + (extractBottomLayer lvl start g).1.length) gs]
      exact List.range'_append_1

end

/- **Top circuit size.**  The skeleton produced by `extractBottomLayer`
    has circuit size at most the original formula's circuit size: every
    replaced subformula has circuit size ≥ 1 and is replaced by an
    `inputGate` (also count 1), so the skeleton can only shrink. -/
mutual

theorem extractBottomLayer_top_ufiFormulaCircuitSize_le :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ufiFormulaCircuitSize (extractBottomLayer lvl start f).2.1 ≤
      ufiFormulaCircuitSize f
  | _, _, .inputGate _ _ => by
      unfold extractBottomLayer ufiFormulaCircuitSize; simp
  | _, _, .constant _ _ => by
      unfold extractBottomLayer ufiFormulaCircuitSize; simp
  | _, _, .notGate g => by
      unfold extractBottomLayer
      change ufiFormulaCircuitSize
              (UnboundedFanInFormula.inputGate _ false) ≤
             ufiFormulaCircuitSize (UnboundedFanInFormula.notGate g)
      simp only [ufiFormulaCircuitSize, Nat.zero_le]
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · change ufiFormulaCircuitSize
                (UnboundedFanInFormula.inputGate _ false) ≤
               ufiFormulaCircuitSize (UnboundedFanInFormula.andGate gates)
        simp only [ufiFormulaCircuitSize, Nat.zero_le]
      · simp only
        have hsum := extractBottomLayerList_top_ufiFormulaCircuitSize_sum_le
                       (lvl - 1) start gates
        have hnc_t : ufiFormulaCircuitSize
            (UnboundedFanInFormula.andGate
              (extractBottomLayerList (lvl - 1) start gates).2.1) =
            1 + ((extractBottomLayerList (lvl - 1) start gates).2.1.map
                  ufiFormulaCircuitSize).sum := by
          simp only [ufiFormulaCircuitSize, Nat.add_comm]
        have hnc : ufiFormulaCircuitSize
            (UnboundedFanInFormula.andGate gates) =
            1 + (gates.map ufiFormulaCircuitSize).sum := by
          simp only [ufiFormulaCircuitSize, Nat.add_comm]
        omega
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · change ufiFormulaCircuitSize
                (UnboundedFanInFormula.inputGate _ false) ≤
               ufiFormulaCircuitSize (UnboundedFanInFormula.orGate gates)
        simp only [ufiFormulaCircuitSize, Nat.zero_le]
      · simp only
        have hsum := extractBottomLayerList_top_ufiFormulaCircuitSize_sum_le
                       (lvl - 1) start gates
        have hnc_t : ufiFormulaCircuitSize
            (UnboundedFanInFormula.orGate
              (extractBottomLayerList (lvl - 1) start gates).2.1) =
            1 + ((extractBottomLayerList (lvl - 1) start gates).2.1.map
                  ufiFormulaCircuitSize).sum := by
          simp only [ufiFormulaCircuitSize, Nat.add_comm]
        have hnc : ufiFormulaCircuitSize
            (UnboundedFanInFormula.orGate gates) =
            1 + (gates.map ufiFormulaCircuitSize).sum := by
          simp only [ufiFormulaCircuitSize, Nat.add_comm]
        omega

theorem extractBottomLayerList_top_ufiFormulaCircuitSize_sum_le :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      ((extractBottomLayerList lvl start gs).2.1.map
        ufiFormulaCircuitSize).sum ≤
      (gs.map ufiFormulaCircuitSize).sum
  | _, _, [] => by unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.map_cons, List.sum_cons]
      have h₁ := extractBottomLayer_top_ufiFormulaCircuitSize_le lvl start g
      have h₂ := extractBottomLayerList_top_ufiFormulaCircuitSize_sum_le
                  lvl (extractBottomLayer lvl start g).2.2 gs
      omega

end

/- **Top is not andGate when input is not andGate.** -/
theorem extractBottomLayer_top_ne_andGate
    (lvl start : Nat) (f : UnboundedFanInFormula)
    (hne : ∀ inner, f ≠ .andGate inner) :
    ∀ inner, (extractBottomLayer lvl start f).2.1 ≠ .andGate inner := by
  intro inner heq
  cases f with
  | inputGate _ _ => unfold extractBottomLayer at heq; cases heq
  | constant _ _ => unfold extractBottomLayer at heq; cases heq
  | notGate _ => unfold extractBottomLayer at heq; cases heq
  | andGate gs => exact hne gs rfl
  | orGate gs =>
      unfold extractBottomLayer at heq
      split_ifs at heq

/- **Top is not orGate when input is not orGate.** -/
theorem extractBottomLayer_top_ne_orGate
    (lvl start : Nat) (f : UnboundedFanInFormula)
    (hne : ∀ inner, f ≠ .orGate inner) :
    ∀ inner, (extractBottomLayer lvl start f).2.1 ≠ .orGate inner := by
  intro inner heq
  cases f with
  | inputGate _ _ => unfold extractBottomLayer at heq; cases heq
  | constant _ _ => unfold extractBottomLayer at heq; cases heq
  | notGate _ => unfold extractBottomLayer at heq; cases heq
  | andGate gs =>
      unfold extractBottomLayer at heq
      split_ifs at heq
  | orGate gs => exact hne gs rfl

/- **Strictly-leveled preservation.**  Stripping out the level-≤-2
    subformulas yields a top skeleton that is strictly assigned-leveled
    at the reduced level `lvl - 2` (with truncated subtraction). -/
mutual

theorem isAlternatingAndLeveledAt_extractBottomLayer_top :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      IsAlternatingAndLeveledAt f lvl →
      IsAlternatingAndLeveledAt
        (extractBottomLayer lvl start f).2.1 (lvl - 2)
  | _, _, .inputGate _ _, _ => by
      unfold extractBottomLayer
      simp only [IsAlternatingAndLeveledAt]
  | _, _, .constant _ _, _ => by
      unfold extractBottomLayer
      simp only [IsAlternatingAndLeveledAt]
  | _, _, .notGate _, h => by
      simp only [IsAlternatingAndLeveledAt] at h
  | lvl, start, .andGate gates, h => by
      unfold extractBottomLayer
      split_ifs with hle
      · simp only [IsAlternatingAndLeveledAt]
      · simp only
        have hlvl : 2 < lvl := Nat.lt_of_not_le hle
        simp only [IsAlternatingAndLeveledAt] at h
        obtain ⟨hno_inner, _, hchild⟩ := h
        simp only [IsAlternatingAndLeveledAt]
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg' inner heq
          obtain ⟨g, hgmem, s, hg'_eq⟩ :=
            exists_extractBottomLayer_top_of_mem_extractBottomLayerList_top (lvl - 1) start gates g' hg'
          have hne := extractBottomLayer_top_ne_andGate (lvl - 1) s g
                        (hno_inner g hgmem) inner
          rw [hg'_eq] at heq; exact hne heq
        · intro _ _ _; omega
        · intro g' hg'
          obtain ⟨g, hgmem, s, hg'_eq⟩ :=
            exists_extractBottomLayer_top_of_mem_extractBottomLayerList_top (lvl - 1) start gates g' hg'
          have hsl := hchild g hgmem
          have hrec :
              IsAlternatingAndLeveledAt
                (extractBottomLayer (lvl - 1) s g).2.1 ((lvl - 1) - 2) :=
            isAlternatingAndLeveledAt_extractBottomLayer_top (lvl - 1) s g hsl
          have heq : (lvl - 1) - 2 = lvl - 2 - 1 := by omega
          rw [heq] at hrec
          rw [hg'_eq]
          exact hrec
  | lvl, start, .orGate gates, h => by
      unfold extractBottomLayer
      split_ifs with hle
      · simp only [IsAlternatingAndLeveledAt]
      · simp only
        have hlvl : 2 < lvl := Nat.lt_of_not_le hle
        simp only [IsAlternatingAndLeveledAt] at h
        obtain ⟨hno_inner, _, hchild⟩ := h
        simp only [IsAlternatingAndLeveledAt]
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg' inner heq
          obtain ⟨g, hgmem, s, hg'_eq⟩ :=
            exists_extractBottomLayer_top_of_mem_extractBottomLayerList_top (lvl - 1) start gates g' hg'
          have hne := extractBottomLayer_top_ne_orGate (lvl - 1) s g
                        (hno_inner g hgmem) inner
          rw [hg'_eq] at heq; exact hne heq
        · intro _ _ _; omega
        · intro g' hg'
          obtain ⟨g, hgmem, s, hg'_eq⟩ :=
            exists_extractBottomLayer_top_of_mem_extractBottomLayerList_top (lvl - 1) start gates g' hg'
          have hsl := hchild g hgmem
          have hrec :
              IsAlternatingAndLeveledAt
                (extractBottomLayer (lvl - 1) s g).2.1 ((lvl - 1) - 2) :=
            isAlternatingAndLeveledAt_extractBottomLayer_top (lvl - 1) s g hsl
          have heq : (lvl - 1) - 2 = lvl - 2 - 1 := by omega
          rw [heq] at hrec
          rw [hg'_eq]
          exact hrec

theorem exists_extractBottomLayer_top_of_mem_extractBottomLayerList_top :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula)
      (g' : UnboundedFanInFormula),
      g' ∈ (extractBottomLayerList lvl start gates).2.1 →
      ∃ g ∈ gates, ∃ s, g' = (extractBottomLayer lvl s g).2.1
  | _, _, [], g', hg' => by
      unfold extractBottomLayerList at hg'; simp at hg'
  | lvl, start, g₀ :: gs, g', hg' => by
      unfold extractBottomLayerList at hg'
      simp only [List.mem_cons] at hg'
      rcases hg' with hg' | hg'
      · exact ⟨g₀, by simp, start, hg'⟩
      · obtain ⟨g, hg, s, heq⟩ :=
          exists_extractBottomLayer_top_of_mem_extractBottomLayerList_top lvl
            (extractBottomLayer lvl start g₀).2.2 gs g' hg'
        exact ⟨g, by simp [hg], s, heq⟩

end

/- **andGate eval depends only on child eval list.** -/
theorem andGate_eval_congr (xs inputs : List Bool) :
    ∀ (gates tops : List UnboundedFanInFormula),
      gates.map (fun g => ufiFormulaEval g xs) =
        tops.map (fun t => ufiFormulaEval t inputs) →
      ufiFormulaEval (.andGate gates) xs =
        ufiFormulaEval (.andGate tops) inputs
  | [], [], _ => by
      show ufiFormulaEval (.andGate []) xs =
            ufiFormulaEval (.andGate []) inputs
      simp only [ufiFormulaEval]
  | [], _ :: _, hmap => by simp at hmap
  | _ :: _, [], hmap => by simp at hmap
  | g :: gs, t :: ts, hmap => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hh, htl⟩ := hmap
    show ufiFormulaEval (.andGate (g :: gs)) xs =
          ufiFormulaEval (.andGate (t :: ts)) inputs
    simp only [ufiFormulaEval, hh]
    cases ufiFormulaEval t inputs with
    | false => rfl
    | true => exact andGate_eval_congr xs inputs gs ts htl

/- **orGate eval depends only on child eval list.** -/
theorem orGate_eval_congr (xs inputs : List Bool) :
    ∀ (gates tops : List UnboundedFanInFormula),
      gates.map (fun g => ufiFormulaEval g xs) =
        tops.map (fun t => ufiFormulaEval t inputs) →
      ufiFormulaEval (.orGate gates) xs =
        ufiFormulaEval (.orGate tops) inputs
  | [], [], _ => by
      show ufiFormulaEval (.orGate []) xs =
            ufiFormulaEval (.orGate []) inputs
      simp only [ufiFormulaEval]
  | [], _ :: _, hmap => by simp at hmap
  | _ :: _, [], hmap => by simp at hmap
  | g :: gs, t :: ts, hmap => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hh, htl⟩ := hmap
    show ufiFormulaEval (.orGate (g :: gs)) xs =
          ufiFormulaEval (.orGate (t :: ts)) inputs
    simp only [ufiFormulaEval, hh]
    cases ufiFormulaEval t inputs with
    | false => exact orGate_eval_congr xs inputs gs ts htl
    | true => rfl

/- **Placeholder lookup.**  If `acc.length = start`, then looking up
    index `start` in `acc ++ [v] ++ pad` returns `some v`. -/
lemma getElem?_placeholder
    (acc : List Bool) (v : Bool) (pad : List Bool) (start : Nat)
    (hacc : acc.length = start) :
    (acc ++ [v] ++ pad)[start]? = some v := by
  subst hacc
  induction acc with
  | nil => simp
  | cons a as ih =>
    -- (a :: (as ++ [v] ++ pad))[as.length + 1]? = (as ++ [v] ++ pad)[as.length]?,
    -- which is exactly ih.
    exact ih

/- **Eval substitution.**  Evaluating the original formula `f` on `xs`
    equals evaluating the top skeleton on the input vector
    `acc ++ raw.map (eval · xs) ++ pad`, where `acc.length = start`
    so the placeholder indices `[start, start + raw.length)` align
    with the embedded evaluations. -/
mutual

theorem extractBottomLayer_eval :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula)
      (xs acc pad : List Bool),
      acc.length = start →
      ufiFormulaEval f xs =
        ufiFormulaEval (extractBottomLayer lvl start f).2.1
          (acc ++ (extractBottomLayer lvl start f).1.map
                    (fun g => ufiFormulaEval g xs) ++ pad)
  | _, start, .inputGate i b, xs, acc, pad, hacc => by
      unfold extractBottomLayer
      simp only [List.map_cons, List.map_nil]
      show ufiFormulaEval (.inputGate i b) xs =
            ufiFormulaEval (UnboundedFanInFormula.inputGate start false)
              (acc ++ [ufiFormulaEval (.inputGate i b) xs] ++ pad)
      have hp := getElem?_placeholder acc
                  (ufiFormulaEval (.inputGate i b) xs) pad start hacc
      simp only [ufiFormulaEval] at hp ⊢
      rw [hp]
  | _, start, .constant b val, xs, acc, pad, hacc => by
      unfold extractBottomLayer
      simp only [List.map_cons, List.map_nil]
      show ufiFormulaEval (.constant b val) xs =
            ufiFormulaEval (UnboundedFanInFormula.inputGate start false)
              (acc ++ [ufiFormulaEval (.constant b val) xs] ++ pad)
      have hp : (acc ++ [b] ++ pad)[start]? = some b :=
        getElem?_placeholder acc b pad start hacc
      simp only [ufiFormulaEval, hp]
  | _, start, .notGate gn, xs, acc, pad, hacc => by
      unfold extractBottomLayer
      simp only [List.map_cons, List.map_nil]
      show ufiFormulaEval (.notGate gn) xs =
            ufiFormulaEval (UnboundedFanInFormula.inputGate start false)
              (acc ++ [ufiFormulaEval (.notGate gn) xs] ++ pad)
      have hp : (acc ++ [not (ufiFormulaEval gn xs)] ++ pad)[start]? =
                some (not (ufiFormulaEval gn xs)) :=
        getElem?_placeholder acc (not (ufiFormulaEval gn xs)) pad start hacc
      simp only [ufiFormulaEval, hp]
  | lvl, start, .andGate gates, xs, acc, pad, hacc => by
      unfold extractBottomLayer
      split_ifs with hle
      · simp only [List.map_cons, List.map_nil]
        show ufiFormulaEval (.andGate gates) xs =
              ufiFormulaEval (UnboundedFanInFormula.inputGate start false)
                (acc ++ [ufiFormulaEval (.andGate gates) xs] ++ pad)
        have hp := getElem?_placeholder acc
                    (ufiFormulaEval (.andGate gates) xs) pad start hacc
        simp only [ufiFormulaEval, hp]
      · simp only
        have hlist := extractBottomLayerList_eval_map (lvl - 1) start gates xs
                        acc pad hacc
        exact andGate_eval_congr xs _ gates _ hlist
  | lvl, start, .orGate gates, xs, acc, pad, hacc => by
      unfold extractBottomLayer
      split_ifs with hle
      · simp only [List.map_cons, List.map_nil]
        show ufiFormulaEval (.orGate gates) xs =
              ufiFormulaEval (UnboundedFanInFormula.inputGate start false)
                (acc ++ [ufiFormulaEval (.orGate gates) xs] ++ pad)
        have hp := getElem?_placeholder acc
                    (ufiFormulaEval (.orGate gates) xs) pad start hacc
        simp only [ufiFormulaEval, hp]
      · simp only
        have hlist := extractBottomLayerList_eval_map (lvl - 1) start gates xs
                        acc pad hacc
        exact orGate_eval_congr xs _ gates _ hlist

theorem extractBottomLayerList_eval_map :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula)
      (xs acc pad : List Bool),
      acc.length = start →
      gates.map (fun g => ufiFormulaEval g xs) =
        (extractBottomLayerList lvl start gates).2.1.map
          (fun t => ufiFormulaEval t
            (acc ++ (extractBottomLayerList lvl start gates).1.map
                      (fun g => ufiFormulaEval g xs) ++ pad))
  | _, _, [], _, _, _, _ => by
      unfold extractBottomLayerList; simp
  | lvl, start, g₀ :: gs, xs, acc, pad, hacc => by
      unfold extractBottomLayerList
      simp only [List.map_cons]
      refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
      · -- head
        have hhead := extractBottomLayer_eval lvl start g₀ xs acc
          ((extractBottomLayerList lvl (extractBottomLayer lvl start g₀).2.2 gs).1.map
            (fun g => ufiFormulaEval g xs) ++ pad) hacc
        simp only [List.map_append, List.append_assoc] at hhead ⊢
        exact hhead
      · -- tail
        have hnext :
            (extractBottomLayer lvl start g₀).2.2 =
              start + (extractBottomLayer lvl start g₀).1.length :=
          extractBottomLayer_next_index lvl start g₀
        have htail := extractBottomLayerList_eval_map lvl
          (extractBottomLayer lvl start g₀).2.2 gs xs
          (acc ++ (extractBottomLayer lvl start g₀).1.map
                    (fun g => ufiFormulaEval g xs))
          pad
          (by simp [List.length_append, hacc, hnext])
        simp only [List.map_append, List.append_assoc] at htail ⊢
        exact htail

end

/-! ### inputGate-bound inheritance for bottom formulas -/

/- Children of an andGate inherit the input-bound from the parent. -/
lemma ufiLargestInput_andGate_child_le
    (n : Nat) (gates : List UnboundedFanInFormula)
    (h_inputs : ufiLargestInput (.andGate gates) < n) :
    ∀ g ∈ gates, ufiLargestInput g < n := by
  intro g hg
  unfold ufiLargestInput ufiCollectInputIndices at h_inputs
  have hsub :
      (ufiCollectInputIndices g).Sublist
        (gates.flatMap ufiCollectInputIndices) :=
    mem_flatMap_implies_sublist ufiCollectInputIndices gates g hg
  have hle : (List.foldr max 0) (ufiCollectInputIndices g) ≤
              (List.foldr max 0) (gates.flatMap ufiCollectInputIndices) :=
    foldr_max_sublist hsub
  unfold ufiLargestInput
  omega

/- Children of an orGate inherit the input-bound from the parent. -/
lemma ufiLargestInput_orGate_child_le
    (n : Nat) (gates : List UnboundedFanInFormula)
    (h_inputs : ufiLargestInput (.orGate gates) < n) :
    ∀ g ∈ gates, ufiLargestInput g < n := by
  intro g hg
  unfold ufiLargestInput ufiCollectInputIndices at h_inputs
  have hsub :
      (ufiCollectInputIndices g).Sublist
        (gates.flatMap ufiCollectInputIndices) :=
    mem_flatMap_implies_sublist ufiCollectInputIndices gates g hg
  have hle : (List.foldr max 0) (ufiCollectInputIndices g) ≤
              (List.foldr max 0) (gates.flatMap ufiCollectInputIndices) :=
    foldr_max_sublist hsub
  unfold ufiLargestInput
  omega

end Circuits.HastadParity
