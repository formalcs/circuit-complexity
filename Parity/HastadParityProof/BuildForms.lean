/-
  Position-aware substitution-form construction.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.DepthTwo

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-! ### Position-aware substitution-form constructors.

    `buildFormsWith` is the single structural recursion shared by the ordinary
    and restriction-aware producers.  Its three callbacks describe the only
    policy choices:

    * the form for an AND/OR bottom;
    * the form for an `inputGate` at the splice base; and
    * the form for an `inputGate` above the splice.

    A source `constant` is preserved explicitly.  Correctness theorems for
    constant-free phases may still rule this branch out, while tolerant phases
    can carry the constant to the common `simplifyConstants` boundary.

    The recursion mirrors `extractBottomLayer`, so its `lvl` parameter
    disambiguates the two leaf positions:

    * A gate bottom (`andGate`/`orGate` reached at `lvl ≤ 2`) becomes the
      caller-provided switched proper form `gf start`.
    * A *splice-base* `inputGate` leaf (reached at `lvl ≤ 2`, i.e. a child of a
      level-3 gate) becomes a one-clause proper CNF/DNF
      `litToProperCNF/DNF` of its rekeyed literal `il start` — polarity
      `needCnf` is threaded down from the parent gate.
    * An *above-splice* `inputGate` leaf (reached at `lvl ≥ 3`) becomes a bare
      rekeyed `inputGate (il start)`.

    A `constant` is preserved by the shared recursion, while the totality
    branch for `notGate` remains an arbitrary placeholder.

    Sibling placeholder indices are threaded exactly as in
    `extractBottomLayer` (via its `.2.2` next-index), so the produced form
    list aligns position-for-position with the extracted bottom list. -/
mutual

def buildFormsWith
    (gateBottom spliceInput : Bool → Nat → UnboundedFanInFormula)
    (aboveInput : Nat → UnboundedFanInFormula) (needCnf : Bool) :
    Nat → Nat → UnboundedFanInFormula → List UnboundedFanInFormula
  | lvl, start, .andGate gates =>
      if lvl ≤ 2 then [gateBottom needCnf start]
      else buildFormsWithList gateBottom spliceInput aboveInput true (lvl - 1) start gates
  | lvl, start, .orGate gates =>
      if lvl ≤ 2 then [gateBottom needCnf start]
      else buildFormsWithList gateBottom spliceInput aboveInput false (lvl - 1) start gates
  | lvl, start, .inputGate _ _ =>
      if lvl ≤ 2 then [spliceInput needCnf start]
      else [aboveInput start]
  | _, _, .constant b label => [UnboundedFanInFormula.constant b label]
  | _, start, .notGate _ => [UnboundedFanInFormula.inputGate start false]

def buildFormsWithList
    (gateBottom spliceInput : Bool → Nat → UnboundedFanInFormula)
    (aboveInput : Nat → UnboundedFanInFormula) (needCnf : Bool) :
    Nat → Nat → List UnboundedFanInFormula → List UnboundedFanInFormula
  | _, _, [] => []
  | lvl, start, g :: gs =>
      buildFormsWith gateBottom spliceInput aboveInput needCnf lvl start g ++
      buildFormsWithList gateBottom spliceInput aboveInput needCnf lvl
        (extractBottomLayer lvl start g).2.2 gs

end

/-- At level `2` any formula extracts exactly one bottom. -/
lemma extractBottomLayer_two_length_one (start : Nat) (g : UnboundedFanInFormula) :
    (extractBottomLayer 2 start g).1.length = 1 := by
  cases g <;> simp [extractBottomLayer]

/-- The level-2 skeleton-list length of `g :: gs` is `1 +` the tail's
    (each head bottom at level 2 contributes exactly one placeholder). -/
lemma extractBottomLayerList_two_cons_length
    (start : Nat) (g : UnboundedFanInFormula) (gs : List UnboundedFanInFormula) :
    (extractBottomLayerList 2 start (g :: gs)).1.length
      = 1 + (extractBottomLayerList 2 (start + 1) gs).1.length := by
  conv_lhs => unfold extractBottomLayerList
  simp only [List.length_append, extractBottomLayer_two_next, extractBottomLayer_two_length_one]

/-- Skeleton-list length of `g :: gs` splits as head plus tail. -/
lemma extractBottomLayerList_cons_length (lvl start : Nat)
    (g : UnboundedFanInFormula) (gs : List UnboundedFanInFormula) :
    (extractBottomLayerList lvl start (g :: gs)).1.length
      = (extractBottomLayer lvl start g).1.length
        + (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1.length := by
  conv_lhs => unfold extractBottomLayerList
  simp [List.length_append]

/-- For an `andGate` above level 2 the extracted bottom list is the
    children's list (the gate itself is not a bottom). -/
lemma extractBottomLayer_andGate_fst_of_two_lt (lvl start : Nat)
    (gates : List UnboundedFanInFormula) (h : ¬ lvl ≤ 2) :
    (extractBottomLayer lvl start (UnboundedFanInFormula.andGate gates)).1
      = (extractBottomLayerList (lvl - 1) start gates).1 := by
  simp [extractBottomLayer, h]

/-- For an `orGate` above level 2 the extracted bottom list is the
    children's list. -/
lemma extractBottomLayer_orGate_fst_of_two_lt (lvl start : Nat)
    (gates : List UnboundedFanInFormula) (h : ¬ lvl ≤ 2) :
    (extractBottomLayer lvl start (UnboundedFanInFormula.orGate gates)).1
      = (extractBottomLayerList (lvl - 1) start gates).1 := by
  simp [extractBottomLayer, h]

/- At level 2 every gate emits exactly one bottom, so the extracted
   bottom-list length equals the number of gates. -/
theorem extractBottomLayerList_two_length :
    ∀ (start : Nat) (gates : List UnboundedFanInFormula),
      (extractBottomLayerList 2 start gates).1.length = gates.length
  | _, [] => by unfold extractBottomLayerList; simp
  | start, g :: gs => by
      rw [extractBottomLayerList_two_cons_length,
          extractBottomLayerList_two_length (start + 1) gs, List.length_cons]
      omega

/-! ### constant-tolerant producer mirror.

    Targets `IsExtractionSubstitutionReadyWithConstants`, allowing `gf` to
    emit a `constant` for a restriction-killed bottom. -/

/- constant-tolerant base-list congruence. -/
theorem isExtractionBaseListSubstitutionReadyWithConstants_congr
    (sub₁ sub₂ : Nat → UnboundedFanInFormula) (needCnf : Bool) :
    ∀ (start : Nat) (gates : List UnboundedFanInFormula),
      (∀ i, start ≤ i →
        i < start + (extractBottomLayerList 2 start gates).1.length →
        sub₁ i = sub₂ i) →
      IsExtractionBaseListSubstitutionReadyWithConstants sub₁ needCnf start gates →
      IsExtractionBaseListSubstitutionReadyWithConstants sub₂ needCnf start gates
  | _, [], _, _ => by unfold IsExtractionBaseListSubstitutionReadyWithConstants; trivial
  | start, g :: gs, hagree, hsr => by
      unfold IsExtractionBaseListSubstitutionReadyWithConstants at hsr ⊢
      obtain ⟨hhead, htail⟩ := hsr
      have hlen := extractBottomLayerList_two_cons_length start g gs
      refine ⟨?_, ?_⟩
      · have he : sub₁ start = sub₂ start :=
          hagree start (Nat.le_refl _) (by rw [hlen]; omega)
        unfold IsSubstitutionProperFormOrConstant IsSubstitutionProperForm at hhead ⊢
        rw [← he]; exact hhead
      · rw [extractBottomLayer_two_next] at htail ⊢
        apply isExtractionBaseListSubstitutionReadyWithConstants_congr sub₁ sub₂ needCnf (start + 1) gs ?_ htail
        intro i hi hi₂
        exact hagree i (by omega) (by rw [hlen]; omega)

/- constant-tolerant top/rec congruence (mutual). -/
mutual

theorem isExtractionSubstitutionReadyWithConstants_congr
    (sub₁ sub₂ : Nat → UnboundedFanInFormula) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      (∀ i, start ≤ i →
        i < start + (extractBottomLayer lvl start f).1.length →
        sub₁ i = sub₂ i) →
      IsExtractionSubstitutionReadyWithConstants sub₁ lvl start f →
      IsExtractionSubstitutionReadyWithConstants sub₂ lvl start f
  | _, _, .inputGate _ _, _, _ => by trivial
  | _, _, .constant _ _, _, _ => by trivial
  | _, _, .notGate _, _, _ => by trivial
  | lvl, start, .andGate gates, hagree, hsr => by
      simp only [IsExtractionSubstitutionReadyWithConstants] at hsr ⊢
      by_cases h₁ : lvl ≤ 2
      · rw [if_pos h₁] at hsr ⊢; trivial
      · rw [if_neg h₁] at hsr ⊢
        by_cases h₂ : lvl ≤ 3
        · rw [if_pos h₂] at hsr ⊢
          have hlv : lvl = 3 := by omega
          subst hlv
          refine isExtractionBaseListSubstitutionReadyWithConstants_congr sub₁ sub₂ true start gates ?_ hsr
          intro i hi hi₂
          refine hagree i hi ?_
          rw [extractBottomLayer_andGate_fst_of_two_lt 3 start gates h₁]
          exact hi₂
        · rw [if_neg h₂] at hsr ⊢
          refine isExtractionRecursiveListSubstitutionReadyWithConstants_congr sub₁ sub₂ (lvl - 1) start gates ?_ hsr
          intro i hi hi₂
          refine hagree i hi ?_
          rw [extractBottomLayer_andGate_fst_of_two_lt lvl start gates h₁]
          exact hi₂
  | lvl, start, .orGate gates, hagree, hsr => by
      simp only [IsExtractionSubstitutionReadyWithConstants] at hsr ⊢
      by_cases h₁ : lvl ≤ 2
      · rw [if_pos h₁] at hsr ⊢; trivial
      · rw [if_neg h₁] at hsr ⊢
        by_cases h₂ : lvl ≤ 3
        · rw [if_pos h₂] at hsr ⊢
          have hlv : lvl = 3 := by omega
          subst hlv
          refine isExtractionBaseListSubstitutionReadyWithConstants_congr sub₁ sub₂ false start gates ?_ hsr
          intro i hi hi₂
          refine hagree i hi ?_
          rw [extractBottomLayer_orGate_fst_of_two_lt 3 start gates h₁]
          exact hi₂
        · rw [if_neg h₂] at hsr ⊢
          refine isExtractionRecursiveListSubstitutionReadyWithConstants_congr sub₁ sub₂ (lvl - 1) start gates ?_ hsr
          intro i hi hi₂
          refine hagree i hi ?_
          rw [extractBottomLayer_orGate_fst_of_two_lt lvl start gates h₁]
          exact hi₂

theorem isExtractionRecursiveListSubstitutionReadyWithConstants_congr
    (sub₁ sub₂ : Nat → UnboundedFanInFormula) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      (∀ i, start ≤ i →
        i < start + (extractBottomLayerList lvl start gates).1.length →
        sub₁ i = sub₂ i) →
      IsExtractionRecursiveListSubstitutionReadyWithConstants sub₁ lvl start gates →
      IsExtractionRecursiveListSubstitutionReadyWithConstants sub₂ lvl start gates
  | _, _, [], _, _ => by trivial
  | lvl, start, g :: gs, hagree, hsr => by
      unfold IsExtractionRecursiveListSubstitutionReadyWithConstants at hsr ⊢
      obtain ⟨hhead, htail⟩ := hsr
      have hcons := extractBottomLayerList_cons_length lvl start g gs
      have hnext : (extractBottomLayer lvl start g).2.2
          = start + (extractBottomLayer lvl start g).1.length :=
        extractBottomLayer_next_index lvl start g
      refine ⟨?_, ?_⟩
      · cases g with
        | inputGate x b =>
          have hg₁ : (extractBottomLayer lvl start (.inputGate x b)).1.length = 1 := by
            simp [extractBottomLayer]
          have he : sub₁ start = sub₂ start :=
            hagree start (Nat.le_refl _) (by rw [hcons, hg₁]; omega)
          unfold IsSubstitutionLeaf at hhead ⊢; rw [← he]; exact hhead
        | constant b m =>
          have hg₁ : (extractBottomLayer lvl start (.constant b m)).1.length = 1 := by
            simp [extractBottomLayer]
          have he : sub₁ start = sub₂ start :=
            hagree start (Nat.le_refl _) (by rw [hcons, hg₁]; omega)
          unfold IsSubstitutionLeaf at hhead ⊢; rw [← he]; exact hhead
        | notGate g₀ =>
          have hg₁ : (extractBottomLayer lvl start (.notGate g₀)).1.length = 1 := by
            simp [extractBottomLayer]
          have he : sub₁ start = sub₂ start :=
            hagree start (Nat.le_refl _) (by rw [hcons, hg₁]; omega)
          unfold IsSubstitutionLeaf at hhead ⊢; rw [← he]; exact hhead
        | andGate gs' =>
          refine isExtractionSubstitutionReadyWithConstants_congr sub₁ sub₂ lvl start (.andGate gs') ?_ hhead
          intro i hi hi₂
          refine hagree i hi ?_
          rw [hcons]; omega
        | orGate gs' =>
          refine isExtractionSubstitutionReadyWithConstants_congr sub₁ sub₂ lvl start (.orGate gs') ?_ hhead
          intro i hi hi₂
          refine hagree i hi ?_
          rw [hcons]; omega
      · refine isExtractionRecursiveListSubstitutionReadyWithConstants_congr sub₁ sub₂ lvl
          (extractBottomLayer lvl start g).2.2 gs ?_ htail
        intro i hi hi₂
        refine hagree i ?_ ?_
        · omega
        · rw [hcons]; omega

end

/- constant-tolerant base-list producer. -/
lemma isExtractionBaseListSubstitutionReadyWithConstants_of_isSubstitutionProperFormOrConstant
    (sub : Nat → UnboundedFanInFormula) (needCnf : Bool) :
    ∀ (start : Nat) (gates : List UnboundedFanInFormula),
      (∀ i, start ≤ i → i < start + gates.length → IsSubstitutionProperFormOrConstant sub needCnf i) →
      IsExtractionBaseListSubstitutionReadyWithConstants sub needCnf start gates
  | start, [], _ => by
      unfold IsExtractionBaseListSubstitutionReadyWithConstants; trivial
  | start, g :: gs, h => by
      unfold IsExtractionBaseListSubstitutionReadyWithConstants
      refine ⟨h start (Nat.le_refl _) ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [extractBottomLayer_two_next]
        apply isExtractionBaseListSubstitutionReadyWithConstants_of_isSubstitutionProperFormOrConstant sub needCnf (start + 1) gs
        intro i hi hi₂
        refine h i (by omega) ?_
        simp only [List.length_cons] at hi₂ ⊢
        omega

end Circuits.HastadParity
