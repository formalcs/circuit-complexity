/-
  Kill-aware construction and iterated depth reduction.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.BuildForms

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-! ### Kill-aware substitution constructor `buildKillAwareForms`.

    This specialization of `buildFormsWith` routes every splice-base bottom
    (gate **and** `inputGate`) through the caller-supplied switched proper
    form `gf`.  The active narrow producer obtains gate forms from
    `exists_bottom_sub_proper_for_polarity` and handles literal bottoms
    directly with `exists_restricted_literal_form_for_polarity`.  At an
    *above-splice* `inputGate` leaf, the recursion consults a `kill`
    oracle: a killed coordinate becomes a `constant` (the restriction's
    fixed bit) and a live coordinate becomes the rekeyed bare
    `inputGate (il start)`.

    This is the substitution map the `exists_switching_depth_reduction` wiring actually needs:
    it tolerates restriction-killed `inputGate` leaves at any depth (the
    standing requirement that the construction not assume inputs only at
    the bottom). `constant`s appear at killed above-splice leaves and are
    preserved if already present in the source. They are absorbed by
    `simplifyConstants` afterwards, restoring `IsConstantFree`.

    This is a policy specialization of the shared `buildFormsWith` recursion;
    it does not duplicate the extraction/index-threading traversal. -/

def buildKillAwareForms
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) :
    Nat → Nat → UnboundedFanInFormula → List UnboundedFanInFormula :=
  buildFormsWith gf gf
    (fun start =>
        match kill start with
        | some bb => UnboundedFanInFormula.constant bb 0
        | none => UnboundedFanInFormula.inputGate (il start).1 (il start).2)
    needCnf

def buildKillAwareFormsList
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) :
    Nat → Nat → List UnboundedFanInFormula → List UnboundedFanInFormula :=
  buildFormsWithList gf gf
    (fun start =>
      match kill start with
      | some bb => UnboundedFanInFormula.constant bb 0
      | none => UnboundedFanInFormula.inputGate (il start).1 (il start).2)
    needCnf

@[simp] theorem buildKillAwareForms_input
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) (lvl start x : Nat) (b : Bool) :
    buildKillAwareForms gf il kill needCnf lvl start (.inputGate x b) =
      if lvl ≤ 2 then [gf needCnf start]
      else
        match kill start with
        | some bb => [.constant bb 0]
        | none => [.inputGate (il start).1 (il start).2] := by
  by_cases h : lvl ≤ 2
  · simp [buildKillAwareForms, buildFormsWith, h]
  · cases hk : kill start <;> simp [buildKillAwareForms, buildFormsWith, h, hk]

@[simp] theorem buildKillAwareForms_andGate
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) (lvl start : Nat)
    (gates : List UnboundedFanInFormula) :
    buildKillAwareForms gf il kill needCnf lvl start (.andGate gates) =
      if lvl ≤ 2 then [gf needCnf start]
      else buildKillAwareFormsList gf il kill true (lvl - 1) start gates := by
  simp [buildKillAwareForms, buildKillAwareFormsList, buildFormsWith]

@[simp] theorem buildKillAwareForms_orGate
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) (lvl start : Nat)
    (gates : List UnboundedFanInFormula) :
    buildKillAwareForms gf il kill needCnf lvl start (.orGate gates) =
      if lvl ≤ 2 then [gf needCnf start]
      else buildKillAwareFormsList gf il kill false (lvl - 1) start gates := by
  simp [buildKillAwareForms, buildKillAwareFormsList, buildFormsWith]

@[simp] theorem buildKillAwareFormsList_nil
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) (lvl start : Nat) :
    buildKillAwareFormsList gf il kill needCnf lvl start [] = [] := by
  simp [buildKillAwareFormsList, buildFormsWithList]

@[simp] theorem buildKillAwareFormsList_cons
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) (lvl start : Nat)
    (g : UnboundedFanInFormula) (gs : List UnboundedFanInFormula) :
    buildKillAwareFormsList gf il kill needCnf lvl start (g :: gs) =
      buildKillAwareForms gf il kill needCnf lvl start g ++
      buildKillAwareFormsList gf il kill needCnf lvl
        (extractBottomLayer lvl start g).2.2 gs := by
  simp [buildKillAwareForms, buildKillAwareFormsList, buildFormsWithList]

/- The kill-aware form list has exactly one entry per extracted bottom. -/
mutual

theorem buildKillAwareForms_length
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      (buildKillAwareForms gf il kill needCnf lvl start f).length
        = (extractBottomLayer lvl start f).1.length
  | lvl, start, .inputGate x b => by
      unfold buildKillAwareForms buildFormsWith extractBottomLayer
      by_cases h : lvl ≤ 2
      · simp only [if_pos h, List.length_cons, List.length_nil]
      · simp only [if_neg h]
        cases kill start <;> simp
  | _, start, .constant b m => by
      unfold buildKillAwareForms buildFormsWith extractBottomLayer; simp
  | _, start, .notGate g => by
      unfold buildKillAwareForms buildFormsWith extractBottomLayer; simp
  | lvl, start, .andGate gates => by
      unfold buildKillAwareForms buildFormsWith extractBottomLayer
      split_ifs with h
      · simp
      · simp only
        exact buildKillAwareFormsList_length gf il kill true (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold buildKillAwareForms buildFormsWith extractBottomLayer
      split_ifs with h
      · simp
      · simp only
        exact buildKillAwareFormsList_length gf il kill false (lvl - 1) start gates

theorem buildKillAwareFormsList_length
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (needCnf : Bool) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      (buildKillAwareFormsList gf il kill needCnf lvl start gates).length
        = (extractBottomLayerList lvl start gates).1.length
  | _, _, [] => by
      simp [buildKillAwareFormsList_nil, extractBottomLayerList]
  | lvl, start, g :: gs => by
      rw [buildKillAwareFormsList_cons]
      unfold extractBottomLayerList
      simp only [List.length_append]
      rw [buildKillAwareForms_length gf il kill needCnf lvl start g,
          buildKillAwareFormsList_length gf il kill needCnf lvl (extractBottomLayer lvl start g).2.2 gs]

end

/- Every form emitted by the kill-aware producer `buildKillAwareForms` is
    `notGate`-free, provided each gate form `gf p i` is (which holds because
    they are proper CNFs/DNFs or constants).  Killed and live `inputGate`
    placeholders and the out-of-window default are leaves, hence `IsNotGateFree`. -/
mutual

theorem isNotGateFree_of_mem_buildKillAwareForms
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (hgfnn : ∀ p i, IsNotGateFree (gf p i)) (needCnf : Bool) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ∀ x ∈ buildKillAwareForms gf il kill needCnf lvl start f, IsNotGateFree x
  | lvl, start, .inputGate i b => by
      unfold buildKillAwareForms buildFormsWith
      by_cases h : lvl ≤ 2
      · simp only [if_pos h, List.mem_singleton]
        intro x hx; subst hx; exact hgfnn needCnf start
      · simp only [if_neg h]
        cases kill start with
        | some bb =>
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp only [IsNotGateFree]
        | none =>
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp only [IsNotGateFree]
  | _, start, .constant b m => by
      unfold buildKillAwareForms buildFormsWith
      intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp only [IsNotGateFree]
  | _, start, .notGate g => by
      unfold buildKillAwareForms buildFormsWith
      intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp only [IsNotGateFree]
  | lvl, start, .andGate gates => by
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hgfnn needCnf start
      · exact isNotGateFree_of_mem_buildKillAwareFormsList gf il kill hgfnn true (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hgfnn needCnf start
      · exact isNotGateFree_of_mem_buildKillAwareFormsList gf il kill hgfnn false (lvl - 1) start gates

theorem isNotGateFree_of_mem_buildKillAwareFormsList
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (hgfnn : ∀ p i, IsNotGateFree (gf p i)) (needCnf : Bool) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      ∀ x ∈ buildKillAwareFormsList gf il kill needCnf lvl start gates, IsNotGateFree x
  | _, _, [] => by unfold buildKillAwareFormsList buildFormsWithList; simp
  | lvl, start, g :: gs => by
      unfold buildKillAwareFormsList buildFormsWithList
      simp only [List.mem_append]
      intro x hx
      rcases hx with hx | hx
      · exact isNotGateFree_of_mem_buildKillAwareForms gf il kill hgfnn needCnf lvl start g x hx
      · exact isNotGateFree_of_mem_buildKillAwareFormsList gf il kill hgfnn needCnf lvl
          (extractBottomLayer lvl start g).2.2 gs x hx

end

/- Every form emitted by `buildKillAwareForms` has both CNF and DNF bottom width
    `≤ t`, provided each gate form `gf p i` does.  The kill/live `inputGate`
    placeholders, killed `constant` leaves, and the out-of-window default are
    leaves, whose `cnfWidth`/`dnfWidth` are `0 ≤ t`. -/
mutual

theorem buildKillAwareForms_width
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (t : Nat)
    (hgfw : ∀ p i, cnfWidth (gf p i) ≤ t ∧ dnfWidth (gf p i) ≤ t) (needCnf : Bool) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ∀ x ∈ buildKillAwareForms gf il kill needCnf lvl start f,
        cnfWidth x ≤ t ∧ dnfWidth x ≤ t
  | lvl, start, .inputGate i b => by
      unfold buildKillAwareForms buildFormsWith
      by_cases h : lvl ≤ 2
      · simp only [if_pos h, List.mem_singleton]
        intro x hx; subst hx; exact hgfw needCnf start
      · simp only [if_neg h]
        cases kill start with
        | some bb =>
            intro x hx; simp only [List.mem_singleton] at hx; subst hx
            exact ⟨by simp [cnfWidth], by simp [dnfWidth]⟩
        | none =>
            intro x hx; simp only [List.mem_singleton] at hx; subst hx
            exact ⟨by simp [cnfWidth], by simp [dnfWidth]⟩
  | _, start, .constant b m => by
      unfold buildKillAwareForms buildFormsWith
      intro x hx; simp only [List.mem_singleton] at hx; subst hx
      exact ⟨by simp [cnfWidth], by simp [dnfWidth]⟩
  | _, start, .notGate g => by
      unfold buildKillAwareForms buildFormsWith
      intro x hx; simp only [List.mem_singleton] at hx; subst hx
      exact ⟨by simp [cnfWidth], by simp [dnfWidth]⟩
  | lvl, start, .andGate gates => by
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx
        exact hgfw needCnf start
      · exact buildKillAwareFormsList_width gf il kill t hgfw true (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx
        exact hgfw needCnf start
      · exact buildKillAwareFormsList_width gf il kill t hgfw false (lvl - 1) start gates

theorem buildKillAwareFormsList_width
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (t : Nat)
    (hgfw : ∀ p i, cnfWidth (gf p i) ≤ t ∧ dnfWidth (gf p i) ≤ t) (needCnf : Bool) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      ∀ x ∈ buildKillAwareFormsList gf il kill needCnf lvl start gates,
        cnfWidth x ≤ t ∧ dnfWidth x ≤ t
  | _, _, [] => by unfold buildKillAwareFormsList buildFormsWithList; simp
  | lvl, start, g :: gs => by
      unfold buildKillAwareFormsList buildFormsWithList
      simp only [List.mem_append]
      intro x hx
      rcases hx with hx | hx
      · exact buildKillAwareForms_width gf il kill t hgfw needCnf lvl start g x hx
      · exact buildKillAwareFormsList_width gf il kill t hgfw needCnf lvl
          (extractBottomLayer lvl start g).2.2 gs x hx

end

/- Every form emitted by `buildKillAwareForms` has `ufiFormulaCircuitSize ≤ bound`, provided each
    gate form `gf p i` does (`hgf_nc`) and `1 ≤ bound`.  The kill/live `inputGate`
    placeholders, killed `constant` leaves, and the out-of-window default are
    leaves, whose `ufiFormulaCircuitSize` is `1 ≤ bound`. -/
mutual

theorem buildKillAwareForms_ufiFormulaCircuitSize
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (bound : Nat) (h_bound_one : 1 ≤ bound)
    (hgf_nc : ∀ p i, ufiFormulaCircuitSize (gf p i) ≤ bound) (needCnf : Bool) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ∀ x ∈ buildKillAwareForms gf il kill needCnf lvl start f,
        ufiFormulaCircuitSize x ≤ bound
  | lvl, start, .inputGate i b => by
      unfold buildKillAwareForms buildFormsWith
      by_cases h : lvl ≤ 2
      · simp only [if_pos h, List.mem_singleton]
        intro x hx; subst hx; exact hgf_nc needCnf start
      · simp only [if_neg h]
        cases kill start with
        | some bb =>
            intro x hx; simp only [List.mem_singleton] at hx; subst hx
            simp only [ufiFormulaCircuitSize]; exact h_bound_one
        | none =>
            intro x hx; simp only [List.mem_singleton] at hx; subst hx
            simp only [ufiFormulaCircuitSize]
            exact Nat.zero_le _
  | _, start, .constant b m => by
      unfold buildKillAwareForms buildFormsWith
      intro x hx; simp only [List.mem_singleton] at hx; subst hx
      simp only [ufiFormulaCircuitSize]
      exact h_bound_one
  | _, start, .notGate g => by
      unfold buildKillAwareForms buildFormsWith
      intro x hx; simp only [List.mem_singleton] at hx; subst hx
      simp only [ufiFormulaCircuitSize]
      exact Nat.zero_le _
  | lvl, start, .andGate gates => by
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx
        exact hgf_nc needCnf start
      · exact buildKillAwareFormsList_ufiFormulaCircuitSize gf il kill bound h_bound_one hgf_nc true (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx
        exact hgf_nc needCnf start
      · exact buildKillAwareFormsList_ufiFormulaCircuitSize gf il kill bound h_bound_one hgf_nc false (lvl - 1) start gates

theorem buildKillAwareFormsList_ufiFormulaCircuitSize
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (bound : Nat) (h_bound_one : 1 ≤ bound)
    (hgf_nc : ∀ p i, ufiFormulaCircuitSize (gf p i) ≤ bound) (needCnf : Bool) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      ∀ x ∈ buildKillAwareFormsList gf il kill needCnf lvl start gates,
        ufiFormulaCircuitSize x ≤ bound
  | _, _, [] => by unfold buildKillAwareFormsList buildFormsWithList; simp
  | lvl, start, g :: gs => by
      unfold buildKillAwareFormsList buildFormsWithList
      simp only [List.mem_append]
      intro x hx
      rcases hx with hx | hx
      · exact buildKillAwareForms_ufiFormulaCircuitSize gf il kill bound h_bound_one hgf_nc needCnf lvl start g x hx
      · exact buildKillAwareFormsList_ufiFormulaCircuitSize gf il kill bound h_bound_one hgf_nc needCnf lvl
          (extractBottomLayer lvl start g).2.2 gs x hx

end

/- Every input index produced by `buildKillAwareForms` is `< N`, provided every
    `gf p i` form has inputs `< N` and every live (`kill i = none`) rekey
    index `(il i).1` is `< N`.  Source constants and negations are excluded by
    the phase invariants `IsConstantFree` and `IsNotGateFree`; restriction-made
    constants contain no input index. -/
mutual

theorem buildKillAwareForms_inputs
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (bound : Nat)
    (hgfi : ∀ p i, ∀ x ∈ ufiCollectInputIndices (gf p i), x < bound)
    (hili : ∀ i, kill i = none → (il i).1 < bound) (needCnf : Bool) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      IsNotGateFree f → IsConstantFree f →
      ∀ form ∈ buildKillAwareForms gf il kill needCnf lvl start f,
        ∀ x ∈ ufiCollectInputIndices form, x < bound
  | lvl, start, .inputGate i b => by
      intro _ _
      unfold buildKillAwareForms buildFormsWith
      by_cases h : lvl ≤ 2
      · simp only [if_pos h, List.mem_singleton]
        intro form hform; subst hform
        exact hgfi needCnf start
      · simp only [if_neg h]
        cases hk : kill start with
        | some bb =>
            intro form hform; simp only [List.mem_singleton] at hform; subst hform
            intro x hx; simp [ufiCollectInputIndices] at hx
        | none =>
            intro form hform; simp only [List.mem_singleton] at hform; subst hform
            intro x hx
            simp only [ufiCollectInputIndices, List.mem_singleton] at hx
            subst hx
            exact hili start hk
  | _, start, .constant b m => by
      intro _ hcf; simp only [IsConstantFree] at hcf
  | _, start, .notGate g => by
      intro hnn _; simp only [IsNotGateFree] at hnn
  | lvl, start, .andGate gates => by
      intro hnn hcf
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro form hform; simp only [List.mem_singleton] at hform; subst hform
        exact hgfi needCnf start
      · simp only [IsNotGateFree] at hnn
        simp only [IsConstantFree] at hcf
        exact buildKillAwareFormsList_inputs gf il kill bound hgfi hili true (lvl - 1) start gates hnn hcf
  | lvl, start, .orGate gates => by
      intro hnn hcf
      unfold buildKillAwareForms buildFormsWith
      split_ifs with h
      · intro form hform; simp only [List.mem_singleton] at hform; subst hform
        exact hgfi needCnf start
      · simp only [IsNotGateFree] at hnn
        simp only [IsConstantFree] at hcf
        exact buildKillAwareFormsList_inputs gf il kill bound hgfi hili false (lvl - 1) start gates hnn hcf

theorem buildKillAwareFormsList_inputs
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (bound : Nat)
    (hgfi : ∀ p i, ∀ x ∈ ufiCollectInputIndices (gf p i), x < bound)
    (hili : ∀ i, kill i = none → (il i).1 < bound) (needCnf : Bool) :
    ∀ (lvl start : Nat) (gates : List UnboundedFanInFormula),
      (∀ g ∈ gates, IsNotGateFree g) → (∀ g ∈ gates, IsConstantFree g) →
      ∀ form ∈ buildKillAwareFormsList gf il kill needCnf lvl start gates,
        ∀ x ∈ ufiCollectInputIndices form, x < bound
  | _, _, [] => by intro _ _; unfold buildKillAwareFormsList buildFormsWithList; simp
  | lvl, start, g :: gs => by
      intro hnn hcf
      unfold buildKillAwareFormsList buildFormsWithList
      simp only [List.mem_append]
      intro form hform
      rcases hform with hform | hform
      · exact buildKillAwareForms_inputs gf il kill bound hgfi hili needCnf lvl start g
          (hnn g (by simp)) (hcf g (by simp)) form hform
      · exact buildKillAwareFormsList_inputs gf il kill bound hgfi hili needCnf lvl
          (extractBottomLayer lvl start g).2.2 gs
          (fun g' hg' => hnn g' (List.mem_cons_of_mem _ hg'))
          (fun g' hg' => hcf g' (List.mem_cons_of_mem _ hg')) form hform

end

/-- At level `2` the kill-aware form list has exactly one entry. -/
lemma buildKillAwareForms_two_length_one
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (nc : Bool)
    (start : Nat) (g : UnboundedFanInFormula) :
    (buildKillAwareForms gf il kill nc 2 start g).length = 1 := by
  rw [buildKillAwareForms_length gf il kill nc 2 start g, extractBottomLayer_two_length_one]

/-- **Base-window readout.** At level 2 the kill-aware form list
    reads off, at position `k`, the single form built for the `k`-th
    gate (placeholder index `start + k`). -/
theorem buildKillAwareFormsList_two_getD
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (nc : Bool) (defaultFormula : UnboundedFanInFormula) :
    ∀ (start k : Nat) (gates : List UnboundedFanInFormula), k < gates.length →
      (buildKillAwareFormsList gf il kill nc 2 start gates).getD k defaultFormula
        = (buildKillAwareForms gf il kill nc 2 (start + k) (gates.getD k defaultFormula)).getD 0 defaultFormula
  | _, _, [], hk => by simp at hk
  | start, k, g :: gs, hk => by
      rw [buildKillAwareFormsList_cons]
      have hlen : (buildKillAwareForms gf il kill nc 2 start g).length = 1 :=
        buildKillAwareForms_two_length_one gf il kill nc start g
      rw [extractBottomLayer_two_next]
      cases k with
      | zero =>
          rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by rw [hlen]; omega),
              ← List.getD_eq_getElem?_getD]
          simp []
      | succ j =>
          have hj : j < gs.length := by simp only [List.length_cons] at hk; omega
          rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by rw [hlen]; omega), hlen,
              ← List.getD_eq_getElem?_getD]
          rw [show j + 1 - 1 = j from rfl,
              buildKillAwareFormsList_two_getD gf il kill nc defaultFormula (start + 1) j gs hj]
          simp only [List.getD_cons_succ]
          congr 2
          omega

/- **Segment readout for the head.** -/
theorem buildKillAwareFormsList_getD_head
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (nc : Bool)
    (defaultFormula : UnboundedFanInFormula) (lvl start : Nat)
    (g : UnboundedFanInFormula) (gs : List UnboundedFanInFormula)
    (k : Nat) (hk : k < (extractBottomLayer lvl start g).1.length) :
    (buildKillAwareFormsList gf il kill nc lvl start (g :: gs)).getD k defaultFormula
      = (buildKillAwareForms gf il kill nc lvl start g).getD k defaultFormula := by
  have hlen : (buildKillAwareForms gf il kill nc lvl start g).length
      = (extractBottomLayer lvl start g).1.length :=
    buildKillAwareForms_length gf il kill nc lvl start g
  rw [buildKillAwareFormsList_cons]
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hlen]; exact hk),
      ← List.getD_eq_getElem?_getD]

/- **Segment readout for the tail.** -/
theorem buildKillAwareFormsList_getD_tail
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (nc : Bool)
    (defaultFormula : UnboundedFanInFormula) (lvl start : Nat)
    (g : UnboundedFanInFormula) (gs : List UnboundedFanInFormula)
    (k : Nat) (hk : (extractBottomLayer lvl start g).1.length ≤ k) :
    (buildKillAwareFormsList gf il kill nc lvl start (g :: gs)).getD k defaultFormula
      = (buildKillAwareFormsList gf il kill nc lvl (extractBottomLayer lvl start g).2.2 gs).getD
          (k - (extractBottomLayer lvl start g).1.length) defaultFormula := by
  have hlen : (buildKillAwareForms gf il kill nc lvl start g).length
      = (extractBottomLayer lvl start g).1.length :=
    buildKillAwareForms_length gf il kill nc lvl start g
  conv_lhs => rw [buildKillAwareFormsList_cons]
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hlen]; exact hk),
      ← List.getD_eq_getElem?_getD, hlen]

/- **Base-window producer discharge.** For the kill-aware
   substitution map read off the produced form list at level 2, every
   placeholder index `i` in the base window carries the required
   matching-polarity proper form `IsSubstitutionProperFormOrConstant`.  Both gate **and**
   splice-base `inputGate` bottoms route to the caller-supplied switched
   form `gf nc i` (proper by `hgf`); `constant`/`notGate` are excluded
   by `IsConstantFree`/`HasProperBottomsAt`. -/
theorem isSubstitutionProperFormOrConstant_buildKillAwareFormsList_two_window
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool)
    (hgf : ∀ p i, IsSubstitutionProperFormOrConstant (fun _ => gf p i) p 0) (nc : Bool)
    (defaultFormula : UnboundedFanInFormula) :
    ∀ (start : Nat) (gates : List UnboundedFanInFormula),
      (∀ g ∈ gates, IsConstantFree g) →
      (∀ g ∈ gates, HasProperBottomsAt g 2) →
      ∀ i, start ≤ i →
        i < start + (extractBottomLayerList 2 start gates).1.length →
        IsSubstitutionProperFormOrConstant
          (fun m => (buildKillAwareFormsList gf il kill nc 2 start gates).getD (m - start) defaultFormula) nc i := by
  intro start gates h_cf h_pl i hi hi₂
  rw [extractBottomLayerList_two_length start gates] at hi₂
  set k := i - start with hk
  have hik : start + k = i := by omega
  have hklt : k < gates.length := by omega
  have hread : (buildKillAwareFormsList gf il kill nc 2 start gates).getD k defaultFormula
      = (buildKillAwareForms gf il kill nc 2 (start + k) (gates.getD k defaultFormula)).getD 0 defaultFormula :=
    buildKillAwareFormsList_two_getD gf il kill nc defaultFormula start k gates hklt
  have hsub_i :
      (fun m => (buildKillAwareFormsList gf il kill nc 2 start gates).getD (m - start) defaultFormula) i
        = (buildKillAwareForms gf il kill nc 2 (start + k) (gates.getD k defaultFormula)).getD 0 defaultFormula := by
    simp only [← hk]; exact hread
  have hmem : gates.getD k defaultFormula ∈ gates := by
    have hge : gates.getD k defaultFormula = gates[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt]; rfl
    rw [hge]; exact List.getElem_mem hklt
  have h_c_fk : IsConstantFree (gates.getD k defaultFormula) := h_cf _ hmem
  have h_p_lk : HasProperBottomsAt (gates.getD k defaultFormula) 2 := h_pl _ hmem
  cases hg : gates.getD k defaultFormula with
  | inputGate x b =>
      have hval :
          (fun m => (buildKillAwareFormsList gf il kill nc 2 start gates).getD (m - start) defaultFormula) i
            = gf nc i := by
        rw [hsub_i, hg]
        simp only [buildKillAwareForms, buildFormsWith, show (2 : ℕ) ≤ 2 from le_refl 2, if_true,
          List.getD_cons_zero, hik]
      have hgfi := hgf nc i
      unfold IsSubstitutionProperFormOrConstant IsSubstitutionProperForm at hgfi ⊢
      rw [hval]; simpa using hgfi
  | constant b m =>
      rw [hg] at h_c_fk; simp only [IsConstantFree] at h_c_fk
  | notGate g₀ =>
      rw [hg] at h_p_lk; simp only [HasProperBottomsAt] at h_p_lk
  | andGate gs' =>
      have hval :
          (fun m => (buildKillAwareFormsList gf il kill nc 2 start gates).getD (m - start) defaultFormula) i
            = gf nc i := by
        rw [hsub_i, hg]
        simp only [buildKillAwareForms, buildFormsWith, show (2 : ℕ) ≤ 2 from le_refl 2, if_true,
          List.getD_cons_zero, hik]
      have hgfi := hgf nc i
      unfold IsSubstitutionProperFormOrConstant IsSubstitutionProperForm at hgfi ⊢
      rw [hval]; simpa using hgfi
  | orGate gs' =>
      have hval :
          (fun m => (buildKillAwareFormsList gf il kill nc 2 start gates).getD (m - start) defaultFormula) i
            = gf nc i := by
        rw [hsub_i, hg]
        simp only [buildKillAwareForms, buildFormsWith, show (2 : ℕ) ≤ 2 from le_refl 2, if_true,
          List.getD_cons_zero, hik]
      have hgfi := hgf nc i
      unfold IsSubstitutionProperFormOrConstant IsSubstitutionProperForm at hgfi ⊢
      rw [hval]; simpa using hgfi

/- **Kill-aware constant-tolerant producer (mutual).** Above-splice `inputGate`
   leaves now consult `kill` — a killed coordinate becomes a `constant`
   (`IsSubstitutionLeaf` via `Or.inr`), a live coordinate a bare `inputGate` (via
   `Or.inl`). -/
mutual

theorem isExtractionSubstitutionReadyWithConstants_buildKillAwareForms
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool)
    (hgf : ∀ p i, IsSubstitutionProperFormOrConstant (fun _ => gf p i) p 0) (defaultFormula : UnboundedFanInFormula) :
    ∀ (nc : Bool) (lvl start : Nat) (f : UnboundedFanInFormula),
      IsConstantFree f →
      HasProperBottomsAt f lvl →
      IsAlternatingAndLeveledAt f lvl →
      IsExtractionSubstitutionReadyWithConstants
        (fun i => (buildKillAwareForms gf il kill nc lvl start f).getD (i - start) defaultFormula)
        lvl start f
  | _, _, _, .inputGate x b, _, _, _ => by trivial
  | _, _, _, .constant b m, _, _, _ => by trivial
  | _, _, _, .notGate g, _, hpl, _ => by
      simp only [HasProperBottomsAt] at hpl
  | nc, lvl, start, .andGate gates, h_cf, hpl, hsl => by
      simp only [IsExtractionSubstitutionReadyWithConstants]
      by_cases h₁ : lvl ≤ 2
      · rw [if_pos h₁]; trivial
      · rw [if_neg h₁]
        have hforms : (fun i => (buildKillAwareForms gf il kill nc lvl start (.andGate gates)).getD (i - start) defaultFormula)
            = (fun i => (buildKillAwareFormsList gf il kill true (lvl - 1) start gates).getD (i - start) defaultFormula) := by
          funext i; simp only [buildKillAwareForms_andGate, if_neg h₁]
        rw [hforms]
        by_cases h₂ : lvl ≤ 3
        · rw [if_pos h₂]
          have hlv : lvl = 3 := by omega
          subst hlv
          simp only [show (3 : ℕ) - 1 = 2 from rfl]
          have h_cf' : ∀ g ∈ gates, IsConstantFree g := by
            simpa only [IsConstantFree] using h_cf
          have hpl' : ∀ g ∈ gates, HasProperBottomsAt g 2 := by
            have := hpl; unfold HasProperBottomsAt at this
            simpa only [if_neg h₁, show (3 : ℕ) - 1 = 2 from rfl] using this
          refine isExtractionBaseListSubstitutionReadyWithConstants_of_isSubstitutionProperFormOrConstant _ true start gates ?_
          intro i hi hi₂
          have hwin := isSubstitutionProperFormOrConstant_buildKillAwareFormsList_two_window gf il kill hgf true defaultFormula
            start gates h_cf' hpl' i hi
          rw [extractBottomLayerList_two_length start gates] at hwin
          exact hwin hi₂
        · rw [if_neg h₂]
          have hsl' := hsl
          simp only [IsAlternatingAndLeveledAt] at hsl'
          obtain ⟨_, _, hsl_ch⟩ := hsl'
          have h_cf' : ∀ g ∈ gates, IsConstantFree g := by
            simpa only [IsConstantFree] using h_cf
          have hpl' : ∀ g ∈ gates, HasProperBottomsAt g (lvl - 1) := by
            have := hpl; unfold HasProperBottomsAt at this
            simpa only [if_neg h₁] using this
          exact isExtractionRecursiveListSubstitutionReadyWithConstants_buildKillAwareFormsList gf il kill hgf defaultFormula true (lvl - 1) start gates
            (by omega) h_cf' hpl' hsl_ch
  | nc, lvl, start, .orGate gates, h_cf, hpl, hsl => by
      simp only [IsExtractionSubstitutionReadyWithConstants]
      by_cases h₁ : lvl ≤ 2
      · rw [if_pos h₁]; trivial
      · rw [if_neg h₁]
        have hforms : (fun i => (buildKillAwareForms gf il kill nc lvl start (.orGate gates)).getD (i - start) defaultFormula)
            = (fun i => (buildKillAwareFormsList gf il kill false (lvl - 1) start gates).getD (i - start) defaultFormula) := by
          funext i; simp only [buildKillAwareForms_orGate, if_neg h₁]
        rw [hforms]
        by_cases h₂ : lvl ≤ 3
        · rw [if_pos h₂]
          have hlv : lvl = 3 := by omega
          subst hlv
          simp only [show (3 : ℕ) - 1 = 2 from rfl]
          have h_cf' : ∀ g ∈ gates, IsConstantFree g := by
            simpa only [IsConstantFree] using h_cf
          have hpl' : ∀ g ∈ gates, HasProperBottomsAt g 2 := by
            have := hpl; unfold HasProperBottomsAt at this
            simpa only [if_neg h₁, show (3 : ℕ) - 1 = 2 from rfl] using this
          refine isExtractionBaseListSubstitutionReadyWithConstants_of_isSubstitutionProperFormOrConstant _ false start gates ?_
          intro i hi hi₂
          have hwin := isSubstitutionProperFormOrConstant_buildKillAwareFormsList_two_window gf il kill hgf false defaultFormula
            start gates h_cf' hpl' i hi
          rw [extractBottomLayerList_two_length start gates] at hwin
          exact hwin hi₂
        · rw [if_neg h₂]
          have hsl' := hsl
          simp only [IsAlternatingAndLeveledAt] at hsl'
          obtain ⟨_, _, hsl_ch⟩ := hsl'
          have h_cf' : ∀ g ∈ gates, IsConstantFree g := by
            simpa only [IsConstantFree] using h_cf
          have hpl' : ∀ g ∈ gates, HasProperBottomsAt g (lvl - 1) := by
            have := hpl; unfold HasProperBottomsAt at this
            simpa only [if_neg h₁] using this
          exact isExtractionRecursiveListSubstitutionReadyWithConstants_buildKillAwareFormsList gf il kill hgf defaultFormula false (lvl - 1) start gates
            (by omega) h_cf' hpl' hsl_ch

theorem isExtractionRecursiveListSubstitutionReadyWithConstants_buildKillAwareFormsList
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool)
    (hgf : ∀ p i, IsSubstitutionProperFormOrConstant (fun _ => gf p i) p 0) (defaultFormula : UnboundedFanInFormula) :
    ∀ (nc : Bool) (lvl start : Nat) (gates : List UnboundedFanInFormula),
      3 ≤ lvl →
      (∀ g ∈ gates, IsConstantFree g) →
      (∀ g ∈ gates, HasProperBottomsAt g lvl) →
      (∀ g ∈ gates, IsAlternatingAndLeveledAt g lvl) →
      IsExtractionRecursiveListSubstitutionReadyWithConstants
        (fun i => (buildKillAwareFormsList gf il kill nc lvl start gates).getD (i - start) defaultFormula)
        lvl start gates
  | _, _, _, [], _, _, _, _ => by trivial
  | nc, lvl, start, g :: gs, hlvl, h_cf, hpl, hsl => by
      unfold IsExtractionRecursiveListSubstitutionReadyWithConstants
      have hnle : ¬ lvl ≤ 2 := by omega
      have h_cf₀ : IsConstantFree g := h_cf g (by simp)
      have hpl₀ : HasProperBottomsAt g lvl := hpl g (by simp)
      have hsl₀ : IsAlternatingAndLeveledAt g lvl := hsl g (by simp)
      have hnext : (extractBottomLayer lvl start g).2.2
          = start + (extractBottomLayer lvl start g).1.length :=
        extractBottomLayer_next_index lvl start g
      refine ⟨?_, ?_⟩
      · cases g with
        | inputGate x b =>
          simp only []
          unfold IsSubstitutionLeaf
          have hread :
              (fun i => (buildKillAwareFormsList gf il kill nc lvl start (UnboundedFanInFormula.inputGate x b :: gs)).getD (i - start) defaultFormula) start
                = (buildKillAwareForms gf il kill nc lvl start (UnboundedFanInFormula.inputGate x b)).getD 0 defaultFormula := by
            simp only [Nat.sub_self]
            rw [buildKillAwareFormsList_getD_head gf il kill nc defaultFormula lvl start (UnboundedFanInFormula.inputGate x b) gs 0
                (by simp [extractBottomLayer])]
          cases hkv : kill start with
          | some bb =>
            refine Or.inr ⟨bb, 0, ?_⟩
            rw [hread]
            unfold buildKillAwareForms buildFormsWith
            rw [if_neg hnle, hkv]
            rfl
          | none =>
            refine Or.inl ⟨(il start).1, (il start).2, ?_⟩
            rw [hread]
            unfold buildKillAwareForms buildFormsWith
            rw [if_neg hnle, hkv]
            rfl
        | constant b m =>
          exact absurd h_cf₀ (by simp [IsConstantFree])
        | notGate g₀ =>
          simp only [HasProperBottomsAt] at hpl₀
        | andGate gs' =>
          simp only []
          have hrec := isExtractionSubstitutionReadyWithConstants_buildKillAwareForms gf il kill hgf defaultFormula nc lvl start (.andGate gs')
            h_cf₀ hpl₀ hsl₀
          refine isExtractionSubstitutionReadyWithConstants_congr _ _ lvl start (.andGate gs') ?_ hrec
          intro i hi hi₂
          symm
          exact buildKillAwareFormsList_getD_head gf il kill nc defaultFormula lvl start (.andGate gs') gs
            (i - start) (by omega)
        | orGate gs' =>
          simp only []
          have hrec := isExtractionSubstitutionReadyWithConstants_buildKillAwareForms gf il kill hgf defaultFormula nc lvl start (.orGate gs')
            h_cf₀ hpl₀ hsl₀
          refine isExtractionSubstitutionReadyWithConstants_congr _ _ lvl start (.orGate gs') ?_ hrec
          intro i hi hi₂
          symm
          exact buildKillAwareFormsList_getD_head gf il kill nc defaultFormula lvl start (.orGate gs') gs
            (i - start) (by omega)
      · have h_cf_tl : ∀ g' ∈ gs, IsConstantFree g' := fun g' hg' => h_cf g' (by simp [hg'])
        have hpl_tl : ∀ g' ∈ gs, HasProperBottomsAt g' lvl := fun g' hg' => hpl g' (by simp [hg'])
        have hsl_tl : ∀ g' ∈ gs, IsAlternatingAndLeveledAt g' lvl :=
          fun g' hg' => hsl g' (by simp [hg'])
        have hrec := isExtractionRecursiveListSubstitutionReadyWithConstants_buildKillAwareFormsList gf il kill hgf defaultFormula nc lvl
          (extractBottomLayer lvl start g).2.2 gs hlvl h_cf_tl hpl_tl hsl_tl
        refine isExtractionRecursiveListSubstitutionReadyWithConstants_congr _ _ lvl
          (extractBottomLayer lvl start g).2.2 gs ?_ hrec
        intro i hi hi₂
        symm
        rw [hnext] at hi
        rw [buildKillAwareFormsList_getD_tail gf il kill nc defaultFormula lvl start g gs (i - start) (by omega)]
        rw [hnext, Nat.sub_sub]

end

/- **Per-bottom eval readout (mutual).**  Walks the `buildKillAwareForms` /
   `extractBottomLayer` recursion in lockstep (mirror of
   `isExtractionSubstitutionReadyWithConstants_buildKillAwareForms`) to read off the *evaluation* of each
   produced bottom form.  The conclusion compares, at every local
   placeholder offset `k`, the produced form `buildKillAwareForms …[k]`
   evaluated on `liveBits` with the *global* extracted bottom
   `raw[start+k]` evaluated on `assemble`.  Three caller-supplied eval
   facts cover the three splice cases:

   * `hgf_eval`: every switched form `gf p m` (used at depth-≤2 bottoms
     **and** depth-≤2 `inputGate` leaves) computes `raw[m]` on `assemble`,
     for *both* polarities `p` (the polarity-independent `gf` interface);
   * `hkill_eval`: a restriction-killed above-splice `inputGate` becomes a
     `constant` whose value equals the dead-coordinate read of `raw[m]`;
   * `hil_eval`: a live above-splice `inputGate` is rekeyed to its live rank.

   The `halign` hypothesis threads the positional identity
   `(extractBottomLayer …).1[k] = raw[start+k]` (needed only to expose
   the `inputGate` witness for `hkill_eval`/`hil_eval`); it is preserved
   across the list recursion by `List.getElem?_append_left/right`. -/
mutual

theorem buildKillAwareForms_eval
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (raw : List UnboundedFanInFormula)
    (defaultFormula : UnboundedFanInFormula) (liveBits assemble : List Bool)
    (hgf_eval : ∀ (p : Bool) (m : Nat), m < raw.length →
        ufiFormulaEval (gf p m) liveBits
          = ufiFormulaEval (raw.getD m defaultFormula) assemble)
    (hkill_eval : ∀ (m x : Nat) (b : Bool) (bb : Bool), m < raw.length →
        raw.getD m defaultFormula = UnboundedFanInFormula.inputGate x b → kill m = some bb →
        ufiFormulaEval (UnboundedFanInFormula.constant bb 0) liveBits
          = ufiFormulaEval (raw.getD m defaultFormula) assemble)
    (hil_eval : ∀ (m x : Nat) (b : Bool), m < raw.length →
        raw.getD m defaultFormula = UnboundedFanInFormula.inputGate x b → kill m = none →
        ufiFormulaEval (UnboundedFanInFormula.inputGate (il m).1 (il m).2) liveBits
          = ufiFormulaEval (raw.getD m defaultFormula) assemble) :
    ∀ (nc : Bool) (lvl start : Nat) (f : UnboundedFanInFormula),
      IsConstantFree f → HasProperBottomsAt f lvl →
      IsAlternatingAndLeveledAt f lvl →
      start + (extractBottomLayer lvl start f).1.length ≤ raw.length →
      (∀ j, j < (extractBottomLayer lvl start f).1.length →
          (extractBottomLayer lvl start f).1.getD j defaultFormula = raw.getD (start + j) defaultFormula) →
      ∀ k, k < (extractBottomLayer lvl start f).1.length →
        ufiFormulaEval ((buildKillAwareForms gf il kill nc lvl start f).getD k defaultFormula) liveBits
          = ufiFormulaEval (raw.getD (start + k) defaultFormula) assemble
  | nc, lvl, start, .inputGate x b, _, _, _, hfit, halign, k, hk => by
      have hlen₁ : (extractBottomLayer lvl start (UnboundedFanInFormula.inputGate x b)).1.length = 1 := rfl
      have hk₀ : k = 0 := by omega
      subst hk₀
      simp only [Nat.add_zero]
      have hslt : start < raw.length := by omega
      have hraw : raw.getD start defaultFormula = UnboundedFanInFormula.inputGate x b := by
        have h := halign 0 (by omega)
        have hl : (extractBottomLayer lvl start (UnboundedFanInFormula.inputGate x b)).1.getD 0 defaultFormula
            = UnboundedFanInFormula.inputGate x b := rfl
        rw [hl, Nat.add_zero] at h
        exact h.symm
      by_cases hl₂ : lvl ≤ 2
      · have hbf : (buildKillAwareForms gf il kill nc lvl start
            (UnboundedFanInFormula.inputGate x b)).getD 0 defaultFormula = gf nc start := by
          simp only [buildKillAwareForms_input, if_pos hl₂, List.getD_cons_zero]
        rw [hbf]; exact hgf_eval nc start hslt
      · cases hks : kill start with
        | some bb =>
            have hbf : (buildKillAwareForms gf il kill nc lvl start
                (UnboundedFanInFormula.inputGate x b)).getD 0 defaultFormula
                = UnboundedFanInFormula.constant bb 0 := by
              simp only [buildKillAwareForms_input, if_neg hl₂, hks, List.getD_cons_zero]
            rw [hbf]
            exact hkill_eval start x b bb hslt hraw hks
        | none =>
            have hbf : (buildKillAwareForms gf il kill nc lvl start
                (UnboundedFanInFormula.inputGate x b)).getD 0 defaultFormula
                = UnboundedFanInFormula.inputGate (il start).1 (il start).2 := by
              simp only [buildKillAwareForms_input, if_neg hl₂, hks, List.getD_cons_zero]
            rw [hbf]
            exact hil_eval start x b hslt hraw hks
  | _, _, _, .constant b m, h_cf, _, _, _, _, _, _ => by
      simp only [IsConstantFree] at h_cf
  | _, _, _, .notGate g, _, hpl, _, _, _, _, _ => by
      simp only [HasProperBottomsAt] at hpl
  | nc, lvl, start, .andGate gates, h_cf, hpl, hsl, hfit, halign, k, hk => by
      by_cases hl₂ : lvl ≤ 2
      · have hlen₁ : (extractBottomLayer lvl start (UnboundedFanInFormula.andGate gates)).1.length = 1 := by
          simp only [extractBottomLayer, if_pos hl₂, List.length_singleton]
        have hk₀ : k = 0 := by omega
        subst hk₀
        simp only [Nat.add_zero]
        have hslt : start < raw.length := by omega
        have hbf : (buildKillAwareForms gf il kill nc lvl start
            (UnboundedFanInFormula.andGate gates)).getD 0 defaultFormula = gf nc start := by
          simp only [buildKillAwareForms, buildFormsWith, if_pos hl₂, List.getD_cons_zero]
        rw [hbf]; exact hgf_eval nc start hslt
      · have hform : buildKillAwareForms gf il kill nc lvl start
            (UnboundedFanInFormula.andGate gates)
            = buildKillAwareFormsList gf il kill true (lvl - 1) start gates := by
          simp only [buildKillAwareForms_andGate, if_neg hl₂]
        have hext : (extractBottomLayer lvl start
            (UnboundedFanInFormula.andGate gates)).1
            = (extractBottomLayerList (lvl - 1) start gates).1 := by
          simp only [extractBottomLayer, if_neg hl₂]
        rw [hform]
        rw [hext] at hk hfit halign
        have hlvl₁ : 2 ≤ lvl - 1 := by omega
        have h_cf' : ∀ g ∈ gates, IsConstantFree g := by
          simpa only [IsConstantFree] using h_cf
        have hpl' : ∀ g ∈ gates, HasProperBottomsAt g (lvl - 1) := by
          have h := hpl; unfold HasProperBottomsAt at h
          simpa only [if_neg hl₂] using h
        have hsl' : ∀ g ∈ gates,
            IsAlternatingAndLeveledAt g (lvl - 1) := by
          have h := hsl
          simp only [IsAlternatingAndLeveledAt] at h
          exact h.2.2
        exact buildKillAwareFormsList_eval gf il kill raw defaultFormula liveBits assemble
          hgf_eval hkill_eval hil_eval true (lvl - 1) start gates hlvl₁
          h_cf' hpl' hsl' hfit halign k hk
  | nc, lvl, start, .orGate gates, h_cf, hpl, hsl, hfit, halign, k, hk => by
      by_cases hl₂ : lvl ≤ 2
      · have hlen₁ : (extractBottomLayer lvl start (UnboundedFanInFormula.orGate gates)).1.length = 1 := by
          simp only [extractBottomLayer, if_pos hl₂, List.length_singleton]
        have hk₀ : k = 0 := by omega
        subst hk₀
        simp only [Nat.add_zero]
        have hslt : start < raw.length := by omega
        have hbf : (buildKillAwareForms gf il kill nc lvl start
            (UnboundedFanInFormula.orGate gates)).getD 0 defaultFormula = gf nc start := by
          simp only [buildKillAwareForms_orGate, if_pos hl₂, List.getD_cons_zero]
        rw [hbf]; exact hgf_eval nc start hslt
      · have hform : buildKillAwareForms gf il kill nc lvl start
            (UnboundedFanInFormula.orGate gates)
            = buildKillAwareFormsList gf il kill false (lvl - 1) start gates := by
          simp only [buildKillAwareForms_orGate, if_neg hl₂]
        have hext : (extractBottomLayer lvl start
            (UnboundedFanInFormula.orGate gates)).1
            = (extractBottomLayerList (lvl - 1) start gates).1 := by
          simp only [extractBottomLayer, if_neg hl₂]
        rw [hform]
        rw [hext] at hk hfit halign
        have hlvl₁ : 2 ≤ lvl - 1 := by omega
        have h_cf' : ∀ g ∈ gates, IsConstantFree g := by
          simpa only [IsConstantFree] using h_cf
        have hpl' : ∀ g ∈ gates, HasProperBottomsAt g (lvl - 1) := by
          have h := hpl; unfold HasProperBottomsAt at h
          simpa only [if_neg hl₂] using h
        have hsl' : ∀ g ∈ gates,
            IsAlternatingAndLeveledAt g (lvl - 1) := by
          have h := hsl
          simp only [IsAlternatingAndLeveledAt] at h
          exact h.2.2
        exact buildKillAwareFormsList_eval gf il kill raw defaultFormula liveBits assemble
          hgf_eval hkill_eval hil_eval false (lvl - 1) start gates hlvl₁
          h_cf' hpl' hsl' hfit halign k hk

theorem buildKillAwareFormsList_eval
    (gf : Bool → Nat → UnboundedFanInFormula) (il : Nat → Nat × Bool)
    (kill : Nat → Option Bool) (raw : List UnboundedFanInFormula)
    (defaultFormula : UnboundedFanInFormula) (liveBits assemble : List Bool)
    (hgf_eval : ∀ (p : Bool) (m : Nat), m < raw.length →
        ufiFormulaEval (gf p m) liveBits
          = ufiFormulaEval (raw.getD m defaultFormula) assemble)
    (hkill_eval : ∀ (m x : Nat) (b : Bool) (bb : Bool), m < raw.length →
        raw.getD m defaultFormula = UnboundedFanInFormula.inputGate x b → kill m = some bb →
        ufiFormulaEval (UnboundedFanInFormula.constant bb 0) liveBits
          = ufiFormulaEval (raw.getD m defaultFormula) assemble)
    (hil_eval : ∀ (m x : Nat) (b : Bool), m < raw.length →
        raw.getD m defaultFormula = UnboundedFanInFormula.inputGate x b → kill m = none →
        ufiFormulaEval (UnboundedFanInFormula.inputGate (il m).1 (il m).2) liveBits
          = ufiFormulaEval (raw.getD m defaultFormula) assemble) :
    ∀ (nc : Bool) (lvl start : Nat) (gates : List UnboundedFanInFormula),
      2 ≤ lvl →
      (∀ g ∈ gates, IsConstantFree g) →
      (∀ g ∈ gates, HasProperBottomsAt g lvl) →
      (∀ g ∈ gates, IsAlternatingAndLeveledAt g lvl) →
      start + (extractBottomLayerList lvl start gates).1.length ≤ raw.length →
      (∀ j, j < (extractBottomLayerList lvl start gates).1.length →
          (extractBottomLayerList lvl start gates).1.getD j defaultFormula = raw.getD (start + j) defaultFormula) →
      ∀ k, k < (extractBottomLayerList lvl start gates).1.length →
        ufiFormulaEval ((buildKillAwareFormsList gf il kill nc lvl start gates).getD k defaultFormula) liveBits
          = ufiFormulaEval (raw.getD (start + k) defaultFormula) assemble
  | _, _, _, [], _, _, _, _, _, _, k, hk => by
      simp only [extractBottomLayerList, List.length_nil] at hk
      omega
  | nc, lvl, start, g :: gs, hlvl, h_cf, hpl, hsl, hfit, halign, k, hk => by
      have hnext : (extractBottomLayer lvl start g).2.2
          = start + (extractBottomLayer lvl start g).1.length :=
        extractBottomLayer_next_index lvl start g
      have hsplit : (extractBottomLayerList lvl start (g :: gs)).1
          = (extractBottomLayer lvl start g).1
            ++ (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1 := rfl
      have hsplitlen : (extractBottomLayerList lvl start (g :: gs)).1.length
          = (extractBottomLayer lvl start g).1.length
            + (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1.length := by
        rw [hsplit, List.length_append]
      by_cases hkc : k < (extractBottomLayer lvl start g).1.length
      · -- head: route into the leading sub-formula `g`.
        rw [buildKillAwareFormsList_getD_head gf il kill nc defaultFormula lvl start g gs k hkc]
        have h_c_fg : IsConstantFree g := h_cf g (by simp)
        have hplg : HasProperBottomsAt g lvl := hpl g (by simp)
        have hslg : IsAlternatingAndLeveledAt g lvl := hsl g (by simp)
        have hfitg : start + (extractBottomLayer lvl start g).1.length ≤ raw.length := by
          rw [hsplitlen] at hfit; omega
        have halign_g : ∀ j, j < (extractBottomLayer lvl start g).1.length →
            (extractBottomLayer lvl start g).1.getD j defaultFormula = raw.getD (start + j) defaultFormula := by
          intro j hj
          have hj' : j < (extractBottomLayerList lvl start (g :: gs)).1.length := by
            rw [hsplitlen]; omega
          have hge := halign j hj'
          rw [hsplit, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD] at hge
          exact hge
        exact buildKillAwareForms_eval gf il kill raw defaultFormula liveBits assemble
          hgf_eval hkill_eval hil_eval nc lvl start g h_c_fg hplg hslg hfitg halign_g k hkc
      · -- tail: route past `g` into the remaining gates `gs`.
        push Not at hkc
        rw [buildKillAwareFormsList_getD_tail gf il kill nc defaultFormula lvl start g gs k hkc]
        have hkk : start + k
            = (extractBottomLayer lvl start g).2.2
              + (k - (extractBottomLayer lvl start g).1.length) := by
          rw [hnext]; omega
        rw [hkk]
        have h_c_ft : ∀ g' ∈ gs, IsConstantFree g' := fun g' hg' => h_cf g' (by simp [hg'])
        have hplt : ∀ g' ∈ gs, HasProperBottomsAt g' lvl := fun g' hg' => hpl g' (by simp [hg'])
        have hslt : ∀ g' ∈ gs,
            IsAlternatingAndLeveledAt g' lvl :=
          fun g' hg' => hsl g' (by simp [hg'])
        have hfitt : (extractBottomLayer lvl start g).2.2
            + (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1.length
              ≤ raw.length := by
          rw [hsplitlen] at hfit; omega
        have halign_t : ∀ j,
            j < (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1.length →
            (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1.getD j defaultFormula
              = raw.getD ((extractBottomLayer lvl start g).2.2 + j) defaultFormula := by
          intro j hj
          have hj' : (extractBottomLayer lvl start g).1.length + j
              < (extractBottomLayerList lvl start (g :: gs)).1.length := by
            rw [hsplitlen]; omega
          have hge := halign ((extractBottomLayer lvl start g).1.length + j) hj'
          rw [hsplit, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD] at hge
          simp only [Nat.add_sub_cancel_left] at hge
          rw [show start + ((extractBottomLayer lvl start g).1.length + j)
              = (extractBottomLayer lvl start g).2.2 + j from by rw [hnext]; omega] at hge
          exact hge
        have hk_tl : k - (extractBottomLayer lvl start g).1.length
            < (extractBottomLayerList lvl (extractBottomLayer lvl start g).2.2 gs).1.length := by
          rw [hsplitlen] at hk; omega
        exact buildKillAwareFormsList_eval gf il kill raw defaultFormula liveBits assemble
          hgf_eval hkill_eval hil_eval nc lvl (extractBottomLayer lvl start g).2.2 gs hlvl
          h_c_ft hplt hslt hfitt halign_t
          (k - (extractBottomLayer lvl start g).1.length) hk_tl

end

/-- A literal bottom is restriction-trivial: dead literals become constants,
    while live literals become rekeyed unit CNFs/DNFs.  Literal occurrences
    therefore do not participate in the switching-lemma union bound. -/
lemma exists_restricted_literal_form_for_polarity
    {n : Nat} (t : Nat) {σ : OpenUnitIntervalQ} (ht : 2 ≤ t)
    (ρ : AssignedRandomRestriction σ n)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (_h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_live_pos : 0 < live.length) (p : Bool) (x : Nat) (b : Bool) (hx : x < n) :
    ∃ g : UnboundedFanInFormula,
      IsSubstitutionProperFormOrConstant (fun _ => g) p 0 ∧
      ufiLargestInput g < live.length ∧
      cnfWidth g ≤ t ∧ dnfWidth g ≤ t ∧
      ufiFormulaCircuitSize g ≤
        1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) ∧
      ∀ liveBits, liveBits.length = live.length →
        ufiFormulaEval (.inputGate x b)
          (assembleInput n live liveBits deadBits) =
          ufiFormulaEval g liveBits := by
  cases ha : mkAssignment ρ.starAssignment.val.val ρ.varAssignments x with
  | some bit =>
      let value := if b then !bit else bit
      refine ⟨.constant value 0, Or.inr ⟨value, 0, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [ufiLargestInput, ufiCollectInputIndices] using h_live_pos
      · simp [cnfWidth]
      · simp [dnfWidth]
      · simp [ufiFormulaCircuitSize]
      · intro liveBits hlen
        have hget := h_assemble liveBits hlen x bit ha
        cases b <;> cases bit <;> simp [value, ufiFormulaEval, hget]
  | none =>
      have hxstar : x ∈ ρ.starAssignment.val.val :=
        mkAssignment_none_imp_mem ρ.starAssignment.val.val ρ.varAssignments n
          ρ.starAssignment.val.property ρ.non_starred_vars_fully_assigned x hx ha
      have hxm : x ∈ ρ.starAssignment.val.val.val := Finset.mem_def.mp hxstar
      rw [← h_live_eq] at hxm
      have hxlive : x ∈ live := Multiset.mem_coe.mp hxm
      let j := live.idxOf x
      have hjlt : j < live.length := List.idxOf_lt_length_iff.mpr hxlive
      have hfind : live.findIdx? (· = x) = some j := by
        rw [List.findIdx?_eq_some_iff_getElem]
        have hgetj : live[j] = x := List.getElem_idxOf hjlt
        refine ⟨hjlt, by simpa using hgetj, ?_⟩
        intro q hq
        simp only [decide_eq_true_eq]
        intro hqx
        have hqlt : q < live.length := Nat.lt_trans hq hjlt
        have heq : live[q] = live[j] := by rw [hqx, hgetj]
        have hqj := (List.Nodup.getElem_inj_iff h_live_nodup).mp heq
        omega
      cases p with
      | false =>
          obtain ⟨_, _, _, hbnd, heval⟩ := litToProperDNF_spec j b live.length hjlt
          refine ⟨litToProperDNF j b, Or.inl ?_, hbnd, ?_, ?_, ?_, ?_⟩
          · exact isSubstitutionProperForm_litToProperDNF _ 0 j b rfl
          · simp [litToProperDNF, cnfWidth]
          · simp [litToProperDNF, dnfWidth]; omega
          · simp only [litToProperDNF, ufiFormulaCircuitSize, List.map_cons,
              List.map_nil, List.sum_cons, List.sum_nil]
            have hposmul : 0 < (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) :=
              Nat.mul_pos (by omega) (by omega)
            omega
          · intro liveBits hlen
            rw [heval liveBits]
            have hget := assembleInput_at_live n live liveBits deadBits hlen
              h_live_lt x hxlive j hfind
            unfold ufiFormulaEval
            rw [hget]
      | true =>
          obtain ⟨_, _, _, hbnd, heval⟩ := litToProperCNF_spec j b live.length hjlt
          refine ⟨litToProperCNF j b, Or.inl ?_, hbnd, ?_, ?_, ?_, ?_⟩
          · exact isSubstitutionProperForm_litToProperCNF _ 0 j b rfl
          · simp [litToProperCNF, cnfWidth]; omega
          · simp [litToProperCNF, dnfWidth]
          · simp only [litToProperCNF, ufiFormulaCircuitSize, List.map_cons,
              List.map_nil, List.sum_cons, List.sum_nil]
            have hposmul : 0 < (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) :=
              Nat.mul_pos (by omega) (by omega)
            omega
          · intro liveBits hlen
            rw [heval liveBits]
            have hget := assembleInput_at_live n live liveBits deadBits hlen
              h_live_lt x hxlive j hfind
            unfold ufiFormulaEval
            rw [hget]

/-- **Polarity-on-demand per-bottom narrow producer.**  Delivers, for every
    requested polarity `p`, a proper CNF (`p = true`) or DNF (`p = false`) on
    the live coordinates that computes the same function as the raw extracted
    bottom. Genuine gates are supplied through the proof-directed `bottom`
    constructor; literals and empty gates are handled directly. Built on
    `exists_bottom_sub_proper_for_polarity`, whose four-way readout makes the eval
    agreement hold unconditionally in `p` — this is what lets the
    `buildKillAwareForms` substitution map drop its polarity gate. -/
lemma exists_build_narrow_sub_for_polarity
    {n : Nat} (t : Nat) {σ : OpenUnitIntervalQ} (ht : 2 ≤ t)
    (raw : List UnboundedFanInFormula)
    (ρ : AssignedRandomRestriction σ n)
    (bottom : ∀ g, g ∈ raw → IsSwitchingGate g → BottomFormula n)
    (h_bottom : ∀ g hg h_gate, (bottom g hg h_gate).toUFI = g)
    (hρ_all : ∀ g (hg : g ∈ raw) (h_gate : IsSwitchingGate g),
        ¬ isBadRestriction t n σ
            (exists_bottomFormula_dnf_view (bottom g hg h_gate)).choose ρ)
    (hraw_kind : ∀ g ∈ raw,
      IsSwitchingGate g ∨ (∃ x b, g = .inputGate x b) ∨
        g = .andGate [] ∨ g = .orGate [])
    (hraw_inputs : ∀ g ∈ raw, ∀ x ∈ ufiCollectInputIndices g, x < n)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_dt_lt : t < live.length) :
    ∃ narrowForm : Bool → Nat → UnboundedFanInFormula,
      (∀ p i, i < raw.length →
        IsSubstitutionProperFormOrConstant (fun _ => narrowForm p i) p 0) ∧
      (∀ p i, i < raw.length → ufiLargestInput (narrowForm p i) < live.length) ∧
      (∀ p i, i < raw.length → cnfWidth (narrowForm p i) ≤ t) ∧
      (∀ p i, i < raw.length → dnfWidth (narrowForm p i) ≤ t) ∧
      (∀ p i, i < raw.length → ufiFormulaCircuitSize (narrowForm p i)
        ≤ 1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2)) ∧
      (∀ p i, i < raw.length → ∀ liveBits, liveBits.length = live.length →
        ufiFormulaEval
            (raw.getD i (.inputGate 0 false))
            (assembleInput n live liveBits deadBits) =
          ufiFormulaEval (narrowForm p i) liveBits) := by
  have hpoint : ∀ (p : Bool) (i : Nat), ∃ g : UnboundedFanInFormula,
      i < raw.length →
        (IsSubstitutionProperFormOrConstant (fun _ => g) p 0 ∧
         ufiLargestInput g < live.length ∧
         cnfWidth g ≤ t ∧
         dnfWidth g ≤ t ∧
         ufiFormulaCircuitSize g ≤ 1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) ∧
         ∀ liveBits, liveBits.length = live.length →
          ufiFormulaEval
              (raw.getD i (.inputGate 0 false))
              (assembleInput n live liveBits deadBits) =
            ufiFormulaEval g liveBits) := by
    intro p i
    by_cases hi : i < raw.length
    · have hmem : raw.getD i (.inputGate 0 false) ∈ raw := by
        have hge : raw.getD i (.inputGate 0 false) = raw[i] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        rw [hge]; exact List.getElem_mem hi
      rcases hraw_kind _ hmem with hgate | ⟨x, b, hinput⟩ | hempty | hempty
      · set f := bottom (raw.getD i (.inputGate 0 false)) hmem hgate with hf_def
        have hρ : ¬ isBadRestriction t n σ
            (exists_bottomFormula_dnf_view f).choose ρ := hρ_all _ hmem hgate
        obtain ⟨g, hg_bnd, hg_cnf, hg_dnf, hg_cw, hg_dw, hg_size, hg_eval⟩ :=
          exists_bottom_sub_proper_for_polarity t p f (exists_bottomFormula_dnf_view f).choose
            (exists_bottomFormula_dnf_view f).choose_spec.2 ρ hρ
            live h_live_lt h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
        refine ⟨g, fun _ => ⟨Or.inl ?_, hg_bnd, ?_, ?_, hg_size, ?_⟩⟩
        · unfold IsSubstitutionProperForm
          by_cases hp : p = true
          · simp only [hp, if_true]; exact hg_cnf hp
          · have hpf : p = false := by
              cases hb : p with
              | true => exact absurd hb hp
              | false => rfl
            simp only [hpf, Bool.false_eq_true, if_false]; exact hg_dnf hpf
        · by_cases hp : p = true
          · have hw := hg_cw hp; omega
          · have hpf : p = false := by
              cases hb : p with
              | true => exact absurd hb hp
              | false => rfl
            have hisd : isDNF g = true := (hg_dnf hpf).1
            have hcw₀ : cnfWidth g = 0 := by
              cases g with
              | andGate gs => simp [isDNF] at hisd
              | orGate gs => rfl
              | inputGate a b => rfl
              | notGate x => rfl
              | constant a b => rfl
            omega
        · by_cases hp : p = true
          · have hisc : isCNF g = true := (hg_cnf hp).1
            have hdw₀ : dnfWidth g = 0 := by
              cases g with
              | orGate gs => simp [isCNF] at hisc
              | andGate gs => rfl
              | inputGate a b => rfl
              | notGate x => rfl
              | constant a b => rfl
            omega
          · have hpf : p = false := by
              cases hb : p with
              | true => exact absurd hb hp
              | false => rfl
            have hw := hg_dw hpf; omega
        · intro liveBits hlen
          rw [← h_bottom (raw.getD i (.inputGate 0 false)) hmem hgate]
          exact hg_eval liveBits hlen
      · have hxmem : x ∈ ufiCollectInputIndices
            (raw.getD i (.inputGate 0 false)) := by
          rw [hinput]
          simp [ufiCollectInputIndices]
        have hx : x < n := hraw_inputs _ hmem x hxmem
        obtain ⟨g, hg⟩ := exists_restricted_literal_form_for_polarity t ht ρ live h_live_lt
          h_live_nodup h_live_eq deadBits h_card h_assemble (by omega) p x b hx
        refine ⟨g, fun _ => ?_⟩
        rw [hinput]
        exact hg
      · refine ⟨.constant true 0, fun _ => ⟨Or.inr ⟨true, 0, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
        · simpa [ufiLargestInput, ufiCollectInputIndices] using
            (show 0 < live.length by omega)
        · simp [cnfWidth]
        · simp [dnfWidth]
        · simp [ufiFormulaCircuitSize]
        · intro liveBits hlen
          rw [hempty]
          simp only [ufiFormulaEval]
      · refine ⟨.constant false 0, fun _ => ⟨Or.inr ⟨false, 0, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
        · simpa [ufiLargestInput, ufiCollectInputIndices] using
            (show 0 < live.length by omega)
        · simp [cnfWidth]
        · simp [dnfWidth]
        · simp [ufiFormulaCircuitSize]
        · intro liveBits hlen
          rw [hempty]
          simp only [ufiFormulaEval]
    · exact ⟨UnboundedFanInFormula.inputGate 0 false, fun h => absurd h hi⟩
  choose narrowForm h_narrow using hpoint
  refine ⟨narrowForm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p i hi; exact (h_narrow p i hi).1
  · intro p i hi; exact (h_narrow p i hi).2.1
  · intro p i hi; exact (h_narrow p i hi).2.2.1
  · intro p i hi; exact (h_narrow p i hi).2.2.2.1
  · intro p i hi; exact (h_narrow p i hi).2.2.2.2.1
  · intro p i hi liveBits hlen; exact (h_narrow p i hi).2.2.2.2.2 liveBits hlen

/-- The invariants carried from one switching round to the next.

    The input-index bound is already the first property of `circuit`, so it is
    not duplicated as a separate field.  Keeping the remaining facts with the
    formula lets a switching step consume one synchronized state and produce
    the state for the next round. -/
structure SwitchingRoundState (n c k d t : Nat) where
  circuit : LeveledUFIFormulaOfSizePolyNAndDepthD n c k d
  constant_free : IsConstantFree circuit.val
  clean : IsCleanFormula circuit.val
  bottom_fan_in : HasBottomFanInLE d circuit.val t
  bottom_budget : switchingGateBudget d circuit.val < 2 ^ t

/-- A depth-`(d+1)` AC0 formula is equivalent, after fixing the
    non-live inputs, to a depth-≤-`d` AC0 formula on the surviving live
    coordinates.  The new formula has polynomial-size parameters `c', k'`
    that may differ from `c, k`, because folding the bottom layer can enlarge
    the constants.

    This is the substantive Håstad switching step.  It invokes
    `exists_switching_lemma_pigeonhole_list` on all bottom formulas to choose
    one restriction that makes every canonical decision tree shallow, then
    folds those trees into the layer above.

    ### Decomposition

    The proof combines the following sub-obligations:

    * **Extraction:** `extractBottomLayer` identifies the list of depth-two
      bottom subformulas and the remaining skeleton.
    * **Budget:** the number of switching events is bounded by the original
      formula's switching-gate budget.
    * **Restriction:** `exists_switching_round_restriction` chooses the exact
      density `σ = ⌊n/(20t)⌋/n` and one restriction satisfying the union bound
      for every genuine bottom gate.
    * **Assembly:** `exists_assembled_restriction` converts the chosen random
      restriction to the `(live, deadBits)` interface used by `assembleInput`.
    * **Conversion:** each bounded-depth canonical decision tree is converted
      to a polarity-appropriate CNF or DNF and substituted into the skeleton.
    * **Evaluation:** evaluation of the original formula on the
      assembled input agrees with evaluation of the rebuilt formula.

    Concretely, the conversion and evaluation steps fold each canonical
    decision tree (of depth ≤ `decisionTreeDepthBound`) for the bottom DNFs
    back into the layer above the bottom layer, yielding a depth-`d` leveled circuit on `live`
    coordinates with new size parameters `c', k'`, and verify
    evaluation agreement.

    The folding uses `decisionTreeToDNF` (or its dual) to convert
    each DT into a width-`decisionTreeDepthBound` CNF/DNF, then substitutes it into
    the bottom layer of the original formula.  Since the original
    layer above the bottom was an OR (or AND), and each DT-derived
    formula is a DNF (or CNF), this *flattens* the bottom two
    layers into one — reducing the depth by 1.

    Size accounting bounds the rebuilt formula by
    `(ufiFormulaCircuitSize formula.val + raw.length) *
      (1 + (2 + 2^(t+1) * (t+1)) * (t+2))`.
    The returned subtype records this expression as `c'` with `k' = 0`.

    The `2 ≤ live.length` requirement (in fact strengthened to
    `3 ≤ live.length`) is enforced by the density `σ` chosen by
    `exists_switching_round_restriction`: with a constant fraction of variables
    surviving, for `n ≥ 3` we have `live.length ≥ 3` whenever `σ · n ≥ 3`.

    The `fs` are polarity-tagged via `BottomFormula`: each `f` is
    either `BottomFormula.dnf` (then the switching lemma applies directly)
    or `BottomFormula.cnf` (then we apply switching to the dual via De Morgan
    before folding).

    This lemma is the substantive switching step: it internally
    chooses exact `σ := ⌊n/(20·t)⌋/n` (so `10·σ·t ≤ 1/2`), applies the
    multi-DNF pigeonhole `exists_switching_lemma_pigeonhole_list`
    (per-polarity, by splitting `fs` and dualizing the CNF half),
    converts the resulting `ρ` into the `(live, deadBits)` shape via
    `exists_assembled_restriction`, and folds the canonical
    decision trees (each of depth ≤ `t`) back into the layer above.

    ### Bottom-fan-in invariant (architectural)

    The input bottoms satisfy the *small* width bound `f.width ≤ t`
    (NOT the loose `c·n^k`, which is unsatisfiable for `k ≥ 1`).  The
    invariant `c·n^k < 2^t` makes the pigeonhole
    `fs.length · (10σt)^t ≤ fs.length · (1/2)^t < 1` close (since
    `fs.length ≤ c·n^k < 2^t`).  The per-round threshold
    `20·t·(t+1) ≤ n` guarantees `t < ⌈σn⌉` and `3 ≤ ⌈σn⌉`, i.e. the
    surviving live set is large and the new bottom fan-in `t` is
    strictly smaller than the live count.  Crucially the returned `next`
    state maintains `HasBottomFanInLE d next.circuit.val t` together with
    the other persistent invariants, so the iterated argument can recurse by
    passing one synchronized value to its induction hypothesis.

    Requires `2 ≤ d` so the source depth `d + 1` has a nonterminal
    switching layer. The depth-two terminal case is handled separately by
    `exists_depth_two_collapse`. -/
lemma exists_switching_depth_reduction
      {c k d n t : Nat}
      (hd : 2 ≤ d)
      (state : SwitchingRoundState n c k (d + 1) t)
      (ht : 2 ≤ t)
      (h_and_or : UnboundedFanInFormula.IsAndOr state.circuit.val)
      (h_ne_circuit : HasNoEmptyAndOrGate state.circuit.val)
      (h_thresh : 20 * t * (t + 1) ≤ n) :
  ∃ (live : List Nat)
    (_h_live_lt : ∀ v ∈ live, v < n)
    (_h_live_nodup : live.Nodup)
    (deadBits : List Bool)
    (c' k' : Nat)
    (next : SwitchingRoundState live.length c' k' d t)
    (_h_live' : n / (20 * t) ≤ live.length),
    ∀ (liveBits : List Bool), liveBits.length = live.length →
      ufiFormulaEval state.circuit.val
          (assembleInput n live liveBits deadBits) =
      ufiFormulaEval next.circuit.val liveBits := by
  rcases state with ⟨formula, h_cf, _h_clean, h_bfi, h_bot⟩
  have h_inputs_bound : ufiLargestInput formula.val < n := formula.property.1
  -- `3 ≤ n` follows from the per-round threshold `20·t·(t+1) ≤ n`
  -- with `2 ≤ t`.
  have h_params : 3 ≤ n := by nlinarith
  have h_proper : HasProperBottomsAt formula.val (d + 1) :=
    Circuits.Leveling.isProperlyLeveled_imp_proper _ _ formula.property.2.2.2.2
  have h_n : 0 < n := by omega
  -- Recompute the extraction components used below so their defining
  -- equalities are available to the proof.
  set raw : List UnboundedFanInFormula :=
    (extractBottomLayer (d + 1) 0 formula.val).1 with hraw_def
  have hraw_proper : ∀ g ∈ raw, HasProperBottomsAt g 2 := by
    intro g hg
    exact hasProperBottomsAt_of_mem_extractBottomLayer (d + 1) 0 formula.val
      h_proper g (hraw_def ▸ hg)
  have hraw_inputs : ∀ g ∈ raw, ∀ x ∈ ufiCollectInputIndices g, x < n := by
    intro g hg x hx
    have hsub := extractBottomLayer_bottoms_collect_subset (d + 1) 0 formula.val g
      (hraw_def ▸ hg) x hx
    have hle := mem_le_foldr_max hsub
    unfold ufiLargestInput at h_inputs_bound
    omega
  have hraw_largest : ∀ g ∈ raw, ufiLargestInput g < n := by
    intro g hg
    unfold ufiLargestInput
    exact ProperizeProto.foldr_max_lt_of_forall_lt h_n (hraw_inputs g hg)
  -- This is the only conversion used for genuine gates in the active path.
  -- Its proof arguments exclude fallback behavior and its `.toUFI` is `g`.
  let bottom : ∀ g, g ∈ raw → IsSwitchingGate g → BottomFormula n :=
    fun g hg h_gate => switchingGateBottom n g h_gate (hraw_largest g hg) (hraw_proper g hg)
  have h_bottom : ∀ g hg h_gate, (bottom g hg h_gate).toUFI = g := by
    intro g hg h_gate
    exact switchingGateBottom_toUFI n g h_gate (hraw_largest g hg) (hraw_proper g hg)
  set gateRaw : List UnboundedFanInFormula :=
    raw.filter IsSwitchingGate with hgate_raw_def
  have hgate_raw_mem : ∀ g ∈ gateRaw, g ∈ raw ∧ IsSwitchingGate g := by
    intro g hg
    rw [hgate_raw_def] at hg
    exact ⟨(List.mem_filter.mp hg).1, by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hg).2⟩
  set skel : UnboundedFanInFormula :=
    (extractBottomLayer (d + 1) 0 formula.val).2.1 with hskel_def
  -- Attach the filter-membership proof so the map can call the partial,
  -- proof-directed constructor without inventing a total fallback case.
  set fvL : List (UnboundedFanInProperDNF n) :=
    gateRaw.attach.map (fun g =>
      (exists_bottomFormula_dnf_view
        (bottom g.val
          (hgate_raw_mem g.val g.property).1
          (hgate_raw_mem g.val g.property).2)).choose) with hfv_l_def
  -- Width bound on each DNF view: ≤ the structural gate width ≤ t.
  have hfv_l_width : ∀ f ∈ fvL, dnfWidth f.val ≤ t := by
    intro f hf
    rw [hfv_l_def, List.mem_map] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    have hgraw : g.val ∈ raw := (hgate_raw_mem g.val g.property).1
    have hgate : IsSwitchingGate g.val := (hgate_raw_mem g.val g.property).2
    have h₁ := (exists_bottomFormula_dnf_view (bottom g.val hgraw hgate)).choose_spec.1
    have h₂ : (bottom g.val hgraw hgate).width ≤ t := by
      exact le_trans
        (switchingGateBottom_width_le_ufiBottomFanIn n g.val hgate
          (hraw_largest g.val hgraw) (hraw_proper g.val hgraw))
        (h_bfi g.val (hraw_def ▸ hgraw))
    omega
  -- Count bound: only genuine AND/OR bottoms enter the union bound.
  have hfv_l_lt : fvL.length < 2 ^ t := by
    rw [hfv_l_def, List.length_map, List.length_attach, hgate_raw_def, hraw_def]
    exact lt_of_le_of_lt
      (extractedBottomGates_length_le_budget (d + 1) 0 formula.val) h_bot
  -- Package as `(hcount, ht_s)` for the pigeonhole using the trivial
  -- witnesses `c := fvL.length`, `k := 0` (so `c·n^0 = fvL.length`).
  have hfv_l_count : fvL.length ≤ fvL.length * n ^ 0 := by simp
  have ht_s₀ : fvL.length * n ^ 0 < 2 ^ t := by simpa using hfv_l_lt
  -- (i) Choose exact σ := ⌊n/(20·t)⌋/n and one restriction good for every bottom.
  obtain ⟨σ, ρ, hρ_list, hlive_gt, hσval⟩ :=
    exists_switching_round_restriction fvL.length 0 t fvL ht hfv_l_width hfv_l_count ht_s₀
      h_thresh
  -- (iii) Convert ρ into the (live, deadBits) shape.
  obtain ⟨live, h_live_lt, h_live_nodup, deadBits, h_card, h_live_eq, h_assemble⟩ :=
    exists_assembled_restriction ρ
  -- Live-count bounds from the restriction cardinality.
  have h_live_card : live.length = Nat.ceil (σ.val * (n : ℚ)) := by
    have h₁ : live.length = ρ.starAssignment.val.val.card := by
      have hcard := congrArg Multiset.card h_live_eq
      simp only [Multiset.coe_card] at hcard
      exact hcard
    rw [h₁, ρ.starAssignment.property]
  have h_dt_lt : t < live.length := by rw [h_live_card]; exact hlive_gt
  -- The list-`∀` good-restriction statement, re-keyed to genuine gate
  -- members of the raw semantic extraction.  Literal leaves are handled
  -- directly by the producer and never enter the switching union bound.
  have hρ_all : ∀ g (hg : g ∈ raw) (h_gate : IsSwitchingGate g),
      ¬ isBadRestriction t n σ
          (exists_bottomFormula_dnf_view (bottom g hg h_gate)).choose ρ := by
    intro g hg h_gate
    have hgate_mem : g ∈ gateRaw := by
      rw [hgate_raw_def]
      exact List.mem_filter.mpr ⟨hg, by simpa only [decide_eq_true_eq] using h_gate⟩
    have hmem : (exists_bottomFormula_dnf_view (bottom g hg h_gate)).choose ∈ fvL := by
      rw [hfv_l_def]
      refine List.mem_map.mpr ⟨⟨g, hgate_mem⟩, by simp, ?_⟩
      rfl
    exact hρ_list _ hmem
  have hraw_kind : ∀ g ∈ raw,
      IsSwitchingGate g ∨ (∃ x b, g = .inputGate x b) ∨
        g = .andGate [] ∨ g = .orGate [] := by
    intro g hg
    have hcfg : IsConstantFree g :=
      isConstantFree_of_mem_extractBottomLayer (d + 1) 0 formula.val h_cf g
        (hraw_def ▸ hg)
    have hpg : HasProperBottomsAt g 2 := hraw_proper g hg
    cases g with
    | inputGate x b => exact Or.inr (Or.inl ⟨x, b, rfl⟩)
    | constant b m => simp [IsConstantFree] at hcfg
    | notGate g => simp [HasProperBottomsAt] at hpg
    | andGate gs =>
        cases gs with
        | nil => exact Or.inr (Or.inr (Or.inl rfl))
        | cons g gs => exact Or.inl (by simp [IsSwitchingGate])
    | orGate gs =>
        cases gs with
        | nil => exact Or.inr (Or.inr (Or.inr rfl))
        | cons g gs => exact Or.inl (by simp [IsSwitchingGate])
  -- (iv) Per-bottom narrow proper forms on the live coordinates.
  obtain ⟨narrowForm, h_narrow_proper, h_narrow_bnd, h_narrow_cw, h_narrow_dw, h_narrow_nc, h_narrow_eval⟩ :=
    exists_build_narrow_sub_for_polarity t ht raw ρ bottom h_bottom hρ_all hraw_kind hraw_inputs live h_live_lt
      h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
  -- The substitution-map ingredients: `gf` returns the polarity-`p` narrow
  -- form at every splice-base index (`narrowForm` computes the bottom in
  -- both polarities, so no polarity gate is needed), `il`/`kill` rekey/kill
  -- above-splice `inputGate` leaves by liveness.
  classical
  set gf : Bool → Nat → UnboundedFanInFormula := fun p i =>
    if i < raw.length then
      narrowForm p i
    else
      (if p then litToProperCNF 0 true else litToProperDNF 0 true) with hgf_def
  set il : Nat → Nat × Bool := fun i =>
    match raw.getD i (.inputGate 0 false) with
    | .inputGate x b => (live.idxOf x, b)
    | _ => (0, false) with hil_def
  set kill : Nat → Option Bool := fun i =>
    match raw.getD i (.inputGate 0 false) with
    | .inputGate x b =>
        if x ∈ live then none
        else some (ufiFormulaEval (UnboundedFanInFormula.inputGate x b)
                    (assembleInput n live (List.replicate live.length false) deadBits))
    | _ => none with hkill_def
  -- `hgf`: every `gf p i` is a proper CNF/DNF (or constant) of polarity `p`.
  have hgf : ∀ p i, IsSubstitutionProperFormOrConstant (fun _ => gf p i) p 0 := by
    intro p i
    by_cases hc : i < raw.length
    · have hsp := h_narrow_proper p i hc
      have hval : gf p i = narrowForm p i := by
        rw [hgf_def]; simp only [hc, if_true]
      have heq : (fun _ : Nat => gf p i) = (fun _ : Nat => narrowForm p i) := by
        funext _; exact hval
      rw [heq]; exact hsp
    · refine Or.inl ?_
      have hval : gf p i =
          (if p then litToProperCNF 0 true else litToProperDNF 0 true) := by
        rw [hgf_def]; simp only [hc, if_false]
      have heq : (fun _ : Nat => gf p i) =
          (fun _ : Nat => if p then litToProperCNF 0 true else litToProperDNF 0 true) := by
        funext _; exact hval
      rw [heq]
      cases p with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact isSubstitutionProperForm_litToProperDNF _ 0 0 true rfl
      | true =>
          simp only [if_true]
          exact isSubstitutionProperForm_litToProperCNF _ 0 0 true rfl
  -- `hgfw`: every `gf p i` has CNF and DNF bottom width `≤ t` (narrow forms
  -- from the switching round; constant fillers have width `1` or `0`).
  have hgfw : ∀ p i, cnfWidth (gf p i) ≤ t ∧ dnfWidth (gf p i) ≤ t := by
    intro p i
    by_cases hc : i < raw.length
    · have hval : gf p i = narrowForm p i := by
        rw [hgf_def]; simp only [hc, if_true]
      rw [hval]
      exact ⟨h_narrow_cw p i hc, h_narrow_dw p i hc⟩
    · have hval : gf p i =
          (if p then litToProperCNF 0 true else litToProperDNF 0 true) := by
        rw [hgf_def]; simp only [hc, if_false]
      rw [hval]
      cases p with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          have hc₁ : cnfWidth (litToProperDNF 0 true) = 0 := by decide
          have hc₂ : dnfWidth (litToProperDNF 0 true) = 1 := by decide
          omega
      | true =>
          simp only [if_true]
          have hc₁ : cnfWidth (litToProperCNF 0 true) = 1 := by decide
          have hc₂ : dnfWidth (litToProperCNF 0 true) = 0 := by decide
          omega
  -- `hgf_nc`: every `gf p i` has `circuit_size ≤ B` with
  -- `B = 1 + (2 + 2^(t+1)·(t+1))·(t+2)` (narrow forms from the switching
  -- round via `exists_build_narrow_sub_for_polarity`; constant fillers have formula-size `2`).
  have hgf_nc : ∀ p i, ufiFormulaCircuitSize (gf p i)
      ≤ 1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) := by
    intro p i
    have h_bge : 4 ≤ (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) := by
      have h := Nat.mul_le_mul (show 2 ≤ 2 + 2 ^ (t + 1) * (t + 1) by omega)
        (show 2 ≤ t + 2 by omega)
      omega
    by_cases hc : i < raw.length
    · have hval : gf p i = narrowForm p i := by
        rw [hgf_def]; simp only [hc, if_true]
      rw [hval]
      exact h_narrow_nc p i hc
    · have hval : gf p i =
          (if p then litToProperCNF 0 true else litToProperDNF 0 true) := by
        rw [hgf_def]; simp only [hc, if_false]
      rw [hval]
      cases p with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          have hcc : ufiFormulaCircuitSize (litToProperDNF 0 true) = 2 := by
            simp [litToProperDNF, ufiFormulaCircuitSize]
          omega
      | true =>
          simp only [if_true]
          have hcc : ufiFormulaCircuitSize (litToProperCNF 0 true) = 2 := by
            simp [litToProperCNF, ufiFormulaCircuitSize]
          omega
  -- `hgfi`: every input index of `gf p i` is `< live.length`.
  have hgfi : ∀ p i, ∀ x ∈ ufiCollectInputIndices (gf p i), x < live.length := by
    intro p i x hx
    by_cases hc : i < raw.length
    · have hval : gf p i = narrowForm p i := by
        rw [hgf_def]; simp only [hc, if_true]
      rw [hval] at hx
      have hbnd := h_narrow_bnd p i hc
      have hle := mem_le_foldr_max hx
      unfold ufiLargestInput at hbnd
      omega
    · have hval : gf p i =
          (if p then litToProperCNF 0 true else litToProperDNF 0 true) := by
        rw [hgf_def]; simp only [hc, if_false]
      rw [hval] at hx
      cases p with
      | false =>
          simp only [Bool.false_eq_true, if_false] at hx
          have hcol : ufiCollectInputIndices (litToProperDNF 0 true) = [0] := by
            simp [litToProperDNF, ufiCollectInputIndices]
          rw [hcol] at hx
          simp only [List.mem_singleton] at hx; omega
      | true =>
          simp only [if_true] at hx
          have hcol : ufiCollectInputIndices (litToProperCNF 0 true) = [0] := by
            simp [litToProperCNF, ufiCollectInputIndices]
          rw [hcol] at hx
          simp only [List.mem_singleton] at hx; omega
  -- `hili`: every live (`kill i = none`) rekey index is `< live.length`.
  have hili : ∀ i, kill i = none → (il i).1 < live.length := by
    intro i hki
    simp only [hil_def]
    cases hg : raw.getD i (.inputGate 0 false) with
    | inputGate x b =>
        simp only []
        simp only [hkill_def, hg] at hki
        by_cases hxl : x ∈ live
        · exact List.idxOf_lt_length_iff.mpr hxl
        · rw [if_neg hxl] at hki; exact absurd hki (by simp)
    | constant b m => simp only []; omega
    | notGate g => simp only []; omega
    | andGate gs => simp only []; omega
    | orGate gs => simp only []; omega
  -- The substitution map: read the `(i-0)`-th producer form.
  set sub : Nat → UnboundedFanInFormula :=
    (fun i => (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).getD (i - 0)
      (.inputGate 0 false)) with hsub_def
  -- The producer satisfies `IsExtractionSubstitutionReadyWithConstants` (every bottom is a
  -- proper CNF/DNF or a constant).
  have h_ready_c : IsExtractionSubstitutionReadyWithConstants sub (d + 1) 0 formula.val := by
    rw [hsub_def]
    exact isExtractionSubstitutionReadyWithConstants_buildKillAwareForms gf il kill hgf (.inputGate 0 false) false (d + 1) 0 formula.val
      h_cf h_proper (Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2)
  -- Every producer form `sub i` has CNF and DNF bottom width `≤ t`.
  have hsubw : ∀ i, cnfWidth (sub i) ≤ t ∧ dnfWidth (sub i) ≤ t := by
    intro i
    rw [hsub_def]
    simp only [Nat.sub_zero]
    rcases Nat.lt_or_ge i (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).length
      with hlt | hge
    · have hmem : (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).getD i
          (.inputGate 0 false) ∈ buildKillAwareForms gf il kill false (d + 1) 0 formula.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact List.getElem_mem hlt
      exact buildKillAwareForms_width gf il kill t hgfw false (d + 1) 0 formula.val _ hmem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      exact ⟨by simp [cnfWidth], by simp [dnfWidth]⟩
  -- Every producer form `sub i` has all input indices `< live.length`.
  have hsubi : ∀ i, ∀ x ∈ ufiCollectInputIndices (sub i), x < live.length := by
    intro i
    rw [hsub_def]
    simp only [Nat.sub_zero]
    have h_n_ncirc : IsNotGateFree formula.val :=
      isNotGateFree_of_strictly_leveled formula.val (d + 1)
        (Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2)
    rcases Nat.lt_or_ge i (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).length
      with hlt | hge
    · have hmem : (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).getD i
          (.inputGate 0 false) ∈ buildKillAwareForms gf il kill false (d + 1) 0 formula.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact List.getElem_mem hlt
      exact buildKillAwareForms_inputs gf il kill live.length hgfi hili false (d + 1) 0 formula.val
        h_n_ncirc h_cf _ hmem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      intro x hx; simp only [ufiCollectInputIndices, List.mem_singleton] at hx
      omega
  -- Every producer form `sub i` has `circuit_size ≤ B` with
  -- `B = 1 + (2 + 2^(t+1)·(t+1))·(t+2)` (gate forms via `buildKillAwareForms_ufiFormulaCircuitSize`,
  -- the out-of-window default `inputGate 0 false` has formula-size `1 ≤ B`).
  have hsub_nc : ∀ i, ufiFormulaCircuitSize (sub i)
      ≤ 1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) := by
    intro i
    have h_bge : 4 ≤ (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2) := by
      have h := Nat.mul_le_mul (show 2 ≤ 2 + 2 ^ (t + 1) * (t + 1) by omega)
        (show 2 ≤ t + 2 by omega)
      omega
    rw [hsub_def]
    simp only [Nat.sub_zero]
    rcases Nat.lt_or_ge i (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).length
      with hlt | hge
    · have hmem : (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).getD i
          (.inputGate 0 false) ∈ buildKillAwareForms gf il kill false (d + 1) 0 formula.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact List.getElem_mem hlt
      exact buildKillAwareForms_ufiFormulaCircuitSize gf il kill _ (by omega) hgf_nc false (d + 1) 0
        formula.val _ hmem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      simp only [ufiFormulaCircuitSize]; omega
  -- The flattened, constant-absorbed formula on the live coordinates.
  set formula'_val : UnboundedFanInFormula :=
    simplifyConstants (substFlatten sub skel) with hcircuit'_def
  -- Proper-leveled at depth `d`.
  have h_proper' : HasProperBottomsAt formula'_val d := by
    rw [hcircuit'_def, hsub_def, hskel_def]
    exact hasProperBottomsAt_simplifyConstants_substFlatten_extractBottomLayer
      (fun i => (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).getD (i - 0)
        (.inputGate 0 false))
      d hd formula.val h_and_or
        (Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2)
        h_proper h_ready_c
  -- constant-free.
  have h_cf' : IsConstantFree formula'_val := by
    rw [hcircuit'_def]; exact isConstantFree_simplifyConstants _
  -- Depth ≤ d follows from the proper-leveling output `h_proper'`.
  have hdepth' : ufiFormulaDepth formula'_val ≤ d :=
    proper_leveled_depth_le formula'_val d hd h_proper'
  -- Shared skeleton hypotheses (reused by the bottom-count, strict-leveling
  -- and bottom-width fields).
  have hle₁ : ¬ (d + 1) ≤ 2 := by omega
  have h_and_or_skel : UnboundedFanInFormula.IsAndOr skel := by
    rw [hskel_def]; exact isAndOr_extractBottomLayer_top (d + 1) 0 formula.val hle₁ h_and_or
  have h_ready_skel : IsProperSubstitutionReadyWithConstants sub skel ((d + 1) - 2) := by
    rw [hskel_def]
    exact isProperSubstitutionReadyWithConstants_extractBottomLayer sub (d + 1) 0 formula.val
      (Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2)
      h_proper h_ready_c
  have h_cf_skel : IsConstantFree skel := by
    rw [hskel_def]; exact isConstantFree_extractBottomLayer_skeleton (d + 1) 0 formula.val
  have h_ne_skel : HasNoEmptyAndOrGate skel := by
    rw [hskel_def]
    exact hasNoEmptyAndOrGate_extractBottomLayer_skeleton (d + 1) 0 formula.val h_ne_circuit
  -- Strict-leveling at depth `d`: downgrade `IsProperSubstitutionReadyWithConstants → IsSubstitutionReady`, run
  -- the general strict-leveling consumer, then push through `simplifyConstants`.
  have hstrict' : IsAlternatingAndLeveledAt formula'_val d := by
    rw [hcircuit'_def]
    apply isAlternatingAndLeveledAt_simplifyConstants
    have hsr : IsSubstitutionReady sub skel ((d + 1) - 2) :=
      isSubstitutionReady_of_isProperSubstitutionReadyWithConstants sub skel ((d + 1) - 2) h_ready_skel
    have hstr_skel : IsAlternatingAndLeveledAt skel ((d + 1) - 2) := by
      rw [hskel_def]
      exact isAlternatingAndLeveledAt_extractBottomLayer_top (d + 1) 0 formula.val
        (Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2)
    have hsl := isAlternatingAndLeveledAt_substFlatten sub skel ((d + 1) - 2) h_and_or_skel hstr_skel hsr
    rw [show (d + 1) - 2 + 1 = d by omega] at hsl
    exact hsl
  -- Bottom fan-in `≤ t`: the substituted-and-absorbed skeleton has bottom
  -- width `≤ t` (each `sub i` does), hence every bottom gate has fan-in `≤ t`.
  have hbfi' : HasBottomFanInLE d formula'_val t := by
    rw [hcircuit'_def]
    have h_pbw := hasProperBottomWidthLE_simplifyConstants_substFlatten sub t
      (fun i => (hsubw i).1) (fun i => (hsubw i).2) skel ((d + 1) - 2) h_and_or_skel h_ready_skel
    rw [show (d + 1) - 2 + 1 = d by omega] at h_pbw
    exact extractBottomLayer_bottoms_fanIn_le t (by omega) d 0
      (simplifyConstants (substFlatten sub skel)) h_pbw
  -- Largest input `< live.length`: each producer `sub i` has inputs `< live.length`,
  -- `substFlatten` only injects those, and `simplifyConstants` never raises the bound.
  have hinputs' : ufiLargestInput formula'_val < live.length := by
    rw [hcircuit'_def]
    apply simplifyConstants_ufiLargestInput_lt
    unfold ufiLargestInput
    have hall : ∀ x ∈ ufiCollectInputIndices (substFlatten sub skel), x < live.length :=
      substFlatten_inputs_lt sub skel live.length (fun i _ x hx => hsubi i x hx)
    have hle := foldr_max_le_of_all_le (l := ufiCollectInputIndices (substFlatten sub skel))
      (b := live.length - 1) (fun x hx => Nat.le_sub_one_of_lt (hall x hx))
    omega
  -- Gate-budget preservation.  The skeleton carries only still-active gates;
  -- literal placeholders have zero budget, substituted narrow forms live below
  -- the new frontier, and constant absorption can only remove active gates.
  have h_bot' : switchingGateBudget d formula'_val < 2 ^ t := by
    rw [hcircuit'_def]
    have hsimp := simplifyConstants_switchingGateBudget_le d (substFlatten sub skel)
    have hsubst := substFlatten_switchingGateBudget_le sub skel ((d + 1) - 2)
      h_and_or_skel h_ready_skel
    rw [show (d + 1) - 2 + 1 = d by omega] at hsubst
    have hskel : ufiFormulaCircuitSize skel ≤
        switchingGateBudget (d + 1) formula.val := by
      rw [hskel_def]
      exact extractBottomLayer_skeleton_size_le_switchingGateBudget (d + 1) 0 formula.val
        h_ne_circuit
    exact lt_of_le_of_lt hsimp (lt_of_le_of_lt hsubst (lt_of_le_of_lt hskel h_bot))
  -- The `IsCleanFormula` output is free: `formula'_val` is `simplifyConstants`
  -- applied to `substFlatten sub skel`, and that argument is `notGate`-free
  -- (the skeleton is unconditionally `IsNotGateFree`, and every producer form is a
  -- proper CNF/DNF or constant, hence `IsNotGateFree`).  Proven before the `refine`
  -- so the `formula'_val` rewrite is in the clean context.
  have hclean' : IsCleanFormula formula'_val := by
    rw [hcircuit'_def]
    apply isCleanFormula_simplifyConstants
    apply isNotGateFree_substFlatten
    · -- every substituted form is `notGate`-free
      have hgfnn : ∀ p j, IsNotGateFree (gf p j) := by
        intro p j
        rcases hgf p j with hspf | ⟨b, m, hconst⟩
        · cases p with
          | true =>
              unfold IsSubstitutionProperForm at hspf
              simp only [if_true] at hspf
              exact isNotGateFree_of_isCNF hspf.1
          | false =>
              unfold IsSubstitutionProperForm at hspf
              simp only [Bool.false_eq_true, if_false] at hspf
              exact isNotGateFree_of_isDNF hspf.1
        · have hconst' : gf p j = .constant b m := hconst
          rw [hconst']; simp only [IsNotGateFree]
      intro i
      rw [hsub_def]
      simp only [Nat.sub_zero]
      rcases Nat.lt_or_ge i (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).length
        with hlt | hge
      · have hmem : (buildKillAwareForms gf il kill false (d + 1) 0 formula.val).getD i
            (.inputGate 0 false) ∈ buildKillAwareForms gf il kill false (d + 1) 0 formula.val := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
          exact List.getElem_mem hlt
        exact isNotGateFree_of_mem_buildKillAwareForms gf il kill hgfnn false (d + 1) 0 formula.val _ hmem
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
        simp only [IsNotGateFree]
    · -- the skeleton is `notGate`-free
      rw [hskel_def]
      exact isNotGateFree_extractBottomLayer_skeleton (d + 1) 0 formula.val
  -- Evaluation agreement. Reduce via `simplifyConstants_eval` and
  -- `extractBottomLayer_substFlatten_eval` to a per-bottom obligation:
  -- each producer form `sub i` evaluates on `liveBits` exactly as the
  -- `i`-th extracted bottom evaluates on the assembled inputs.
  have heval : ∀ (liveBits : List Bool), liveBits.length = live.length →
      ufiFormulaEval formula.val (assembleInput n live liveBits deadBits) =
      ufiFormulaEval formula'_val liveBits := by
    intro liveBits hlb
    -- Per-input eval congruence for `inputGate` leaves.
    have h_input_eval : ∀ (x : Nat) (bb : Bool) (A B : List Bool),
        A[x]? = B[x]? →
        ufiFormulaEval (UnboundedFanInFormula.inputGate x bb) A
          = ufiFormulaEval (UnboundedFanInFormula.inputGate x bb) B := by
      intro x bb A B h
      unfold ufiFormulaEval
      rw [h]
    -- `gf` readout: every placeholder-index narrow form evaluates on the
    -- live bits exactly as the corresponding raw bottom on the assembly.
    have hgf_eval : ∀ (p : Bool) (m : Nat), m < raw.length →
        ufiFormulaEval (gf p m) liveBits
          = ufiFormulaEval (raw.getD m (.inputGate 0 false))
              (assembleInput n live liveBits deadBits) := by
      intro p m hm
      have hval : gf p m = narrowForm p m := by rw [hgf_def]; simp only [hm, if_true]
      rw [hval, ← h_narrow_eval p m hm liveBits hlb]
    -- `kill` readout: a killed `inputGate` leaf is replaced by the dead-bit
    -- constant, which agrees with the raw leaf on the assembly.
    have hkill_eval : ∀ (m x : Nat) (b : Bool) (bb : Bool), m < raw.length →
        raw.getD m (.inputGate 0 false) = UnboundedFanInFormula.inputGate x b → kill m = some bb →
        ufiFormulaEval (UnboundedFanInFormula.constant bb 0) liveBits
          = ufiFormulaEval (raw.getD m (.inputGate 0 false))
              (assembleInput n live liveBits deadBits) := by
      intro m x b bb _ hraw hks
      rw [hraw]
      simp only [ufiFormulaEval]
      rw [hkill_def] at hks
      simp only [hraw] at hks
      by_cases hxl : x ∈ live
      · rw [if_pos hxl] at hks; exact absurd hks (by simp)
      · rw [if_neg hxl] at hks
        have hbb : bb = ufiFormulaEval (UnboundedFanInFormula.inputGate x b)
            (assembleInput n live (List.replicate live.length false) deadBits) := by
          injection hks with hks'; exact hks'.symm
        rw [hbb]
        have hget :
            (assembleInput n live (List.replicate live.length false) deadBits)[x]? =
              (assembleInput n live liveBits deadBits)[x]? := by
          by_cases hxn : x < n
          · rw [assembleInput_get_at n live _ deadBits x hxn,
                assembleInput_get_at n live liveBits deadBits x hxn]
            unfold assembleInputFn
            rw [findIdx?_eq_none_of_notMem live x hxl]
          · rw [assembleInput_eq_map, assembleInput_eq_map,
                List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega),
                List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)]
        simp only [ufiFormulaEval]
        rw [hget]
    -- `il` readout: a live `inputGate` leaf is rekeyed to its live rank, which
    -- reads the same bit as the raw leaf on the assembly.
    have hil_eval : ∀ (m x : Nat) (b : Bool), m < raw.length →
        raw.getD m (.inputGate 0 false) = UnboundedFanInFormula.inputGate x b → kill m = none →
        ufiFormulaEval (UnboundedFanInFormula.inputGate (il m).1 (il m).2) liveBits
          = ufiFormulaEval (raw.getD m (.inputGate 0 false))
              (assembleInput n live liveBits deadBits) := by
      intro m x b _ hraw hkn
      rw [hraw]
      have hilm : il m = (live.idxOf x, b) := by rw [hil_def]; simp only [hraw]
      rw [hilm]
      rw [hkill_def] at hkn; simp only [hraw] at hkn
      have hxl : x ∈ live := by
        by_contra hxl
        rw [if_neg hxl] at hkn; exact absurd hkn (by simp)
      have hbridge : live.findIdx? (· = x) = some (live.idxOf x) := by
        rw [List.findIdx?_eq_some_iff_getElem]
        have hlt : live.idxOf x < live.length := List.idxOf_lt_length_iff.mpr hxl
        have hidx_eq : live[live.idxOf x] = x := List.getElem_idxOf hlt
        refine ⟨hlt, by simp only [decide_eq_true_eq]; exact hidx_eq, ?_⟩
        intro j' hj'
        simp only [decide_eq_true_eq]
        intro hcontra
        have hj'lt : j' < live.length := Nat.lt_trans hj' hlt
        have heq₂ : live[j'] = live[live.idxOf x] := by rw [hcontra, hidx_eq]
        have := (List.Nodup.getElem_inj_iff h_live_nodup).mp heq₂
        omega
      have hget := assembleInput_at_live n live liveBits deadBits hlb h_live_lt
        x hxl (live.idxOf x) hbridge
      unfold ufiFormulaEval
      rw [hget]
    rw [hcircuit'_def, simplifyConstants_eval (substFlatten sub skel) liveBits, hskel_def]
    symm
    apply extractBottomLayer_substFlatten_eval sub (d + 1) formula.val liveBits
      (assembleInput n live liveBits deadBits)
    intro i g hsome
    rw [hsub_def]
    simp only [Nat.sub_zero]
    rw [← hraw_def] at hsome
    have hi : i < raw.length := by
      by_contra hge
      push Not at hge
      rw [List.getElem?_eq_none hge] at hsome
      exact absurd hsome (by simp)
    have hgi : raw.getD i (.inputGate 0 false) = g := by
      rw [List.getD_eq_getElem?_getD, hsome, Option.getD_some]
    have hlen : (extractBottomLayer (d + 1) 0 formula.val).1.length = raw.length := by
      rw [hraw_def]
    have hfit : 0 + (extractBottomLayer (d + 1) 0 formula.val).1.length ≤ raw.length := by
      rw [hlen]; omega
    have halign : ∀ j, j < (extractBottomLayer (d + 1) 0 formula.val).1.length →
        (extractBottomLayer (d + 1) 0 formula.val).1.getD j (.inputGate 0 false)
          = raw.getD (0 + j) (.inputGate 0 false) := by
      intro j _; rw [Nat.zero_add, hraw_def]
    have hk : i < (extractBottomLayer (d + 1) 0 formula.val).1.length := by rw [hlen]; exact hi
    have hres := buildKillAwareForms_eval gf il kill raw (.inputGate 0 false) liveBits
      (assembleInput n live liveBits deadBits) hgf_eval hkill_eval hil_eval
      false (d + 1) 0 formula.val h_cf h_proper
        (Circuits.Leveling.isProperlyLeveled_imp_strict _ _ formula.property.2.2.2.2)
        hfit halign i hk
    rw [Nat.zero_add, hgi] at hres
    exact hres
  -- Live count lower bound is exact: `⌈σ·n⌉ = n/(20·t)`.
  have hlive' : n / (20 * t) ≤ live.length := by
    rw [h_live_card]
    have hσn : σ.val * (n : ℚ) = (n / (20 * t) : Nat) := by
      rw [hσval]
      field_simp [ne_of_gt (by exact_mod_cast h_n : (0 : ℚ) < (n : ℚ))]
    rw [hσn]
    norm_num
  -- Assemble the output existential.  `next.circuit` carries `formula'_val`
  -- as its underlying formula, and `next` bundles every invariant preserved
  -- by the round.  The size constants `c'`/`k'` are chosen after the
  -- formula-size bound is established.
  refine ⟨live, h_live_lt, h_live_nodup, deadBits,
    ?c', ?k',
    ⟨⟨formula'_val, ?count, ?depth, ?ncount, ?dpos, ?strict⟩,
      h_cf', hclean', hbfi', h_bot'⟩,
    hlive', heval⟩
  case c' => exact (ufiFormulaCircuitSize formula.val + raw.length) *
      (1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2))
  case k' => exact 0
  case dpos => omega
  case count => exact hinputs'
  case depth => exact hdepth'
  case ncount =>
    rw [pow_zero, Nat.mul_one]
    have hsimp := simplifyConstants_ufiFormulaCircuitSize_le (substFlatten sub skel)
    have hsub_route :
        ufiFormulaCircuitSize (substFlatten sub skel) ≤
          (ufiFormulaCircuitSize formula.val + raw.length) *
            (1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2)) := by
      rw [hskel_def]
      simpa [hraw_def] using extractBottomLayer_substFlatten_ufiFormulaCircuitSize_le sub (d + 1)
        (1 + (2 + 2 ^ (t + 1) * (t + 1)) * (t + 2)) (by omega) hsub_nc formula.val
    rw [hcircuit'_def]
    exact le_trans hsimp hsub_route
  case strict =>
    exact Circuits.Leveling.isProperlyLeveled_of_strict_proper _ _ hstrict' h_proper'

#print axioms exists_switching_depth_reduction

/-- Helper: in `(List.range n).filter p`, the element at position
    `((List.range j).filter p).length` is `j`, provided `j < n` and `p j = true`.
    This is the rank-counting identity behind dead-bit lookups. -/
lemma exists_filter_range_getElem_at_rank
    (p : Nat → Bool) :
    ∀ {n j : Nat}, j < n → p j = true →
    ∃ (h : ((List.range j).filter p).length < ((List.range n).filter p).length),
    ((List.range n).filter p)[((List.range j).filter p).length]'h = j := by
  intro n
  induction n with
  | zero => intro j hj _; omega
  | succ k ih =>
    intro j hj hp_j
    rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    by_cases h_jk : j = k
    · subst h_jk
      simp only [hp_j, if_true]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_cons, List.length_nil]; omega
      · rw [List.getElem_append_right (Nat.le_refl _)]
        simp
    · have hj_lt_k : j < k := by omega
      obtain ⟨h_lt_k, h_eq_k⟩ := ih hj_lt_k hp_j
      by_cases hp_k : p k = true
      · simp only [hp_k, if_true]
        refine ⟨?_, ?_⟩
        · rw [List.length_append, List.length_cons, List.length_nil]; omega
        · rw [List.getElem_append_left h_lt_k]
          exact h_eq_k
      · have hp_k_false : p k = false := by
          cases h : p k with
          | true => exact absurd h hp_k
          | false => rfl
        simp only [hp_k_false, Bool.false_eq_true, if_false, List.append_nil]
        exact ⟨h_lt_k, h_eq_k⟩

/-- Compose an outer restriction (mapping `n` inputs
    down to `m₁ := live₁.length` live inputs with dead bits
    `deadBits₁`) with an inner restriction on the live coordinates
    (mapping `m₁` inputs down to `m₂ := live₂.length` live inputs
    with dead bits `deadBits₂`).  Produces a single restriction on
    the original `n` inputs.

    The composed live list is `live₂.map (live₁.getD · 0)` (selecting
    the inner-live positions through the outer-live indexing). -/
lemma exists_composed_collapse
    (n : Nat)
    (live₁ : List Nat)
    (h_live₁_lt : ∀ v ∈ live₁, v < n)
    (h_live₁_nodup : live₁.Nodup)
    (deadBits₁ : List Bool)
    (live₂ : List Nat)
    (h_live₂_lt : ∀ v ∈ live₂, v < live₁.length)
    (h_live₂_nodup : live₂.Nodup)
    (deadBits₂ : List Bool) :
    ∃ (live : List Nat)
      (_h_live_lt : ∀ v ∈ live, v < n)
      (_h_live_nodup : live.Nodup)
      (deadBits : List Bool)
      (_h_card : deadBits.length + live.length = n),
      live.length = live₂.length ∧
      ∀ (innerBits : List Bool), innerBits.length = live₂.length →
        assembleInput n live innerBits deadBits =
        assembleInput n live₁
          (assembleInput live₁.length live₂ innerBits deadBits₂)
          deadBits₁ := by
  -- Composed live list: pick the live₁ positions indexed by live₂.
  let live : List Nat := live₂.map (fun i => live₁.getD i 0)
  -- Length.
  have h_live_len : live.length = live₂.length := List.length_map _
  -- Sub-n.
  have h_live_lt : ∀ v ∈ live, v < n := by
    intro v hv
    obtain ⟨i, hi, hv_eq⟩ := List.mem_map.mp hv
    have hi_lt : i < live₁.length := h_live₂_lt i hi
    have h_get : live₁.getD i 0 = live₁[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]
      rfl
    have h_mem : live₁[i] ∈ live₁ := List.getElem_mem hi_lt
    have : v = live₁[i] := by rw [← hv_eq, h_get]
    rw [this]
    exact h_live₁_lt _ h_mem
  -- Nodup.  The map `fun i => live₁.getD i 0` is injective on the indices in `live₂`,
  -- because `live₂ ⊆ [0, live₁.length)` and `live₁.Nodup`.
  have h_live_nodup : live.Nodup := by
    refine List.Nodup.map_on ?_ h_live₂_nodup
    intro i hi j hj h_eq
    have hi_lt : i < live₁.length := h_live₂_lt i hi
    have hj_lt : j < live₁.length := h_live₂_lt j hj
    have hi_get : live₁.getD i 0 = live₁[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]; rfl
    have hj_get : live₁.getD j 0 = live₁[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt]; rfl
    rw [hi_get, hj_get] at h_eq
    exact (List.Nodup.getElem_inj_iff h_live₁_nodup).mp h_eq
  -- Composed deadBits: for each non-live j ∈ [0,n), produce the value the
  -- composition demands at j.  Two sub-cases driven by whether `j ∈ live₁`:
  --   (a) j ∉ live₁: take `deadBits₁` at its rank in non-live₁ positions of [0,n).
  --   (b) j ∈ live₁ but j ∉ live (so j = live₁[k] with k ∉ live₂):
  --       take `deadBits₂` at the rank of k in non-live₂ positions of [0, live₁.length).
  let deadBits : List Bool :=
    ((List.range n).filter (fun j => !live.contains j)).map (fun j =>
      match live₁.findIdx? (· = j) with
      | some k =>
          deadBits₂.getD
            (((List.range k).filter (fun m => !live₂.contains m)).length) false
      | none =>
          deadBits₁.getD
            (((List.range j).filter (fun m => !live₁.contains m)).length) false)
  -- Length of composed deadBits.
  have h_card : deadBits.length + live.length = n := by
    -- `deadBits.length = ((range n).filter (¬ live.contains)).length`.
    have h_db_len : deadBits.length =
        ((List.range n).filter (fun j => !live.contains j)).length :=
      List.length_map _
    rw [h_db_len]
    -- `((range n).filter live.contains).Perm live` ⇒ lengths agree.
    have hperm : ((List.range n).filter (fun i => live.contains i)).Perm live := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact List.nodup_range.filter _
      · exact h_live_nodup
      · ext x
        simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
        refine ⟨fun ⟨_, hx⟩ => List.mem_of_elem_eq_true hx,
          fun hx => ⟨h_live_lt x hx, List.elem_eq_true_of_mem hx⟩⟩
    have h_pos_len :
        ((List.range n).filter (fun i => live.contains i)).length = live.length :=
      hperm.length_eq
    -- Splitting [0, n) by `live.contains`.
    have h_split :
        ((List.range n).filter (fun i => live.contains i)).length +
          ((List.range n).filter (fun j => !live.contains j)).length =
          (List.range n).length := by
      have hperm_split :=
        perm_filter_append_filter_not (List.range n) (fun i => live.contains i)
      have := hperm_split.length_eq
      simp only [List.length_append] at this
      omega
    rw [List.length_range] at h_split
    omega
  refine ⟨live, h_live_lt, h_live_nodup, deadBits, h_card,
          h_live_len, ?_⟩
  intro innerBits h_inner_len
  -- Show the two assemblies agree position-by-position.
  -- Both have length n, so we use `List.ext_getElem?` (or equivalently,
  -- compare `assembleInput_get_at`'s underlying inner functions on [0,n)).
  apply List.ext_getElem?
  intro j
  by_cases hj_lt : j < n
  · -- In-range: both sides give `some <value>`.
    rw [assembleInput_get_at n live innerBits deadBits j hj_lt]
    rw [assembleInput_get_at n live₁ _ deadBits₁ j hj_lt]
    congr 1
    -- Now: `assembleInputFn live innerBits deadBits j =
    --       assembleInputFn live₁
    --         (assembleInput live₁.length live₂ innerBits deadBits₂)
    --         deadBits₁ j`.
    -- Three cases on j: j ∈ live; j ∈ live₁ \ live; j ∉ live₁.
    by_cases hj_in_live : j ∈ live
    · -- Case A: j ∈ live, i.e. j = live₁[i₀] for some i₀ ∈ live₂.
      -- Find i₀.
      obtain ⟨i₀, hi₀_in, hf_eq⟩ := List.mem_map.mp hj_in_live
      have hi₀_lt : i₀ < live₁.length := h_live₂_lt i₀ hi₀_in
      have hi₀_get : live₁.getD i₀ 0 = live₁[i₀] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₀_lt]; rfl
      have hj_eq : j = live₁[i₀] := by rw [← hf_eq, hi₀_get]
      -- RHS: live₁.findIdx? (· = j) = some i₀ by Nodup.
      have h_live₁_find : live₁.findIdx? (· = j) = some i₀ := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨hi₀_lt, ?_, ?_⟩
        · simp [hj_eq]
        · intro j' hj'_lt
          have hj'_lt' : j' < live₁.length := Nat.lt_trans hj'_lt hi₀_lt
          simp only [decide_eq_true_eq, hj_eq]
          intro h_eq
          have h_inj := (List.Nodup.getElem_inj_iff h_live₁_nodup).mp h_eq
          omega
      -- LHS: live₂.findIdx? (· = i₀) = some k₀ by Nodup.
      obtain ⟨k₀, hk₀_lt, hk₀_eq⟩ : ∃ k₀, ∃ _ : k₀ < live₂.length,
          live₂[k₀] = i₀ := by
        have : ∃ k₀, ∃ h : k₀ < live₂.length, live₂[k₀] = i₀ :=
          List.getElem_of_mem hi₀_in
        obtain ⟨k₀, hlt, heq⟩ := this
        exact ⟨k₀, hlt, heq⟩
      have h_live₂_find : live₂.findIdx? (· = i₀) = some k₀ := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨hk₀_lt, ?_, ?_⟩
        · simp [hk₀_eq]
        · intro j' hj'_lt
          have hj'_lt' : j' < live₂.length := Nat.lt_trans hj'_lt hk₀_lt
          simp only [decide_eq_true_eq, ← hk₀_eq]
          intro h_eq
          have h_inj := (List.Nodup.getElem_inj_iff h_live₂_nodup).mp h_eq
          omega
      -- LHS find on `live`: use findIdx?_map.
      have h_live_find : live.findIdx? (· = j) = some k₀ := by
        change (live₂.map (fun i => live₁.getD i 0)).findIdx? (· = j) = some k₀
        rw [List.findIdx?_map]
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨hk₀_lt, ?_, ?_⟩
        · simp only [Function.comp_apply, decide_eq_true_eq]
          have hlt : live₂[k₀]'hk₀_lt < live₁.length := by
            rw [hk₀_eq]; exact hi₀_lt
          have h_get : live₁.getD live₂[k₀] 0 = live₁[live₂[k₀]'hk₀_lt]'hlt := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
          rw [h_get, hj_eq]
          congr 1
        · intro j' hj'_lt
          have hj'_lt' : j' < live₂.length := Nat.lt_trans hj'_lt hk₀_lt
          have hlt' : live₂[j']'hj'_lt' < live₁.length :=
            h_live₂_lt _ (List.getElem_mem hj'_lt')
          simp only [Function.comp_apply, decide_eq_true_eq, hj_eq]
          have h_get : live₁.getD live₂[j'] 0 = live₁[live₂[j']'hj'_lt']'hlt' := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']; rfl
          rw [h_get]
          intro h_eq
          have h_inj₁ := (List.Nodup.getElem_inj_iff h_live₁_nodup).mp h_eq
          have hk₀_eq' : live₂[j']'hj'_lt' = live₂[k₀]'hk₀_lt := by
            rw [h_inj₁, hk₀_eq]
          have h_inj₂ := (List.Nodup.getElem_inj_iff h_live₂_nodup).mp hk₀_eq'
          omega
      -- Inner assembly value at i₀.
      have h_inner_at : (assembleInput live₁.length live₂ innerBits deadBits₂)[i₀]? =
          some (assembleInputFn live₂ innerBits deadBits₂ i₀) :=
        assembleInput_get_at live₁.length live₂ innerBits deadBits₂ i₀ hi₀_lt
      have h_rhs_inner :
          (assembleInput live₁.length live₂ innerBits deadBits₂).getD i₀ false =
          assembleInputFn live₂ innerBits deadBits₂ i₀ := by
        rw [List.getD_eq_getElem?_getD, h_inner_at]; rfl
      -- Compute both sides.
      change assembleInputFn live innerBits deadBits j =
        assembleInputFn live₁
          (assembleInput live₁.length live₂ innerBits deadBits₂)
          deadBits₁ j
      unfold assembleInputFn
      rw [h_live_find, h_live₁_find]
      change innerBits.getD k₀ false =
        (assembleInput live₁.length live₂ innerBits deadBits₂).getD i₀ false
      rw [h_rhs_inner]
      unfold assembleInputFn
      rw [h_live₂_find]
    · -- Case B/C: j ∉ live.  Both fall through to their `deadBits` branch.
      -- LHS: live.findIdx? (· = j) = none ⟹ LHS = deadBits.getD r false,
      -- where r = ((range j).filter ¬live.contains).length.
      have h_live_find_none : live.findIdx? (· = j) = none := by
        rw [List.findIdx?_eq_none_iff]
        intro x hx
        simp only [decide_eq_false_iff_not]
        rintro rfl
        exact hj_in_live hx
      -- The constructor function used to build deadBits.
      set assembleDeadBit : Nat → Bool := fun j =>
        match live₁.findIdx? (· = j) with
        | some k =>
            deadBits₂.getD
              (((List.range k).filter (fun m => !live₂.contains m)).length) false
        | none =>
            deadBits₁.getD
              (((List.range j).filter (fun m => !live₁.contains m)).length) false
        with h_assemble_dead_bit
      have h_dead_eq :
          deadBits = ((List.range n).filter (fun j => !live.contains j)).map assembleDeadBit :=
        rfl
      -- Predicate "not in live" and rank-position-of-j claim.
      set pNotLive : Nat → Bool := fun m => !live.contains m with hpnl_def
      have hp_j : pNotLive j = true := by
        simp only [hpnl_def, Bool.not_eq_eq_eq_not, Bool.not_true,
          Bool.eq_false_iff]
        intro h_elem
        exact hj_in_live (List.mem_of_elem_eq_true h_elem)
      obtain ⟨h_rank_lt, h_rank_eq⟩ :=
        exists_filter_range_getElem_at_rank pNotLive hj_lt hp_j
      -- Look up deadBits at the rank: equals assembleDeadBit j.
      have h_dead_lookup :
          deadBits.getD ((List.range j).filter pNotLive).length false = assembleDeadBit j := by
        rw [h_dead_eq]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem h_rank_lt]
        simp only [Option.map_some, Option.getD_some]
        rw [h_rank_eq]
      -- LHS computation.
      change assembleInputFn live innerBits deadBits j =
        assembleInputFn live₁
          (assembleInput live₁.length live₂ innerBits deadBits₂)
          deadBits₁ j
      conv_lhs =>
        unfold assembleInputFn
        rw [h_live_find_none]
      change deadBits.getD ((List.range j).filter pNotLive).length false = _
      rw [h_dead_lookup, h_assemble_dead_bit]
      simp only []  -- beta-reduce `(fun j => match...) j`
      -- Now LHS is `match live₁.findIdx? (· = j) with ...`.
      -- Unfold RHS and split on the same findIdx?.
      conv_rhs => unfold assembleInputFn
      cases h_find₁ : live₁.findIdx? (· = j) with
      | none => rfl
      | some k =>
          -- j ∈ live₁ at position k, but j ∉ live ⟹ k ∉ live₂.
          rw [List.findIdx?_eq_some_iff_getElem] at h_find₁
          obtain ⟨hk_lt, hk_eq, _⟩ := h_find₁
          have hk_eq' : live₁[k]'hk_lt = j := by
            simp only [decide_eq_true_eq] at hk_eq; exact hk_eq
          -- k ∉ live₂: else j = live₁[k] would be in live.
          have hk_not_in_live₂ : k ∉ live₂ := by
            intro hk_in
            apply hj_in_live
            refine List.mem_map.mpr ⟨k, hk_in, ?_⟩
            rw [show live₁.getD k 0 = live₁[k]'hk_lt by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt]; rfl]
            exact hk_eq'
          have h_live₂_find_none : live₂.findIdx? (· = k) = none := by
            rw [List.findIdx?_eq_none_iff]
            intro x hx
            simp only [decide_eq_false_iff_not]
            rintro rfl
            exact hk_not_in_live₂ hx
          -- Inner assemble at k: since k < live₁.length, getD agrees with fn.
          have h_inner_at : (assembleInput live₁.length live₂ innerBits deadBits₂)[k]? =
              some (assembleInputFn live₂ innerBits deadBits₂ k) :=
            assembleInput_get_at live₁.length live₂ innerBits deadBits₂ k hk_lt
          have h_rhs_val :
              (assembleInput live₁.length live₂ innerBits deadBits₂).getD k false =
              assembleInputFn live₂ innerBits deadBits₂ k := by
            rw [List.getD_eq_getElem?_getD, h_inner_at]; rfl
          -- Reduce both `match some k` branches.
          change deadBits₂.getD
              ((List.range k).filter (fun m => !live₂.contains m)).length false =
            (assembleInput live₁.length live₂ innerBits deadBits₂).getD k false
          rw [h_rhs_val]
          unfold assembleInputFn
          rw [h_live₂_find_none]
  · -- Out-of-range: both `getElem?` return `none` by length.
    push Not at hj_lt
    have h_lhs_len :
        (assembleInput n live innerBits deadBits).length = n :=
      length_assembleInput n live innerBits deadBits
    have h_rhs_len :
        (assembleInput n live₁
            (assembleInput live₁.length live₂ innerBits deadBits₂)
            deadBits₁).length = n :=
      length_assembleInput n live₁ _ deadBits₁
    rw [List.getElem?_eq_none (by rw [h_lhs_len]; exact hj_lt),
        List.getElem?_eq_none (by rw [h_rhs_len]; exact hj_lt)]

/-- Iterate switching from a complete round state.  The remaining-round
    threshold is kept separate: unlike the fields of `SwitchingRoundState`,
    it decreases according to how many rounds are still to be performed. -/
lemma exists_iterated_switching_depth_collapse
      {c k d n t : Nat}
      (hd : 1 ≤ d)
      (state : SwitchingRoundState n c k d t)
      (ht : 2 ≤ t)
      (h_thresh : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ n) :
  ∃ (live : List Nat)
    (_h_live_lt : ∀ v ∈ live, v < n)
    (_h_live_nodup : live.Nodup)
    (_h_live_big : 2 ≤ live.length)
    (deadBits : List Bool)
    (w : Nat) (_hw : w < live.length)
    (g : UnboundedFanInDNF live.length),
    dnfWidth g.val ≤ w ∧
    ∀ (liveBits : List Bool), liveBits.length = live.length →
      ufiFormulaEval state.circuit.val
          (assembleInput n live liveBits deadBits) =
      ufiFormulaEval g.val liveBits := by
  -- Depth one is purely structural and spends no switching round.
  by_cases hd_one : d = 1
  · subst d
    obtain ⟨live, h_live_lt, h_live_nodup, h_live_big,
            deadBits, w, hw, g, hgw, heval⟩ :=
      exists_depth_one_collapse state.circuit t ht (by simpa using h_thresh)
    exact ⟨live, h_live_lt, h_live_nodup, h_live_big,
      deadBits, w, hw, g, hgw, heval⟩
  -- For every remaining depth, start the induction at depth two.  This makes
  -- the terminal switching argument the base case and ensures that the
  -- successor case always has at least three circuit layers.
  have hd_two : 2 ≤ d := by omega
  clear hd hd_one
  -- Keep `c, k, n, state` universally quantified at each step because
  -- peeling a layer changes the input count, polynomial-size parameters, and
  -- all synchronized invariants.
  -- The bottom-fan-in parameter `t` remains fixed throughout the induction.
  revert h_thresh state n k c
  induction d, hd_two using Nat.le_induction with
  | base =>
    intro c k n state h_thresh
    -- At overall depth two, the reserve is exactly `20t(t+1)`; no uniform
    -- `n ↦ n/(20t)` switching round is spent.
    have h_thresh_full : 20 * t * (t + 1) ≤ n := by
      simpa using h_thresh
    -- The depth-two circuit is its own sole extracted bottom, so the
    -- maintained bottom-fan-in invariant bounds its root fan-in by `t`.
    have h_node_t : ufiBottomFanIn state.circuit.val ≤ t := by
      have hmem : state.circuit.val ∈
          (extractBottomLayer 2 0 state.circuit.val).1 :=
        extractBottomLayer_two_self state.circuit.val
      exact state.bottom_fan_in state.circuit.val hmem
    have h_depth_two_threshold : 20 * (t + 1) < n := by
      have hstep : 20 * (t + 1) < 20 * t * (t + 1) := by
        exact (Nat.mul_lt_mul_right (show 0 < t + 1 by omega)).mpr (by omega)
      exact Nat.lt_of_lt_of_le hstep h_thresh_full
    obtain ⟨live, h_live_lt, h_live_nodup, h_live_big,
            deadBits, w, hw, g, hgw, heval⟩ :=
      exists_depth_two_collapse state.circuit state.circuit.property.1
        t h_node_t h_depth_two_threshold
    exact ⟨live, h_live_lt, h_live_nodup, h_live_big,
      deadBits, w, hw, g, hgw, heval⟩
  | succ d hd ih =>
    intro c k n state h_thresh
    -- Here `2 ≤ d`, so the circuit has depth bound `d + 1 ≥ 3`.  Peel one
    -- layer and invoke the induction hypothesis on the depth-`d` result.
    exact by
      let circuit := state.circuit
      have h_inputs_bound : ufiLargestInput circuit.val < n := circuit.property.1
      have h_cf : IsConstantFree circuit.val := state.constant_free
      have h_clean : IsCleanFormula circuit.val := state.clean
      -- Per-round threshold `20·t·(t+1) ≤ n` from the iterated one
      -- (the leading `(20t)^(d-1)` factor is at least one).
      have h_twenty_mul_t_pos : 0 < 20 * t := by omega
      have h_thr_round : 20 * t * (t + 1) ≤ n := by
        have hfac : 1 ≤ (20 * t) ^ ((d + 1) - 2) :=
          Nat.one_le_pow _ _ h_twenty_mul_t_pos
        calc 20 * t * (t + 1)
            = 1 * (20 * t * (t + 1)) := by ring
          _ ≤ (20 * t) ^ ((d + 1) - 2) * (20 * t * (t + 1)) :=
              Nat.mul_le_mul_right _ hfac
          _ ≤ n := h_thresh
      by_cases h_input : ∃ i b, circuit.val = UnboundedFanInFormula.inputGate i b
      · obtain ⟨i, b, hval⟩ := h_input
        let circuit₁ :
            LeveledUFIFormulaOfSizePolyNAndDepthD n c k 1 :=
          ⟨UnboundedFanInFormula.inputGate i b,
            by simpa [hval] using h_inputs_bound,
            by simp [ufiFormulaDepth],
            by
              have hs := circuit.property.2.2.1
              simp [ufiFormulaCircuitSize],
            by omega,
            by
              exact Circuits.Leveling.isProperlyLeveled_of_strict_proper _ _
                (by simp [IsAlternatingAndLeveledAt])
                (by simp [HasProperBottomsAt])⟩
        obtain ⟨live, h_live_lt, h_live_nodup, h_live_big,
                deadBits, w, hw, g, hgw, heval⟩ :=
          exists_depth_one_collapse circuit₁ t ht h_thr_round
        refine ⟨live, h_live_lt, h_live_nodup, h_live_big,
                deadBits, w, hw, g, hgw, ?_⟩
        intro liveBits hlen
        simpa [circuit, circuit₁, hval] using heval liveBits hlen
      by_cases h_empty : circuit.val = UnboundedFanInFormula.andGate [] ∨
          circuit.val = UnboundedFanInFormula.orGate []
      · rcases h_empty with hval | hval
        · let circuit₁ :
              LeveledUFIFormulaOfSizePolyNAndDepthD n c k 1 :=
            ⟨UnboundedFanInFormula.andGate [],
              by
                simp only [ufiLargestInput, ufiCollectInputIndices, List.flatMap_nil]
                unfold List.foldr
                omega,
              by
                simp only [ufiFormulaDepth, List.map_nil]
                unfold List.foldr
                omega,
              by
                have hs := circuit.property.2.2.1
                simpa [hval, ufiFormulaCircuitSize] using hs,
              by omega,
              by
                exact Circuits.Leveling.isProperlyLeveled_of_strict_proper _ _
                  (by simp [IsAlternatingAndLeveledAt])
                  (by
                    unfold HasProperBottomsAt
                    rw [if_pos (by decide : 1 ≤ 2)]
                    decide)⟩
          obtain ⟨live, h_live_lt, h_live_nodup, h_live_big,
                  deadBits, w, hw, g, hgw, heval⟩ :=
            exists_depth_one_collapse circuit₁ t ht h_thr_round
          refine ⟨live, h_live_lt, h_live_nodup, h_live_big,
                  deadBits, w, hw, g, hgw, ?_⟩
          intro liveBits hlen
          simpa [circuit, circuit₁, hval] using heval liveBits hlen
        · let circuit₁ :
              LeveledUFIFormulaOfSizePolyNAndDepthD n c k 1 :=
            ⟨UnboundedFanInFormula.orGate [],
              by
                simp only [ufiLargestInput, ufiCollectInputIndices, List.flatMap_nil]
                unfold List.foldr
                omega,
              by
                simp only [ufiFormulaDepth, List.map_nil]
                unfold List.foldr
                omega,
              by
                have hs := circuit.property.2.2.1
                simpa [hval, ufiFormulaCircuitSize] using hs,
              by omega,
              by
                exact Circuits.Leveling.isProperlyLeveled_of_strict_proper _ _
                  (by simp [IsAlternatingAndLeveledAt])
                  (by
                    unfold HasProperBottomsAt
                    rw [if_pos (by decide : 1 ≤ 2)]
                    decide)⟩
          obtain ⟨live, h_live_lt, h_live_nodup, h_live_big,
                  deadBits, w, hw, g, hgw, heval⟩ :=
            exists_depth_one_collapse circuit₁ t ht h_thr_round
          refine ⟨live, h_live_lt, h_live_nodup, h_live_big,
                  deadBits, w, hw, g, hgw, ?_⟩
          intro liveBits hlen
          simpa [circuit, circuit₁, hval] using heval liveBits hlen
      obtain ⟨live₁, h_live₁_lt, h_live₁_nodup, deadBits₁,
              c', k', next, h_live', h_eq_step⟩ :=
        have h_and_or : UnboundedFanInFormula.IsAndOr circuit.val := by
          cases hcv : circuit.val with
          | inputGate i b => exact absurd ⟨i, b, hcv⟩ h_input
          | constant b m =>
              rw [hcv] at h_cf
              simp only [IsConstantFree] at h_cf
          | notGate g =>
              have hstrict :=
                Circuits.Leveling.isProperlyLeveled_imp_strict _ _ circuit.property.2.2.2.2
              rw [hcv] at hstrict
              simp only [IsAlternatingAndLeveledAt] at hstrict
          | andGate gates => exact True.intro
          | orGate gates => exact True.intro
        have h_ne : HasNoEmptyAndOrGate circuit.val := by
          rcases h_clean with hclean_empty | hne
          · exact absurd hclean_empty h_empty
          · exact hne
        exists_switching_depth_reduction hd state ht h_and_or h_ne h_thr_round
      -- The iterated threshold survives one round: feeding `live₁`
      -- (whose length is ≥ ⌊n/(20t)⌋) the remaining `(20t)^(d-2)`
      -- budget still fits.
      have h_thr_ih : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ live₁.length := by
        have hsurv : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ n / (20 * t) := by
          rw [Nat.le_div_iff_mul_le h_twenty_mul_t_pos]
          have hpow :
              (20 * t) ^ (d - 2) * (20 * t) =
                (20 * t) ^ ((d + 1) - 2) := by
            rw [show (d + 1) - 2 = (d - 2) + 1 by omega, pow_succ]
          calc (20 * t) ^ (d - 2) * (20 * t * (t + 1)) * (20 * t)
              = ((20 * t) ^ (d - 2) * (20 * t)) * (20 * t * (t + 1)) := by ring
            _ = (20 * t) ^ ((d + 1) - 2) * (20 * t * (t + 1)) := by rw [hpow]
            _ ≤ n := h_thresh
        exact le_trans hsurv h_live'
      -- Apply IH to the peeled circuit on `live₁.length` inputs, carrying
      -- the maintained invariant and the surviving threshold.
      obtain ⟨live₂, h_live₂_lt, h_live₂_nodup, h_live₂_big,
              deadBits₂,
              w, hw, g, hgw, h_eq_ih⟩ :=
        ih next h_thr_ih
      -- Compose the two restrictions into one on the original `n`.
      obtain ⟨live, h_live_lt, h_live_nodup, deadBits,
              _, h_len_eq, h_assemble⟩ :=
        exists_composed_collapse n live₁ h_live₁_lt h_live₁_nodup
          deadBits₁ live₂ h_live₂_lt h_live₂_nodup
          deadBits₂
      have h_live_big : 2 ≤ live.length := by rw [h_len_eq]; exact h_live₂_big
      -- Rewire `w, g` from `live₂.length` to `live.length` via `h_len_eq`.
      -- Build the recast DNF explicitly (so `.val` is definitionally `g.val`,
      -- avoiding the `Eq.rec` transport).
      refine ⟨live, h_live_lt, h_live_nodup, h_live_big, deadBits,
              w, ?_, ⟨g.val, by rw [h_len_eq]; exact g.property.1, g.property.2⟩, ?_, ?_⟩
      · rw [h_len_eq]; exact hw
      · -- `dnfWidth g.val ≤ w`: the recast leaves the DNF value unchanged.
        exact hgw
      · intro liveBits h_len
        -- Chain: original eval on `assemble n live liveBits deadBits`
        --   = original eval on `assemble n live₁ (assemble live₁.length
        --     live₂ liveBits deadBits₂) deadBits₁`      (by h_assemble)
        --   = next circuit eval on `assemble live₁.length live₂ liveBits
        --     deadBits₂`                                  (by h_eq_step)
        --   = g eval on liveBits                          (by h_eq_ih)
        have hlb₂ : liveBits.length = live₂.length := by rw [h_len, h_len_eq]
        rw [h_assemble liveBits hlb₂]
        rw [h_eq_step (assembleInput live₁.length live₂ liveBits deadBits₂)
              (length_assembleInput live₁.length live₂ liveBits deadBits₂)]
        exact h_eq_ih liveBits hlb₂

end Circuits.HastadParity
