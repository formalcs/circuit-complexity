/-
  Flattening substitution for leveled formulas.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.DecisionTree

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

section SubstFlatten
open UnboundedFanInFormula

theorem UnboundedFanInFormula.induction {motive : UnboundedFanInFormula → Prop}
    (input : ∀ i b, motive (inputGate i b))
    (const : ∀ b m, motive (constant b m))
    (notg : ∀ g, motive g → motive (notGate g))
    (andg : ∀ gs, (∀ g ∈ gs, motive g) → motive (andGate gs))
    (org : ∀ gs, (∀ g ∈ gs, motive g) → motive (orGate gs))
    (g : UnboundedFanInFormula) : motive g := by
  have key : ∀ n (g : UnboundedFanInFormula), sizeOf g < n → motive g := by
    intro n
    induction n with
    | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro g hg
      cases g with
      | inputGate i b => exact input i b
      | constant b m => exact const b m
      | notGate g₀ =>
          apply notg; apply ih
          simp only [UnboundedFanInFormula.notGate.sizeOf_spec] at hg; omega
      | andGate gs =>
          apply andg; intro x hx; apply ih
          have h₁ : sizeOf x < sizeOf gs := List.sizeOf_lt_of_mem hx
          simp only [UnboundedFanInFormula.andGate.sizeOf_spec] at hg; omega
      | orGate gs =>
          apply org; intro x hx; apply ih
          have h₁ : sizeOf x < sizeOf gs := List.sizeOf_lt_of_mem hx
          simp only [UnboundedFanInFormula.orGate.sizeOf_spec] at hg; omega
  exact key (sizeOf g + 1) g (Nat.lt_succ_self _)

def flattenAndChild : UnboundedFanInFormula → List UnboundedFanInFormula
  | andGate inner => inner
  | inputGate i b => [inputGate i b]
  | constant b m => [constant b m]
  | notGate g => [notGate g]
  | orGate gs => [orGate gs]

def flattenOrChild : UnboundedFanInFormula → List UnboundedFanInFormula
  | orGate inner => inner
  | inputGate i b => [inputGate i b]
  | constant b m => [constant b m]
  | notGate g => [notGate g]
  | andGate gs => [andGate gs]

def substFlatten (sub : Nat → UnboundedFanInFormula) :
    UnboundedFanInFormula → UnboundedFanInFormula
  | inputGate i _ => sub i
  | constant b m => constant b m
  | notGate g => notGate (substFlatten sub g)
  | andGate gs => andGate (gs.attach.flatMap (fun g => flattenAndChild (substFlatten sub g.1)))
  | orGate gs => orGate (gs.attach.flatMap (fun g => flattenOrChild (substFlatten sub g.1)))
  termination_by g => sizeOf g
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        | omega
        | (have := List.sizeOf_lt_of_mem g.2; omega)

lemma list_attach_flatMap {α β} (l : List α) (f : α → List β) :
    (l.attach.flatMap fun x => f x.1) = l.flatMap f := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.attach_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_map]
    rw [ih]

lemma substFlatten_and (sub : Nat → UnboundedFanInFormula)
    (gs : List UnboundedFanInFormula) :
    substFlatten sub (andGate gs)
      = andGate (gs.flatMap (fun g => flattenAndChild (substFlatten sub g))) := by
  conv_lhs => rw [substFlatten]
  congr 1
  exact list_attach_flatMap gs (fun g => flattenAndChild (substFlatten sub g))

lemma substFlatten_or (sub : Nat → UnboundedFanInFormula)
    (gs : List UnboundedFanInFormula) :
    substFlatten sub (orGate gs)
      = orGate (gs.flatMap (fun g => flattenOrChild (substFlatten sub g))) := by
  conv_lhs => rw [substFlatten]
  congr 1
  exact list_attach_flatMap gs (fun g => flattenOrChild (substFlatten sub g))

/- flattenAndChild preserves the multiset of input indices: unwrapping a top andGate
   does not add or remove any inputGate leaves. -/
lemma flattenAndChild_collect (h : UnboundedFanInFormula) :
    (flattenAndChild h).flatMap ufiCollectInputIndices = ufiCollectInputIndices h := by
  cases h with
  | inputGate i b => simp [flattenAndChild, ufiCollectInputIndices]
  | constant b m => simp [flattenAndChild, ufiCollectInputIndices]
  | notGate g => simp [flattenAndChild, ufiCollectInputIndices]
  | andGate gs => simp [flattenAndChild, ufiCollectInputIndices]
  | orGate gs => simp [flattenAndChild, ufiCollectInputIndices]

lemma flattenOrChild_collect (h : UnboundedFanInFormula) :
    (flattenOrChild h).flatMap ufiCollectInputIndices = ufiCollectInputIndices h := by
  cases h with
  | inputGate i b => simp [flattenOrChild, ufiCollectInputIndices]
  | constant b m => simp [flattenOrChild, ufiCollectInputIndices]
  | notGate g => simp [flattenOrChild, ufiCollectInputIndices]
  | andGate gs => simp [flattenOrChild, ufiCollectInputIndices]
  | orGate gs => simp [flattenOrChild, ufiCollectInputIndices]

/- Every input index appearing in `substFlatten sub g` comes from some `sub i`
   where `i` is an input index of `g`. -/
lemma exists_mem_collect_of_mem_collect_substFlatten (sub : Nat → UnboundedFanInFormula)
    (g : UnboundedFanInFormula) :
    ∀ x ∈ ufiCollectInputIndices (substFlatten sub g),
      ∃ i ∈ ufiCollectInputIndices g, x ∈ ufiCollectInputIndices (sub i) := by
  induction g using UnboundedFanInFormula.induction with
  | input i b =>
    intro x hx
    refine ⟨i, ?_, ?_⟩
    · simp [ufiCollectInputIndices]
    · simpa [substFlatten] using hx
  | const b m =>
    intro x hx
    simp [substFlatten, ufiCollectInputIndices] at hx
  | notg g ih =>
    intro x hx
    simp only [substFlatten, ufiCollectInputIndices] at hx
    obtain ⟨i, hi, hxi⟩ := ih x hx
    exact ⟨i, by simpa [ufiCollectInputIndices] using hi, hxi⟩
  | andg gs ih =>
    intro x hx
    rw [substFlatten_and] at hx
    simp only [ufiCollectInputIndices] at hx
    rw [List.mem_flatMap] at hx
    obtain ⟨child, hchild, hxchild⟩ := hx
    rw [List.mem_flatMap] at hchild
    obtain ⟨g, hg, hchildg⟩ := hchild
    have hxg : x ∈ ufiCollectInputIndices (substFlatten sub g) := by
      rw [← flattenAndChild_collect (substFlatten sub g), List.mem_flatMap]
      exact ⟨child, hchildg, hxchild⟩
    obtain ⟨i, hi, hxi⟩ := ih g hg x hxg
    refine ⟨i, ?_, hxi⟩
    simp only [ufiCollectInputIndices, List.mem_flatMap]
    exact ⟨g, hg, hi⟩
  | org gs ih =>
    intro x hx
    rw [substFlatten_or] at hx
    simp only [ufiCollectInputIndices] at hx
    rw [List.mem_flatMap] at hx
    obtain ⟨child, hchild, hxchild⟩ := hx
    rw [List.mem_flatMap] at hchild
    obtain ⟨g, hg, hchildg⟩ := hchild
    have hxg : x ∈ ufiCollectInputIndices (substFlatten sub g) := by
      rw [← flattenOrChild_collect (substFlatten sub g), List.mem_flatMap]
      exact ⟨child, hchildg, hxchild⟩
    obtain ⟨i, hi, hxi⟩ := ih g hg x hxg
    refine ⟨i, ?_, hxi⟩
    simp only [ufiCollectInputIndices, List.mem_flatMap]
    exact ⟨g, hg, hi⟩

/- Corollary: if every `sub i` (for `i` an input of `g`) has all input indices `< n`,
   then `substFlatten sub g` has all input indices `< n`. -/
lemma substFlatten_inputs_lt (sub : Nat → UnboundedFanInFormula)
    (g : UnboundedFanInFormula) (n : Nat)
    (hsub : ∀ i ∈ ufiCollectInputIndices g, ∀ x ∈ ufiCollectInputIndices (sub i), x < n) :
    ∀ x ∈ ufiCollectInputIndices (substFlatten sub g), x < n := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := exists_mem_collect_of_mem_collect_substFlatten sub g x hx
  exact hsub i hi x hxi

def ufiNegInputs : UnboundedFanInFormula → List Nat
  | inputGate n b => if b then [n] else []
  | constant _ _ => []
  | notGate g => ufiNegInputs g
  | andGate gs => gs.flatMap ufiNegInputs
  | orGate gs => gs.flatMap ufiNegInputs

lemma flattenAndChild_all_eq (g : UnboundedFanInFormula) (ys : List Bool) :
    ((flattenAndChild g).map (fun c => ufiFormulaEval c ys)).all (· == true)
      = (ufiFormulaEval g ys == true) := by
  cases g with
  | andGate inner =>
    simp only [flattenAndChild]
    rw [ufi_eval_andGate_eq_all]
    cases (inner.map (fun c => ufiFormulaEval c ys)).all (· == true) <;> rfl
  | inputGate i b =>
    simp only [flattenAndChild, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true]
  | constant b m =>
    simp only [flattenAndChild, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true]
  | notGate g₀ =>
    simp only [flattenAndChild, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true]
  | orGate gs =>
    simp only [flattenAndChild, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true]

lemma flattenOrChild_any_eq (g : UnboundedFanInFormula) (ys : List Bool) :
    ((flattenOrChild g).map (fun c => ufiFormulaEval c ys)).any (· == true)
      = (ufiFormulaEval g ys == true) := by
  cases g with
  | orGate inner =>
    simp only [flattenOrChild]
    rw [ufi_eval_orGate_eq_any]
    cases (inner.map (fun c => ufiFormulaEval c ys)).any (· == true) <;> rfl
  | inputGate i b =>
    simp only [flattenOrChild, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false]
  | constant b m =>
    simp only [flattenOrChild, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false]
  | notGate g₀ =>
    simp only [flattenOrChild, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false]
  | andGate gs =>
    simp only [flattenOrChild, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false]

lemma andGate_flatMap_flattenAndChild_eval (hs : List UnboundedFanInFormula)
    (ys : List Bool) :
    ufiFormulaEval (andGate (hs.flatMap flattenAndChild)) ys
      = ufiFormulaEval (andGate hs) ys := by
  have hcond : ((hs.flatMap flattenAndChild).map (fun c => ufiFormulaEval c ys)).all
      (· == true) = ((hs.map (fun c => ufiFormulaEval c ys)).all (· == true)) := by
    induction hs with
    | nil => rfl
    | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.all_append, List.map_cons,
        List.all_cons, flattenAndChild_all_eq a ys, ih]
  rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all, hcond]

lemma orGate_flatMap_flattenOrChild_eval (hs : List UnboundedFanInFormula)
    (ys : List Bool) :
    ufiFormulaEval (orGate (hs.flatMap flattenOrChild)) ys
      = ufiFormulaEval (orGate hs) ys := by
  have hcond : ((hs.flatMap flattenOrChild).map (fun c => ufiFormulaEval c ys)).any
      (· == true) = ((hs.map (fun c => ufiFormulaEval c ys)).any (· == true)) := by
    induction hs with
    | nil => rfl
    | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.any_append, List.map_cons,
        List.any_cons, flattenOrChild_any_eq a ys, ih]
  rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any, hcond]

lemma substFlatten_eval (sub : Nat → UnboundedFanInFormula) (ys vals : List Bool)
    (g : UnboundedFanInFormula) :
    ufiNegInputs g = [] →
    (∀ i ∈ ufiCollectInputIndices g,
        vals[i]? = some (ufiFormulaEval (sub i) ys)) →
    ufiFormulaEval (substFlatten sub g) ys = ufiFormulaEval g vals := by
  induction g using UnboundedFanInFormula.induction with
  | input i b =>
    intro hpos hlook
    have hb : b = false := by
      simp only [ufiNegInputs] at hpos
      cases b with
      | false => rfl
      | true => simp at hpos
    subst hb
    have hmem : i ∈ ufiCollectInputIndices (inputGate i false) := by
      simp [ufiCollectInputIndices]
    have hget := hlook i hmem
    simp only [substFlatten]
    conv_rhs => unfold ufiFormulaEval
    rw [hget]
  | const b m =>
    intro hpos hlook
    simp only [substFlatten, ufiFormulaEval]
  | notg g ih =>
    intro hpos hlook
    simp only [ufiNegInputs] at hpos
    have hlook' : ∀ i ∈ ufiCollectInputIndices g,
        vals[i]? = some (ufiFormulaEval (sub i) ys) := by
      intro i hi; exact hlook i (by simpa [ufiCollectInputIndices] using hi)
    simp only [substFlatten, ufiFormulaEval, ih hpos hlook']
  | andg gs ih =>
    intro hpos hlook
    simp only [ufiNegInputs] at hpos
    rw [substFlatten_and]
    have hchild : (gs.flatMap (fun g => flattenAndChild (substFlatten sub g)))
        = (gs.map (substFlatten sub)).flatMap flattenAndChild := by
      rw [List.flatMap_map]
    rw [hchild, andGate_flatMap_flattenAndChild_eval]
    have hmap : (gs.map (substFlatten sub)).map (fun c => ufiFormulaEval c ys)
        = gs.map (fun c => ufiFormulaEval c vals) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro g hg
      have hposg : ufiNegInputs g = [] := (List.flatMap_eq_nil_iff.mp hpos) g hg
      have hlookg : ∀ i ∈ ufiCollectInputIndices g,
          vals[i]? = some (ufiFormulaEval (sub i) ys) := by
        intro i hi
        apply hlook i
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨g, hg, hi⟩
      simp only [Function.comp_apply]
      exact ih g hg hposg hlookg
    rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all, hmap]
  | org gs ih =>
    intro hpos hlook
    simp only [ufiNegInputs] at hpos
    rw [substFlatten_or]
    have hchild : (gs.flatMap (fun g => flattenOrChild (substFlatten sub g)))
        = (gs.map (substFlatten sub)).flatMap flattenOrChild := by
      rw [List.flatMap_map]
    rw [hchild, orGate_flatMap_flattenOrChild_eval]
    have hmap : (gs.map (substFlatten sub)).map (fun c => ufiFormulaEval c ys)
        = gs.map (fun c => ufiFormulaEval c vals) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro g hg
      have hposg : ufiNegInputs g = [] := (List.flatMap_eq_nil_iff.mp hpos) g hg
      have hlookg : ∀ i ∈ ufiCollectInputIndices g,
          vals[i]? = some (ufiFormulaEval (sub i) ys) := by
        intro i hi
        apply hlook i
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨g, hg, hi⟩
      simp only [Function.comp_apply]
      exact ih g hg hposg hlookg
    rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any, hmap]

/- ### (3a) Alternation: substFlatten output never nests a gate inside the same gate type. -/

/- An element of `flattenAndChild h` either comes from splicing an `andGate`'s inner
   children, or is `h` itself when `h` is not an andGate. -/
lemma flattenAndChild_mem (h x : UnboundedFanInFormula) (hx : x ∈ flattenAndChild h) :
    (∃ inner, h = andGate inner ∧ x ∈ inner) ∨ (x = h ∧ ∀ inner, h ≠ andGate inner) := by
  cases h with
  | andGate inner =>
    left; exact ⟨inner, rfl, by simpa [flattenAndChild] using hx⟩
  | inputGate i b =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenAndChild] using hx
    · intro inner; simp
  | constant b m =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenAndChild] using hx
    · intro inner; simp
  | notGate g₀ =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenAndChild] using hx
    · intro inner; simp
  | orGate gs =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenAndChild] using hx
    · intro inner; simp

lemma flattenOrChild_mem (h x : UnboundedFanInFormula) (hx : x ∈ flattenOrChild h) :
    (∃ inner, h = orGate inner ∧ x ∈ inner) ∨ (x = h ∧ ∀ inner, h ≠ orGate inner) := by
  cases h with
  | orGate inner =>
    left; exact ⟨inner, rfl, by simpa [flattenOrChild] using hx⟩
  | inputGate i b =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenOrChild] using hx
    · intro inner; simp
  | constant b m =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenOrChild] using hx
    · intro inner; simp
  | notGate g₀ =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenOrChild] using hx
    · intro inner; simp
  | andGate gs =>
    right; refine ⟨?_, ?_⟩
    · simpa [flattenOrChild] using hx
    · intro inner; simp

/- ### (3b) Depth bound: substFlatten of a leveled gate has depth ≤ depth + 1. -/

lemma ufiFormulaDepth_andGate (gs : List UnboundedFanInFormula) :
    ufiFormulaDepth (andGate gs) = 1 + (List.foldr max 0) (gs.map ufiFormulaDepth) := by
  simp only [ufiFormulaDepth]

lemma ufiFormulaDepth_orGate (gs : List UnboundedFanInFormula) :
    ufiFormulaDepth (orGate gs) = 1 + (List.foldr max 0) (gs.map ufiFormulaDepth) := by
  simp only [ufiFormulaDepth]

/- ### (3c) Leveling preservation: substFlatten lifts a strictly-leveled gate one level. -/

/- Strict assigned-leveling is monotone increasing in the level argument: raising the
   level only relaxes the `IsAndOr → 1 ≤ n` constraints. -/
lemma isAlternatingAndLeveledAt_mono (g : UnboundedFanInFormula) :
    ∀ n n', n ≤ n' →
      IsAlternatingAndLeveledAt g n → IsAlternatingAndLeveledAt g n' := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => intro n n' _ _; simp only [IsAlternatingAndLeveledAt]
  | const b m => intro n n' _ _; simp only [IsAlternatingAndLeveledAt]
  | notg g ih => intro n n' _ h; simp only [IsAlternatingAndLeveledAt] at h
  | andg gs ih =>
    intro n n' hle h
    simp only [IsAlternatingAndLeveledAt] at h ⊢
    obtain ⟨h₁, h₂, h₃⟩ := h
    refine ⟨h₁, ?_, ?_⟩
    · intro g hg hand; exact le_trans (h₂ g hg hand) hle
    · intro g hg; exact ih g hg (n - 1) (n' - 1) (by omega) (h₃ g hg)
  | org gs ih =>
    intro n n' hle h
    simp only [IsAlternatingAndLeveledAt] at h ⊢
    obtain ⟨h₁, h₂, h₃⟩ := h
    refine ⟨h₁, ?_, ?_⟩
    · intro g hg hand; exact le_trans (h₂ g hg hand) hle
    · intro g hg; exact ih g hg (n - 1) (n' - 1) (by omega) (h₃ g hg)

/- The substitution is "leveling-ready" at level `n` for gate `g`: every inputGate leaf
   directly under an andGate (resp. orGate) maps either to a same-type gate (which then
   splices, requiring the gate to be strictly leveled at `n+1`) or to a non-same-type
   formula (kept as a singleton child, requiring strict leveling at `n`). -/
def IsSubstitutionReady (sub : Nat → UnboundedFanInFormula) :
    UnboundedFanInFormula → Nat → Prop
  | inputGate _ _, _ => True
  | constant _ _, _ => True
  | notGate _, _ => False
  | andGate gs, n =>
      (∀ i b, inputGate i b ∈ gs →
        ((∃ cl, sub i = andGate cl) ∧ IsAlternatingAndLeveledAt (sub i) (n + 1)) ∨
        ((∀ cl, sub i ≠ andGate cl) ∧ IsAlternatingAndLeveledAt (sub i) n)) ∧
      (∀ g ∈ gs, IsSubstitutionReady sub g (n - 1))
  | orGate gs, n =>
      (∀ i b, inputGate i b ∈ gs →
        ((∃ cl, sub i = orGate cl) ∧ IsAlternatingAndLeveledAt (sub i) (n + 1)) ∨
        ((∀ cl, sub i ≠ orGate cl) ∧ IsAlternatingAndLeveledAt (sub i) n)) ∧
      (∀ g ∈ gs, IsSubstitutionReady sub g (n - 1))

lemma isAlternatingAndLeveledAt_substFlatten (sub : Nat → UnboundedFanInFormula)
    (g : UnboundedFanInFormula) :
    ∀ n, IsAndOr g → IsAlternatingAndLeveledAt g n → IsSubstitutionReady sub g n →
      IsAlternatingAndLeveledAt (substFlatten sub g) (n + 1) := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => intro n hand _ _; exact absurd hand (by simp [IsAndOr])
  | const b m => intro n hand _ _; exact absurd hand (by simp [IsAndOr])
  | notg g ih => intro n hand _ _; exact absurd hand (by simp [IsAndOr])
  | andg gs ih =>
    intro n _ h hsub
    simp only [IsAlternatingAndLeveledAt] at h
    obtain ⟨_, h_andor, h_rec⟩ := h
    simp only [IsSubstitutionReady] at hsub
    obtain ⟨h_subinput, h_subrec⟩ := hsub
    rw [substFlatten_and]
    have key : ∀ c ∈ gs.flatMap (fun g => flattenAndChild (substFlatten sub g)),
        (∀ inner, c ≠ andGate inner) ∧ IsAlternatingAndLeveledAt c n := by
      intro c hc
      rw [List.mem_flatMap] at hc
      obtain ⟨gc, hgc, hcc⟩ := hc
      cases gc with
      | inputGate i b =>
        simp only [substFlatten] at hcc
        rcases flattenAndChild_mem _ c hcc with ⟨inner, hsplit, hcin⟩ | ⟨hceq, hcne⟩
        · rcases h_subinput i b hgc with ⟨_, hlev⟩ | ⟨hne, _⟩
          · rw [hsplit] at hlev
            simp only [IsAlternatingAndLeveledAt] at hlev
            obtain ⟨hl₁, _, hl₃⟩ := hlev
            exact ⟨hl₁ c hcin, hl₃ c hcin⟩
          · exact absurd hsplit (hne inner)
        · rcases h_subinput i b hgc with ⟨⟨cl, hcl⟩, _⟩ | ⟨_, hlev⟩
          · exact absurd hcl (hcne cl)
          · subst hceq; exact ⟨hcne, hlev⟩
      | constant b m =>
        simp only [substFlatten, flattenAndChild, List.mem_singleton] at hcc
        subst hcc
        exact ⟨by simp, by simp [IsAlternatingAndLeveledAt]⟩
      | notGate g₀ =>
        have hf := h_rec (notGate g₀) hgc
        simp only [IsAlternatingAndLeveledAt] at hf
      | andGate gs' =>
        rw [substFlatten_and] at hcc
        change c ∈ gs'.flatMap (fun g => flattenAndChild (substFlatten sub g)) at hcc
        have hih := ih (andGate gs') hgc (n - 1) (by simp [IsAndOr])
          (h_rec _ hgc) (h_subrec _ hgc)
        rw [substFlatten_and] at hih
        simp only [IsAlternatingAndLeveledAt] at hih
        obtain ⟨hi₁, _, hi₃⟩ := hih
        exact ⟨hi₁ c hcc, isAlternatingAndLeveledAt_mono c (n - 1) n (by omega) (hi₃ c hcc)⟩
      | orGate gs' =>
        rw [substFlatten_or] at hcc
        simp only [flattenAndChild, List.mem_singleton] at hcc
        have hn₁ := h_andor (orGate gs') hgc (by simp [IsAndOr])
        have hih := ih (orGate gs') hgc (n - 1) (by simp [IsAndOr])
          (h_rec _ hgc) (h_subrec _ hgc)
        rw [substFlatten_or] at hih
        have hnn : n - 1 + 1 = n := by omega
        rw [hnn] at hih
        subst hcc
        exact ⟨by simp, hih⟩
    simp only [IsAlternatingAndLeveledAt]
    exact ⟨fun c hc inner => (key c hc).1 inner, fun c hc _ => by omega,
      fun c hc => (key c hc).2⟩
  | org gs ih =>
    intro n _ h hsub
    simp only [IsAlternatingAndLeveledAt] at h
    obtain ⟨_, h_andor, h_rec⟩ := h
    simp only [IsSubstitutionReady] at hsub
    obtain ⟨h_subinput, h_subrec⟩ := hsub
    rw [substFlatten_or]
    have key : ∀ c ∈ gs.flatMap (fun g => flattenOrChild (substFlatten sub g)),
        (∀ inner, c ≠ orGate inner) ∧ IsAlternatingAndLeveledAt c n := by
      intro c hc
      rw [List.mem_flatMap] at hc
      obtain ⟨gc, hgc, hcc⟩ := hc
      cases gc with
      | inputGate i b =>
        simp only [substFlatten] at hcc
        rcases flattenOrChild_mem _ c hcc with ⟨inner, hsplit, hcin⟩ | ⟨hceq, hcne⟩
        · rcases h_subinput i b hgc with ⟨_, hlev⟩ | ⟨hne, _⟩
          · rw [hsplit] at hlev
            simp only [IsAlternatingAndLeveledAt] at hlev
            obtain ⟨hl₁, _, hl₃⟩ := hlev
            exact ⟨hl₁ c hcin, hl₃ c hcin⟩
          · exact absurd hsplit (hne inner)
        · rcases h_subinput i b hgc with ⟨⟨cl, hcl⟩, _⟩ | ⟨_, hlev⟩
          · exact absurd hcl (hcne cl)
          · subst hceq; exact ⟨hcne, hlev⟩
      | constant b m =>
        simp only [substFlatten, flattenOrChild, List.mem_singleton] at hcc
        subst hcc
        exact ⟨by simp, by simp [IsAlternatingAndLeveledAt]⟩
      | notGate g₀ =>
        have hf := h_rec (notGate g₀) hgc
        simp only [IsAlternatingAndLeveledAt] at hf
      | orGate gs' =>
        rw [substFlatten_or] at hcc
        change c ∈ gs'.flatMap (fun g => flattenOrChild (substFlatten sub g)) at hcc
        have hih := ih (orGate gs') hgc (n - 1) (by simp [IsAndOr])
          (h_rec _ hgc) (h_subrec _ hgc)
        rw [substFlatten_or] at hih
        simp only [IsAlternatingAndLeveledAt] at hih
        obtain ⟨hi₁, _, hi₃⟩ := hih
        exact ⟨hi₁ c hcc, isAlternatingAndLeveledAt_mono c (n - 1) n (by omega) (hi₃ c hcc)⟩
      | andGate gs' =>
        rw [substFlatten_and] at hcc
        simp only [flattenOrChild, List.mem_singleton] at hcc
        have hn₁ := h_andor (andGate gs') hgc (by simp [IsAndOr])
        have hih := ih (andGate gs') hgc (n - 1) (by simp [IsAndOr])
          (h_rec _ hgc) (h_subrec _ hgc)
        rw [substFlatten_and] at hih
        have hnn : n - 1 + 1 = n := by omega
        rw [hnn] at hih
        subst hcc
        exact ⟨by simp, hih⟩
    simp only [IsAlternatingAndLeveledAt]
    exact ⟨fun c hc inner => (key c hc).1 inner, fun c hc _ => by omega,
      fun c hc => (key c hc).2⟩

/- ### (3e) Circuit-size bound: substFlatten blows up circuit size by at most a factor `B`,
   where `B` bounds every `circuit_size (sub i)`. -/

lemma ufiFormulaCircuitSize_andGate (gs : List UnboundedFanInFormula) :
    ufiFormulaCircuitSize (andGate gs) = 1 + (gs.map ufiFormulaCircuitSize).sum := by
  simp only [ufiFormulaCircuitSize, Nat.add_comm]

lemma ufiFormulaCircuitSize_orGate (gs : List UnboundedFanInFormula) :
    ufiFormulaCircuitSize (orGate gs) = 1 + (gs.map ufiFormulaCircuitSize).sum := by
  simp only [ufiFormulaCircuitSize, Nat.add_comm]

/- Splicing an And/Or child never increases the summed circuit size of the produced list. -/
lemma flattenAndChild_size_sum_le (h : UnboundedFanInFormula) :
    ((flattenAndChild h).map ufiFormulaCircuitSize).sum ≤ ufiFormulaCircuitSize h := by
  cases h with
  | andGate inner => simp only [flattenAndChild, ufiFormulaCircuitSize_andGate]; omega
  | inputGate i b => simp [flattenAndChild, ufiFormulaCircuitSize]
  | constant b m => simp [flattenAndChild, ufiFormulaCircuitSize]
  | notGate g₀ => simp [flattenAndChild, ufiFormulaCircuitSize]
  | orGate gs => simp [flattenAndChild, ufiFormulaCircuitSize]

lemma flattenOrChild_size_sum_le (h : UnboundedFanInFormula) :
    ((flattenOrChild h).map ufiFormulaCircuitSize).sum ≤ ufiFormulaCircuitSize h := by
  cases h with
  | orGate inner => simp only [flattenOrChild, ufiFormulaCircuitSize_orGate]; omega
  | inputGate i b => simp [flattenOrChild, ufiFormulaCircuitSize]
  | constant b m => simp [flattenOrChild, ufiFormulaCircuitSize]
  | notGate g₀ => simp [flattenOrChild, ufiFormulaCircuitSize]
  | andGate gs => simp [flattenOrChild, ufiFormulaCircuitSize]

lemma flatMap_size_sum_eq (gs : List UnboundedFanInFormula)
    (f : UnboundedFanInFormula → List UnboundedFanInFormula) :
    ((gs.flatMap f).map ufiFormulaCircuitSize).sum
      = (gs.map (fun g => ((f g).map ufiFormulaCircuitSize).sum)).sum := by
  induction gs with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma sum_map_mul_factor {α : Type*} (b : Nat) (l : List α) (f : α → Nat) :
    (l.map (fun x => f x * b)).sum = (l.map f).sum * b := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.map_cons, List.sum_cons, ih, Nat.add_mul]

lemma list_sum_map_le {l : List UnboundedFanInFormula}
    {f g : UnboundedFanInFormula → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

lemma substFlatten_ufiFormulaCircuitSize_le (sub : Nat → UnboundedFanInFormula) (b : Nat)
    (hb : 1 ≤ b) (hsub : ∀ i, ufiFormulaCircuitSize (sub i) ≤ b)
    (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (substFlatten sub g) ≤
      (ufiFormulaCircuitSize g + (ufiCollectInputIndices g).length) * b := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => simpa [substFlatten, ufiFormulaCircuitSize,
      ufiCollectInputIndices] using hsub i
  | const b m =>
      simp only [substFlatten, ufiFormulaCircuitSize, ufiCollectInputIndices,
        List.length_nil, Nat.add_zero, Nat.one_mul]
      exact hb
  | notg g ih =>
    simp only [substFlatten, ufiFormulaCircuitSize, ufiCollectInputIndices]
    simp only [Nat.add_mul] at ih ⊢
    omega
  | andg gs ih =>
    rw [substFlatten_and, ufiFormulaCircuitSize_andGate, ufiFormulaCircuitSize_andGate, flatMap_size_sum_eq]
    have hbound : (gs.map (fun g =>
        ((flattenAndChild (substFlatten sub g)).map ufiFormulaCircuitSize).sum)).sum
        ≤ (gs.map (fun g =>
          (ufiFormulaCircuitSize g + (ufiCollectInputIndices g).length) * b)).sum :=
      list_sum_map_le (fun g hg =>
        le_trans (flattenAndChild_size_sum_le _) (ih g hg))
    simp only [ufiCollectInputIndices, List.length_flatMap] at hbound ⊢
    simp only [Nat.add_mul, List.sum_map_add] at hbound
    rw [sum_map_mul_factor, sum_map_mul_factor] at hbound
    simp only [Nat.add_mul]
    omega
  | org gs ih =>
    rw [substFlatten_or, ufiFormulaCircuitSize_orGate, ufiFormulaCircuitSize_orGate, flatMap_size_sum_eq]
    have hbound : (gs.map (fun g =>
        ((flattenOrChild (substFlatten sub g)).map ufiFormulaCircuitSize).sum)).sum
        ≤ (gs.map (fun g =>
          (ufiFormulaCircuitSize g + (ufiCollectInputIndices g).length) * b)).sum :=
      list_sum_map_le (fun g hg =>
        le_trans (flattenOrChild_size_sum_le _) (ih g hg))
    simp only [ufiCollectInputIndices, List.length_flatMap] at hbound ⊢
    simp only [Nat.add_mul, List.sum_map_add] at hbound
    rw [sum_map_mul_factor, sum_map_mul_factor] at hbound
    simp only [Nat.add_mul]
    omega

/- ### (3d-core) Bottom-level `HasProperBottomsAt` merge.

   When a level-2 skeleton `andGate` whose children are placeholders `inputGate i` has each
   `sub i` a matching-polarity proper CNF (`andGate` of OR-of-inputs clauses), the flattened
   result `substFlatten sub (andGate gs)` is again a proper CNF (`isCNF`, nonempty clauses,
   Nodup clause-vars).  This is the delicate, polarity-specific case the (3d) counterexample
   flagged: a CNF clause (OR of inputs) at level 2 must pass `isCNF`, never `isDNF`.  Dual
   for `orGate`/DNF.  These lemmas supply the bottom case of the brick-[4] `HasProperBottomsAt`
   proof for the concrete `circuit' = substFlatten g_i' top.val`. -/

lemma isCNF_proper_flatten (h : UnboundedFanInFormula)
    (hcnf : isCNF h = true) : ∀ x ∈ flattenAndChild h, isOrOfInputsOnly x = true := by
  cases h with
  | andGate inner =>
    intro x hx
    simp only [flattenAndChild] at hx
    simp only [isCNF, List.all_eq_true] at hcnf
    exact hcnf x hx
  | inputGate i b => simp only [isCNF, Bool.false_eq_true] at hcnf
  | constant b m => simp only [isCNF, Bool.false_eq_true] at hcnf
  | notGate g => simp only [isCNF, Bool.false_eq_true] at hcnf
  | orGate gs => simp only [isCNF, Bool.false_eq_true] at hcnf

lemma exists_eq_andGate_of_isCNF (f : UnboundedFanInFormula) (h : isCNF f = true) :
    ∃ inner, f = andGate inner := by
  cases f with
  | andGate inner => exact ⟨inner, rfl⟩
  | inputGate i b => simp only [isCNF, Bool.false_eq_true] at h
  | constant b m => simp only [isCNF, Bool.false_eq_true] at h
  | notGate g => simp only [isCNF, Bool.false_eq_true] at h
  | orGate gs => simp only [isCNF, Bool.false_eq_true] at h

lemma isDNF_proper_flatten (h : UnboundedFanInFormula)
    (hdnf : isDNF h = true) : ∀ x ∈ flattenOrChild h, isAndOfInputsOnly x = true := by
  cases h with
  | orGate inner =>
    intro x hx
    simp only [flattenOrChild] at hx
    simp only [isDNF, List.all_eq_true] at hdnf
    exact hdnf x hx
  | inputGate i b => simp only [isDNF, Bool.false_eq_true] at hdnf
  | constant b m => simp only [isDNF, Bool.false_eq_true] at hdnf
  | notGate g => simp only [isDNF, Bool.false_eq_true] at hdnf
  | andGate gs => simp only [isDNF, Bool.false_eq_true] at hdnf

lemma exists_eq_orGate_of_isDNF (f : UnboundedFanInFormula) (h : isDNF f = true) :
    ∃ inner, f = orGate inner := by
  cases f with
  | orGate inner => exact ⟨inner, rfl⟩
  | inputGate i b => simp only [isDNF, Bool.false_eq_true] at h
  | constant b m => simp only [isDNF, Bool.false_eq_true] at h
  | notGate g => simp only [isDNF, Bool.false_eq_true] at h
  | andGate gs => simp only [isDNF, Bool.false_eq_true] at h

/-! ### Substitution-form predicates and extraction helpers. -/
def IsSubstitutionProperForm (sub : Nat → UnboundedFanInFormula)
    (needCnf : Bool) (i : Nat) : Prop :=
  if needCnf then
    isCNF (sub i) = true ∧
    (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), c ≠ []) ∧
    (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), (c.map Prod.fst).Nodup)
  else
    isDNF (sub i) = true ∧
    (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), c ≠ []) ∧
    (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), (c.map Prod.fst).Nodup)

def IsSubstitutionLeaf (sub : Nat → UnboundedFanInFormula) (i : Nat) : Prop :=
  (∃ x d, sub i = inputGate x d) ∨ (∃ b m, sub i = constant b m)

/-- At `lvl ≤ 2` the skeleton of any formula is the single placeholder
    `inputGate start false`. -/
lemma extractBottomLayer_two_top (start : Nat)
    (g : UnboundedFanInFormula) :
    (extractBottomLayer 2 start g).2.1 = inputGate start false := by
  cases g <;> simp [extractBottomLayer]

/-- At `lvl ≤ 2` the next placeholder index advances by exactly one. -/
lemma extractBottomLayer_two_next (start : Nat)
    (g : UnboundedFanInFormula) :
    (extractBottomLayer 2 start g).2.2 = start + 1 := by
  cases g <;> simp [extractBottomLayer]

/-- At `lvl = 2` the formula is its own (sole) extracted bottom. -/
lemma extractBottomLayer_two_self (g : UnboundedFanInFormula) :
    g ∈ (extractBottomLayer 2 0 g).1 := by
  cases g <;> simp [extractBottomLayer]

/-- The skeleton top of `extractBottomLayer` is an `andGate`/`orGate`
    (`IsAndOr`) whenever the source `f` is and `lvl > 2`. -/
lemma isAndOr_extractBottomLayer_top (lvl start : Nat)
    (f : UnboundedFanInFormula) (hle : ¬ lvl ≤ 2) (hand : IsAndOr f) :
    IsAndOr (extractBottomLayer lvl start f).2.1 := by
  cases f with
  | inputGate i b => exact absurd hand (by simp [IsAndOr])
  | constant b m => exact absurd hand (by simp [IsAndOr])
  | notGate g => exact absurd hand (by simp [IsAndOr])
  | andGate gates =>
      have h : (extractBottomLayer lvl start (andGate gates)).2.1
          = andGate (extractBottomLayerList (lvl - 1) start gates).2.1 := by
        simp [extractBottomLayer, hle]
      rw [h]; simp [IsAndOr]
  | orGate gates =>
      have h : (extractBottomLayer lvl start (orGate gates)).2.1
          = orGate (extractBottomLayerList (lvl - 1) start gates).2.1 := by
        simp [extractBottomLayer, hle]
      rw [h]; simp [IsAndOr]

/-- A proper CNF (`isCNF`) is `IsAlternatingAndLeveledAt` at every level `m ≥ 1`:
    its `orGate`-of-inputs clauses are never `andGate`, are `IsAndOr` (so the `1 ≤ m`
    obligation needs `hm`), and their `inputGate` children are strictly leveled below. -/
lemma isAlternatingAndLeveledAt_of_isCNF (g : UnboundedFanInFormula)
    (h : isCNF g = true) (m : Nat) (hm : 1 ≤ m) :
    IsAlternatingAndLeveledAt g m := by
  cases g with
  | inputGate i b => simp [isCNF] at h
  | constant b m' => simp [isCNF] at h
  | notGate g => simp [isCNF] at h
  | orGate gs => simp [isCNF] at h
  | andGate gs =>
    simp only [isCNF, List.all_eq_true] at h
    simp only [IsAlternatingAndLeveledAt]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx inner
      have hox := h x hx
      cases x with
      | inputGate i b => simp
      | constant b m' => simp
      | notGate g => simp [isOrOfInputsOnly] at hox
      | andGate gs' => simp [isOrOfInputsOnly] at hox
      | orGate ins => simp
    · intro _ _ _; exact hm
    · intro x hx
      have hox := h x hx
      cases x with
      | inputGate i b => simp [IsAlternatingAndLeveledAt]
      | constant b m' => simp [IsAlternatingAndLeveledAt]
      | notGate g => simp [isOrOfInputsOnly] at hox
      | andGate gs' => simp [isOrOfInputsOnly] at hox
      | orGate ins =>
        simp only [isOrOfInputsOnly, List.all_eq_true] at hox
        simp only [IsAlternatingAndLeveledAt]
        refine ⟨?_, ?_, ?_⟩
        · intro y hy inner
          have hiy := hox y hy
          cases y with
          | inputGate i b => simp
          | constant b m' => simp [isInput] at hiy
          | notGate g => simp [isInput] at hiy
          | andGate gs'' => simp [isInput] at hiy
          | orGate gs'' => simp [isInput] at hiy
        · intro y hy hand
          have hiy := hox y hy
          cases y with
          | inputGate i b => simp [IsAndOr] at hand
          | constant b m' => simp [isInput] at hiy
          | notGate g => simp [isInput] at hiy
          | andGate gs'' => simp [isInput] at hiy
          | orGate gs'' => simp [isInput] at hiy
        · intro y hy
          have hiy := hox y hy
          cases y with
          | inputGate i b => simp [IsAlternatingAndLeveledAt]
          | constant b m' => simp [IsAlternatingAndLeveledAt]
          | notGate g => simp [isInput] at hiy
          | andGate gs'' => simp [isInput] at hiy
          | orGate gs'' => simp [isInput] at hiy

/-- A proper DNF (`isDNF`) is `IsAlternatingAndLeveledAt` at every level `m ≥ 1`. Dual
    of `isAlternatingAndLeveledAt_of_isCNF`. -/
lemma isAlternatingAndLeveledAt_of_isDNF (g : UnboundedFanInFormula)
    (h : isDNF g = true) (m : Nat) (hm : 1 ≤ m) :
    IsAlternatingAndLeveledAt g m := by
  cases g with
  | inputGate i b => simp [isDNF] at h
  | constant b m' => simp [isDNF] at h
  | notGate g => simp [isDNF] at h
  | andGate gs => simp [isDNF] at h
  | orGate gs =>
    simp only [isDNF, List.all_eq_true] at h
    simp only [IsAlternatingAndLeveledAt]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx inner
      have hox := h x hx
      cases x with
      | inputGate i b => simp
      | constant b m' => simp
      | notGate g => simp [isAndOfInputsOnly] at hox
      | orGate gs' => simp [isAndOfInputsOnly] at hox
      | andGate ins => simp
    · intro _ _ _; exact hm
    · intro x hx
      have hox := h x hx
      cases x with
      | inputGate i b => simp [IsAlternatingAndLeveledAt]
      | constant b m' => simp [IsAlternatingAndLeveledAt]
      | notGate g => simp [isAndOfInputsOnly] at hox
      | orGate gs' => simp [isAndOfInputsOnly] at hox
      | andGate ins =>
        simp only [isAndOfInputsOnly, List.all_eq_true] at hox
        simp only [IsAlternatingAndLeveledAt]
        refine ⟨?_, ?_, ?_⟩
        · intro y hy inner
          have hiy := hox y hy
          cases y with
          | inputGate i b => simp
          | constant b m' => simp [isInput] at hiy
          | notGate g => simp [isInput] at hiy
          | andGate gs'' => simp [isInput] at hiy
          | orGate gs'' => simp [isInput] at hiy
        · intro y hy hand
          have hiy := hox y hy
          cases y with
          | inputGate i b => simp [IsAndOr] at hand
          | constant b m' => simp [isInput] at hiy
          | notGate g => simp [isInput] at hiy
          | andGate gs'' => simp [isInput] at hiy
          | orGate gs'' => simp [isInput] at hiy
        · intro y hy
          have hiy := hox y hy
          cases y with
          | inputGate i b => simp [IsAlternatingAndLeveledAt]
          | constant b m' => simp [IsAlternatingAndLeveledAt]
          | notGate g => simp [isInput] at hiy
          | andGate gs'' => simp [isInput] at hiy
          | orGate gs'' => simp [isInput] at hiy

/-- **Circuit-size consumer.**  Each skeleton gate is charged by circuit size,
    while each placeholder input is charged once for its substituted formula. -/
lemma extractBottomLayer_substFlatten_ufiFormulaCircuitSize_le
    (sub : Nat → UnboundedFanInFormula) (lvl B : Nat) (h_b : 1 ≤ B)
    (hsub : ∀ i, ufiFormulaCircuitSize (sub i) ≤ B)
    (circuit : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (substFlatten sub (extractBottomLayer lvl 0 circuit).2.1)
      ≤ (ufiFormulaCircuitSize circuit + (extractBottomLayer lvl 0 circuit).1.length) * B := by
  have h₁ := substFlatten_ufiFormulaCircuitSize_le sub B h_b hsub (extractBottomLayer lvl 0 circuit).2.1
  have h₂ := extractBottomLayer_top_ufiFormulaCircuitSize_le lvl 0 circuit
  have hcollect :
      (ufiCollectInputIndices (extractBottomLayer lvl 0 circuit).2.1).length =
        (extractBottomLayer lvl 0 circuit).1.length := by
    rw [extractBottomLayer_collect_eq, List.length_range']
  rw [hcollect] at h₁
  exact le_trans h₁ (Nat.mul_le_mul (Nat.add_le_add_right h₂ _) (le_refl B))

/-- An `orGate`-of-inputs clause has depth ≤ 1. -/
lemma isOrOfInputsOnly_depth_le (g : UnboundedFanInFormula)
    (h : isOrOfInputsOnly g = true) : ufiFormulaDepth g ≤ 1 := by
  cases g with
  | inputGate i b => simp [isOrOfInputsOnly] at h
  | constant b m => simp [isOrOfInputsOnly] at h
  | notGate g => simp [isOrOfInputsOnly] at h
  | andGate gs => simp [isOrOfInputsOnly] at h
  | orGate gs =>
      rw [ufiFormulaDepth_orGate]
      have hzero : (List.foldr max 0) (gs.map ufiFormulaDepth) ≤ 0 := by
        apply foldr_max_map_le
        intro x hx
        simp only [isOrOfInputsOnly, List.all_eq_true] at h
        have hin := h x hx
        cases x with
        | inputGate i b => simp [ufiFormulaDepth]
        | constant b m => simp [isInput] at hin
        | notGate g => simp [isInput] at hin
        | andGate gs => simp [isInput] at hin
        | orGate gs => simp [isInput] at hin
      omega

/-- An `andGate`-of-inputs clause has depth ≤ 1. -/
lemma isAndOfInputsOnly_depth_le (g : UnboundedFanInFormula)
    (h : isAndOfInputsOnly g = true) : ufiFormulaDepth g ≤ 1 := by
  cases g with
  | inputGate i b => simp [isAndOfInputsOnly] at h
  | constant b m => simp [isAndOfInputsOnly] at h
  | notGate g => simp [isAndOfInputsOnly] at h
  | orGate gs => simp [isAndOfInputsOnly] at h
  | andGate gs =>
      rw [ufiFormulaDepth_andGate]
      have hzero : (List.foldr max 0) (gs.map ufiFormulaDepth) ≤ 0 := by
        apply foldr_max_map_le
        intro x hx
        simp only [isAndOfInputsOnly, List.all_eq_true] at h
        have hin := h x hx
        cases x with
        | inputGate i b => simp [ufiFormulaDepth]
        | constant b m => simp [isInput] at hin
        | notGate g => simp [isInput] at hin
        | andGate gs => simp [isInput] at hin
        | orGate gs => simp [isInput] at hin
      omega

/-- A proper CNF has depth ≤ 2. -/
lemma isCNF_depth_le (g : UnboundedFanInFormula)
    (h : isCNF g = true) : ufiFormulaDepth g ≤ 2 := by
  cases g with
  | inputGate i b => simp [isCNF] at h
  | constant b m => simp [isCNF] at h
  | notGate g => simp [isCNF] at h
  | orGate gs => simp [isCNF] at h
  | andGate gs =>
      rw [ufiFormulaDepth_andGate]
      have hone : (List.foldr max 0) (gs.map ufiFormulaDepth) ≤ 1 := by
        apply foldr_max_map_le
        intro x hx
        simp only [isCNF, List.all_eq_true] at h
        exact isOrOfInputsOnly_depth_le x (h x hx)
      omega

/-- A proper DNF has depth ≤ 2. -/
lemma isDNF_depth_le (g : UnboundedFanInFormula)
    (h : isDNF g = true) : ufiFormulaDepth g ≤ 2 := by
  cases g with
  | inputGate i b => simp [isDNF] at h
  | constant b m => simp [isDNF] at h
  | notGate g => simp [isDNF] at h
  | andGate gs => simp [isDNF] at h
  | orGate gs =>
      rw [ufiFormulaDepth_orGate]
      have hone : (List.foldr max 0) (gs.map ufiFormulaDepth) ≤ 1 := by
        apply foldr_max_map_le
        intro x hx
        simp only [isDNF, List.all_eq_true] at h
        exact isAndOfInputsOnly_depth_le x (h x hx)
      omega

/-- A proper-leveled formula at level `n ≥ 2` has depth ≤ `n`. -/
lemma proper_leveled_depth_le :
    ∀ (f : UnboundedFanInFormula) (n : Nat), 2 ≤ n → HasProperBottomsAt f n →
      ufiFormulaDepth f ≤ n := by
  intro f
  induction f using UnboundedFanInFormula.induction with
  | input i b => intro n hn _; simp [ufiFormulaDepth]
  | const b m => intro n hn _; simp [ufiFormulaDepth]
  | notg g ih => intro n hn h; simp only [HasProperBottomsAt] at h
  | andg gs ih =>
      intro n hn h
      by_cases hle : n ≤ 2
      · simp only [HasProperBottomsAt, if_pos hle] at h
        obtain ⟨hcnf, _, _⟩ := h
        have hd := isCNF_depth_le (andGate gs) hcnf
        omega
      · simp only [HasProperBottomsAt, if_neg hle] at h
        rw [ufiFormulaDepth_andGate]
        have hb : (List.foldr max 0) (gs.map ufiFormulaDepth) ≤ n - 1 := by
          apply foldr_max_map_le
          intro x hx
          exact ih x hx (n - 1) (by omega) (h x hx)
        omega
  | org gs ih =>
      intro n hn h
      by_cases hle : n ≤ 2
      · simp only [HasProperBottomsAt, if_pos hle] at h
        obtain ⟨hdnf, _, _⟩ := h
        have hd := isDNF_depth_le (orGate gs) hdnf
        omega
      · simp only [HasProperBottomsAt, if_neg hle] at h
        rw [ufiFormulaDepth_orGate]
        have hb : (List.foldr max 0) (gs.map ufiFormulaDepth) ≤ n - 1 := by
          apply foldr_max_map_le
          intro x hx
          exact ih x hx (n - 1) (by omega) (h x hx)
        omega

/- **All skeleton placeholders have polarity `false`**, so the
    skeleton has no negated inputs.  Mirrors `extractBottomLayer_collect_eq`. -/
mutual

theorem extractBottomLayer_top_neg_inputs_nil :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ufiNegInputs (extractBottomLayer lvl start f).2.1 = []
  | _, _, .inputGate _ _ => by
      unfold extractBottomLayer ufiNegInputs; simp
  | _, _, .constant _ _ => by
      unfold extractBottomLayer ufiNegInputs; simp
  | _, _, .notGate _ => by
      unfold extractBottomLayer ufiNegInputs; simp
  | lvl, start, .andGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp [ufiNegInputs]
      · simp only
        unfold ufiNegInputs
        exact extractBottomLayerList_flatMap_neg_inputs_nil (lvl - 1) start gates
  | lvl, start, .orGate gates => by
      unfold extractBottomLayer
      split_ifs with h
      · simp [ufiNegInputs]
      · simp only
        unfold ufiNegInputs
        exact extractBottomLayerList_flatMap_neg_inputs_nil (lvl - 1) start gates

theorem extractBottomLayerList_flatMap_neg_inputs_nil :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      (extractBottomLayerList lvl start gs).2.1.flatMap ufiNegInputs = []
  | _, _, [] => by
      unfold extractBottomLayerList; simp
  | lvl, start, g :: gs => by
      unfold extractBottomLayerList
      simp only [List.flatMap_cons]
      rw [extractBottomLayer_top_neg_inputs_nil lvl start g,
          extractBottomLayerList_flatMap_neg_inputs_nil lvl
            (extractBottomLayer lvl start g).2.2 gs]
      simp

end

/-- **Eval consumer.**  Substituting each placeholder `i` of the
    `extractBottomLayer` skeleton with `sub i`, the flattened result
    evaluated at `ys` agrees with `circuit` evaluated at `xs`, provided
    every extracted bottom `g` (at index `i`) satisfies
    `eval (sub i) ys = eval g xs`. -/
lemma extractBottomLayer_substFlatten_eval
    (sub : Nat → UnboundedFanInFormula) (lvl : Nat)
    (circuit : UnboundedFanInFormula) (ys xs : List Bool)
    (hval : ∀ i g, (extractBottomLayer lvl 0 circuit).1[i]? = some g →
        ufiFormulaEval (sub i) ys = ufiFormulaEval g xs) :
    ufiFormulaEval (substFlatten sub (extractBottomLayer lvl 0 circuit).2.1) ys
      = ufiFormulaEval circuit xs := by
  have hbottom := extractBottomLayer_eval lvl 0 circuit xs [] [] rfl
  simp only [List.nil_append, List.append_nil] at hbottom
  rw [hbottom]
  have hneg : ufiNegInputs (extractBottomLayer lvl 0 circuit).2.1 = [] :=
    extractBottomLayer_top_neg_inputs_nil lvl 0 circuit
  apply substFlatten_eval sub ys
    ((extractBottomLayer lvl 0 circuit).1.map (fun g => ufiFormulaEval g xs))
    (extractBottomLayer lvl 0 circuit).2.1 hneg
  intro i hi
  have hcollect : ufiCollectInputIndices (extractBottomLayer lvl 0 circuit).2.1
      = List.range' 0 (extractBottomLayer lvl 0 circuit).1.length :=
    extractBottomLayer_collect_eq lvl 0 circuit
  rw [hcollect, ← List.range_eq_range'] at hi
  have hi_lt : i < (extractBottomLayer lvl 0 circuit).1.length := List.mem_range.mp hi
  have hsome : (extractBottomLayer lvl 0 circuit).1[i]?
      = some ((extractBottomLayer lvl 0 circuit).1[i]'hi_lt) := by
    exact List.getElem?_eq_getElem hi_lt
  rw [List.getElem?_map, List.getElem?_eq_getElem hi_lt]
  exact congrArg some (hval i _ hsome).symm

end SubstFlatten

end Circuits.HastadParity
