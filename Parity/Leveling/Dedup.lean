import Parity.Leveling.Invariants
import Formulas.UFITransformations

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.Leveling
open Circuits
open UnboundedFanInFormula

private theorem ufi_strong_induction {P : UnboundedFanInFormula → Prop}
    (input : ∀ i b, P (inputGate i b))
    (const : ∀ b m, P (constant b m))
    (notg : ∀ g, P g → P (notGate g))
    (andg : ∀ gs, (∀ g ∈ gs, P g) → P (andGate gs))
    (org : ∀ gs, (∀ g ∈ gs, P g) → P (orGate gs))
    (g : UnboundedFanInFormula) : P g := by
  have key : ∀ n (g : UnboundedFanInFormula), sizeOf g < n → P g := by
    intro n
    induction n with
    | zero => intro g h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro g hg
      cases g with
      | inputGate i b => exact input i b
      | constant b m => exact const b m
      | notGate g0 =>
          apply notg; apply ih
          simp only [UnboundedFanInFormula.notGate.sizeOf_spec] at hg; omega
      | andGate gs =>
          apply andg; intro x hx; apply ih
          have h1 : sizeOf x < sizeOf gs := List.sizeOf_lt_of_mem hx
          simp only [UnboundedFanInFormula.andGate.sizeOf_spec] at hg; omega
      | orGate gs =>
          apply org; intro x hx; apply ih
          have h1 : sizeOf x < sizeOf gs := List.sizeOf_lt_of_mem hx
          simp only [UnboundedFanInFormula.orGate.sizeOf_spec] at hg; omega
  exact key (sizeOf g + 1) g (Nat.lt_succ_self _)

private lemma foldr_max_le_of_all_le {l : List Nat} {b : Nat}
    (h : ∀ i ∈ l, i ≤ b) : (List.foldr max 0) l ≤ b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      exact max_le (h x (by simp)) (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

mutual
/-- Recursively remove duplicate children without collapsing gate constructors. -/
def dedupChildren : UnboundedFanInFormula → UnboundedFanInFormula
  | .inputGate i b => .inputGate i b
  | .constant b m => .constant b m
  | .notGate g => .notGate (dedupChildren g)
  | .andGate gs => .andGate (Formulas.UFITransformations.dedupFormulas (dedupChildrenList gs))
  | .orGate gs => .orGate (Formulas.UFITransformations.dedupFormulas (dedupChildrenList gs))
def dedupChildrenList : List UnboundedFanInFormula → List UnboundedFanInFormula
  | [] => []
  | g :: gs => dedupChildren g :: dedupChildrenList gs
end

theorem dedupChildrenList_eq_map (gs : List UnboundedFanInFormula) :
    dedupChildrenList gs = gs.map dedupChildren := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [dedupChildrenList, ih]

/-- Every unbounded gate has a duplicate-free child list. -/
def LocallyNodup : UnboundedFanInFormula → Prop
  | .inputGate _ _ | .constant _ _ => True
  | .notGate g => LocallyNodup g
  | .andGate gs | .orGate gs => gs.Nodup ∧ ∀ g ∈ gs, LocallyNodup g

mutual
theorem dedupChildren_locallyNodup : ∀ f, LocallyNodup (dedupChildren f)
  | .inputGate _ _ | .constant _ _ => by simp [dedupChildren, LocallyNodup]
  | .notGate g => by
      simp only [dedupChildren, LocallyNodup]
      exact dedupChildren_locallyNodup g
  | .andGate gs => by
      simp only [dedupChildren, LocallyNodup]
      refine ⟨Formulas.UFITransformations.dedupFormulas_nodup _, ?_⟩
      intro g hg
      exact dedupChildrenList_locallyNodup gs g
        ((Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg)
  | .orGate gs => by
      simp only [dedupChildren, LocallyNodup]
      refine ⟨Formulas.UFITransformations.dedupFormulas_nodup _, ?_⟩
      intro g hg
      exact dedupChildrenList_locallyNodup gs g
        ((Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg)
theorem dedupChildrenList_locallyNodup :
    ∀ gs g, g ∈ dedupChildrenList gs → LocallyNodup g
  | [], _, h => by simp [dedupChildrenList] at h
  | g :: gs, x, h => by
      simp only [dedupChildrenList, List.mem_cons] at h
      rcases h with rfl | h
      · exact dedupChildren_locallyNodup g
      · exact dedupChildrenList_locallyNodup gs x h
end

private lemma dedup_all_eq (l : List UnboundedFanInFormula)
    (p : UnboundedFanInFormula → Bool) :
    ((Formulas.UFITransformations.dedupFormulas l).map p).all (fun x => x == true) =
      (l.map p).all (fun x => x == true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro h x hx
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact h (p g) (List.mem_map.mpr
      ⟨g, (Formulas.UFITransformations.mem_dedupFormulas_iff l g).mpr hg, rfl⟩)
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact h (p g) (List.mem_map.mpr
      ⟨g, (Formulas.UFITransformations.mem_dedupFormulas_iff l g).mp hg, rfl⟩)

private lemma dedup_any_eq (l : List UnboundedFanInFormula)
    (p : UnboundedFanInFormula → Bool) :
    ((Formulas.UFITransformations.dedupFormulas l).map p).any (fun x => x == true) =
      (l.map p).any (fun x => x == true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact ⟨p g, List.mem_map.mpr
      ⟨g, (Formulas.UFITransformations.mem_dedupFormulas_iff l g).mp hg, rfl⟩, hp⟩
  · rintro ⟨x, hx, hp⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact ⟨p g, List.mem_map.mpr
      ⟨g, (Formulas.UFITransformations.mem_dedupFormulas_iff l g).mpr hg, rfl⟩, hp⟩

private theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem dedupChildren_eval (f : UnboundedFanInFormula) (xs : List Bool) :
    ufiFormulaEval (dedupChildren f) xs = ufiFormulaEval f xs := by
  induction f using ufi_strong_induction with
  | input i b | const b i => rfl
  | notg g ih => simp only [dedupChildren, ufiFormulaEval]; rw [ih]
  | andg gs ih =>
      simp only [dedupChildren, ufi_eval_andGate_eq_all]
      rw [dedup_all_eq, dedupChildrenList_eq_map, List.map_map]
      have hmap : gs.map ((fun c => ufiFormulaEval c xs) ∘ dedupChildren) =
          gs.map (fun c => ufiFormulaEval c xs) :=
        List.map_congr_left (fun g hg => ih g hg)
      rw [hmap]
  | org gs ih =>
      simp only [dedupChildren, ufi_eval_orGate_eq_any]
      rw [dedup_any_eq, dedupChildrenList_eq_map, List.map_map]
      have hmap : gs.map ((fun c => ufiFormulaEval c xs) ∘ dedupChildren) =
          gs.map (fun c => ufiFormulaEval c xs) :=
        List.map_congr_left (fun g hg => ih g hg)
      rw [hmap]

theorem dedupChildren_circuit_size_le (f : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (dedupChildren f) ≤ ufiFormulaCircuitSize f := by
  induction f using ufi_strong_induction with
  | input i b | const b i => simp [dedupChildren, ufiFormulaCircuitSize]
  | notg g ih =>
      simp only [dedupChildren, ufiFormulaCircuitSize]
      exact Nat.add_le_add_right ih 1
  | andg gs ih | org gs ih =>
      simp only [dedupChildren, ufiFormulaCircuitSize]
      rw [dedupChildrenList_eq_map]
      have hchildren : ((gs.map dedupChildren).map ufiFormulaCircuitSize).sum ≤
          (gs.map ufiFormulaCircuitSize).sum := by
        simpa only [List.map_map] using
          sum_map_le gs (ufiFormulaCircuitSize ∘ dedupChildren)
            ufiFormulaCircuitSize (fun g hg => ih g hg)
      exact Nat.add_le_add_right
        (le_trans (Formulas.UFITransformations.dedupFormulas_sum_map_le _ _) hchildren) 1

theorem dedupChildren_depth_le (f : UnboundedFanInFormula) :
    ufiFormulaDepth (dedupChildren f) ≤ ufiFormulaDepth f := by
  induction f using ufi_strong_induction with
  | input i b | const b i => simp [dedupChildren, ufiFormulaDepth]
  | notg g ih => simp only [dedupChildren, ufiFormulaDepth]; omega
  | andg gs ih | org gs ih =>
      simp only [dedupChildren, ufiFormulaDepth]
      apply Nat.add_le_add_left
      apply foldr_max_le_of_all_le
      intro m hm
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
      rw [dedupChildrenList_eq_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
      exact le_trans (ih g0 hg0)
        (mem_le_foldr_max (List.mem_map.mpr ⟨g0, hg0, rfl⟩))

theorem dedupChildren_inputs_subset (f : UnboundedFanInFormula) :
    ∀ i, i ∈ ufiCollectInputIndices (dedupChildren f) →
      i ∈ ufiCollectInputIndices f := by
  induction f using ufi_strong_induction with
  | input j b => simp [dedupChildren, ufiCollectInputIndices]
  | const b m => simp [dedupChildren, ufiCollectInputIndices]
  | notg g ih => simp only [dedupChildren, ufiCollectInputIndices]; exact ih
  | andg gs ih | org gs ih =>
      intro i hi
      simp only [dedupChildren, ufiCollectInputIndices] at hi ⊢
      obtain ⟨g, hg, hig⟩ := List.mem_flatMap.mp hi
      have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
      rw [dedupChildrenList_eq_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
      exact List.mem_flatMap.mpr ⟨g0, hg0, ih g0 hg0 i hig⟩

theorem dedupChildren_largest_input_lt {f : UnboundedFanInFormula} {n : Nat}
    (h : ufiLargestInput f < n) : ufiLargestInput (dedupChildren f) < n := by
  unfold ufiLargestInput at h ⊢
  have hle := foldr_max_le_of_all_le
    (l := ufiCollectInputIndices (dedupChildren f))
    (b := List.foldr max 0 (ufiCollectInputIndices f))
    (fun i hi => mem_le_foldr_max (dedupChildren_inputs_subset f i hi))
  omega

theorem dedupChildren_hasNoNotGates : ∀ f, HasNoNotGates f → HasNoNotGates (dedupChildren f)
  | .inputGate _ _, _ | .constant _ _, _ => by simp [dedupChildren, HasNoNotGates]
  | .notGate _, h => by simp only [HasNoNotGates] at h
  | .andGate gs, h | .orGate gs, h => by
      simp only [HasNoNotGates] at h
      simp only [dedupChildren, HasNoNotGates]
      intro g hg
      have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
      rw [dedupChildrenList_eq_map] at hg'
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
      exact dedupChildren_hasNoNotGates g0 (h g0 hg0)

private lemma dedupChildren_isAndOr_iff (f : UnboundedFanInFormula) :
    IsAndOr (dedupChildren f) ↔ IsAndOr f := by cases f <;> simp [dedupChildren, IsAndOr]

private lemma dedupChildren_ne_andGate {f : UnboundedFanInFormula}
    (h : ∀ inner, f ≠ .andGate inner) : ∀ inner, dedupChildren f ≠ .andGate inner := by
  cases f <;> simp_all [dedupChildren]

private lemma dedupChildren_ne_orGate {f : UnboundedFanInFormula}
    (h : ∀ inner, f ≠ .orGate inner) : ∀ inner, dedupChildren f ≠ .orGate inner := by
  cases f <;> simp_all [dedupChildren]

theorem dedupChildren_alternating : ∀ f lvl,
    IsAlternatingAndLeveledAt f lvl →
      IsAlternatingAndLeveledAt (dedupChildren f) lvl
  | .inputGate _ _, _, _ | .constant _ _, _, _ => by
      simp only [dedupChildren, IsAlternatingAndLeveledAt]
  | .notGate _, _, h => by simp only [IsAlternatingAndLeveledAt] at h
  | .andGate gs, lvl, h => by
      simp only [dedupChildren, IsAlternatingAndLeveledAt] at h ⊢
      obtain ⟨hshape, hlevel, hrec⟩ := h
      refine ⟨?_, ?_, ?_⟩ <;> intro g hg
      · have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
        rw [dedupChildrenList_eq_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        exact dedupChildren_ne_andGate (hshape g0 hg0)
      · intro h_ao
        have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
        rw [dedupChildrenList_eq_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        exact hlevel g0 hg0 (dedupChildren_isAndOr_iff g0 |>.mp h_ao)
      · have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
        rw [dedupChildrenList_eq_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        exact dedupChildren_alternating g0 (lvl - 1) (hrec g0 hg0)
  | .orGate gs, lvl, h => by
      simp only [dedupChildren, IsAlternatingAndLeveledAt] at h ⊢
      obtain ⟨hshape, hlevel, hrec⟩ := h
      refine ⟨?_, ?_, ?_⟩ <;> intro g hg
      · have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
        rw [dedupChildrenList_eq_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        exact dedupChildren_ne_orGate (hshape g0 hg0)
      · intro h_ao
        have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
        rw [dedupChildrenList_eq_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        exact hlevel g0 hg0 (dedupChildren_isAndOr_iff g0 |>.mp h_ao)
      · have hg' := (Formulas.UFITransformations.mem_dedupFormulas_iff _ _).mp hg
        rw [dedupChildrenList_eq_map] at hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        exact dedupChildren_alternating g0 (lvl - 1) (hrec g0 hg0)

private def inputCode : UnboundedFanInFormula → Option Nat
  | .inputGate i b => some (2 * i + b.toNat)
  | _ => none

private def inputWeight : UnboundedFanInFormula → Nat
  | .inputGate _ _ => 1
  | _ => 0

private lemma inputCode_injective {a a' : UnboundedFanInFormula} {z : Nat}
    (ha : z ∈ inputCode a) (ha' : z ∈ inputCode a') : a = a' := by
  cases a with
  | inputGate i b =>
      cases a' with
      | inputGate i' b' =>
          change some (2 * i + b.toNat) = some z at ha
          change some (2 * i' + b'.toNat) = some z at ha'
          injection ha with hi
          injection ha' with hi'
          have hcode : 2 * i + b.toNat = 2 * i' + b'.toNat := hi.trans hi'.symm
          have hparts : i = i' ∧ b = b' := by
            cases b <;> cases b' <;> simp_all [Bool.toNat] <;> omega
          rw [hparts.1, hparts.2]
      | constant _ _ | notGate _ | andGate _ | orGate _ =>
          change (none : Option Nat) = some z at ha'
          contradiction
  | constant _ _ | notGate _ | andGate _ | orGate _ =>
      change (none : Option Nat) = some z at ha
      contradiction

private lemma inputWeight_sum_eq_filterMap_length (l : List UnboundedFanInFormula) :
    (l.map inputWeight).sum = (l.filterMap inputCode).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases a with
      | inputGate i b =>
          simp only [List.map_cons, inputWeight, List.sum_cons, List.filterMap_cons,
            inputCode, List.length_cons]
          omega
      | constant b n | notGate b | andGate b | orGate b =>
          simpa only [List.map_cons, inputWeight, List.sum_cons, List.filterMap_cons,
            inputCode, Nat.zero_add] using ih

private lemma nodup_input_count_le (n : Nat) (l : List UnboundedFanInFormula)
    (hnd : l.Nodup)
    (hin : ∀ i, i ∈ l.flatMap ufiCollectInputIndices → i < n) :
    (l.map inputWeight).sum ≤ 2 * n := by
  rw [inputWeight_sum_eq_filterMap_length]
  have hcodes : (l.filterMap inputCode).Nodup :=
    hnd.filterMap (fun a a' z ha ha' => inputCode_injective ha ha')
  have hsubset : (l.filterMap inputCode).toFinset ⊆ Finset.range (2 * n) := by
    intro z hz
    obtain ⟨g, hg, hcode⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hz)
    cases g with
    | inputGate i b =>
        simp only [inputCode] at hcode
        injection hcode with hzcode
        subst z
        have hi : i < n := hin i (List.mem_flatMap.mpr
          ⟨.inputGate i b, hg, by simp [ufiCollectInputIndices]⟩)
        simp only [Finset.mem_range]
        cases b <;> simp [Bool.toNat] <;> omega
    | constant _ _ | notGate _ | andGate _ | orGate _ => simp [inputCode] at hcode
  have hc := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hcodes, Finset.card_range] at hc
  exact hc

private lemma sum_scaled_add_weight (scale : Nat) (l : List UnboundedFanInFormula) :
    (l.map (fun g => scale * ufiFormulaCircuitSize g + inputWeight g)).sum =
      scale * (l.map ufiFormulaCircuitSize).sum + (l.map inputWeight).sum := by
  induction l with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]; omega

private theorem locallyNodup_input_occurrences_le_aux (n : Nat) (hn : 0 < n) :
    ∀ f, LocallyNodup f →
      (∀ i, i ∈ ufiCollectInputIndices f → i < n) →
      (ufiCollectInputIndices f).length ≤
        2 * n * ufiFormulaCircuitSize f + inputWeight f := by
  intro f hlocal hin
  induction f using ufi_strong_induction with
  | input i b => simp [ufiCollectInputIndices, ufiFormulaCircuitSize, inputWeight]
  | const b m => simp [ufiCollectInputIndices, ufiFormulaCircuitSize, inputWeight]
  | notg g ih =>
      simp only [LocallyNodup] at hlocal
      have hchild := ih hlocal (fun i hi => hin i
        (by simpa [ufiCollectInputIndices] using hi))
      have hwg : inputWeight g ≤ 1 := by cases g <;> simp [inputWeight]
      simp only [ufiCollectInputIndices, ufiFormulaCircuitSize, inputWeight]
      rw [Nat.mul_add]
      omega
  | andg gs ih | org gs ih =>
      simp only [LocallyNodup] at hlocal
      obtain ⟨hnd, hchildren⟩ := hlocal
      have hpoint : ∀ g ∈ gs, (ufiCollectInputIndices g).length ≤
          2 * n * ufiFormulaCircuitSize g + inputWeight g := by
        intro g hg
        exact ih g hg (hchildren g hg) (fun i hi => hin i
          (by simp only [ufiCollectInputIndices]; exact List.mem_flatMap.mpr ⟨g, hg, hi⟩))
      have hsum := sum_map_le gs (fun g => (ufiCollectInputIndices g).length)
        (fun g => 2 * n * ufiFormulaCircuitSize g + inputWeight g) hpoint
      have hw := nodup_input_count_le n gs hnd (by
        intro i hi
        exact hin i (by simpa [ufiCollectInputIndices] using hi))
      rw [sum_scaled_add_weight] at hsum
      simp only [ufiCollectInputIndices, List.length_flatMap, ufiFormulaCircuitSize,
        inputWeight]
      rw [Nat.mul_add]
      omega

/-- A locally deduplicated `n`-input formula has only linearly many input
    occurrences per circuit gate.  This is the circuit-size bridge used by
    normalization; it avoids exposing a formula-node metric. -/
theorem locallyNodup_input_occurrences_le (n : Nat) (hn : 0 < n)
    (f : UnboundedFanInFormula) (hlocal : LocallyNodup f)
    (hin : ∀ i, i ∈ ufiCollectInputIndices f → i < n) :
    (ufiCollectInputIndices f).length ≤
      2 * n * ufiFormulaCircuitSize f + 1 := by
  have h := locallyNodup_input_occurrences_le_aux n hn f hlocal hin
  have hw : inputWeight f ≤ 1 := by cases f <;> simp [inputWeight]
  omega

end Circuits.Leveling
