import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import Formulas.ConversionDepth
import Formulas.NotGateFree

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Formulas.UFITransformations
open Circuits
open Circuits.UnboundedFanInFormula
open Circuits.Leveling

/-!
# Unbounded-fan-in formula transformations

Formula-only helpers for contracting adjacent same-type gates and
deduplicating formula lists.
-/

/-- Children-extractor for `andGate`: if `g` is `andGate gs`, return
    its children `gs`; otherwise return the singleton `[g]`.  Used to
    absorb nested `andGate`s during contraction. -/
def asAndChildren : UnboundedFanInFormula → List UnboundedFanInFormula
  | andGate gs => gs
  | g          => [g]

/-- Children-extractor for `orGate`: dual of `asAndChildren`. -/
def asOrChildren : UnboundedFanInFormula → List UnboundedFanInFormula
  | orGate gs => gs
  | g         => [g]

/- Recursively contract nested same-type gates.  Mutual with `flattenList`
    so children are contracted first; each `andGate` then absorbs any
    immediate `andGate` children of its (already-contracted) children
    via `List.flatMap asAndChildren`, and dually for `orGate`. -/
mutual
def flatten : UnboundedFanInFormula → UnboundedFanInFormula
  | inputGate i n      => inputGate i n
  | constant v lbl => constant v lbl
  | notGate g      => notGate (flatten g)
  | andGate gs     => andGate ((flattenList gs).flatMap asAndChildren)
  | orGate gs      => orGate ((flattenList gs).flatMap asOrChildren)

def flattenList :
    List UnboundedFanInFormula → List UnboundedFanInFormula
  | []      => []
  | g :: gs => flatten g :: flattenList gs
end

/-! #### Evaluation correctness for `flatten` ───────────────────────── -/

/-- Boolean identity: `(if b then true else false) == true` is `b`. -/
private lemma cond_bit_one_eq_one (b : Bool) :
    ((if b then true else false) == true) = b := by
  cases b <;> decide

/-- `((asAndChildren g).map eval).all (· == one)` equals `eval g == one`.
    When `g = andGate gs`, the children unfold directly; otherwise the
    singleton list contributes the single equality `eval g == one`. -/
private lemma asAndChildren_all_eq
    (g : UnboundedFanInFormula) (inputs : List Bool) :
    ((asAndChildren g).map fun c => ufiFormulaEval c inputs).all (· == true) =
    (ufiFormulaEval g inputs == true) := by
  cases g with
  | inputGate i n =>
    change (([inputGate i n].map fun c => ufiFormulaEval c inputs).all (· == true)) =
         (ufiFormulaEval (inputGate i n) inputs == true)
    simp [List.all_cons, List.all_nil]
  | constant v lbl =>
    change (([constant v lbl].map fun c => ufiFormulaEval c inputs).all (· == true)) =
         (ufiFormulaEval (constant v lbl) inputs == true)
    simp [List.all_cons, List.all_nil]
  | notGate g' =>
    change (([notGate g'].map fun c => ufiFormulaEval c inputs).all (· == true)) =
         (ufiFormulaEval (notGate g') inputs == true)
    simp [List.all_cons, List.all_nil]
  | andGate gs =>
    change ((gs.map fun c => ufiFormulaEval c inputs).all (· == true)) =
         (ufiFormulaEval (andGate gs) inputs == true)
    rw [ufi_eval_andGate_eq_all, cond_bit_one_eq_one]
  | orGate gs =>
    change (([orGate gs].map fun c => ufiFormulaEval c inputs).all (· == true)) =
         (ufiFormulaEval (orGate gs) inputs == true)
    simp [List.all_cons, List.all_nil]

/-- Dual: `((asOrChildren g).map eval).any (· == one) = eval g == one`. -/
private lemma asOrChildren_any_eq
    (g : UnboundedFanInFormula) (inputs : List Bool) :
    ((asOrChildren g).map fun c => ufiFormulaEval c inputs).any (· == true) =
    (ufiFormulaEval g inputs == true) := by
  cases g with
  | inputGate i n =>
    change (([inputGate i n].map fun c => ufiFormulaEval c inputs).any (· == true)) =
         (ufiFormulaEval (inputGate i n) inputs == true)
    simp [List.any_cons, List.any_nil]
  | constant v lbl =>
    change (([constant v lbl].map fun c => ufiFormulaEval c inputs).any (· == true)) =
         (ufiFormulaEval (constant v lbl) inputs == true)
    simp [List.any_cons, List.any_nil]
  | notGate g' =>
    change (([notGate g'].map fun c => ufiFormulaEval c inputs).any (· == true)) =
         (ufiFormulaEval (notGate g') inputs == true)
    simp [List.any_cons, List.any_nil]
  | andGate gs =>
    change (([andGate gs].map fun c => ufiFormulaEval c inputs).any (· == true)) =
         (ufiFormulaEval (andGate gs) inputs == true)
    simp [List.any_cons, List.any_nil]
  | orGate gs =>
    change ((gs.map fun c => ufiFormulaEval c inputs).any (· == true)) =
         (ufiFormulaEval (orGate gs) inputs == true)
    rw [ufi_eval_orGate_eq_any, cond_bit_one_eq_one]

/-- Boolean-level identity: the `.all` value over the flattened absorbed
    list of `andGate` children equals the `.all` value over the original. -/
private lemma flatMap_asAndChildren_all
    (xs : List UnboundedFanInFormula) (inputs : List Bool) :
    ((xs.flatMap asAndChildren).map fun c => ufiFormulaEval c inputs).all (· == true) =
    (xs.map fun c => ufiFormulaEval c inputs).all (· == true) := by
  induction xs with
  | nil => simp [List.flatMap]
  | cons x xs ih =>
    have hsplit : (x :: xs).flatMap asAndChildren =
                  asAndChildren x ++ xs.flatMap asAndChildren := by
      simp [List.flatMap]
    rw [hsplit]
    rw [List.map_append, List.all_append]
    rw [List.map_cons, List.all_cons]
    rw [asAndChildren_all_eq, ih]

/-- Dual: `.any` view over `orGate` absorption. -/
private lemma flatMap_asOrChildren_any
    (xs : List UnboundedFanInFormula) (inputs : List Bool) :
    ((xs.flatMap asOrChildren).map fun c => ufiFormulaEval c inputs).any (· == true) =
    (xs.map fun c => ufiFormulaEval c inputs).any (· == true) := by
  induction xs with
  | nil => simp [List.flatMap]
  | cons x xs ih =>
    have hsplit : (x :: xs).flatMap asOrChildren =
                  asOrChildren x ++ xs.flatMap asOrChildren := by
      simp [List.flatMap]
    rw [hsplit]
    rw [List.map_append, List.any_append]
    rw [List.map_cons, List.any_cons]
    rw [asOrChildren_any_eq, ih]

/-- Folding the `asAndChildren`-absorption across a list preserves
    `andGate` evaluation. -/
private lemma andGate_eval_flatMap_asAndChildren
    (xs : List UnboundedFanInFormula) (inputs : List Bool) :
    ufiFormulaEval (andGate (xs.flatMap asAndChildren)) inputs =
    ufiFormulaEval (andGate xs) inputs := by
  rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all,
      flatMap_asAndChildren_all]

/-- Dual: folding `asOrChildren`-absorption preserves `orGate` evaluation. -/
private lemma orGate_eval_flatMap_asOrChildren
    (xs : List UnboundedFanInFormula) (inputs : List Bool) :
    ufiFormulaEval (orGate (xs.flatMap asOrChildren)) inputs =
    ufiFormulaEval (orGate xs) inputs := by
  rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any,
      flatMap_asOrChildren_any]

/- Evaluating `flatten g` agrees with evaluating `g`.  Mutual with
    `flattenList_eval`. -/
mutual
theorem flatten_eval (g : UnboundedFanInFormula) (inputs : List Bool) :
    ufiFormulaEval (flatten g) inputs = ufiFormulaEval g inputs := by
  cases g with
  | inputGate i n =>
    change ufiFormulaEval (inputGate i n) inputs = _; rfl
  | constant v lbl =>
    change ufiFormulaEval (constant v lbl) inputs = _; rfl
  | notGate g' =>
    change ufiFormulaEval (notGate (flatten g')) inputs = _
    have ih := flatten_eval g' inputs
    simp only [ufiFormulaEval]; rw [ih]
  | andGate gs =>
    change ufiFormulaEval (andGate ((flattenList gs).flatMap asAndChildren)) inputs =
         ufiFormulaEval (andGate gs) inputs
    rw [andGate_eval_flatMap_asAndChildren]
    rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all]
    have h_l := flattenList_eval gs inputs
    rw [h_l]
  | orGate gs =>
    change ufiFormulaEval (orGate ((flattenList gs).flatMap asOrChildren)) inputs =
         ufiFormulaEval (orGate gs) inputs
    rw [orGate_eval_flatMap_asOrChildren]
    rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any]
    have h_l := flattenList_eval gs inputs
    rw [h_l]
termination_by sizeOf g

theorem flattenList_eval (gs : List UnboundedFanInFormula)
    (inputs : List Bool) :
    (flattenList gs).map (fun c => ufiFormulaEval c inputs) =
    gs.map (fun c => ufiFormulaEval c inputs) := by
  match gs with
  | [] => simp [flattenList]
  | g :: rest =>
    simp only [flattenList, List.map_cons]
    rw [flatten_eval g inputs, flattenList_eval rest inputs]
termination_by sizeOf gs
end

/-! ### `flatten` produces an AND/OR-leveled formula -/

private theorem hasAlternatingAndOrGates_of_mem_asAndChildren
    (g x : UnboundedFanInFormula) (hg : g.HasAlternatingAndOrGates)
    (hx : x ∈ asAndChildren g) : x.HasAlternatingAndOrGates := by
  cases g with
  | inputGate i n =>
      simp only [asAndChildren, List.mem_singleton] at hx
      subst x
      exact hg
  | constant v lbl =>
      simp only [asAndChildren, List.mem_singleton] at hx
      subst x
      exact hg
  | notGate g =>
      simp only [HasAlternatingAndOrGates] at hg
  | andGate gs =>
      simp only [asAndChildren] at hx
      simp only [HasAlternatingAndOrGates] at hg
      exact hg.1 x hx
  | orGate gs =>
      simp only [asAndChildren, List.mem_singleton] at hx
      subst x
      exact hg

private theorem ne_andGate_of_mem_asAndChildren
    (g x : UnboundedFanInFormula) (hg : g.HasAlternatingAndOrGates)
    (hx : x ∈ asAndChildren g) : ∀ inner, x ≠ andGate inner := by
  cases g with
  | inputGate i n =>
      simp only [asAndChildren, List.mem_singleton] at hx
      subst x
      intro inner h
      exact UnboundedFanInFormula.noConfusion h
  | constant v lbl =>
      simp only [asAndChildren, List.mem_singleton] at hx
      subst x
      intro inner h
      exact UnboundedFanInFormula.noConfusion h
  | notGate g =>
      simp only [HasAlternatingAndOrGates] at hg
  | andGate gs =>
      simp only [asAndChildren] at hx
      simp only [HasAlternatingAndOrGates] at hg
      exact hg.2 x hx
  | orGate gs =>
      simp only [asAndChildren, List.mem_singleton] at hx
      subst x
      intro inner h
      exact UnboundedFanInFormula.noConfusion h

private theorem hasAlternatingAndOrGates_of_mem_asOrChildren
    (g x : UnboundedFanInFormula) (hg : g.HasAlternatingAndOrGates)
    (hx : x ∈ asOrChildren g) : x.HasAlternatingAndOrGates := by
  cases g with
  | inputGate i n =>
      simp only [asOrChildren, List.mem_singleton] at hx
      subst x
      exact hg
  | constant v lbl =>
      simp only [asOrChildren, List.mem_singleton] at hx
      subst x
      exact hg
  | notGate g =>
      simp only [HasAlternatingAndOrGates] at hg
  | andGate gs =>
      simp only [asOrChildren, List.mem_singleton] at hx
      subst x
      exact hg
  | orGate gs =>
      simp only [asOrChildren] at hx
      simp only [HasAlternatingAndOrGates] at hg
      exact hg.1 x hx

private theorem ne_orGate_of_mem_asOrChildren
    (g x : UnboundedFanInFormula) (hg : g.HasAlternatingAndOrGates)
    (hx : x ∈ asOrChildren g) : ∀ inner, x ≠ orGate inner := by
  cases g with
  | inputGate i n =>
      simp only [asOrChildren, List.mem_singleton] at hx
      subst x
      intro inner h
      exact UnboundedFanInFormula.noConfusion h
  | constant v lbl =>
      simp only [asOrChildren, List.mem_singleton] at hx
      subst x
      intro inner h
      exact UnboundedFanInFormula.noConfusion h
  | notGate g =>
      simp only [HasAlternatingAndOrGates] at hg
  | andGate gs =>
      simp only [asOrChildren, List.mem_singleton] at hx
      subst x
      intro inner h
      exact UnboundedFanInFormula.noConfusion h
  | orGate gs =>
      simp only [asOrChildren] at hx
      simp only [HasAlternatingAndOrGates] at hg
      exact hg.2 x hx

mutual
/-- Contracting adjacent gates of the same kind makes every `notGate`-free
    formula structurally AND/OR-leveled.  Empty gates need no special case:
    `HasAlternatingAndOrGates` constrains children only when they exist. -/
theorem flatten_hasAlternatingAndOrGates (g : UnboundedFanInFormula)
    (h_nn : HasNoNotGates g) : (flatten g).HasAlternatingAndOrGates := by
  cases g with
  | inputGate i n =>
      change HasAlternatingAndOrGates (inputGate i n)
      simp only [HasAlternatingAndOrGates]
  | constant v lbl =>
      change HasAlternatingAndOrGates (constant v lbl)
      simp only [HasAlternatingAndOrGates]
  | notGate g =>
      simp only [HasNoNotGates] at h_nn
  | andGate gs =>
      change HasAlternatingAndOrGates
        (andGate ((flattenList gs).flatMap asAndChildren))
      simp only [HasAlternatingAndOrGates]
      simp only [HasNoNotGates] at h_nn
      have hflat : ∀ y ∈ flattenList gs, y.HasAlternatingAndOrGates :=
        flattenList_hasAlternatingAndOrGates gs h_nn
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_flatMap.mp hx with ⟨y, hy, hxy⟩
        exact hasAlternatingAndOrGates_of_mem_asAndChildren y x (hflat y hy) hxy
      · intro x hx inner
        rcases List.mem_flatMap.mp hx with ⟨y, hy, hxy⟩
        exact ne_andGate_of_mem_asAndChildren y x (hflat y hy) hxy inner
  | orGate gs =>
      change HasAlternatingAndOrGates
        (orGate ((flattenList gs).flatMap asOrChildren))
      simp only [HasAlternatingAndOrGates]
      simp only [HasNoNotGates] at h_nn
      have hflat : ∀ y ∈ flattenList gs, y.HasAlternatingAndOrGates :=
        flattenList_hasAlternatingAndOrGates gs h_nn
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_flatMap.mp hx with ⟨y, hy, hxy⟩
        exact hasAlternatingAndOrGates_of_mem_asOrChildren y x (hflat y hy) hxy
      · intro x hx inner
        rcases List.mem_flatMap.mp hx with ⟨y, hy, hxy⟩
        exact ne_orGate_of_mem_asOrChildren y x (hflat y hy) hxy inner
termination_by sizeOf g

theorem flattenList_hasAlternatingAndOrGates (gs : List UnboundedFanInFormula)
    (h_nn : ∀ g ∈ gs, HasNoNotGates g) :
    ∀ y ∈ flattenList gs, y.HasAlternatingAndOrGates := by
  match gs with
  | [] => intro y hy; simp [flattenList] at hy
  | g :: rest =>
      intro y hy
      simp only [flattenList, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact flatten_hasAlternatingAndOrGates g (h_nn g List.mem_cons_self)
      · exact flattenList_hasAlternatingAndOrGates rest
          (fun z hz => h_nn z (List.mem_cons_of_mem _ hz)) y hy
termination_by sizeOf gs
end

/-- For each y in `flattenList gs` there is some `z ∈ gs` with `flatten z = y`. -/
private theorem flattenList_mem_iff
    (gs : List UnboundedFanInFormula) (y : UnboundedFanInFormula)
    (hy : y ∈ flattenList gs) : ∃ z ∈ gs, flatten z = y := by
  match gs with
  | [] => simp [flattenList] at hy
  | g :: rest =>
      simp only [flattenList, List.mem_cons] at hy
      rcases hy with rfl | hy_rest
      · exact ⟨g, List.mem_cons_self, rfl⟩
      · obtain ⟨z, hz_mem, hz_eq⟩ := flattenList_mem_iff rest y hy_rest
        exact ⟨z, List.mem_cons_of_mem _ hz_mem, hz_eq⟩

/-! ### `flatten` does not increase UFI formula depth ──────────────────── -/

/-- For each y in the flattened list, `depth y ≤ depth z` for some `z` in the
    original list. This is the key combinatorial step: each child of an
    `asAndChildren`/`asOrChildren` extraction has depth bounded by its parent
    (which itself came from `flatten z` for some `z ∈ gs`). -/
private lemma asAndChildren_depth_le (y : UnboundedFanInFormula) :
    ∀ x ∈ asAndChildren y, ufiFormulaDepth x ≤ ufiFormulaDepth y := by
  intro x hx
  cases y with
  | inputGate _ _      => simp [asAndChildren] at hx; subst hx; exact le_rfl
  | constant _ _   => simp [asAndChildren] at hx; subst hx; exact le_rfl
  | notGate _      => simp [asAndChildren] at hx; subst hx; exact le_rfl
  | andGate gs     =>
      simp only [asAndChildren] at hx
      simp only [ufiFormulaDepth]
      have := mem_le_foldr_max_map (f := ufiFormulaDepth) hx
      omega
  | orGate _       => simp [asAndChildren] at hx; subst hx; exact le_rfl

private lemma asOrChildren_depth_le (y : UnboundedFanInFormula) :
    ∀ x ∈ asOrChildren y, ufiFormulaDepth x ≤ ufiFormulaDepth y := by
  intro x hx
  cases y with
  | inputGate _ _      => simp [asOrChildren] at hx; subst hx; exact le_rfl
  | constant _ _   => simp [asOrChildren] at hx; subst hx; exact le_rfl
  | notGate _      => simp [asOrChildren] at hx; subst hx; exact le_rfl
  | andGate _      => simp [asOrChildren] at hx; subst hx; exact le_rfl
  | orGate gs      =>
      simp only [asOrChildren] at hx
      simp only [ufiFormulaDepth]
      have := mem_le_foldr_max_map (f := ufiFormulaDepth) hx
      omega

theorem flatten_depth_le (g : UnboundedFanInFormula) :
    ufiFormulaDepth (flatten g) ≤ ufiFormulaDepth g := by
  cases g with
  | inputGate i n      => exact le_rfl
  | constant v lbl => exact le_rfl
  | notGate g'     =>
      change ufiFormulaDepth (notGate (flatten g')) ≤ ufiFormulaDepth (notGate g')
      have ih : ufiFormulaDepth (flatten g') ≤ ufiFormulaDepth g' :=
        flatten_depth_le g'
      simp only [ufiFormulaDepth]; omega
  | andGate gs =>
      change ufiFormulaDepth (andGate ((flattenList gs).flatMap asAndChildren))
              ≤ ufiFormulaDepth (andGate gs)
      simp only [ufiFormulaDepth]
      -- Need: 1 + (List.foldr max 0) (L.map depth) ≤ 1 + (List.foldr max 0) (gs.map depth)
      -- where L = (flattenList gs).flatMap asAndChildren
      suffices h :
          (List.foldr max 0) (((flattenList gs).flatMap asAndChildren).map ufiFormulaDepth) ≤
            (List.foldr max 0) (gs.map ufiFormulaDepth) by omega
      apply foldr_max_map_le
      intro x hx
      rcases List.mem_flatMap.mp hx with ⟨y, hy_mem, hx_mem⟩
      -- y ∈ flattenList gs ⇒ y = flatten z for some z ∈ gs.
      obtain ⟨z, hz_mem, hz_eq⟩ := flattenList_mem_iff gs y hy_mem
      have h_xy : ufiFormulaDepth x ≤ ufiFormulaDepth y :=
        asAndChildren_depth_le y x hx_mem
      have h_yz : ufiFormulaDepth y ≤ ufiFormulaDepth z := by
        rw [← hz_eq]
        have hsz : sizeOf z < sizeOf (andGate gs) := by
          have h1 : sizeOf z < sizeOf gs := List.sizeOf_lt_of_mem hz_mem
          have h2 : sizeOf (andGate gs) = 1 + sizeOf gs := by simp
          omega
        exact flatten_depth_le z
      have h_z_max : ufiFormulaDepth z ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
        mem_le_foldr_max_map hz_mem
      omega
  | orGate gs =>
      change ufiFormulaDepth (orGate ((flattenList gs).flatMap asOrChildren))
              ≤ ufiFormulaDepth (orGate gs)
      simp only [ufiFormulaDepth]
      suffices h :
          (List.foldr max 0) (((flattenList gs).flatMap asOrChildren).map ufiFormulaDepth) ≤
            (List.foldr max 0) (gs.map ufiFormulaDepth) by omega
      apply foldr_max_map_le
      intro x hx
      rcases List.mem_flatMap.mp hx with ⟨y, hy_mem, hx_mem⟩
      obtain ⟨z, hz_mem, hz_eq⟩ := flattenList_mem_iff gs y hy_mem
      have h_xy : ufiFormulaDepth x ≤ ufiFormulaDepth y :=
        asOrChildren_depth_le y x hx_mem
      have h_yz : ufiFormulaDepth y ≤ ufiFormulaDepth z := by
        rw [← hz_eq]
        have hsz : sizeOf z < sizeOf (orGate gs) := by
          have h1 : sizeOf z < sizeOf gs := List.sizeOf_lt_of_mem hz_mem
          have h2 : sizeOf (orGate gs) = 1 + sizeOf gs := by simp
          omega
        exact flatten_depth_le z
      have h_z_max : ufiFormulaDepth z ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
        mem_le_foldr_max_map hz_mem
      omega
termination_by sizeOf g

/-! ### `flatten` does not increase circuit size ──────────────────────── -/

private lemma asAndChildren_size_le (y : UnboundedFanInFormula) :
    ((asAndChildren y).map ufiFormulaCircuitSize).sum ≤ ufiFormulaCircuitSize y := by
  cases y with
  | inputGate _ _      => simp [asAndChildren, ufiFormulaCircuitSize]
  | constant _ _   => simp [asAndChildren, ufiFormulaCircuitSize]
  | notGate _      => simp [asAndChildren, ufiFormulaCircuitSize]
  | andGate gs     => simp only [asAndChildren, ufiFormulaCircuitSize]; omega
  | orGate _       => simp [asAndChildren, ufiFormulaCircuitSize]

private lemma asOrChildren_size_le (y : UnboundedFanInFormula) :
    ((asOrChildren y).map ufiFormulaCircuitSize).sum ≤ ufiFormulaCircuitSize y := by
  cases y with
  | inputGate _ _      => simp [asOrChildren, ufiFormulaCircuitSize]
  | constant _ _   => simp [asOrChildren, ufiFormulaCircuitSize]
  | notGate _      => simp [asOrChildren, ufiFormulaCircuitSize]
  | andGate _      => simp [asOrChildren, ufiFormulaCircuitSize]
  | orGate gs      => simp only [asOrChildren, ufiFormulaCircuitSize]; omega

private lemma flatMap_asAndChildren_size_le (xs : List UnboundedFanInFormula) :
    ((xs.flatMap asAndChildren).map ufiFormulaCircuitSize).sum ≤
      (xs.map ufiFormulaCircuitSize).sum := by
  induction xs with
  | nil => simp [List.flatMap]
  | cons x rest ih =>
      have hsplit : (x :: rest).flatMap asAndChildren =
                    asAndChildren x ++ rest.flatMap asAndChildren := by
        simp [List.flatMap]
      rw [hsplit, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      have h1 := asAndChildren_size_le x
      omega

private lemma flatMap_asOrChildren_size_le (xs : List UnboundedFanInFormula) :
    ((xs.flatMap asOrChildren).map ufiFormulaCircuitSize).sum ≤
      (xs.map ufiFormulaCircuitSize).sum := by
  induction xs with
  | nil => simp [List.flatMap]
  | cons x rest ih =>
      have hsplit : (x :: rest).flatMap asOrChildren =
                    asOrChildren x ++ rest.flatMap asOrChildren := by
        simp [List.flatMap]
      rw [hsplit, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      have h1 := asOrChildren_size_le x
      omega

mutual
theorem flatten_size_le (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (flatten g) ≤ ufiFormulaCircuitSize g := by
  cases g with
  | inputGate i n      => simp [flatten, ufiFormulaCircuitSize]
  | constant v lbl => simp [flatten, ufiFormulaCircuitSize]
  | notGate g'     =>
      change ufiFormulaCircuitSize (notGate (flatten g')) ≤
            ufiFormulaCircuitSize (notGate g')
      have := flatten_size_le g'
      simp only [ufiFormulaCircuitSize]; omega
  | andGate gs     =>
      change ufiFormulaCircuitSize (andGate ((flattenList gs).flatMap asAndChildren)) ≤
            ufiFormulaCircuitSize (andGate gs)
      simp only [ufiFormulaCircuitSize]
      have h1 := flatMap_asAndChildren_size_le (flattenList gs)
      have h2 := flattenList_size_le gs
      omega
  | orGate gs      =>
      change ufiFormulaCircuitSize (orGate ((flattenList gs).flatMap asOrChildren)) ≤
            ufiFormulaCircuitSize (orGate gs)
      simp only [ufiFormulaCircuitSize]
      have h1 := flatMap_asOrChildren_size_le (flattenList gs)
      have h2 := flattenList_size_le gs
      omega
termination_by sizeOf g

theorem flattenList_size_le (gs : List UnboundedFanInFormula) :
    ((flattenList gs).map ufiFormulaCircuitSize).sum ≤
      (gs.map ufiFormulaCircuitSize).sum := by
  match gs with
  | [] => simp [flattenList]
  | g :: rest =>
      simp only [flattenList, List.map_cons, List.sum_cons]
      have h1 := flatten_size_le g
      have h2 := flattenList_size_le rest
      omega
termination_by sizeOf gs
end

/- Custom transparent Boolean equality on `UnboundedFanInFormula`.
   Lean can derive `BEq` for this nested-recursive type, but it cannot derive
   `DecidableEq`, `ReflBEq`, or `LawfulBEq` through the
   `List UnboundedFanInFormula` fields.  The verified deduplication below
   needs explicit reflexivity and soundness proofs, so we keep the comparator
   transparent and prove those properties directly. -/
mutual
def formulaBEq : UnboundedFanInFormula → UnboundedFanInFormula → Bool
  | inputGate i n,        inputGate i' n'      => decide (i = i') && decide (n = n')
  | constant v lbl,   constant v' lbl' => (v == v') && decide (lbl = lbl')
  | notGate g,        notGate g'       => formulaBEq g g'
  | andGate gs,       andGate gs'      => formulaListBEq gs gs'
  | orGate gs,        orGate gs'       => formulaListBEq gs gs'
  | _,                _                => false

def formulaListBEq :
    List UnboundedFanInFormula → List UnboundedFanInFormula → Bool
  | [],     []        => true
  | g :: gs, g' :: gs' => formulaBEq g g' && formulaListBEq gs gs'
  | _,      _         => false
end

mutual
theorem formulaBEq_refl : ∀ g, formulaBEq g g = true
  | .inputGate i b => by simp [formulaBEq]
  | .constant b m => by simp [formulaBEq]
  | .notGate g => by simp [formulaBEq, formulaBEq_refl g]
  | .andGate gs => by simp [formulaBEq, formulaListBEq_refl gs]
  | .orGate gs => by simp [formulaBEq, formulaListBEq_refl gs]
theorem formulaListBEq_refl : ∀ gs, formulaListBEq gs gs = true
  | [] => by simp [formulaListBEq]
  | g :: gs => by simp [formulaListBEq, formulaBEq_refl g, formulaListBEq_refl gs]
end

/- `formulaBEq` is sound: returning `true` implies syntactic equality. -/
mutual
theorem formulaBEq_sound :
    ∀ g g', formulaBEq g g' = true → g = g' := by
  intro g g' h
  cases g with
  | inputGate i n =>
      cases g' with
      | inputGate i' n' =>
          simp [formulaBEq] at h
          obtain ⟨hi, hn⟩ := h
          rw [hi, hn]
      | constant _ _ => simp [formulaBEq] at h
      | notGate _    => simp [formulaBEq] at h
      | andGate _    => simp [formulaBEq] at h
      | orGate _     => simp [formulaBEq] at h
  | constant v lbl =>
      cases g' with
      | inputGate _ _   => simp [formulaBEq] at h
      | constant v' lbl' =>
          simp [formulaBEq] at h
          obtain ⟨hv, hlbl⟩ := h
          have hv' : v = v' := by
            cases v <;> cases v' <;> first
              | rfl
              | (exfalso; revert hv; decide)
          rw [hv', hlbl]
      | notGate _    => simp [formulaBEq] at h
      | andGate _    => simp [formulaBEq] at h
      | orGate _     => simp [formulaBEq] at h
  | notGate g₀ =>
      cases g' with
      | inputGate _ _    => simp [formulaBEq] at h
      | constant _ _ => simp [formulaBEq] at h
      | notGate g₀'  =>
          simp only [formulaBEq] at h
          have := formulaBEq_sound g₀ g₀' h
          rw [this]
      | andGate _    => simp [formulaBEq] at h
      | orGate _     => simp [formulaBEq] at h
  | andGate gs =>
      cases g' with
      | inputGate _ _    => simp [formulaBEq] at h
      | constant _ _ => simp [formulaBEq] at h
      | notGate _    => simp [formulaBEq] at h
      | andGate gs'  =>
          simp only [formulaBEq] at h
          have := formulaListBEq_sound gs gs' h
          rw [this]
      | orGate _     => simp [formulaBEq] at h
  | orGate gs =>
      cases g' with
      | inputGate _ _    => simp [formulaBEq] at h
      | constant _ _ => simp [formulaBEq] at h
      | notGate _    => simp [formulaBEq] at h
      | andGate _    => simp [formulaBEq] at h
      | orGate gs'   =>
          simp only [formulaBEq] at h
          have := formulaListBEq_sound gs gs' h
          rw [this]
termination_by g => sizeOf g

theorem formulaListBEq_sound :
    ∀ gs gs', formulaListBEq gs gs' = true → gs = gs' := by
  intro gs gs' h
  cases gs with
  | nil =>
      cases gs' with
      | nil => rfl
      | cons _ _ => simp [formulaListBEq] at h
  | cons g rest =>
      cases gs' with
      | nil => simp [formulaListBEq] at h
      | cons g' rest' =>
          simp only [formulaListBEq, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          have e1 := formulaBEq_sound g g' h1
          have e2 := formulaListBEq_sound rest rest' h2
          rw [e1, e2]
termination_by gs => sizeOf gs
end

/-- Dedup a list of UFI formulas using `formulaBEq`. Order-preserving:
    keeps the *first* occurrence of each equivalence class. -/
def dedupFormulas : List UnboundedFanInFormula → List UnboundedFanInFormula
  | []      => []
  | g :: gs =>
      let rest := dedupFormulas gs
      if rest.any (fun x => formulaBEq x g) then rest else g :: rest

/-- Membership in `dedupFormulas` — modulo `formulaBEq`-soundness, this
    coincides with membership in the original list. -/
lemma mem_dedupFormulas_iff
    (gs : List UnboundedFanInFormula) (g : UnboundedFanInFormula) :
    g ∈ dedupFormulas gs ↔ g ∈ gs := by
  induction gs with
  | nil => simp [dedupFormulas]
  | cons h rest ih =>
      change g ∈ (if (dedupFormulas rest).any (fun x => formulaBEq x h)
                 then dedupFormulas rest
                 else h :: dedupFormulas rest) ↔ g ∈ h :: rest
      by_cases hany : ((dedupFormulas rest).any (fun x => formulaBEq x h)) = true
      · rw [if_pos hany]
        constructor
        · intro hg; right; exact ih.mp hg
        · intro hg
          rcases List.mem_cons.mp hg with rfl | hg
          · rcases List.any_eq_true.mp hany with ⟨w, hw_mem, hw_eq⟩
            have hw_eq_g : w = g := formulaBEq_sound w g hw_eq
            rw [← hw_eq_g]; exact hw_mem
          · exact ih.mpr hg
      · rw [if_neg hany]
        constructor
        · intro hg
          rcases List.mem_cons.mp hg with rfl | hg
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih.mp hg)
        · intro hg
          rcases List.mem_cons.mp hg with rfl | hg
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih.mpr hg)

theorem dedupFormulas_nodup : ∀ gs, (dedupFormulas gs).Nodup
  | [] => by simp [dedupFormulas]
  | g :: gs => by
      simp only [dedupFormulas]
      split_ifs with h
      · exact dedupFormulas_nodup gs
      · refine List.nodup_cons.mpr ⟨?_, dedupFormulas_nodup gs⟩
        intro hg
        apply h
        rw [List.any_eq_true]
        exact ⟨g, hg, formulaBEq_refl g⟩

theorem dedupFormulas_sum_map_le (gs : List UnboundedFanInFormula)
    (w : UnboundedFanInFormula → Nat) :
    ((dedupFormulas gs).map w).sum ≤ (gs.map w).sum := by
  induction gs with
  | nil => simp [dedupFormulas]
  | cons g gs ih =>
      simp only [dedupFormulas]
      split_ifs
      · exact le_trans ih (Nat.le_add_left _ _)
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add_left ih _

end Formulas.UFITransformations
