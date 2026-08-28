import Parity.Leveling.Invariants

/-!
# Leveling pipeline — Stage 1: NOT-gate elimination

The first stage pushes every `notGate` constructor down to the leaves
using De Morgan's laws (`pushNeg`), so that negation is carried only on
`inputGate` literals (their `Bool` flag) and `constant` leaves.  It then
canonicalizes input indices so that `ufiLargestInput · < n` (folding
out-of-range references into constants so that `ufiLargestInput · < n`).

* **Transformation:** `pushNeg` / `pushNegList` (mutually recursive) and
  the wrapper `elimNotGates := pushNeg false`.
* **Proved lemma:** `elimNotGates_hasNoNotGates` — the output never
  contains a `notGate` constructor.
* **Stage contract:** `elimNotGates_contract` — the full stage
  contract including evaluation equivalence, index canonicalization, and
  the polynomial size bound.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.Leveling
open Circuits
open UnboundedFanInFormula

/- De Morgan push-down.  `pushNeg neg f` is a formula equivalent to
    `f` (if `neg = false`) or to `¬f` (if `neg = true`) in which every
    `notGate` has been eliminated: negation lives only on `inputGate`
    literal flags and `constant` values. -/
mutual
def pushNeg (neg : Bool) (f : UnboundedFanInFormula) : UnboundedFanInFormula :=
  match f with
  | .inputGate i b    => .inputGate i (Bool.xor neg b)
  | .constant c lbl => .constant (if neg then not c else c) lbl
  | .notGate g    => pushNeg (!neg) g
  | .andGate gs   =>
      if neg then .orGate (pushNegList neg gs) else .andGate (pushNegList neg gs)
  | .orGate gs    =>
      if neg then .andGate (pushNegList neg gs) else .orGate (pushNegList neg gs)
def pushNegList (neg : Bool) (l : List UnboundedFanInFormula) :
    List UnboundedFanInFormula :=
  match l with
  | []      => []
  | g :: gs => pushNeg neg g :: pushNegList neg gs
end

/-- Stage-1 transformation: eliminate all `notGate`s by De Morgan
    push-down (equivalence-preserving, `neg = false`). -/
def elimNotGates (f : UnboundedFanInFormula) : UnboundedFanInFormula :=
  pushNeg false f

/- The De Morgan push-down never produces a `notGate`. -/
mutual
theorem pushNeg_hasNoNotGates (neg : Bool) (f : UnboundedFanInFormula) :
    HasNoNotGates (pushNeg neg f) := by
  match f with
  | .inputGate i b =>
      simp only [pushNeg, HasNoNotGates]
  | .constant c lbl =>
      simp only [pushNeg, HasNoNotGates]
  | .notGate g =>
      simp only [pushNeg]
      exact pushNeg_hasNoNotGates (!neg) g
  | .andGate gs =>
      simp only [pushNeg]
      split
      · simp only [HasNoNotGates]
        exact pushNegList_hasNoNotGates neg gs
      · simp only [HasNoNotGates]
        exact pushNegList_hasNoNotGates neg gs
  | .orGate gs =>
      simp only [pushNeg]
      split
      · simp only [HasNoNotGates]
        exact pushNegList_hasNoNotGates neg gs
      · simp only [HasNoNotGates]
        exact pushNegList_hasNoNotGates neg gs
theorem pushNegList_hasNoNotGates (neg : Bool) (l : List UnboundedFanInFormula) :
    ∀ g ∈ pushNegList neg l, HasNoNotGates g := by
  match l with
  | [] =>
      intro g hg
      simp only [pushNegList, List.not_mem_nil] at hg
  | g :: gs =>
      intro x hx
      simp only [pushNegList, List.mem_cons] at hx
      rcases hx with h | h
      · subst h; exact pushNeg_hasNoNotGates neg g
      · exact pushNegList_hasNoNotGates neg gs x h
end

/-- `elimNotGates` removes every `notGate` constructor. -/
theorem elimNotGates_hasNoNotGates (f : UnboundedFanInFormula) :
    HasNoNotGates (elimNotGates f) :=
  pushNeg_hasNoNotGates false f

/- Rewriting shims: `pushNeg` on an `andGate`/`orGate` reduces (definitionally)
   to the dual or same gate over the pushed-down children, for each concrete
   polarity.  These let us peel the De-Morgan step without fighting the
   `if neg then … else …` in the definition. -/
theorem pushNeg_andGate_false (gs : List UnboundedFanInFormula) :
    pushNeg false (.andGate gs) = .andGate (pushNegList false gs) := rfl
theorem pushNeg_andGate_true (gs : List UnboundedFanInFormula) :
    pushNeg true (.andGate gs) = .orGate (pushNegList true gs) := rfl
theorem pushNeg_orGate_false (gs : List UnboundedFanInFormula) :
    pushNeg false (.orGate gs) = .orGate (pushNegList false gs) := rfl
theorem pushNeg_orGate_true (gs : List UnboundedFanInFormula) :
    pushNeg true (.orGate gs) = .andGate (pushNegList true gs) := rfl

/- **Index preservation.**  De-Morgan push-down never changes which input
   indices occur (it only flips literal polarities and dualizes gates), so the
   collected index list is preserved verbatim. Consequently both
   `ufiUniqueInputs` and `ufiLargestInput` are preserved. -/
mutual
theorem pushNeg_collect (neg : Bool) (f : UnboundedFanInFormula) :
    ufiCollectInputIndices (pushNeg neg f) = ufiCollectInputIndices f := by
  match f with
  | .inputGate i b => cases neg <;> simp [pushNeg, ufiCollectInputIndices]
  | .constant c l => cases neg <;> simp [pushNeg, ufiCollectInputIndices]
  | .notGate g =>
      simp only [pushNeg]
      rw [ufiCollectInputIndices, pushNeg_collect (!neg) g]
  | .andGate gs =>
      cases neg with
      | false =>
          rw [pushNeg_andGate_false, ufiCollectInputIndices,
            ufiCollectInputIndices, pushNegList_collect false gs]
      | true =>
          rw [pushNeg_andGate_true, ufiCollectInputIndices,
            ufiCollectInputIndices, pushNegList_collect true gs]
  | .orGate gs =>
      cases neg with
      | false =>
          rw [pushNeg_orGate_false, ufiCollectInputIndices,
            ufiCollectInputIndices, pushNegList_collect false gs]
      | true =>
          rw [pushNeg_orGate_true, ufiCollectInputIndices,
            ufiCollectInputIndices, pushNegList_collect true gs]
theorem pushNegList_collect (neg : Bool) (gs : List UnboundedFanInFormula) :
    (pushNegList neg gs).flatMap ufiCollectInputIndices
      = gs.flatMap ufiCollectInputIndices := by
  match gs with
  | [] => simp [pushNegList]
  | g :: gs' =>
      simp only [pushNegList, List.flatMap_cons]
      rw [pushNeg_collect neg g, pushNegList_collect neg gs']
end

theorem pushNeg_largest (neg : Bool) (f : UnboundedFanInFormula) :
    ufiLargestInput (pushNeg neg f) = ufiLargestInput f := by
  unfold ufiLargestInput
  rw [pushNeg_collect]

/- **Depth does not increase.**  Removing `notGate` constructors can only
   shrink depth; dualizing AND/OR keeps it. -/
mutual
theorem pushNeg_depth_le (neg : Bool) (f : UnboundedFanInFormula) :
    ufiFormulaDepth (pushNeg neg f) ≤ ufiFormulaDepth f := by
  match f with
  | .inputGate i b => cases neg <;> simp [pushNeg, ufiFormulaDepth]
  | .constant c l => cases neg <;> simp [pushNeg, ufiFormulaDepth]
  | .notGate g =>
      simp only [pushNeg, ufiFormulaDepth]
      exact le_trans (pushNeg_depth_le (!neg) g) (Nat.le_succ _)
  | .andGate gs =>
      cases neg with
      | false =>
          rw [pushNeg_andGate_false, ufiFormulaDepth, ufiFormulaDepth]
          exact Nat.add_le_add_left (pushNegList_depth_le false gs) 1
      | true =>
          rw [pushNeg_andGate_true, ufiFormulaDepth, ufiFormulaDepth]
          exact Nat.add_le_add_left (pushNegList_depth_le true gs) 1
  | .orGate gs =>
      cases neg with
      | false =>
          rw [pushNeg_orGate_false, ufiFormulaDepth, ufiFormulaDepth]
          exact Nat.add_le_add_left (pushNegList_depth_le false gs) 1
      | true =>
          rw [pushNeg_orGate_true, ufiFormulaDepth, ufiFormulaDepth]
          exact Nat.add_le_add_left (pushNegList_depth_le true gs) 1
theorem pushNegList_depth_le (neg : Bool) (gs : List UnboundedFanInFormula) :
    (List.foldr max 0) (List.map ufiFormulaDepth (pushNegList neg gs))
      ≤ (List.foldr max 0) (List.map ufiFormulaDepth gs) := by
  match gs with
  | [] => simp [pushNegList]
  | g :: gs' =>
      simp only [pushNegList, List.map_cons, List.foldr_cons, List.foldr_nil]
      exact max_le_max (pushNeg_depth_le neg g) (pushNegList_depth_le neg gs')
end

/- **Circuit size does not increase.** -/
mutual
theorem pushNeg_circuit_size_le (neg : Bool) (f : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (pushNeg neg f) ≤ ufiFormulaCircuitSize f := by
  match f with
  | .inputGate i b => cases neg <;> simp [pushNeg, ufiFormulaCircuitSize]
  | .constant c l => cases neg <;> simp [pushNeg, ufiFormulaCircuitSize]
  | .notGate g =>
      simp only [pushNeg, ufiFormulaCircuitSize]
      exact le_trans (pushNeg_circuit_size_le (!neg) g) (Nat.le_add_right _ 1)
  | .andGate gs =>
      cases neg with
      | false =>
          rw [pushNeg_andGate_false, ufiFormulaCircuitSize, ufiFormulaCircuitSize]
          exact Nat.add_le_add_right (pushNegList_circuit_size_le false gs) 1
      | true =>
          rw [pushNeg_andGate_true, ufiFormulaCircuitSize, ufiFormulaCircuitSize]
          exact Nat.add_le_add_right (pushNegList_circuit_size_le true gs) 1
  | .orGate gs =>
      cases neg with
      | false =>
          rw [pushNeg_orGate_false, ufiFormulaCircuitSize, ufiFormulaCircuitSize]
          exact Nat.add_le_add_right (pushNegList_circuit_size_le false gs) 1
      | true =>
          rw [pushNeg_orGate_true, ufiFormulaCircuitSize, ufiFormulaCircuitSize]
          exact Nat.add_le_add_right (pushNegList_circuit_size_le true gs) 1
theorem pushNegList_circuit_size_le (neg : Bool) (gs : List UnboundedFanInFormula) :
    (List.map ufiFormulaCircuitSize (pushNegList neg gs)).sum
      ≤ (List.map ufiFormulaCircuitSize gs).sum := by
  match gs with
  | [] => simp [pushNegList]
  | g :: gs' =>
      simp only [pushNegList, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (pushNeg_circuit_size_le neg g)
        (pushNegList_circuit_size_le neg gs')
end

/- **Evaluation correctness (De Morgan).**  `pushNeg neg f` computes `f`
   when `neg = false` and `¬f` when `neg = true`, provided every input
   referenced by `f` is present. -/
mutual
theorem pushNeg_eval (neg : Bool) (f : UnboundedFanInFormula) (inputs : List Bool)
    (hbound : ∀ i ∈ ufiCollectInputIndices f, i < inputs.length) :
    ufiFormulaEval (pushNeg neg f) inputs
      = (if neg = true then not (ufiFormulaEval f inputs)
         else ufiFormulaEval f inputs) := by
  match f with
  | .inputGate i b =>
      have hi : i < inputs.length := hbound i (by simp [ufiCollectInputIndices])
      cases h : inputs[i]? with
      | none => simp [List.getElem?_eq_getElem hi] at h
      | some v => cases neg <;> cases b <;> cases v <;>
          simp [pushNeg, ufiFormulaEval, h, not]
  | .constant c l =>
      cases neg <;> cases c <;> simp [pushNeg, ufiFormulaEval, not]
  | .notGate g =>
      simp only [pushNeg, ufiFormulaEval]
      rw [pushNeg_eval (!neg) g inputs (by simpa [ufiCollectInputIndices] using hbound)]
      cases neg <;> cases h : ufiFormulaEval g inputs <;> simp [not]
  | .andGate gs => exact pushNeg_eval_and_list neg gs inputs hbound
  | .orGate gs => exact pushNeg_eval_or_list neg gs inputs hbound
theorem pushNeg_eval_and_list (neg : Bool) (gs : List UnboundedFanInFormula)
    (inputs : List Bool)
    (hbound : ∀ i ∈ ufiCollectInputIndices (.andGate gs), i < inputs.length) :
    ufiFormulaEval (pushNeg neg (.andGate gs)) inputs
      = (if neg = true then not (ufiFormulaEval (.andGate gs) inputs)
         else ufiFormulaEval (.andGate gs) inputs) := by
  match gs with
  | [] => cases neg <;> simp [pushNeg, pushNegList, ufiFormulaEval, not]
  | g :: gs' =>
      have hhead := pushNeg_eval neg g inputs (by
        intro i hi; apply hbound i
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨g, List.mem_cons_self, hi⟩)
      have htail := pushNeg_eval_and_list neg gs' inputs (by
        intro i hi; apply hbound i
        simp only [ufiCollectInputIndices, List.mem_flatMap] at hi ⊢
        obtain ⟨g', hg', hi'⟩ := hi
        exact ⟨g', List.mem_cons_of_mem g hg', hi'⟩)
      cases neg with
      | false =>
          simp only [Bool.false_eq_true, if_false] at hhead htail ⊢
          rw [pushNeg_andGate_false] at htail ⊢
          simp only [pushNegList, ufiFormulaEval]
          rw [hhead]
          cases hv : ufiFormulaEval g inputs with
          | false => simp [ufiFormulaEval]
          | true =>
              simp only [ufiFormulaEval] at htail ⊢
              exact htail
      | true =>
          simp only [if_true] at hhead htail ⊢
          rw [pushNeg_andGate_true] at htail ⊢
          simp only [pushNegList, ufiFormulaEval]
          rw [hhead]
          cases hv : ufiFormulaEval g inputs with
          | false => simp [ufiFormulaEval, not]
          | true =>
              simp only [ufiFormulaEval, not] at htail ⊢
              exact htail
theorem pushNeg_eval_or_list (neg : Bool) (gs : List UnboundedFanInFormula)
    (inputs : List Bool)
    (hbound : ∀ i ∈ ufiCollectInputIndices (.orGate gs), i < inputs.length) :
    ufiFormulaEval (pushNeg neg (.orGate gs)) inputs
      = (if neg = true then not (ufiFormulaEval (.orGate gs) inputs)
         else ufiFormulaEval (.orGate gs) inputs) := by
  match gs with
  | [] => cases neg <;> simp [pushNeg, pushNegList, ufiFormulaEval, not]
  | g :: gs' =>
      have hhead := pushNeg_eval neg g inputs (by
        intro i hi; apply hbound i
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨g, List.mem_cons_self, hi⟩)
      have htail := pushNeg_eval_or_list neg gs' inputs (by
        intro i hi; apply hbound i
        simp only [ufiCollectInputIndices, List.mem_flatMap] at hi ⊢
        obtain ⟨g', hg', hi'⟩ := hi
        exact ⟨g', List.mem_cons_of_mem g hg', hi'⟩)
      cases neg with
      | false =>
          simp only [Bool.false_eq_true, if_false] at hhead htail ⊢
          rw [pushNeg_orGate_false] at htail ⊢
          simp only [pushNegList, ufiFormulaEval]
          rw [hhead]
          cases hv : ufiFormulaEval g inputs with
          | true => simp [ufiFormulaEval]
          | false =>
              simp only [ufiFormulaEval] at htail ⊢
              exact htail
      | true =>
          simp only [if_true] at hhead htail ⊢
          rw [pushNeg_orGate_true] at htail ⊢
          simp only [pushNegList, ufiFormulaEval]
          rw [hhead]
          cases hv : ufiFormulaEval g inputs with
          | true => simp [ufiFormulaEval, not]
          | false =>
              simp only [ufiFormulaEval, not] at htail ⊢
              exact htail
end

/-- `elimNotGates` preserves evaluation when all referenced inputs are present. -/
theorem elimNotGates_eval (f : UnboundedFanInFormula) (inputs : List Bool)
    (hbound : ∀ i ∈ ufiCollectInputIndices f, i < inputs.length) :
    ufiFormulaEval (elimNotGates f) inputs = ufiFormulaEval f inputs := by
  rw [elimNotGates, pushNeg_eval false f inputs hbound]; simp

/-- **Stage-1 contract (tracked core).**

    For any input polynomial bound `a · n^b`, every depth-≤`d`, `n`-input
    formula of circuit size `≤ a · n^b`, **with input
    indices already in canonical range** (`ufiLargestInput f < n`), can
    be turned into an equivalent (`AgreesOn`) `notGate`-free formula of
    depth ≤ `d`, circuit size ≤ `a · n^b`, with `n` inputs all indexed `< n`.

    The transformation assumes a canonical input layout and preserves it.
    Establishing canonical layout from an arbitrary formula is a separate
    normalization stage; the `notGate`-elimination stage only has to
    preserve it. The precondition is essential: without
    it the postcondition is unsatisfiable — a literal referencing an
    out-of-range index (e.g. `andGate [inputGate 0 false, inputGate 2 true]` at
    `n = 2`, `d = 1`) behaves like a constant on length-`n` inputs but
    cannot be reproduced by any in-range, depth-≤`d`, `notGate`-free
    formula keeping all indices `< n` (machine-checked counterexample).

    With the precondition, the witness is `elimNotGates f`
    (= `pushNeg false f`): De-Morgan push-down preserves the input-index
    list verbatim (`pushNeg_collect`), so `ufiUniqueInputs` and
    `ufiLargestInput` are unchanged; it never raises depth
    (`pushNeg_depth_le`) or circuit size (`pushNeg_circuit_size_le`); and it
    preserves evaluation (`elimNotGates_eval`). -/
theorem elimNotGates_contract (d : Nat) (_hd : 1 ≤ d) :
    ∀ a b : Nat, ∀ (n : Nat) (f : UnboundedFanInFormula),
      ufiLargestInput f < n →
      ufiFormulaDepth f ≤ d →
      ufiFormulaCircuitSize f ≤ a * n ^ b →
      ∃ g : UnboundedFanInFormula,
        HasNoNotGates g ∧
        ufiLargestInput g < n ∧
        ufiFormulaDepth g ≤ d ∧
        ufiFormulaCircuitSize g ≤ a * n ^ b ∧
        AgreesOn f g n := by
  intro a b n f hlarge hdepth hbound
  refine ⟨elimNotGates f, elimNotGates_hasNoNotGates f, ?_, ?_, ?_, ?_⟩
  · rw [elimNotGates, pushNeg_largest]; exact hlarge
  · exact le_trans (by rw [elimNotGates]; exact pushNeg_depth_le false f) hdepth
  · exact le_trans (by rw [elimNotGates]; exact pushNeg_circuit_size_le false f) hbound
  · intro inputs hlen
    rw [elimNotGates_eval f inputs]
    intro i hi
    have hle : i ≤ ufiLargestInput f := by
      unfold ufiLargestInput
      exact mem_le_foldr_max hi
    omega

end Circuits.Leveling
