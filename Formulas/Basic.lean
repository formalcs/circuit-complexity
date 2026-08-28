/-
Author: Saint Wesonga
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits

inductive UnboundedFanInFormula where
  | inputGate : Nat -> Bool -> UnboundedFanInFormula -- Bool indicates whether the input is negated
  | constant : Bool -> Nat -> UnboundedFanInFormula -- Nat is just label for easy tracking
  | notGate : UnboundedFanInFormula -> UnboundedFanInFormula
  | andGate : List UnboundedFanInFormula -> UnboundedFanInFormula
  | orGate : List UnboundedFanInFormula -> UnboundedFanInFormula
  deriving Repr

/-- A Boolean formula whose AND and OR gates have fan-in two. -/
inductive BoundedFanInFormula where
  | inputGate : Nat → Bool → BoundedFanInFormula
  | constant : Bool → Nat → BoundedFanInFormula
  | notGate : BoundedFanInFormula → BoundedFanInFormula
  | andGate : BoundedFanInFormula → BoundedFanInFormula → BoundedFanInFormula
  | orGate : BoundedFanInFormula → BoundedFanInFormula → BoundedFanInFormula
  deriving Repr

open UnboundedFanInFormula

/-
The andGate and orGate can have an empty list of input gates.
andGate will evaluate to true and orGate false in this case.
This convention means that an empty list as an argument will
not change the output of the gate operation.
-/
-- ============================================================
-- Helper lemmas for (List.foldr max 0) bounds
-- ============================================================

theorem adder_foldr_max_le_of_all_le {l : List Nat} {k : Nat}
    (h : ∀ x ∈ l, x ≤ k) : (List.foldr max 0) l ≤ k := by
  induction l with
  | nil => simp [List.foldr_cons, List.foldr_nil]
  | cons x xs ih =>
    simp only [List.foldr_cons, List.foldr_nil]
    apply Nat.max_le.mpr
    exact ⟨h x (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))⟩

theorem adder_foldr_max_map_le {α : Type*} {f : α → Nat} {l : List α} {k : Nat}
    (h : ∀ x ∈ l, f x ≤ k) : (List.foldr max 0) (l.map f) ≤ k := by
  apply adder_foldr_max_le_of_all_le
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact h a ha

theorem adder_foldr_max_ge_of_mem {l : List Nat} {x : Nat}
    (h : x ∈ l) : x ≤ (List.foldr max 0) l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.foldr_cons, List.foldr_nil]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

def isInput (gate : UnboundedFanInFormula) : Bool :=
  match gate with
  | inputGate _ _ => true
  | _ => false

/-- Count the non-input gates in a bounded-fan-in formula. -/
def bfiFormulaCircuitSize : BoundedFanInFormula → Nat
  | .inputGate _ _ => 0
  | .constant _ _ => 1
  | .notGate gate => bfiFormulaCircuitSize gate + 1
  | .andGate left right =>
      bfiFormulaCircuitSize left + bfiFormulaCircuitSize right + 1
  | .orGate left right =>
      bfiFormulaCircuitSize left + bfiFormulaCircuitSize right + 1

/-- Count of non-inputGate nodes in an `UnboundedFanInFormula`.

    This equals the number of gates that the analogous circuit builder would
    add for the formula. -/
def ufiFormulaCircuitSize : UnboundedFanInFormula → Nat
  | .inputGate _ _    => 0
  | .constant _ _ => 1
  | .notGate c    => ufiFormulaCircuitSize c + 1
  | .andGate cs   => (cs.map ufiFormulaCircuitSize).sum + 1
  | .orGate  cs   => (cs.map ufiFormulaCircuitSize).sum + 1

-- Custom measure function that counts total number of gate nodes
-- This gives us a well-founded relation based on the structure depth
def ufiFormulaNodeCount (c : UnboundedFanInFormula) : Nat :=
  match c with
  | inputGate    _ _  => 1
  | constant _ _  => 1
  | notGate  gate  => 1 + ufiFormulaNodeCount gate
  | andGate  gates => 1 + (gates.map ufiFormulaNodeCount).sum
  | orGate   gates => 1 + (gates.map ufiFormulaNodeCount).sum

end Circuits
