import Formulas.Basic
import Formulas.CnfDnf.CnfDnfBasic

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

def ufiFormulaDepth (ufi_formula : UnboundedFanInFormula) : Nat :=
  match ufi_formula with
  | inputGate    _ _   => 0
  | constant _ _   => 0
  | notGate  gate  => Nat.succ (ufiFormulaDepth gate)
  -- Explain why none of these work
  -- | andGate gates => 1 + max (List.map circuitDepth gates)
  -- | andGate gates => 1 + List.max (List.map circuitDepth gates)
  -- | andGate gates => 1 + (List.map circuitDepth gates).max
  | andGate  gates => 1 + (List.foldr max 0) (List.map ufiFormulaDepth gates)
  | orGate   gates => 1 + (List.foldr max 0) (List.map ufiFormulaDepth gates)

/-- Depth of a bounded-fan-in formula. Inputs and constants have depth zero. -/
def bfiFormulaDepth : BoundedFanInFormula → Nat
  | .inputGate _ _ => 0
  | .constant _ _ => 0
  | .notGate gate => bfiFormulaDepth gate + 1
  | .andGate left right =>
      max (bfiFormulaDepth left) (bfiFormulaDepth right) + 1
  | .orGate left right =>
      max (bfiFormulaDepth left) (bfiFormulaDepth right) + 1

/-- Input indices occurring in a bounded-fan-in formula, with repetitions. -/
def bfiCollectInputIndices : BoundedFanInFormula → List Nat
  | .inputGate index _ => [index]
  | .constant _ _ => []
  | .notGate gate => bfiCollectInputIndices gate
  | .andGate left right =>
      bfiCollectInputIndices left ++ bfiCollectInputIndices right
  | .orGate left right =>
      bfiCollectInputIndices left ++ bfiCollectInputIndices right

/-- Largest input index occurring in a bounded-fan-in formula. Formulas with
    no inputs return zero. -/
def bfiLargestInput (formula : BoundedFanInFormula) : Nat :=
  (bfiCollectInputIndices formula).foldr max 0

def ufiCollectInputIndices
  (ufi_formula : UnboundedFanInFormula) : List Nat
  :=
  match ufi_formula with
  | inputGate    n _   => [n]
  | constant _ _   => []
  | notGate  gate  => ufiCollectInputIndices gate
  | andGate  gates => gates.flatMap ufiCollectInputIndices
  | orGate   gates => gates.flatMap ufiCollectInputIndices

def ufiUniqueInputs (circuit : UnboundedFanInFormula) : List Nat :=
    (ufiCollectInputIndices circuit).dedup

def ufiLargestInput
  (circuit : UnboundedFanInFormula) : Nat :=
    (List.foldr max 0) (ufiCollectInputIndices circuit)

-- Helper: flatMap creates a superlist of each individual map
theorem mem_flatMap_implies_sublist {α β : Type*} (f : α → List β) (l : List α) (x : α)
    (h : x ∈ l) : (f x).Sublist (l.flatMap f) := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp [List.Mem] at h
    match h with
    | Or.inl h_eq =>
      rw [h_eq]
      simp only [List.flatMap]
      exact List.sublist_append_left (f head) (tail.flatMap f)
    | Or.inr h_mem =>
      simp only [List.flatMap]
      have ih' := ih h_mem
      exact List.Sublist.trans ih' (List.sublist_append_right (f head) (tail.flatMap f))

mutual
theorem ufiFormulaCircuitSize_le_node_count
    (c : UnboundedFanInFormula) :
    ufiFormulaCircuitSize c ≤ ufiFormulaNodeCount c := by
  match c with
  | .inputGate _ _ => simp [ufiFormulaCircuitSize, ufiFormulaNodeCount]
  | .constant _ _ => simp [ufiFormulaCircuitSize, ufiFormulaNodeCount]
  | .notGate child =>
      simp only [ufiFormulaCircuitSize, ufiFormulaNodeCount]
      have h := ufiFormulaCircuitSize_le_node_count child
      omega
  | .andGate children =>
      simp only [ufiFormulaCircuitSize, ufiFormulaNodeCount]
      have h := ufiFormulaCircuitSize_list_le_node_count_list children
      omega
  | .orGate children =>
      simp only [ufiFormulaCircuitSize, ufiFormulaNodeCount]
      have h := ufiFormulaCircuitSize_list_le_node_count_list children
      omega
  termination_by sizeOf c

theorem ufiFormulaCircuitSize_list_le_node_count_list
    (cs : List UnboundedFanInFormula) :
    (cs.map ufiFormulaCircuitSize).sum ≤
      (cs.map ufiFormulaNodeCount).sum := by
  match cs with
  | [] => simp
  | c :: rest =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (ufiFormulaCircuitSize_le_node_count c)
        (ufiFormulaCircuitSize_list_le_node_count_list rest)
  termination_by sizeOf cs
end

/-! ### Assigned leveling for UFI formulas

UFI formulas are tree-structured, so the "edges" are direct
parent–child pairs in the syntax tree.  An `andGate gates` /
`orGate gates` parent has children `g ∈ gates`; a `notGate g`
parent has the single child `g`.  `inputGate _ _` and `constant _ _`
are leaves. -/

namespace UnboundedFanInFormula

/-- An UFI formula is an `andGate` or an `orGate` (i.e. an
    "AND/OR gate" in the layered sense). -/
def IsAndOr : UnboundedFanInFormula → Prop
  | UnboundedFanInFormula.andGate _ => True
  | UnboundedFanInFormula.orGate  _ => True
  | _                                => False

/-- A UFI formula is **AND/OR-leveled** when:

    * it contains no `notGate` constructors anywhere in its
      syntax tree, and
    * its `andGate`/`orGate` subformulas form alternating layers:
      whenever an `andGate`/`orGate` parent has an
      `andGate`/`orGate` child, their constructors must differ
      (so any chain of nested AND/OR subformulas strictly
      alternates between AND and OR).

    `inputGate` and `constant` subformulas are exempt and may appear
    as children of any AND/OR gate. -/
def HasAlternatingAndOrGates : UnboundedFanInFormula → Prop
  | UnboundedFanInFormula.inputGate    _ _ => True
  | UnboundedFanInFormula.constant _ _ => True
  | UnboundedFanInFormula.notGate  _   => False
  | UnboundedFanInFormula.andGate  gates =>
      (∀ g ∈ gates, HasAlternatingAndOrGates g) ∧
      (∀ g ∈ gates, ∀ inner, g ≠ UnboundedFanInFormula.andGate inner)
  | UnboundedFanInFormula.orGate   gates =>
      (∀ g ∈ gates, HasAlternatingAndOrGates g) ∧
      (∀ g ∈ gates, ∀ inner, g ≠ UnboundedFanInFormula.orGate inner)

/-- **Position-indexed strict assigned-leveling** for UFI formulas.

    `IsAlternatingAndLeveledAt f n` says that the syntax tree of
    `f`, considered as living at root level `n`, satisfies
    AND/OR-alternation (no `notGate` constructors anywhere) **and**
    every AND/OR-to-AND/OR parent–child pair in the tree spans
    exactly one level: an `andGate` at level `m` may have
    `orGate` children only at level `m - 1`, and *vice versa*.

    This predicate keys the level on the *occurrence* of a subformula
    (its position in the tree, encoded by recursion depth), rather than
    on its extensional value. Consequently, distinct gates may produce
    equal subformulas without collapsing their occurrence levels. -/
def IsAlternatingAndLeveledAt :
    UnboundedFanInFormula → Nat → Prop
  | UnboundedFanInFormula.inputGate    _ _, _ => True
  | UnboundedFanInFormula.constant _ _, _ => True
  | UnboundedFanInFormula.notGate  _,   _ => False
  | UnboundedFanInFormula.andGate gates, n =>
      (∀ g ∈ gates, ∀ inner, g ≠ UnboundedFanInFormula.andGate inner) ∧
      (∀ g ∈ gates, IsAndOr g → 1 ≤ n) ∧
      (∀ g ∈ gates, IsAlternatingAndLeveledAt g (n - 1))
  | UnboundedFanInFormula.orGate gates, n =>
      (∀ g ∈ gates, ∀ inner, g ≠ UnboundedFanInFormula.orGate inner) ∧
      (∀ g ∈ gates, IsAndOr g → 1 ≤ n) ∧
      (∀ g ∈ gates, IsAlternatingAndLeveledAt g (n - 1))

end UnboundedFanInFormula

/-! ### `HasProperBottomsAt` strengthening of `IsAlternatingAndLeveledAt`.

    This predicate records stronger bottom-level well-formedness than
    `IsAlternatingAndLeveledAt`:

    * Every depth-≤-2 AND/OR subformula is *proper-CNF* / *proper-DNF*:
      the shape predicate `isCNF`/`isDNF` holds, no clause is empty,
      and no clause has duplicate variables.
    * `notGate` is forbidden everywhere (matches
      `IsAlternatingAndLeveledAt`'s convention).
    * Mid-tree `inputGate` and `constant` leaves are permitted at any level. -/
def HasProperBottomsAt : UnboundedFanInFormula → Nat → Prop
  | .inputGate _ _, _ => True
  | .constant _ _, _ => True
  | .notGate _, _ => False
  | .andGate gates, lvl =>
      if lvl ≤ 2 then
        Circuits.CnfDnf.isCNF (.andGate gates) = true ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (.andGate gates), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (.andGate gates),
            (c.map Prod.fst).Nodup)
      else
        ∀ g ∈ gates, HasProperBottomsAt g (lvl - 1)
  | .orGate gates, lvl =>
      if lvl ≤ 2 then
        Circuits.CnfDnf.isDNF (.orGate gates) = true ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (.orGate gates), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (.orGate gates),
            (c.map Prod.fst).Nodup)
      else
        ∀ g ∈ gates, HasProperBottomsAt g (lvl - 1)

/-- A structural bottom-width bound, following the same level descent as
    `HasProperBottomsAt`.  At a depth-`≤ 2` AND/OR gate it bounds the actual
    CNF/DNF clause width; above that cut it recursively bounds every child. -/
def HasProperBottomWidthLE : UnboundedFanInFormula → Nat → Nat → Prop
  | .inputGate _ _, _, _ => True
  | .constant _ _, _, _ => True
  | .notGate _, _, _ => False
  | .andGate gates, lvl, width =>
      if lvl ≤ 2 then Circuits.CnfDnf.cnfWidth (.andGate gates) ≤ width
      else ∀ g ∈ gates, HasProperBottomWidthLE g (lvl - 1) width
  | .orGate gates, lvl, width =>
      if lvl ≤ 2 then Circuits.CnfDnf.dnfWidth (.orGate gates) ≤ width
      else ∀ g ∈ gates, HasProperBottomWidthLE g (lvl - 1) width

/-! ### Fused predicate: `IsProperlyLeveled`.

    `UnboundedFanInFormula.IsAlternatingAndLeveledAt` and
    `HasProperBottomsAt` are *both* required by the switching-lemma
    machinery, and neither implies the other:

    * `IsAlternatingAndLeveledAt f d` enforces strict AND/OR
      *alternation* and the one-step level discipline throughout the
      *whole* tree (and forbids `notGate`), but says nothing about the
      bottom two layers forming genuine clauses — it permits a
      depth-≤-2 `andGate`/`orGate` whose clauses are empty or repeat a
      variable.
    * `HasProperBottomsAt f d` enforces the proper-CNF/DNF *shape* of the
      bottom two layers (`isCNF`/`isDNF`, nonempty clauses, per-clause
      `Nodup` variables) and forbids `notGate`, but does *not* enforce
      alternation in the upper (`lvl > 2`) layers — it permits an
      `andGate` directly under an `andGate` there.

    `IsProperlyLeveled` fuses both into a *single* recursive
    traversal — rather than the trivial conjunction
    `IsAlternatingAndLeveledAt f d ∧ HasProperBottomsAt f d`.  At every
    AND/OR node it checks the alternation + level-step discipline; then,
    mirroring `HasProperBottomsAt`'s branching, when `lvl ≤ 2` it stops the
    *proper-shape* recursion and asserts the proper-CNF/DNF shape, while
    when `lvl > 2` it recurses the *fused* predicate into the children
    at `lvl - 1`.

    Stopping the proper recursion at `lvl ≤ 2` is essential: the bottom
    `andGate`/`orGate` is a CNF/DNF whose children are clauses
    (`orGate`/`andGate` of input literals).  A clause such as
    `orGate [inputGate ..]` is *not* itself a proper DNF, so recursing the
    proper-shape check into it would make the predicate unsatisfiable.
    The proper-CNF/DNF shape (`isCNF`/`isDNF`) already forces every
    clause to be an AND/OR of plain inputs, so the residual strict
    discipline at the clause level holds automatically (see
    `isAlternatingAndLeveledAt_of_isOrOfInputsOnly` /
    `isAlternatingAndLeveledAt_of_isAndOfInputsOnly`) — no
    explicit `IsAlternatingAndLeveledAt` conjunct is needed.

    The projection lemmas `Leveling.isProperlyLeveled_imp_strict` /
    `Leveling.isProperlyLeveled_imp_proper` show it covers both requirements,
    and `Leveling.isProperlyLeveled_of_strict_proper` shows the two together
    reconstitute it (so the subtype carrying it is exactly as inhabited
    as one carrying both predicates separately). -/
namespace Leveling

def IsProperlyLeveled : UnboundedFanInFormula → Nat → Prop
  | .inputGate _ _, _ => True
  | .constant _ _, _ => True
  | .notGate _, _ => False
  | .andGate gates, lvl =>
      (∀ g ∈ gates, ∀ inner, g ≠ .andGate inner) ∧
      (∀ g ∈ gates, UnboundedFanInFormula.IsAndOr g → 1 ≤ lvl) ∧
      (if lvl ≤ 2 then
        Circuits.CnfDnf.IsProperCNF (.andGate gates)
      else
        ∀ g ∈ gates, IsProperlyLeveled g (lvl - 1))
  | .orGate gates, lvl =>
      (∀ g ∈ gates, ∀ inner, g ≠ .orGate inner) ∧
      (∀ g ∈ gates, UnboundedFanInFormula.IsAndOr g → 1 ≤ lvl) ∧
      (if lvl ≤ 2 then
        Circuits.CnfDnf.IsProperDNF (.orGate gates)
      else
        ∀ g ∈ gates, IsProperlyLeveled g (lvl - 1))

end Leveling

/- A clause `orGate lits` that passes `isOrOfInputsOnly` (all its
   children are plain `inputGate`s) is `IsAlternatingAndLeveledAt` at any
   level: it has no AND/OR children, so the alternation/level-step
   obligations hold vacuously.  This is what makes the explicit
   per-clause `IsAlternatingAndLeveledAt` conjunct redundant inside
   `IsProperlyLeveled` (it is recovered here from the proper-CNF
   shape). -/
theorem isAlternatingAndLeveledAt_of_isOrOfInputsOnly
    (g : UnboundedFanInFormula) (m : Nat)
    (h : Circuits.CnfDnf.isOrOfInputsOnly g = true) :
    IsAlternatingAndLeveledAt g m := by
  cases g with
  | inputGate _ _ => simp [Circuits.CnfDnf.isOrOfInputsOnly] at h
  | constant _ _ => simp [Circuits.CnfDnf.isOrOfInputsOnly] at h
  | notGate _ => simp [Circuits.CnfDnf.isOrOfInputsOnly] at h
  | andGate _ => simp [Circuits.CnfDnf.isOrOfInputsOnly] at h
  | orGate lits =>
      simp only [Circuits.CnfDnf.isOrOfInputsOnly, List.all_eq_true] at h
      simp only [IsAlternatingAndLeveledAt]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx _
        have hx' := h x hx
        cases x <;> simp_all [isInput]
      · intro x hx hand
        have hx' := h x hx
        cases x <;> simp_all [isInput, UnboundedFanInFormula.IsAndOr]
      · intro x hx
        have hx' := h x hx
        cases x <;>
          simp_all [isInput, IsAlternatingAndLeveledAt]

/- Dual of `isAlternatingAndLeveledAt_of_isOrOfInputsOnly` for DNF
   clauses: an `andGate lits` of plain `inputGate`s is
   `IsAlternatingAndLeveledAt` at any level. -/
theorem isAlternatingAndLeveledAt_of_isAndOfInputsOnly
    (g : UnboundedFanInFormula) (m : Nat)
    (h : Circuits.CnfDnf.isAndOfInputsOnly g = true) :
    IsAlternatingAndLeveledAt g m := by
  cases g with
  | inputGate _ _ => simp [Circuits.CnfDnf.isAndOfInputsOnly] at h
  | constant _ _ => simp [Circuits.CnfDnf.isAndOfInputsOnly] at h
  | notGate _ => simp [Circuits.CnfDnf.isAndOfInputsOnly] at h
  | orGate _ => simp [Circuits.CnfDnf.isAndOfInputsOnly] at h
  | andGate lits =>
      simp only [Circuits.CnfDnf.isAndOfInputsOnly, List.all_eq_true] at h
      simp only [IsAlternatingAndLeveledAt]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx _
        have hx' := h x hx
        cases x <;> simp_all [isInput]
      · intro x hx hand
        have hx' := h x hx
        cases x <;> simp_all [isInput, UnboundedFanInFormula.IsAndOr]
      · intro x hx
        have hx' := h x hx
        cases x <;>
          simp_all [isInput, IsAlternatingAndLeveledAt]

namespace Leveling

/- `IsProperlyLeveled` implies `IsAlternatingAndLeveledAt`: the
   first three conjuncts at each AND/OR node are exactly the
   alternation + level-step discipline, and the recursion descends with
   the same `lvl - 1` step. -/
mutual
theorem isProperlyLeveled_imp_strict :
    ∀ (f : UnboundedFanInFormula) (n : Nat),
      IsProperlyLeveled f n →
      IsAlternatingAndLeveledAt f n
  | .inputGate _ _, _, _ => by
      simp only [IsAlternatingAndLeveledAt]
  | .constant _ _, _, _ => by
      simp only [IsAlternatingAndLeveledAt]
  | .notGate _, _, h => by simp only [IsProperlyLeveled] at h
  | .andGate gates, n, h => by
      simp only [IsProperlyLeveled] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [IsAlternatingAndLeveledAt]
      refine ⟨h1, h2, ?_⟩
      by_cases hle : n ≤ 2
      · rw [if_pos hle] at h3
        simp only [Circuits.CnfDnf.IsProperCNF] at h3
        obtain ⟨hcnf, _, _⟩ := h3
        simp only [Circuits.CnfDnf.isCNF, List.all_eq_true] at hcnf
        intro g hg
        exact Circuits.isAlternatingAndLeveledAt_of_isOrOfInputsOnly g (n - 1) (hcnf g hg)
      · rw [if_neg hle] at h3
        exact isProperlyLeveled_imp_strict_list gates (n - 1) h3
  | .orGate gates, n, h => by
      simp only [IsProperlyLeveled] at h
      obtain ⟨h1, h2, h3⟩ := h
      simp only [IsAlternatingAndLeveledAt]
      refine ⟨h1, h2, ?_⟩
      by_cases hle : n ≤ 2
      · rw [if_pos hle] at h3
        simp only [Circuits.CnfDnf.IsProperDNF] at h3
        obtain ⟨hdnf, _, _⟩ := h3
        simp only [Circuits.CnfDnf.isDNF, List.all_eq_true] at hdnf
        intro g hg
        exact Circuits.isAlternatingAndLeveledAt_of_isAndOfInputsOnly g (n - 1) (hdnf g hg)
      · rw [if_neg hle] at h3
        exact isProperlyLeveled_imp_strict_list gates (n - 1) h3
theorem isProperlyLeveled_imp_strict_list :
    ∀ (gates : List UnboundedFanInFormula) (m : Nat),
      (∀ g ∈ gates, IsProperlyLeveled g m) →
      ∀ g ∈ gates, IsAlternatingAndLeveledAt g m
  | [], _, _ => by intro g hg; simp only [List.not_mem_nil] at hg
  | g0 :: gs, m, h => by
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl he => subst he; exact isProperlyLeveled_imp_strict x m (h x (by simp))
      | inr hmem =>
          exact isProperlyLeveled_imp_strict_list gs m
            (fun y hy => h y (by simp [hy])) x hmem
end

/- `IsProperlyLeveled` implies `HasProperBottomsAt`: at the bottom
   (`lvl ≤ 2`) the fourth conjunct supplies the proper-CNF/DNF shape,
   and above the bottom the recursion conjunct supplies the per-child
   obligation. -/
mutual
theorem isProperlyLeveled_imp_proper :
    ∀ (f : UnboundedFanInFormula) (n : Nat),
      IsProperlyLeveled f n → HasProperBottomsAt f n
  | .inputGate _ _, _, _ => by simp only [HasProperBottomsAt]
  | .constant _ _, _, _ => by simp only [HasProperBottomsAt]
  | .notGate _, _, h => by simp only [IsProperlyLeveled] at h
  | .andGate gates, n, h => by
      simp only [IsProperlyLeveled] at h
      obtain ⟨_, _, h3⟩ := h
      by_cases hle : n ≤ 2
      · rw [if_pos hle] at h3
        simp only [HasProperBottomsAt, if_pos hle]
        exact h3
      · rw [if_neg hle] at h3
        simp only [HasProperBottomsAt, if_neg hle]
        exact isProperlyLeveled_imp_proper_list gates (n - 1) h3
  | .orGate gates, n, h => by
      simp only [IsProperlyLeveled] at h
      obtain ⟨_, _, h3⟩ := h
      by_cases hle : n ≤ 2
      · rw [if_pos hle] at h3
        simp only [HasProperBottomsAt, if_pos hle]
        exact h3
      · rw [if_neg hle] at h3
        simp only [HasProperBottomsAt, if_neg hle]
        exact isProperlyLeveled_imp_proper_list gates (n - 1) h3
theorem isProperlyLeveled_imp_proper_list :
    ∀ (gates : List UnboundedFanInFormula) (m : Nat),
      (∀ g ∈ gates, IsProperlyLeveled g m) →
      ∀ g ∈ gates, HasProperBottomsAt g m
  | [], _, _ => by intro g hg; simp only [List.not_mem_nil] at hg
  | g0 :: gs, m, h => by
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl he => subst he; exact isProperlyLeveled_imp_proper x m (h x (by simp))
      | inr hmem =>
          exact isProperlyLeveled_imp_proper_list gs m
            (fun y hy => h y (by simp [hy])) x hmem
end

/- The converse fusion: `IsAlternatingAndLeveledAt f n` together with
   `HasProperBottomsAt f n` reconstitute `IsProperlyLeveled f n`.  This
   lets a subtype field carrying `IsProperlyLeveled` be constructed from
   the two separate predicates. -/
mutual
theorem isProperlyLeveled_of_strict_proper :
    ∀ (f : UnboundedFanInFormula) (n : Nat),
      IsAlternatingAndLeveledAt f n →
      HasProperBottomsAt f n → IsProperlyLeveled f n
  | .inputGate _ _, _, _, _ => by simp only [IsProperlyLeveled]
  | .constant _ _, _, _, _ => by simp only [IsProperlyLeveled]
  | .notGate _, _, hs, _ => by
      simp only [IsAlternatingAndLeveledAt] at hs
  | .andGate gates, n, hs, hp => by
      simp only [IsAlternatingAndLeveledAt] at hs
      obtain ⟨hs1, hs2, hs3⟩ := hs
      simp only [IsProperlyLeveled]
      refine ⟨hs1, hs2, ?_⟩
      by_cases hle : n ≤ 2
      · rw [if_pos hle]
        simp only [HasProperBottomsAt, if_pos hle] at hp
        exact hp
      · rw [if_neg hle]
        simp only [HasProperBottomsAt, if_neg hle] at hp
        exact isProperlyLeveled_of_strict_proper_list gates (n - 1) hs3 hp
  | .orGate gates, n, hs, hp => by
      simp only [IsAlternatingAndLeveledAt] at hs
      obtain ⟨hs1, hs2, hs3⟩ := hs
      simp only [IsProperlyLeveled]
      refine ⟨hs1, hs2, ?_⟩
      by_cases hle : n ≤ 2
      · rw [if_pos hle]
        simp only [HasProperBottomsAt, if_pos hle] at hp
        exact hp
      · rw [if_neg hle]
        simp only [HasProperBottomsAt, if_neg hle] at hp
        exact isProperlyLeveled_of_strict_proper_list gates (n - 1) hs3 hp
theorem isProperlyLeveled_of_strict_proper_list :
    ∀ (gates : List UnboundedFanInFormula) (m : Nat),
      (∀ g ∈ gates, IsAlternatingAndLeveledAt g m) →
      (∀ g ∈ gates, HasProperBottomsAt g m) →
      ∀ g ∈ gates, IsProperlyLeveled g m
  | [], _, _, _ => by intro g hg; simp only [List.not_mem_nil] at hg
  | g0 :: gs, m, hs, hp => by
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl he =>
          subst he
          exact isProperlyLeveled_of_strict_proper x m (hs x (by simp)) (hp x (by simp))
      | inr hmem =>
          exact isProperlyLeveled_of_strict_proper_list gs m
            (fun y hy => hs y (by simp [hy])) (fun y hy => hp y (by simp [hy])) x hmem
end

end Leveling

end Circuits
