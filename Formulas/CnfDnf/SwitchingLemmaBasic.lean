/-
  SwitchingLemmaBasic.lean — Common definitions for the switching lemma

  Contains the common building blocks used by the encoder and decoder:
  - DNF restriction primitives (`simpleRestrictLiteral`, `simpleRestrictTerm`,
    and `simpleRestrictDNF`)
  - Assignment construction (mkAssignment, mkAssignmentList)
  - Encoding primitives (encodeBaseW, decodeBaseW, encodeBits, decodeBits)
  - Clause operations (`isClauseKilled`, `restrictClauseByListAssignment`, and
    `firstTermNotKilledByList`)
  - Injection target set
  - Helper utilities (`allBitLists`, `combineRestrictions`, ...)
-/

import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import DecisionTrees.DecisionTree
import Formulas.CnfDnf.CnfDnfBasic
import Formulas.CnfDnf.CnfDnfFamilies
import Formulas.CnfDnf.RandomRestriction
import Lists.ListLemmas
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Circuits.CnfDnf.Restrictions
open Circuits.CnfDnf.Families
open DecisionTrees
open Lists.ListLemmas

section
set_option linter.style.setOption false
set_option linter.flexible false

-- ════════════════════════════════════════════════════════════════════════════
-- §1. DNF clause extraction and variable ordering
-- ════════════════════════════════════════════════════════════════════════════

/-- The variable query order of the canonical decision tree: clause-by-clause
    ordering using `dedupFirst` — all variables of clause 0 first, then new
    variables of clause 1, etc. This is the order used by the full-query
    canonical decision tree. -/
def canonicalDTVarOrder (dnf : UnboundedFanInFormula) : List Nat :=
  dedupFirst ((dnfClauses dnf).flatMap (fun c => c.map Prod.fst))

/-- The satisfying polarity for a literal (v, negated):
    - negated = false (positive xᵥ): true makes it true
    - negated = true (negated ¬xᵥ): false makes it true -/
def literalSatisfyingBit (negated : Bool) : Bool :=
  if negated then false else true

/-- Find the position of variable `v` in a clause (list of (var, negated) pairs).
    Returns the index of the first literal with first component `v`,
    or `clause.length` if `v` does not appear. -/
def findPositionInClause' (clause : List (Nat × Bool)) (v : Nat) : Nat :=
  match clause.findIdx? (fun lit => lit.1 == v) with
  | some i => i
  | none   => clause.length

def isClauseKilledBy (clause : List (Nat × Bool))
                     (asgn : List (Nat × Bool))
                     : Bool :=
  clause.any fun (v, neg) =>
    match asgn.find? (fun p => p.1 == v) with
    | none => false
    | some (_, b) => !(b == literalSatisfyingBit neg)

def firstTermNotKilledByList (clauses : List (List (Nat × Bool)))
                         (asgn : List (Nat × Bool))
                         : List (Nat × Bool) :=
  match clauses.findIdx? (fun c => !isClauseKilledBy c asgn) with
  | some i => clauses.getD i []
  | none => []

def restrictClauseByListAssignment (clause : List (Nat × Bool))
                   (asgn : List (Nat × Bool))
                   : List (Nat × Bool) :=
  if isClauseKilledBy clause asgn then
    []
  else
    clause.filter fun (v, _) => !asgn.any fun (w, _) => w == v

-- ════════════════════════════════════════════════════════════════════════════
-- §2. Restriction primitives
-- ════════════════════════════════════════════════════════════════════════════

/-- Restrict a single literal under an assignment.
    Live variables (assignment = none) are kept; dead variables become constants. -/
def simpleRestrictLiteral (asgn : Nat → Option Bool)
    (lit : UnboundedFanInFormula) : UnboundedFanInFormula :=
  match lit with
  | .inputGate i negated =>
    match asgn i with
    | none => .inputGate i negated
    | some b => .constant (if negated then Bool.not b else b) 0
  | c => c

/-- Restrict a term (AND of literals). Returns `none` if any literal evaluates to false
    (the term is killed). Otherwise returns the surviving (live) literals. -/
def simpleRestrictTerm (asgn : Nat → Option Bool)
    (term : UnboundedFanInFormula) : Option UnboundedFanInFormula :=
  match term with
  | .andGate lits =>
    let applied := lits.map (simpleRestrictLiteral asgn)
    if applied.any (fun l => match l with | .constant false _ => true | _ => false) then
      none
    else
      some (.andGate (applied.filter (fun l => match l with | .constant _ _ => false | _ => true)))
  | c => some c

def restrictionAsFunction (asgn : List (Nat × Bool)) : Nat → Option Bool :=
  fun v =>
    match asgn.find? (fun p => p.1 == v) with
    | some (_, b) => some b
    | none => none

/-- Restrict a DNF (OR of terms) under an assignment. Falsified terms are dropped. -/
def simpleRestrictDNF (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula) : UnboundedFanInFormula :=
  match dnf with
  | .orGate terms => .orGate (terms.filterMap (simpleRestrictTerm asgn))
  | c => c

-- ════════════════════════════════════════════════════════════════════════════
-- §3. Assignment construction
-- ════════════════════════════════════════════════════════════════════════════

/-- Build an assignment function from a live set and bit list:
    live variables get `none`, dead variable `i` gets its bit by rank among dead vars. -/
def mkAssignment (live : Finset Nat) (dead_bits : List Bool) : Nat → Option Bool :=
  fun i => if i ∈ live then none else dead_bits[((Finset.range i \ live).card)]?

/-- Build a list-based assignment from a live set and bit list.
    Returns `[(v₀, b₀), (v₁, b₁), ...]` for each dead variable `vᵢ < n`
    (in increasing order) paired with its bit from `dead_bits`. -/
def mkAssignmentList (live : Finset Nat) (dead_bits : List Bool) (n : Nat)
    : List (Nat × Bool) :=
  (List.range n).filterMap (fun v =>
    if v ∈ live then
      none
    else
      let j := (Finset.range v \ live).card
      match dead_bits[j]? with
        | some b => some (v, b)
        | none => none)

def restrictDNF (dnf : UnboundedFanInFormula)
                (ρ : AssignedRandomRestriction σ n) : UnboundedFanInFormula :=
  let asgn := mkAssignmentList ρ.starAssignment.val.val
                                 ρ.varAssignments
                                 n
  let asgn_fn := restrictionAsFunction asgn
  match dnf with
  | .orGate terms => .orGate (terms.filterMap (simpleRestrictTerm asgn_fn))
  | c => c

-- ════════════════════════════════════════════════════════════════════════════
-- §4. Mixed-radix and bit encoding/decoding
-- ════════════════════════════════════════════════════════════════════════════

/-- Mixed-radix encoding: encode a list of naturals in base `w`.
    `encodeBaseW [a₀, a₁, ..., a_{k-1}] w = a₀ + w·a₁ + w²·a₂ + ...` -/
def encodeBaseW : List Nat → Nat → Nat
  | [], _ => 0
  | a :: rest, w => a + w * encodeBaseW rest w

/-- The mixed-radix encoding is < w^k when all entries are < w. -/
lemma encodeBaseW_lt {l : List Nat} {w : Nat}
    (hbound : ∀ a ∈ l, a < w) :
    encodeBaseW l w < w ^ l.length := by
  induction l with
  | nil => simp [encodeBaseW]
  | cons a rest ih =>
    simp only [encodeBaseW, List.length_cons, pow_succ]
    have ha : a < w := hbound _ (List.mem_cons_self ..)
    have hrest : ∀ b ∈ rest, b < w := fun b hb => hbound b (List.mem_cons_of_mem _ hb)
    have hih := ih hrest
    nlinarith

/-- Mixed-radix decoding: decode a natural number to a list of `len` digits in base `w`.
    `decodeBaseW val w len = [val % w, (val / w) % w, ...]` (little-endian). -/
def decodeBaseW : Nat → Nat → Nat → List Nat
  | _, _, 0 => []
  | val, w, len + 1 => val % w :: decodeBaseW (val / w) w len

/-- `decodeBaseW` is a left inverse of `encodeBaseW` on lists with entries `< w`. -/
lemma decodeBaseW_encodeBaseW {l : List Nat} {w : Nat} (hw : 0 < w)
    (hbound : ∀ a ∈ l, a < w) :
    decodeBaseW (encodeBaseW l w) w l.length = l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [encodeBaseW, List.length_cons, decodeBaseW]
    have ha : a < w := hbound _ (List.mem_cons_self ..)
    have hrest : ∀ b ∈ rest, b < w := fun b hb => hbound b (List.mem_cons_of_mem _ hb)
    congr 1
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    · rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
      exact ih hrest

/-- Encode a bit list as a natural number (little-endian binary). -/
def encodeBits : List Bool → Nat
  | [] => 0
  | false :: rest => 2 * encodeBits rest
  | true :: rest => 1 + 2 * encodeBits rest

/-- The bit encoding is < 2^k for a list of length k. -/
lemma encodeBits_lt {l : List Bool} :
    encodeBits l < 2 ^ l.length := by
  induction l with
  | nil => simp [encodeBits]
  | cons b rest ih =>
    cases b <;> simp only [encodeBits, List.length_cons, pow_succ] <;> omega

/-- Decode a natural number to a bit list of given length (little-endian binary). -/
def decodeBits : Nat → Nat → List Bool
  | _, 0 => []
  | val, len + 1 =>
    (if val % 2 = 0 then false else true) :: decodeBits (val / 2) len

/-- `decodeBits` is a left inverse of `encodeBits`. -/
lemma decodeBits_encodeBits (l : List Bool) :
    decodeBits (encodeBits l) l.length = l := by
  induction l with
  | nil => rfl
  | cons b rest ih =>
    cases b <;> simp only [encodeBits, List.length_cons, decodeBits]
    · congr 1
      · simp [Nat.mul_mod_right]
      · rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]; exact ih
    · congr 1
      · simp [Nat.add_mul_mod_self_left]
      · rw [show (1 + 2 * encodeBits rest) / 2 = encodeBits rest from by omega]; exact ih

-- ════════════════════════════════════════════════════════════════════════════
-- §5. Clause operations and simplification
-- ════════════════════════════════════════════════════════════════════════════

/-- Map each literal `(v, neg)` to `(v, literalSatisfyingBit neg)`. -/
def gammaBitsForClause (clause : List (Nat × Bool))
                          : List (Nat × Bool) :=
  clause.map fun (v, neg) => (v, literalSatisfyingBit neg)

/-- `gammaBitsForClause` preserves first components. -/
lemma gamma_bits_map_fst_eq
    (clause : List (Nat × Bool)) :
    (gammaBitsForClause clause).map Prod.fst =
      clause.map Prod.fst := by
  simp [gammaBitsForClause, List.map_map, Function.comp]

/-- A clause is killed by an assignment if some literal evaluates to false. -/
def isClauseKilled
    (clause : List (Nat × Bool))
    (asgn : Nat → Option Bool) : Bool :=
  clause.any fun (v, neg) =>
    match asgn v with
    | none => false
    | some b => !(b == literalSatisfyingBit neg)

-- ════════════════════════════════════════════════════════════════════════════
-- §6. Assignment combination
-- ════════════════════════════════════════════════════════════════════════════

def combineRestrictions
    (base : List (Nat × Bool))
    (overrides : List (Nat × Bool))
    : List (Nat × Bool) :=
  -- overrides ++ base.filter fun (v, _) => !overrides.any fun (w, _) => w == v
  base ++ overrides.filter fun (v, _) => !base.any fun (w, _) => w == v

-- ════════════════════════════════════════════════════════════════════════════
-- §7. Injection target set
-- ════════════════════════════════════════════════════════════════════════════

/-- **Target set for the Razborov injection.**

    An element `(S', bit_idx, adv_idx)` represents:
    - `S'` : the reduced live set, an `(s−d)`-subset of `[n]`
    - `bit_idx` : an index in `[0, 2^(n−(s−d)))`, representing a dead-variable assignment
    - `adv_idx` : an index in `[0, (4w)^d)` encoding the position + direction + chunk boundary
      advice -/
def injectionTargetSet (n s d w : Nat) : Finset (Finset Nat × Nat × Nat) :=
  ((Finset.range n).powersetCard (s - d))
  ×ˢ (Finset.range (2 ^ (n - (s - d)))
  ×ˢ Finset.range ((4 * w) ^ d))

/-- The target set has cardinality `C(n, s−d) · (4w)^d · 2^(n−(s−d))`. -/
lemma injection_target_card (n s d w : Nat) :
    (injectionTargetSet n s d w).card =
      Nat.choose n (s - d) * (4 * w) ^ d * 2 ^ (n - (s - d)) := by
  simp only [injectionTargetSet, Finset.card_product, Finset.card_powersetCard,
    Finset.card_range, Finset.card_range]
  ring

-- ════════════════════════════════════════════════════════════════════════════
-- §8. Bool list enumeration
-- ════════════════════════════════════════════════════════════════════════════

/-- All bit lists of length k. -/
def allBitLists : (k : Nat) → List (List Bool)
  | 0 => [[]]
  | k + 1 => ((allBitLists k).map fun l => [false :: l, true :: l]).flatten

lemma allBitLists_length (k : Nat) :
    (allBitLists k).length = 2 ^ k := by
  induction k with
  | zero => simp [allBitLists]
  | succ k ih =>
    simp only [allBitLists]
    rw [List.length_flatten]
    have heq : (List.map (fun l => [false :: l, true :: l]) (allBitLists k)).map
        List.length = (allBitLists k).map (fun _ => 2) := by
      rw [List.map_map]; rfl
    rw [heq, List.map_const', List.sum_replicate, ih]
    ring

lemma allBitLists_mem_length (k : Nat) :
    ∀ l ∈ allBitLists k, l.length = k := by
  induction k with
  | zero =>
    simp [allBitLists]
  | succ k ih =>
    intro bits hbits
    simp only [allBitLists, List.mem_flatten, List.mem_map] at hbits
    obtain ⟨pair, ⟨l, hl_mem, rfl⟩, hbits_mem⟩ := hbits
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbits_mem
    rcases hbits_mem with rfl | rfl <;> simp [ih l hl_mem]

-- ════════════════════════════════════════════════════════════════════════════
-- §9. Helper lemmas
-- ════════════════════════════════════════════════════════════════════════════

/-- If `mkAssignment live bits v = none` and `v < n` and |live| + |bits| = n
    and live ⊆ range n, then `v ∈ live`. -/
lemma mkAssignment_none_imp_mem
    (live : Finset Nat) (bits : List Bool) (n : Nat)
    (hlive : live ⊆ Finset.range n) (hlen : live.card + bits.length = n)
    (v : Nat) (hv : v < n) (ha : mkAssignment live bits v = none) :
    v ∈ live := by
  simp only [mkAssignment] at ha
  split_ifs at ha with h
  · exact h
  · exfalso
    have hrank : (Finset.range v \ live).card < bits.length := by
      have hsub : Finset.range v \ live ⊂ Finset.range n \ live := by
        constructor
        · exact Finset.sdiff_subset_sdiff (Finset.range_mono (Nat.le_of_lt hv)) Finset.Subset.rfl
        · intro heq
          have : v ∈ Finset.range n \ live := by
            simp [Finset.mem_sdiff, Finset.mem_range, hv, h]
          have : v ∈ Finset.range v \ live := heq this
          simp [Finset.mem_sdiff, Finset.mem_range] at this
      have hcard_eq : (Finset.range n \ live).card = bits.length := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hlive, Finset.card_range]
        omega
      rw [← hcard_eq]; exact Finset.card_lt_card hsub
    exact Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp ha) hrank

/-- Elements of `mkAssignmentList` have first component not in `live`. -/
lemma mkAssignmentList_fst_notMem_live
    (live : Finset Nat) (dead_bits : List Bool) (n : Nat)
    (w : Nat) (b : Bool) (h : (w, b) ∈ mkAssignmentList live dead_bits n) :
    w ∉ live := by
  unfold mkAssignmentList at h
  rw [List.mem_filterMap] at h
  obtain ⟨i, _, hi⟩ := h
  by_cases hi_live : i ∈ live
  · rw [if_pos hi_live] at hi; simp at hi
  · rw [if_neg hi_live] at hi
    have hw_eq : w = i := by
      revert hi
      dsimp only
      cases dead_bits[((Finset.range i \ live).card)]? with
      | none => simp
      | some bv => intro hi; exact (Prod.mk.inj (Option.some.inj hi)).1.symm
    rw [hw_eq]; exact hi_live

/-- Extract the dead-variable bit values from an assignment, in rank order. -/
def extractDeadBits
    (B : Nat → Option Bool) (live : Finset Nat) (n : Nat) : List Bool :=
  (List.range n).filterMap (fun v => if v ∈ live then none else B v)

/-- Compute chunk-end bits: for each position in the flat list of chunks,
    the bit is `.one` if it's the last entry of its chunk, `.zero` otherwise. -/
def chunkEndBitsOfChunks {α : Type*} (chunks : List (List α)) : List Bool :=
  chunks.flatMap fun chunk =>
    List.replicate (chunk.length - 1) .false ++
      (if chunk.isEmpty then [] else [.true])

-- ════════════════════════════════════════════════════════════════════════════
-- §10. Sftnkb (simplified first term not killed by) positions
-- ════════════════════════════════════════════════════════════════════════════

/-- The list `any` check `asgn.any (fun (w, _) => w == v)` is equivalent to
    the function `restrictionAsFunction asgn v ≠ none`. -/
lemma list_any_eq_cr_none_isSome (asgn : List (Nat × Bool)) (v : Nat) :
    (asgn.any fun (w, _) => w == v) =
    (restrictionAsFunction asgn v).isSome := by
  simp only [restrictionAsFunction]
  induction asgn with
  | nil => simp [List.find?]
  | cons a rest ih =>
    simp only [List.any_cons, List.find?_cons]
    cases hbeq : (a.1 == v)
    · -- a.1 ≠ v
      simp only [Bool.false_or, ih]
    · -- a.1 == v
      simp only [Bool.true_or, Option.isSome]

/-- `restrictionAsFunction (mkAssignmentList S bits n)` agrees
    with `mkAssignment S bits` for `v < n`. -/
lemma cr_none_mkAssignmentList_eq
    (live : Finset Nat) (dead_bits : List Bool) (n : Nat)
    (v : Nat) (hv : v < n) :
    restrictionAsFunction
      (mkAssignmentList live dead_bits n) v =
    mkAssignment live dead_bits v := by
  by_cases hv_live : v ∈ live
  · -- v ∈ live: mkAssignment gives none
    simp only [mkAssignment, if_pos hv_live]
    have hany : (mkAssignmentList live dead_bits n).any (fun (w, _) => w == v) = false := by
      rw [List.any_eq_false]
      intro ⟨w, bw⟩ hmem
      simp only [beq_iff_eq]
      exact fun heq => absurd hv_live (heq ▸
        mkAssignmentList_fst_notMem_live live dead_bits n w bw hmem)
    rw [list_any_eq_cr_none_isSome] at hany
    simp at hany; exact hany
  · -- v ∉ live
    simp only [mkAssignment, if_neg hv_live]
    cases hget : dead_bits[((Finset.range v \ live).card)]? with
    | none =>
      have hany : (mkAssignmentList live dead_bits n).any (fun (w, _) => w == v) = false := by
        rw [List.any_eq_false]
        intro ⟨w, bw⟩ hmem
        simp only [beq_iff_eq]
        intro heq; rw [heq] at hmem
        unfold mkAssignmentList at hmem
        rw [List.mem_filterMap] at hmem
        obtain ⟨i, _, hi⟩ := hmem
        by_cases hi_live : i ∈ live
        · rw [if_pos hi_live] at hi; simp at hi
        · rw [if_neg hi_live] at hi
          have hvi : v = i := by
            revert hi
            dsimp only
            cases dead_bits[((Finset.range i \ live).card)]? with
            | none => simp
            | some bval => simp [Option.some.injEq, Prod.mk.injEq]; exact fun h _ => h.symm
          rw [hvi] at hget; revert hi; dsimp only; rw [hget]; simp
      rw [list_any_eq_cr_none_isSome] at hany
      simp at hany; exact hany
    | some b =>
      have hmem : (v, b) ∈ mkAssignmentList live dead_bits n := by
        unfold mkAssignmentList
        exact List.mem_filterMap.mpr ⟨v, List.mem_range.mpr hv, by
          rw [if_neg hv_live]; dsimp only; rw [hget]⟩
      unfold restrictionAsFunction
      match hf : (mkAssignmentList live dead_bits n).find? (fun p => p.1 == v) with
      | none =>
        exfalso
        exact List.find?_eq_none.mp hf (v, b) hmem (by simp)
      | some (w', b') =>
        have hprop := List.find?_some hf
        simp only [beq_iff_eq] at hprop
        have hmem' := List.mem_of_find?_eq_some hf
        rw [hprop] at hmem'
        unfold mkAssignmentList at hmem'
        rw [List.mem_filterMap] at hmem'
        obtain ⟨i, _, hi⟩ := hmem'
        by_cases hi_live : i ∈ live
        · rw [if_pos hi_live] at hi; simp at hi
        · rw [if_neg hi_live] at hi
          have hvi : v = i := by
            revert hi
            dsimp only
            cases dead_bits[((Finset.range i \ live).card)]? with
            | none => simp
            | some bval => simp [Option.some.injEq, Prod.mk.injEq]; exact fun h _ => h.symm
          rw [hvi] at hget
          have : b' = b := by
            revert hi
            dsimp only
            rw [hget]
            simp [Option.some.injEq, Prod.mk.injEq]
            exact fun _ h => h.symm
          subst this; rw [hf]

/-- `(!asgn.any …)` equals `(restrictionAsFunction asgn v == none)`. -/
lemma not_list_any_iff_cr_none_eq_none (asgn : List (Nat × Bool)) (v : Nat) :
    (!asgn.any fun (w, _) => w == v) =
    (restrictionAsFunction asgn v == none) := by
  rw [list_any_eq_cr_none_isSome]
  cases restrictionAsFunction asgn v with
  | none => simp
  | some _ => simp

/-- Killed clauses stay killed under any extension that agrees on already-set variables. -/
lemma killed_clause_stays_killed
    (clause : List (Nat × Bool))
    (A₁ A₂ : Nat → Option Bool)
    (hagree : ∀ w, A₁ w ≠ none → A₂ w = A₁ w)
    (hkill : isClauseKilled clause A₁ = true) :
    isClauseKilled clause A₂ = true := by
  simp only [isClauseKilled, List.any_eq_true] at hkill ⊢
  obtain ⟨⟨v, neg⟩, hmem, hlit⟩ := hkill
  refine ⟨⟨v, neg⟩, hmem, ?_⟩
  simp only at hlit ⊢
  cases h1 : A₁ v with
  | none => simp [h1] at hlit
  | some b =>
    have h2 : A₂ v = some b := by
      rw [hagree v (by simp [h1])]; exact h1
    rw [h2]; rw [h1] at hlit; exact hlit

lemma cr_none_combineRestrictions_extends_base (β dead : List (Nat × Bool)) (v : Nat)
    (h : restrictionAsFunction β v ≠ none) :
    restrictionAsFunction (combineRestrictions β dead) v =
    restrictionAsFunction β v := by
  simp only [combineRestrictions, restrictionAsFunction, List.find?_append]
  cases hβ : β.find? (fun p => p.1 == v) with
  | some val => simp
  | none =>
    exfalso
    apply h
    simp only [restrictionAsFunction]
    rw [hβ]

lemma not_killed_by_satisfying
    (clause : List (Nat × Bool))
    (asgn : Nat → Option Bool)
    (hsat : ∀ (p : Nat × Bool), p ∈ clause →
      asgn p.1 = none ∨ asgn p.1 = some (literalSatisfyingBit p.2)) :
    isClauseKilled clause asgn = false := by
  simp only [isClauseKilled]
  rw [List.any_eq_false]
  intro ⟨v, neg⟩ hmem
  simp only
  cases h : asgn v with
  | none => simp
  | some b =>
    have := hsat ⟨v, neg⟩ hmem
    cases this with
    | inl h' => simp [h'] at h
    | inr h' =>
      rw [h'] at h; obtain rfl := Option.some.inj h
      cases neg <;> simp [literalSatisfyingBit]

/-- If `overrides.map Prod.fst` has no duplicates and `(v, b) ∈ overrides`,
    then `find?` returns `(v, b)`. -/
lemma find?_eq_of_nodup_mem
    (overrides : List (Nat × Bool))
    (v : Nat) (b : Bool)
    (hnodup : (overrides.map Prod.fst).Nodup)
    (hmem : (v, b) ∈ overrides) :
    overrides.find? (fun p => p.1 == v) = some (v, b) := by
  induction overrides with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.find?_cons]
    cases hmem with
    | head =>
      simp
    | tail _ htl =>
      by_cases hfst : hd.1 == v
      · rw [beq_iff_eq] at hfst
        exfalso
        exact hnodup.1 (hfst ▸ List.mem_map_of_mem (f := Prod.fst) htl)
      · simp only [hfst]
        exact ih hnodup.2 htl

lemma findPositionInClause'_lt
    (clause : List (Nat × Bool)) (v : Nat)
    (hv : clause.any (fun lit => lit.1 == v) = true) :
    findPositionInClause' clause v < clause.length := by
  simp only [findPositionInClause']
  split
  case h_1 i h =>
    exact (List.findIdx?_eq_some_iff_getElem.mp h).1
  case h_2 h =>
    exfalso
    rw [List.any_eq_true] at hv
    obtain ⟨x, hmem, hlit⟩ := hv
    rw [List.findIdx?_eq_none_iff.mp h x hmem] at hlit
    exact absurd hlit (by decide)

/-- Position roundtrip: when `v` appears in `clause`, decoding the encoded
    position recovers `v`: `(clause.getD (findPositionInClause' clause v) default).1 = v`. -/
lemma findPositionInClause'_roundtrip
    (clause : List (Nat × Bool)) (v : Nat)
    (hv : clause.any (fun lit => lit.1 == v) = true) :
    (clause.getD (findPositionInClause' clause v) (0, false)).1 = v := by
  simp only [findPositionInClause']
  have his_some : (clause.findIdx? (fun lit => lit.1 == v)).isSome = true := by
    rw [List.findIdx?_isSome]; exact hv
  rw [Option.isSome_iff_exists] at his_some
  obtain ⟨p, hp⟩ := his_some
  rw [hp]; simp only
  rw [List.findIdx?_eq_some_iff_getElem] at hp
  obtain ⟨hp_lt, hp_pred, _⟩ := hp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_lt]; simp
  simp [BEq.beq] at hp_pred
  exact hp_pred

lemma extractDeadBits_succ
    (B : Nat → Option Bool) (live : Finset Nat) (n : Nat) :
    extractDeadBits B live (n + 1) =
      extractDeadBits B live n ++
        (if n ∈ live then [] else match B n with | none => [] | some b => [b]) := by
  simp only [extractDeadBits, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil]
  split <;> simp_all

lemma extractDeadBits_length
    (B : Nat → Option Bool) (live : Finset Nat) (n : Nat)
    (hlive : live ⊆ Finset.range n)
    (hdead : ∀ v, v < n → v ∉ live → B v ≠ none) :
    (extractDeadBits B live n).length = n - live.card := by
  unfold extractDeadBits
  induction n generalizing live with
  | zero =>
    simp only [List.range_zero, List.filterMap_nil, List.length_nil]
    have : live = ∅ := by
      ext x; constructor
      · intro hx; exact absurd (Finset.mem_range.mp (hlive hx)) (Nat.not_lt_zero x)
      · intro hx; simp at hx
    rw [this]; simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append,
        List.filterMap_cons, List.filterMap_nil]
    by_cases hn : n ∈ live
    · -- n ∈ live: filterMap [n] = [], length contribution = 0
      simp only [if_pos hn, List.length_nil, Nat.add_zero]
      set live' := live.erase n with hlive'_def
      have h_agree : ∀ v ∈ List.range n,
          (if v ∈ live then (none : Option Bool) else B v) =
          (if v ∈ live' then none else B v) := by
        intro v hv
        rw [List.mem_range] at hv
        have hv_ne : v ≠ n := Nat.ne_of_lt hv
        by_cases hv_live : v ∈ live
        · have : v ∈ live' := Finset.mem_erase.mpr ⟨hv_ne, hv_live⟩
          simp [hv_live, this]
        · have : v ∉ live' := fun h => hv_live (Finset.mem_of_mem_erase h)
          simp [hv_live, this]
      rw [List.filterMap_congr h_agree]
      have h_live'_sub : live' ⊆ Finset.range n := by
        intro x hx
        have ⟨hx_ne, hx_mem⟩ := Finset.mem_erase.mp hx
        have := hlive hx_mem
        rw [Finset.mem_range] at this ⊢
        omega
      have h_dead' : ∀ v, v < n → v ∉ live' → B v ≠ none := by
        intro v hv hnotmem
        apply hdead v (Nat.lt_succ_of_lt hv)
        intro hmem
        exact hnotmem (Finset.mem_erase.mpr ⟨Nat.ne_of_lt hv, hmem⟩)
      rw [ih live' h_live'_sub h_dead']
      have hcard_erase : live'.card = live.card - 1 := Finset.card_erase_of_mem hn
      have hcard_le : live.card ≤ n + 1 := by
        have := Finset.card_le_card hlive
        rw [Finset.card_range] at this
        exact this
      have hcard_pos : 0 < live.card := Finset.card_pos.mpr ⟨n, hn⟩
      omega
    · -- n ∉ live: filterMap [n] produces B n = some b, length contribution = 1
      simp only [if_neg hn]
      have h_bn : B n ≠ none := hdead n (Nat.lt_succ_iff.mpr le_rfl) hn
      cases h_bn_val : B n with
      | none => exact absurd h_bn_val h_bn
      | some b =>
        simp only [List.length_cons, List.length_nil]
        have h_live_sub_n : live ⊆ Finset.range n := by
          intro x hx
          have := hlive hx
          rw [Finset.mem_range] at this ⊢
          have : x ≠ n := fun h => hn (h ▸ hx)
          omega
        have h_dead_n : ∀ v, v < n → v ∉ live → B v ≠ none :=
          fun v hv => hdead v (Nat.lt_succ_of_lt hv)
        rw [ih live h_live_sub_n h_dead_n]
        have hcard_le : live.card ≤ n := by
          have := Finset.card_le_card h_live_sub_n
          rw [Finset.card_range] at this
          exact this
        omega

lemma extractDeadBits_getElem
    (B : Nat → Option Bool) (live : Finset Nat) (n : Nat)
    (hlive : live ⊆ Finset.range n)
    (h_b_none : ∀ v, v < n → (B v = none ↔ v ∈ live)) :
    ∀ v, v < n → v ∉ live →
      (extractDeadBits B live n)[(Finset.range v \ live).card]? = B v := by
  induction n generalizing live with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv hv_live
    rw [extractDeadBits_succ]
    by_cases hn_live : n ∈ live
    · simp only [if_pos hn_live, List.append_nil]
      have hv_lt_n : v < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | h
        · exact h
        · subst h; exact absurd hn_live hv_live
      set live' := live.erase n
      have hlive_eq : ∀ w, w < n → (w ∈ live ↔ w ∈ live') := by
        intro w hw; constructor
        · intro h; exact Finset.mem_erase.mpr ⟨Nat.ne_of_lt hw, h⟩
        · intro h; exact (Finset.mem_erase.mp h).2
      have h_eq_live' : extractDeadBits B live n = extractDeadBits B live' n := by
        simp only [extractDeadBits]; apply List.filterMap_congr
        intro w hw; rw [List.mem_range] at hw
        by_cases hw_live : w ∈ live
        · simp [hw_live, (hlive_eq w hw).mp hw_live]
        · have : w ∉ live' := fun h => hw_live ((hlive_eq w hw).mpr h)
          simp [hw_live, this]
      rw [h_eq_live']
      have hrank_eq : Finset.range v \ live = Finset.range v \ live' := by
        ext w; simp only [Finset.mem_sdiff, Finset.mem_range]; constructor
        · intro ⟨hw, hw_l⟩; exact ⟨hw, fun h => hw_l ((hlive_eq w (by omega)).mpr h)⟩
        · intro ⟨hw, hw_l'⟩; exact ⟨hw, fun h => hw_l' ((hlive_eq w (by omega)).mp h)⟩
      rw [hrank_eq]
      have h_live'_sub : live' ⊆ Finset.range n := by
        intro x hx; have ⟨hx_ne, hx_mem⟩ := Finset.mem_erase.mp hx
        have hx_succ := hlive hx_mem
        rw [Finset.mem_range] at hx_succ ⊢; omega
      have h_b_none' : ∀ w, w < n → (B w = none ↔ w ∈ live') := by
        intro w hw; constructor
        · intro habs; exact (hlive_eq w hw).mp ((h_b_none w (Nat.lt_succ_of_lt hw)).mp habs)
        · intro hmem; exact (h_b_none w (Nat.lt_succ_of_lt hw)).mpr ((hlive_eq w hw).mpr hmem)
      exact ih live' h_live'_sub h_b_none' v hv_lt_n
        (fun h => hv_live ((hlive_eq v hv_lt_n).mpr h))
    · have h_bn : B n ≠ none := by
        intro habs; exact hn_live ((h_b_none n (Nat.lt_succ_iff.mpr le_rfl)).mp habs)
      obtain ⟨b, h_bn_eq⟩ := Option.ne_none_iff_exists'.mp h_bn
      simp only [if_neg hn_live, h_bn_eq]
      have h_live_sub_n : live ⊆ Finset.range n := by
        intro x hx
        have hx_succ := hlive hx
        rw [Finset.mem_range] at hx_succ ⊢
        have hx_ne : x ≠ n := fun h => hn_live (h ▸ hx)
        omega
      have h_b_none_n : ∀ w, w < n → (B w = none ↔ w ∈ live) :=
        fun w hw => h_b_none w (Nat.lt_succ_of_lt hw)
      have hlen : (extractDeadBits B live n).length = n - live.card :=
        extractDeadBits_length B live n h_live_sub_n
          (fun w hw hw_live => by
            intro habs; exact hw_live ((h_b_none_n w hw).mp habs))
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv_lt_n | hv_eq_n
      · have hv_ssubset : Finset.range v \ live ⊂ Finset.range n \ live := by
          constructor
          · exact Finset.sdiff_subset_sdiff
              (Finset.range_mono (Nat.le_of_lt hv_lt_n)) Finset.Subset.rfl
          · intro heq
            have hv_in : v ∈ Finset.range n \ live :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hv_lt_n, hv_live⟩
            exact absurd
              (Finset.mem_range.mp (Finset.mem_sdiff.mp (heq hv_in)).1)
              (Nat.lt_irrefl v)
        have hrank_lt :
            (Finset.range v \ live).card <
              (extractDeadBits B live n).length := by
          calc (Finset.range v \ live).card
              < (Finset.range n \ live).card := Finset.card_lt_card hv_ssubset
            _ = n - live.card := by
                rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h_live_sub_n,
                    Finset.card_range]
            _ = _ := hlen.symm
        rw [List.getElem?_append_left hrank_lt]
        exact ih live h_live_sub_n h_b_none_n v hv_lt_n hv_live
      · subst hv_eq_n
        have hrank_v :
            (Finset.range v \ live).card =
              (extractDeadBits B live v).length := by
          rw [hlen, Finset.card_sdiff, Finset.inter_eq_left.mpr h_live_sub_n,
              Finset.card_range]
        rw [List.getElem?_append_right (by omega), hrank_v, Nat.sub_self]
        exact h_bn_eq.symm

lemma extractDeadBits_length_le
    (B : Nat → Option Bool) (live : Finset Nat) (n : Nat)
    (hlive : live ⊆ Finset.range n) :
    (extractDeadBits B live n).length ≤ n - live.card := by
  unfold extractDeadBits
  induction n generalizing live with
  | zero =>
    simp only [List.range_zero, List.filterMap_nil, List.length_nil]
    have : live = ∅ := by
      ext x; constructor
      · intro hx; exact absurd (Finset.mem_range.mp (hlive hx)) (Nat.not_lt_zero x)
      · intro hx; simp at hx
    rw [this]; simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append,
        List.filterMap_cons, List.filterMap_nil]
    by_cases hn : n ∈ live
    · simp only [if_pos hn, List.length_nil, Nat.add_zero]
      set live' := live.erase n with hlive'_def
      have h_agree : ∀ v ∈ List.range n,
          (if v ∈ live then (none : Option Bool) else B v) =
          (if v ∈ live' then none else B v) := by
        intro v hv
        rw [List.mem_range] at hv
        have hv_ne : v ≠ n := Nat.ne_of_lt hv
        by_cases hv_live : v ∈ live
        · have : v ∈ live' := Finset.mem_erase.mpr ⟨hv_ne, hv_live⟩
          simp [hv_live, this]
        · have : v ∉ live' := fun h => hv_live (Finset.mem_of_mem_erase h)
          simp [hv_live, this]
      rw [List.filterMap_congr h_agree]
      have h_live'_sub : live' ⊆ Finset.range n := by
        intro x hx
        have ⟨hx_ne, hx_mem⟩ := Finset.mem_erase.mp hx
        have := hlive hx_mem
        rw [Finset.mem_range] at this ⊢
        omega
      have hcard_erase : live'.card = live.card - 1 := Finset.card_erase_of_mem hn
      have hcard_le : live.card ≤ n + 1 := by
        have := Finset.card_le_card hlive
        rw [Finset.card_range] at this; exact this
      have hcard_pos : 0 < live.card := Finset.card_pos.mpr ⟨n, hn⟩
      have hih := ih live' h_live'_sub
      omega
    · simp only [if_neg hn]
      have h_live_sub_n : live ⊆ Finset.range n := by
        intro x hx
        have := hlive hx
        rw [Finset.mem_range] at this ⊢
        have : x ≠ n := fun h => hn (h ▸ hx)
        omega
      have hcard_le : live.card ≤ n := by
        have := Finset.card_le_card h_live_sub_n
        rw [Finset.card_range] at this; exact this
      cases h_bn : B n with
      | none =>
        simp only [List.length_nil, Nat.add_zero]
        have hih := ih live h_live_sub_n
        omega
      | some b =>
        simp only [List.length_cons, List.length_nil]
        have hih := ih live h_live_sub_n
        omega

lemma mkAssignment_extractDeadBits_eq
    (B : Nat → Option Bool) (live : Finset Nat) (n : Nat)
    (hlive : live ⊆ Finset.range n)
    (h_b_none : ∀ v, v < n → (B v = none ↔ v ∈ live)) :
    ∀ v, v < n →
      mkAssignment live (extractDeadBits B live n) v = B v := by
  intro v hv
  simp only [mkAssignment]
  by_cases hv_live : v ∈ live
  · simp only [if_pos hv_live]
    exact ((h_b_none v hv).mpr hv_live).symm
  · simp only [if_neg hv_live]
    exact extractDeadBits_getElem B live n hlive h_b_none v hv hv_live

lemma extractDeadBits_mkAssignment_eq
    (live : Finset Nat) (bits : List Bool) (n : Nat)
    (hlive : live ⊆ Finset.range n) (hlen : live.card + bits.length = n) :
    extractDeadBits (mkAssignment live bits) live n = bits := by
  simp only [extractDeadBits, mkAssignment]
  simp_rw [show ∀ v, (if v ∈ live then (none : Option Bool) else
    if v ∈ live then none else bits[((Finset.range v \ live).card)]?) =
    (if v ∈ live then none else bits[((Finset.range v \ live).card)]?) from
    fun v => by split_ifs <;> rfl]
  induction n generalizing live bits with
  | zero =>
    simp only [List.range_zero, List.filterMap_nil]
    have hlive_empty : live = ∅ := by
      simp only [Finset.range_zero] at hlive
      exact Finset.subset_empty.mp hlive
    rw [hlive_empty] at hlen; simp at hlen; exact hlen.symm
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    by_cases hm : m ∈ live
    · -- m ∈ live: filtered out
      simp only [if_pos hm, List.append_nil]
      set live' := live.erase m
      have hlive' : live' ⊆ Finset.range m := by
        intro x hx
        have ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
        exact Finset.mem_range.mpr (by
          have := Finset.mem_range.mp (hlive hmem); omega)
      have hlen' : live'.card + bits.length = m := by
        have h1 : live'.card = live.card - 1 := Finset.card_erase_of_mem hm
        have h2 : 1 ≤ live.card := Finset.one_le_card.mpr ⟨m, hm⟩
        omega
      have h_fm_eq_live : (List.range m).filterMap
          (fun v => if v ∈ live then none
            else bits[((Finset.range v \ live).card)]?) =
        (List.range m).filterMap
          (fun v => if v ∈ live' then none
            else bits[((Finset.range v \ live').card)]?) := by
        apply List.filterMap_congr
        intro v hv; rw [List.mem_range] at hv
        by_cases hv_live : v ∈ live
        · have hv_ne : v ≠ m := by omega
          simp [hv_live, show v ∈ live' from Finset.mem_erase.mpr ⟨hv_ne, hv_live⟩]
        · have hv_live' : v ∉ live' := fun h => hv_live (Finset.mem_of_mem_erase h)
          simp only [if_neg hv_live, if_neg hv_live']
          congr 2
          ext x
          constructor
          · intro hx
            have ⟨hxr, hxl⟩ := Finset.mem_sdiff.mp hx
            exact Finset.mem_sdiff.mpr ⟨hxr, fun h => hxl ((Finset.mem_erase.mp h).2)⟩
          · intro hx
            have ⟨hxr, hxl⟩ := Finset.mem_sdiff.mp hx
            refine Finset.mem_sdiff.mpr ⟨hxr, fun hxm => hxl (Finset.mem_erase.mpr ⟨?_, hxm⟩)⟩
            intro heq; rw [heq] at hxr
            exact Nat.lt_irrefl m (Nat.lt_trans (Finset.mem_range.mp hxr) hv)
      rw [h_fm_eq_live, ih live' bits hlive' hlen']
    · -- m ∉ live: contributes bits[rank(m)]
      simp only [if_neg hm]
      have hlive_sub_m : live ⊆ Finset.range m := by
        intro x hx
        have hne : x ≠ m := fun h => hm (h ▸ hx)
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hlive hx); omega)
      have hrank_eq : (Finset.range m \ live).card = m - live.card := by
        rw [Finset.card_sdiff_of_subset hlive_sub_m, Finset.card_range]
      have hrank_lt : (Finset.range m \ live).card < bits.length := by
        have : live.card ≤ m := by
          calc live.card ≤ (Finset.range m).card := Finset.card_le_card hlive_sub_m
          _ = m := Finset.card_range m
        omega
      rw [List.getElem?_eq_some_iff.mpr ⟨hrank_lt, rfl⟩]
      have hbits_ne : bits ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen
        have : live.card ≤ m := by
          calc live.card ≤ (Finset.range m).card := Finset.card_le_card hlive_sub_m
          _ = m := Finset.card_range m
        omega
      have hbits_pos : bits.length ≥ 1 := by
        cases bits with
        | nil => exact absurd rfl hbits_ne
        | cons _ _ => simp
      have hlen_dl : live.card + bits.dropLast.length = m := by
        rw [List.length_dropLast]; omega
      have h_fm_eq : (List.range m).filterMap
          (fun v => if v ∈ live then none
            else bits[((Finset.range v \ live).card)]?) =
        (List.range m).filterMap
          (fun v => if v ∈ live then none
            else bits.dropLast[((Finset.range v \ live).card)]?) := by
        apply List.filterMap_congr
        intro v hv; rw [List.mem_range] at hv
        by_cases hv_live : v ∈ live
        · simp [hv_live]
        · simp only [if_neg hv_live]
          have hv_rank_lt : (Finset.range v \ live).card < bits.length - 1 := by
            rw [List.length_dropLast] at *
            have : (Finset.range v \ live).card < (Finset.range m \ live).card := by
              apply Finset.card_lt_card
              exact ⟨Finset.sdiff_subset_sdiff (Finset.range_mono (by omega)) Finset.Subset.rfl,
                fun heq => by
                  have := heq (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hv, hv_live⟩)
                  simp [Finset.mem_sdiff, Finset.mem_range] at this⟩
            omega
          rw [List.getElem?_dropLast, if_pos hv_rank_lt]
      rw [h_fm_eq, ih live bits.dropLast hlive_sub_m hlen_dl]
      have hrank_last : (Finset.range m \ live).card = bits.length - 1 := by omega
      have hlast_eq : bits[(Finset.range m \ live).card] = bits.getLast hbits_ne := by
        rw [List.getLast_eq_getElem]; congr 1
      rw [hlast_eq, List.dropLast_append_getLast]

-- ════════════════════════════════════════════════════════════════════════════
-- §  Generic list / restriction / clause lemmas
-- ════════════════════════════════════════════════════════════════════════════

/-- `combineRestrictions` is associative when `a` and `b` have disjoint fst,
    and all of `a` and `b` are disjoint from `ρ`'s fst. -/
lemma combineRestrictions_append_eq_nested
    (ρ a b : List (Nat × Bool))
    (ha_disj_ρ : ∀ x ∈ a, (ρ.any fun (z, _) => z == x.1) = false)
    (hb_disj_ρ : ∀ x ∈ b, (ρ.any fun (z, _) => z == x.1) = false)
    (hb_disj_a : ∀ x ∈ b, (a.any fun (z, _) => z == x.1) = false) :
    combineRestrictions ρ (a ++ b) =
    combineRestrictions (combineRestrictions ρ a) b := by
  unfold combineRestrictions
  rw [List.filter_append]
  have ha_filt : a.filter (fun (v, _) => !ρ.any fun (w, _) => w == v) = a :=
    List.filter_eq_self.mpr fun ⟨v, bv⟩ hv => by
      simp only [Bool.not_eq_true']; exact ha_disj_ρ (v, bv) hv
  have hb_filt : b.filter (fun (v, _) => !ρ.any fun (w, _) => w == v) = b :=
    List.filter_eq_self.mpr fun ⟨v, bv⟩ hv => by
      simp only [Bool.not_eq_true']; exact hb_disj_ρ (v, bv) hv
  rw [ha_filt, hb_filt, List.append_assoc]
  have hb_filt2 : b.filter (fun x => !(ρ ++ a).any fun x_1 => x_1.1 == x.1) = b := by
    rw [List.filter_eq_self]; intro ⟨v, bv⟩ hv
    simp only [Bool.not_eq_true', List.any_append]
    rw [hb_disj_ρ (v, bv) hv, hb_disj_a (v, bv) hv]; simp
  rw [hb_filt2]

/-- Helper: `(mkAssignmentList S bits n).map Prod.fst` is `Nodup`.

    `mkAssignmentList` is a `filterMap` over `List.range n` whose output
    pairs always have first component equal to the iteration variable, so
    the result's first projection is a sublist of `List.range n`. -/
lemma mkAssignmentList_map_fst_nodup
    (S : Finset Nat) (bits : List Bool) (n : Nat) :
    ((mkAssignmentList S bits n).map Prod.fst).Nodup := by
  unfold mkAssignmentList
  rw [List.map_filterMap]
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro a₁ a₂ b h₁ h₂
  have key : ∀ a,
      b ∈ ((if a ∈ S then (none : Option (Nat × Bool))
        else match bits[((Finset.range a \ S).card)]? with
          | some bv => some (a, bv)
          | none => none).map Prod.fst) → b = a := by
    intro a h
    by_cases h_s : a ∈ S
    · simp [h_s] at h
    · simp only [if_neg h_s, Option.mem_def, Option.map_eq_some_iff] at h
      obtain ⟨val, hval, hsnd⟩ := h
      cases hgb : bits[((Finset.range a \ S).card)]? with
      | none => rw [hgb] at hval; simp at hval
      | some bv =>
        rw [hgb] at hval
        simp only [Option.some.injEq] at hval
        rw [← hval] at hsnd
        exact hsnd.symm
  exact (key a₁ h₁).symm.trans (key a₂ h₂)

end
end Circuits.CnfDnf.Restrictions
