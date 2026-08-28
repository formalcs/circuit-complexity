import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import DecisionTrees.DecisionTree
import Formulas.CnfDnf.CnfDnfBasic
import Formulas.CnfDnf.CnfDnfFamilies
import Formulas.CnfDnf.RandomRestriction
import Formulas.CnfDnf.SwitchingLemmaBasic

/-!
# Full-query canonical decision trees

Construction, correctness, path extraction, and path-decomposition lemmas
for the canonical decision trees used by the switching-lemma encoder and decoder.
-/

set_option linter.style.longLine false

namespace Circuits.CnfDnf.Restrictions
open Circuits.CnfDnf.Families
open DecisionTrees

def restrictionOfFirstTermNotKilledByList
    (clauses : List (List (Nat × Bool)))
    (asgn : List (Nat × Bool)) : List (Nat × Bool) :=
  restrictClauseByListAssignment (firstTermNotKilledByList clauses asgn) asgn

section


/-- A dead subtree that queries all remaining clause variables but always
    reaches a 0-leaf. Used by `clauseToPathTreeFull` to ensure every
    root-to-leaf path queries all clause variables, matching the Beame
    canonical DT construction. -/
def deadTree : List (Nat × Bool) → DecisionTree
  | [] => .dtLeaf .false
  | (v, _) :: rest => .dtNode v (deadTree rest) (deadTree rest)

/-- Build a full-query chain-shaped decision tree for a single clause.

    The non-satisfying branch at each literal leads to a `deadTree` that
    queries all remaining clause variables before reaching a false leaf.

    This ensures every root-to-leaf path queries ALL clause variables.
    The unique satisfying path reaches 1-leaf; all other paths reach 0-leaf
    after querying all remaining variables.

    This matches the Beame switching lemma canonical DT (Figure 1 in
    "A Switching Lemma Primer"), where the leftmost path through a clause
    always sets all clause variables before hitting 0 and being grafted
    to the next clause. -/
def clauseToPathTreeFull : List (Nat × Bool) → DecisionTree
  | [] => .dtLeaf .true
  | (v, neg) :: rest =>
      let sat := literalSatisfyingBit neg
      match sat with
      | .false =>
          .dtNode v (clauseToPathTreeFull rest) (deadTree rest)
      | .true  =>
          .dtNode v (deadTree rest) (clauseToPathTreeFull rest)


mutual
/-- Graft the remaining clauses onto false leaves of the full-query clause
    tree produced by `clauseToPathTreeFull`. -/
def graftOnZeroLeavesWithSimplificationFull :
    DecisionTree → List (List (Nat × Bool)) → Nat → DecisionTree
  | .dtLeaf .true, _, _ => .dtLeaf .true
  | .dtLeaf .false, clauses, fuel =>
      canonicalDecisionTreeAuxPreciseFull fuel clauses
  | .dtNode v l r, clauses, fuel =>
      .dtNode v
        (graftOnZeroLeavesWithSimplificationFull l
          (simplifyClausesLeft clauses v) fuel)
        (graftOnZeroLeavesWithSimplificationFull r
          (simplifyClausesRight clauses v) fuel)

/-- Full-query canonical DT: `canonicalDecisionTreeAuxPreciseFull` uses
    `clauseToPathTreeFull` so every root-to-leaf path queries ALL
    variables of each clause before moving to the next.

    This matches the Beame switching lemma canonical DT construction
    (Figure 1 in "A Switching Lemma Primer"). -/
def canonicalDecisionTreeAuxPreciseFull :
    Nat → List (List (Nat × Bool)) → DecisionTree
  | 0, _ => .dtLeaf .false
  | _, [] => .dtLeaf .false
  | fuel + 1, clause :: rest =>
      let clause_dt := clauseToPathTreeFull clause
      graftOnZeroLeavesWithSimplificationFull clause_dt rest fuel
end

/-- Full-query canonical DT with path-aware grafting (Beame-style).
    Every root-to-leaf path queries all variables of each clause it
    traverses, ensuring the Beame encoder property:
    "if π₁ ≠ π then π₁ sets all the variables in K". -/
def canonicalDecisionTree
    (dnf : UnboundedFanInFormula)
    (asgn : List (Nat × Bool))
    : DecisionTree :=
  let asgn_fn := restrictionAsFunction asgn
  let restricted := simpleRestrictDNF asgn_fn dnf
  let clauses := dnfClauses restricted
  canonicalDecisionTreeAuxPreciseFull clauses.length clauses

def properDNFCanonicalDecisionTree
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n) : DecisionTree :=
  let restricted := restrictDNF f.val ρ
  let clauses := dnfClauses restricted
  canonicalDecisionTreeAuxPreciseFull clauses.length clauses



-- ────────────────────────────────────────────────────────────────────────
-- §4b. Soundness of full-query canonical DT (Beame-style)
-- ────────────────────────────────────────────────────────────────────────

/-- `deadTree` always evaluates to 0. -/
private lemma deadTree_eval_zero
    (clause : List (Nat × Bool)) (inputs : List Bool) :
    evalDecisionTree (deadTree clause) inputs = .false := by
  induction clause with
  | nil => simp [deadTree, evalDecisionTree]
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    simp only [deadTree, evalDecisionTree]
    cases inputs[v]? with
    | none => rfl
    | some b => cases b <;> exact ih

/-- If `clauseToPathTreeFull clause` evaluates to 1, all literals are satisfied. -/
theorem clauseToPathTreeFull_sound
    (clause : List (Nat × Bool)) (inputs : List Bool) :
    evalDecisionTree (clauseToPathTreeFull clause) inputs = .true →
    evalClause inputs clause = .true := by
  induction clause with
  | nil => intro; rfl
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    intro h
    cases neg
    · simp only [clauseToPathTreeFull, literalSatisfyingBit, Bool.false_eq_true, ↓reduceIte] at h
      simp only [evalClause, evalLiteral, evalDecisionTree] at h ⊢
      cases hv : inputs[v]? with
      | none => simp [hv] at h
      | some val =>
        simp only [hv] at h ⊢
        cases val with
        | false => simp [deadTree_eval_zero] at h
        | true => simpa using ih h
    · simp only [clauseToPathTreeFull, literalSatisfyingBit, ↓reduceIte] at h
      simp only [evalClause, evalLiteral, evalDecisionTree] at h ⊢
      cases hv : inputs[v]? with
      | none => simp [hv] at h
      | some val =>
        simp only [hv] at h ⊢
        cases val with
        | false => simp only [Bool.not] at h ⊢; exact ih h
        | true => simp [deadTree_eval_zero] at h

/-- Grafting with path-aware simplification (full-query) is sound. -/
theorem graftOnZeroLeavesWithSimplificationFull_sound
    (tree : DecisionTree) :
    ∀ (clauses : List (List (Nat × Bool))) (fuel : Nat) (inputs : List Bool)
    (_ih_fuel : ∀ clauses' inputs',
      evalDecisionTree (canonicalDecisionTreeAuxPreciseFull fuel clauses') inputs' = .true →
      evalClauses inputs' clauses' = .true),
    evalDecisionTree (graftOnZeroLeavesWithSimplificationFull tree clauses fuel)
                       inputs = .true →
    evalDecisionTree tree inputs = .true ∨ evalClauses inputs clauses = .true := by
  induction tree with
  | dtLeaf b =>
    intro clauses fuel inputs _ih_fuel h
    cases b with
    | true => left; rfl
    | false =>
      right
      simp only [graftOnZeroLeavesWithSimplificationFull] at h
      exact _ih_fuel clauses inputs h
  | dtNode v l r ih_l ih_r =>
    intro clauses fuel inputs ih_fuel h
    simp only [graftOnZeroLeavesWithSimplificationFull] at h
    simp only [evalDecisionTree] at h ⊢
    cases hv : inputs[v]? with
    | none => simp [hv] at h
    | some b =>
      simp only [hv] at h ⊢
      cases b with
      | false =>
        have := ih_l (simplifyClausesLeft clauses v) fuel inputs ih_fuel h
        rcases this with h1 | h2
        · left; exact h1
        · right; rwa [evalClauses_simplify_left inputs clauses v
            (by exact hv)] at h2
      | true =>
        have := ih_r (simplifyClausesRight clauses v) fuel inputs ih_fuel h
        rcases this with h1 | h2
        · left; exact h1
        · right; rwa [evalClauses_simplify_right inputs clauses v
            (by exact hv)] at h2

/-- `canonicalDecisionTreeAuxPreciseFull` is sound. -/
theorem canonicalDecisionTreeAuxPreciseFull_sound
    (fuel : Nat) (clauses : List (List (Nat × Bool))) (inputs : List Bool) :
    evalDecisionTree (canonicalDecisionTreeAuxPreciseFull fuel clauses) inputs = .true →
    evalClauses inputs clauses = .true := by
  induction fuel generalizing clauses inputs with
  | zero =>
    simp [canonicalDecisionTreeAuxPreciseFull, evalDecisionTree]
  | succ n ih =>
    intro h
    match hcl : clauses with
    | [] =>
      simp [canonicalDecisionTreeAuxPreciseFull, evalDecisionTree] at h
    | clause :: rest =>
      simp only [canonicalDecisionTreeAuxPreciseFull] at h
      have hgraft := graftOnZeroLeavesWithSimplificationFull_sound
        (clauseToPathTreeFull clause) rest n inputs ih h
      simp only [evalClauses]
      rcases hgraft with h1 | h2
      · rw [clauseToPathTreeFull_sound clause inputs h1]
      · cases evalClause inputs clause with
        | true => rfl
        | false => exact h2

/-- **1-leaf preservation**: if the full-query canonical decision tree
    (Beame-style, grafting variant) evaluates to 1 on some input, then
    the clauses of the restricted DNF also evaluate to 1 on that input.
    No 1-leaf is unreachable—every 1-leaf witnesses a genuine satisfying
    assignment of some clause. -/
theorem canonicalDecisionTree_sound
    (dnf : UnboundedFanInFormula) (asgn : List (Nat × Bool)) (inputs : List Bool) :
    evalDecisionTree
      (canonicalDecisionTree dnf asgn) inputs = .true →
    evalClauses inputs
      (dnfClauses
        (simpleRestrictDNF (restrictionAsFunction asgn) dnf)) = .true := by
  intro h
  simp only [canonicalDecisionTree] at h
  exact canonicalDecisionTreeAuxPreciseFull_sound _ _ _ h

-- ────────────────────────────────────────────────────────────────────────
-- §4c. Completeness of full-query canonical DT (Beame-style)
-- ────────────────────────────────────────────────────────────────────────

/-- All variables in a clause are within bounds of the input list. -/
def ClauseVarsInBounds (clause : List (Nat × Bool)) (inputs : List Bool) : Prop :=
  ∀ lit ∈ clause, lit.1 < inputs.length

/-- All variables in all clauses are within bounds of the input list. -/
def ClausesVarsInBounds (clauses : List (List (Nat × Bool))) (inputs : List Bool) : Prop :=
  ∀ c ∈ clauses, ClauseVarsInBounds c inputs

private lemma clauseVarsInBounds_cons {l : Nat × Bool} {ls : List (Nat × Bool)}
    {inputs : List Bool} (h : ClauseVarsInBounds (l :: ls) inputs) :
    l.1 < inputs.length ∧ ClauseVarsInBounds ls inputs := by
  have h' : ∀ lit ∈ (l :: ls), lit.1 < inputs.length := h
  exact ⟨h' l (.head _), fun lit hlit => h' lit (.tail _ hlit)⟩

private lemma clausesVarsInBounds_cons {c : List (Nat × Bool)}
    {rest : List (List (Nat × Bool))} {inputs : List Bool}
    (h : ClausesVarsInBounds (c :: rest) inputs) :
    ClauseVarsInBounds c inputs ∧ ClausesVarsInBounds rest inputs := by
  have h' : ∀ c' ∈ (c :: rest), ClauseVarsInBounds c' inputs := h
  exact ⟨h' c (.head _), fun c' hc' => h' c' (.tail _ hc')⟩

private lemma clausesVarsInBounds_simplify_left
    {clauses : List (List (Nat × Bool))} {inputs : List Bool} {v : Nat}
    (h : ClausesVarsInBounds clauses inputs) :
    ClausesVarsInBounds (simplifyClausesLeft clauses v) inputs := by
  intro c hc lit hlit
  simp only [simplifyClausesLeft] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  have hc'_in := List.mem_of_mem_filter hc'_mem
  exact h c' hc'_in lit (List.mem_of_mem_filter hlit)

private lemma clausesVarsInBounds_simplify_right
    {clauses : List (List (Nat × Bool))} {inputs : List Bool} {v : Nat}
    (h : ClausesVarsInBounds clauses inputs) :
    ClausesVarsInBounds (simplifyClausesRight clauses v) inputs := by
  intro c hc lit hlit
  simp only [simplifyClausesRight] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  have hc'_in := List.mem_of_mem_filter hc'_mem
  exact h c' hc'_in lit (List.mem_of_mem_filter hlit)

/-- All queried variables in a decision tree are within bounds. -/
def TreeVarsInBounds : DecisionTree → List Bool → Prop
  | .dtLeaf _, _ => True
  | .dtNode v l r, inputs => v < inputs.length ∧
      TreeVarsInBounds l inputs ∧ TreeVarsInBounds r inputs

private lemma deadTree_vars_in_bounds
    (clause : List (Nat × Bool)) (inputs : List Bool)
    (h : ClauseVarsInBounds clause inputs) :
    TreeVarsInBounds (deadTree clause) inputs := by
  induction clause with
  | nil => simp [deadTree, TreeVarsInBounds]
  | cons lit rest ih =>
    have ⟨hv, hrest⟩ := clauseVarsInBounds_cons h
    unfold deadTree TreeVarsInBounds
    exact ⟨hv, ih hrest, ih hrest⟩

private lemma clauseToPathTreeFull_vars_in_bounds
    (clause : List (Nat × Bool)) (inputs : List Bool)
    (h : ClauseVarsInBounds clause inputs) :
    TreeVarsInBounds (clauseToPathTreeFull clause) inputs := by
  induction clause with
  | nil => simp [clauseToPathTreeFull, TreeVarsInBounds]
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    have ⟨hv, hrest⟩ := clauseVarsInBounds_cons h
    simp only [clauseToPathTreeFull]
    cases literalSatisfyingBit neg <;> unfold TreeVarsInBounds
    · -- false: left is recursive, right is dead
      exact ⟨hv, ih hrest, deadTree_vars_in_bounds rest inputs hrest⟩
    · -- true: left is dead, right is recursive
      exact ⟨hv, deadTree_vars_in_bounds rest inputs hrest, ih hrest⟩

/-- If all literals of a clause are satisfied and all variables are in bounds,
    `clauseToPathTreeFull` evaluates to 1. -/
theorem clauseToPathTreeFull_complete
    (clause : List (Nat × Bool)) (inputs : List Bool)
    (hbounds : ClauseVarsInBounds clause inputs) :
    evalClause inputs clause = .true →
    evalDecisionTree (clauseToPathTreeFull clause) inputs = .true := by
  induction clause with
  | nil => intro; simp [clauseToPathTreeFull, evalDecisionTree]
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    intro h
    have ⟨hv_bound, hrest_bounds⟩ := clauseVarsInBounds_cons hbounds
    have hv_some : ∃ val, inputs[v]? = some val := by
      exact ⟨inputs[v], List.getElem?_eq_getElem hv_bound⟩
    obtain ⟨val, hval⟩ := hv_some
    -- hval : inputs[v]? = some val
    cases neg
    · -- neg = false: literalSatisfyingBit false = one
      change evalDecisionTree
        (DecisionTree.dtNode v (deadTree rest) (clauseToPathTreeFull rest)) inputs = .true
      have hlit : evalLiteral inputs (v, false) = val := by
        simp [evalLiteral, hval]
      cases val with
      | false =>
        exfalso
        have : evalClause inputs ((v, false) :: rest) = false := by
          simp only [evalClause, hlit]
        rw [this] at h; exact absurd h (by simp)
      | true =>
        change evalDecisionTree
          (DecisionTree.dtNode v (deadTree rest) (clauseToPathTreeFull rest)) inputs = .true
        simp only [evalDecisionTree, hval]
        have : evalClause inputs ((v, false) :: rest) = evalClause inputs rest := by
          simp only [evalClause, hlit]
        rw [this] at h
        exact ih hrest_bounds h
    · -- neg = true: literalSatisfyingBit true = zero
      change evalDecisionTree
        (DecisionTree.dtNode v (clauseToPathTreeFull rest) (deadTree rest)) inputs = .true
      have hlit : evalLiteral inputs (v, true) = Bool.not val := by
        simp [evalLiteral, hval]
      cases val with
      | false =>
        change evalDecisionTree
          (DecisionTree.dtNode v (clauseToPathTreeFull rest) (deadTree rest)) inputs = .true
        simp only [evalDecisionTree, hval]
        have : evalClause inputs ((v, true) :: rest) = evalClause inputs rest := by
          simp only [evalClause, hlit, Bool.not]
        rw [this] at h
        exact ih hrest_bounds h
      | true =>
        exfalso
        have : evalClause inputs ((v, true) :: rest) = false := by
          simp only [evalClause, hlit, Bool.not]
        rw [this] at h; exact absurd h (by simp)

/-- Length of `simplifyClausesLeft` is ≤ input length. -/
private lemma simplifyClausesLeft_length_le
    (cls : List (List (Nat × Bool))) (v : Nat) :
    (simplifyClausesLeft cls v).length ≤ cls.length := by
  simp only [simplifyClausesLeft, List.length_map]
  exact List.length_filter_le _ _

/-- Length of `simplifyClausesRight` is ≤ input length. -/
private lemma simplifyClausesRight_length_le
    (cls : List (List (Nat × Bool))) (v : Nat) :
    (simplifyClausesRight cls v).length ≤ cls.length := by
  simp only [simplifyClausesRight, List.length_map]
  exact List.length_filter_le _ _

mutual
theorem graftOnZeroLeavesWithSimplificationFull_complete
    (tree : DecisionTree) (clauses : List (List (Nat × Bool)))
    (fuel : Nat) (inputs : List Bool)
    (hfuel : fuel ≥ clauses.length)
    (htree : TreeVarsInBounds tree inputs)
    (hclauses : ClausesVarsInBounds clauses inputs) :
    evalDecisionTree tree inputs = .true ∨ evalClauses inputs clauses = .true →
    evalDecisionTree
      (graftOnZeroLeavesWithSimplificationFull tree clauses fuel) inputs = .true := by
  intro h
  match tree with
  | .dtLeaf .true =>
    simp [graftOnZeroLeavesWithSimplificationFull, evalDecisionTree]
  | .dtLeaf .false =>
    rcases h with h1 | h2
    · simp [evalDecisionTree] at h1
    · simp only [graftOnZeroLeavesWithSimplificationFull]
      exact canonicalDecisionTreeAuxPreciseFull_complete fuel clauses inputs hfuel hclauses h2
  | .dtNode v l r =>
    have ⟨hv_bound, htl, htr⟩ := htree
    simp only [graftOnZeroLeavesWithSimplificationFull,
      evalDecisionTree]
    have hv_some := List.getElem?_eq_getElem hv_bound
    rw [hv_some]
    cases hval : inputs[v] with
    | false =>
      apply graftOnZeroLeavesWithSimplificationFull_complete
        l (simplifyClausesLeft clauses v) fuel inputs
        (Nat.le_trans (simplifyClausesLeft_length_le clauses v) hfuel)
        htl (clausesVarsInBounds_simplify_left hclauses)
      simp only [evalDecisionTree, hv_some, hval] at h
      rcases h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by rwa [evalClauses_simplify_left inputs clauses v
          (by simp [hv_some, hval])])
    | true =>
      apply graftOnZeroLeavesWithSimplificationFull_complete
        r (simplifyClausesRight clauses v) fuel inputs
        (Nat.le_trans (simplifyClausesRight_length_le clauses v) hfuel)
        htr (clausesVarsInBounds_simplify_right hclauses)
      simp only [evalDecisionTree, hv_some, hval] at h
      rcases h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by rwa [evalClauses_simplify_right inputs clauses v
          (by simp [hv_some, hval])])

theorem canonicalDecisionTreeAuxPreciseFull_complete
    (fuel : Nat) (clauses : List (List (Nat × Bool))) (inputs : List Bool)
    (hfuel : fuel ≥ clauses.length)
    (hclauses : ClausesVarsInBounds clauses inputs) :
    evalClauses inputs clauses = .true →
    evalDecisionTree (canonicalDecisionTreeAuxPreciseFull fuel clauses) inputs = .true := by
  match fuel, clauses with
  | 0, [] => intro h; simp [evalClauses] at h
  | 0, _ :: _ => intro; simp at hfuel
  | _ + 1, [] => intro h; simp [evalClauses] at h
  | fuel' + 1, clause :: rest =>
    intro h
    have ⟨hclause, hrest⟩ := clausesVarsInBounds_cons hclauses
    simp only [canonicalDecisionTreeAuxPreciseFull]
    have hfuel' : fuel' ≥ rest.length := by simp at hfuel; omega
    apply graftOnZeroLeavesWithSimplificationFull_complete
      (clauseToPathTreeFull clause) rest fuel' inputs hfuel'
      (clauseToPathTreeFull_vars_in_bounds clause inputs hclause) hrest
    simp only [evalClauses] at h
    cases hc : evalClause inputs clause with
    | true =>
      exact Or.inl (clauseToPathTreeFull_complete clause inputs hclause hc)
    | false =>
      simp only [hc] at h
      exact Or.inr h
end

/-- **Completeness (converse of soundness)**: if the clauses of the restricted
    DNF evaluate to 1 on some input, the full-query canonical decision tree
    also evaluates to 1 on that input. Together with soundness, this means
    the canonical DT computes the exact same Boolean function as the DNF. -/
theorem canonicalDecisionTree_complete
    (dnf : UnboundedFanInFormula) (asgn : List (Nat × Bool)) (inputs : List Bool)
    (hbounds : ClausesVarsInBounds
      (dnfClauses
        (simpleRestrictDNF (restrictionAsFunction asgn) dnf)) inputs) :
    evalClauses inputs
      (dnfClauses
        (simpleRestrictDNF (restrictionAsFunction asgn) dnf)) = .true →
    evalDecisionTree
      (canonicalDecisionTree dnf asgn) inputs = .true := by
  intro h
  simp only [canonicalDecisionTree]
  exact canonicalDecisionTreeAuxPreciseFull_complete _ _ _ (le_refl _) hbounds h

-- ════════════════════════════════════════════════════════════════════════════
-- §5. Path extraction
-- ════════════════════════════════════════════════════════════════════════════

/-- The leftmost root-to-leaf path in a decision tree (always goes left). -/
def leftmostPath : DecisionTree → List (Nat × Bool)
  | .dtLeaf _ => []
  | .dtNode v left _ => (v, .false) :: leftmostPath left

/-- The lexicographically leftmost root-to-leaf path of depth exceeding `d`.

    Returns `none` if no root-to-leaf path has length > `d` (i.e. the tree's
    depth is ≤ `d`). -/
def leftmostPathExceedingDepth :
    DecisionTree → Nat → Option (List (Nat × Bool))
  | .dtLeaf _, _ => none
  | .dtNode v left _, 0 =>
      some ((v, .false) :: leftmostPath left)
  | .dtNode v left right, d + 1 =>
      match leftmostPathExceedingDepth left d with
      | some path => some ((v, .false) :: path)
      | none =>
        match leftmostPathExceedingDepth right d with
        | some path => some ((v, .true) :: path)
        | none => none

/-- If `leftmostPathExceedingDepth dt d = none`, then the DT depth ≤ d. -/
lemma leftmostPathExceedingDepth_none_imp_depth_le
    (dt : DecisionTree) (d : Nat)
    (h : leftmostPathExceedingDepth dt d = none) :
    decisionTreeDepth dt ≤ d := by
  induction dt generalizing d with
  | dtLeaf _ => simp [decisionTreeDepth]
  | dtNode v left right ih_left ih_right =>
    simp only [decisionTreeDepth]
    cases d with
    | zero => simp [leftmostPathExceedingDepth] at h
    | succ d' =>
      simp only [leftmostPathExceedingDepth] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hnone_left
        split at h
        · exact absurd h (by simp)
        · rename_i hnone_right
          have hl := ih_left d' hnone_left
          have hr := ih_right d' hnone_right
          omega

/-- If the DT depth > d, then `leftmostPathExceedingDepth` returns `some`. -/
lemma leftmostPathExceedingDepth_depth_gt_imp_isSome
    (dt : DecisionTree) (d : Nat)
    (hdepth : decisionTreeDepth dt > d) :
    (leftmostPathExceedingDepth dt d).isSome = true := by
  by_contra h
  simp only [Bool.not_eq_true] at h
  have hnone : leftmostPathExceedingDepth dt d = none :=
    Option.not_isSome_iff_eq_none.mp (by simp [h])
  have := leftmostPathExceedingDepth_none_imp_depth_le dt d hnone
  omega

/-- When `leftmostPathExceedingDepth dt d = some path`, the path has length > d. -/
lemma leftmostPathExceedingDepth_some_path_length_gt
    (dt : DecisionTree) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth dt d = some path) :
    path.length > d := by
  induction dt generalizing d path with
  | dtLeaf _ => simp [leftmostPathExceedingDepth] at hpath
  | dtNode v left right ih_left ih_right =>
    cases d with
    | zero =>
      simp only [leftmostPathExceedingDepth] at hpath
      rw [Option.some.injEq] at hpath; subst hpath
      simp [List.length_cons]
    | succ d' =>
      simp only [leftmostPathExceedingDepth] at hpath
      split at hpath
      · rename_i lpath hlpath
        rw [Option.some.injEq] at hpath; subst hpath
        simp only [List.length_cons]
        have := ih_left d' lpath hlpath; omega
      · split at hpath
        · rename_i rpath hrpath
          rw [Option.some.injEq] at hpath; subst hpath
          simp only [List.length_cons]
          have := ih_right d' rpath hrpath; omega
        · exact absurd hpath (by simp)

-- ────────────────────────────────────────────────────────────────────────
-- §  Full-query tree depth and path properties
-- ────────────────────────────────────────────────────────────────────────


/-- `dnfClauses` for an `orGate` equals `gates.map extractAndLiterals`. -/
lemma dnfClauses_eq_extractAndLiterals (gates : List UnboundedFanInFormula) :
    dnfClauses (.orGate gates) = gates.map extractAndLiterals := by
  simp only [dnfClauses]
  rfl

/-- The restriction pipeline on a single term's literals produces a sublist
    of the original extractAndLiterals result. -/
private lemma restrict_lits_extract_sublist (asgn : Nat → Option Bool)
    (lits : List UnboundedFanInFormula) :
    List.Sublist
      (((lits.map (simpleRestrictLiteral asgn)).filter
        (fun l => match l with | .constant _ _ => false | _ => true)).filterMap
        (fun g => match g with | .inputGate i b => some (i, b) | _ => none))
      (lits.filterMap (fun g => match g with | .inputGate i b => some (i, b) | _ => none)) := by
  induction lits with
  | nil => exact List.Sublist.slnil
  | cons lit rest ih =>
    cases lit with
    | inputGate i b =>
      simp only [List.map_cons, simpleRestrictLiteral, List.filterMap_cons]
      cases h : asgn i with
      | none =>
        simp only [List.filter_cons]
        exact ih.cons_cons _
      | some v =>
        simp only [List.filter_cons]
        exact ih.cons _
    | constant b n =>
      simp only [List.map_cons, simpleRestrictLiteral, List.filter_cons, List.filterMap_cons]
      exact ih
    | notGate g =>
      simp only [List.map_cons, simpleRestrictLiteral, List.filter_cons, List.filterMap_cons]
      exact ih
    | andGate gs =>
      simp only [List.map_cons, simpleRestrictLiteral, List.filter_cons, List.filterMap_cons]
      exact ih
    | orGate gs =>
      simp only [List.map_cons, simpleRestrictLiteral, List.filter_cons, List.filterMap_cons]
      exact ih

/-- Restricting a DNF preserves clause variable Nodup. Each restricted clause
    is a filter of an original clause, hence a sublist. -/
lemma restrictDNF_preserves_clause_nodup
    (dnf : UnboundedFanInFormula) (asgn : Nat → Option Bool)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (c : List (Nat × Bool))
    (hc : c ∈ dnfClauses (simpleRestrictDNF asgn dnf)) :
    (c.map Prod.fst).Nodup := by
  cases dnf with
  | orGate terms =>
    simp only [simpleRestrictDNF, dnfClauses] at hc
    rw [List.mem_map] at hc
    obtain ⟨restricted_term, hrt_mem, rfl⟩ := hc
    rw [List.mem_filterMap] at hrt_mem
    obtain ⟨orig_term, horig_mem, hsome⟩ := hrt_mem
    rw [dnfClauses_eq_extractAndLiterals] at hnodup
    simp only [simpleRestrictTerm] at hsome
    split at hsome
    · rename_i lits
      split at hsome
      · simp at hsome
      · rw [Option.some.injEq] at hsome; subst hsome
        have horig_nd := hnodup (extractAndLiterals (.andGate lits))
          (by rw [List.mem_map]; exact ⟨.andGate lits, horig_mem, rfl⟩)
        simp only [extractAndLiterals] at horig_nd ⊢
        exact horig_nd.sublist (List.Sublist.map Prod.fst (restrict_lits_extract_sublist asgn lits))
    · rename_i h_not_and
      rw [Option.some.injEq] at hsome; subst hsome
      cases orig_term with
      | andGate lits => exact absurd rfl (h_not_and lits)
      | inputGate => simp
      | constant => simp
      | notGate => simp
      | orGate => simp
  | inputGate _ _ => simp [simpleRestrictDNF, dnfClauses] at hc
  | constant _ _ => simp [simpleRestrictDNF, dnfClauses] at hc
  | notGate _ => simp [simpleRestrictDNF, dnfClauses] at hc
  | andGate _ => simp [simpleRestrictDNF, dnfClauses] at hc

/-- Variables in `leftmostPath` are node variables of the DT. -/
private lemma leftmostPath_vars_in_dt
    (dt : DecisionTree) (v : Nat) (b : Bool)
    (hv : (v, b) ∈ leftmostPath dt) :
    v ∈ dtCollectInputIndices dt := by
  induction dt with
  | dtLeaf _ => simp [leftmostPath] at hv
  | dtNode w left _ ih =>
    simp only [leftmostPath, List.mem_cons] at hv
    rcases hv with ⟨rfl, _⟩ | hv_rest
    · simp [dtCollectInputIndices]
    · simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inr (ih hv_rest))

/-- Variables in a path from `leftmostPathExceedingDepth` are node variables. -/
private lemma leftmostPath_exceeding_vars_in_dt
    (dt : DecisionTree) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth dt d = some path)
    (v : Nat) (b : Bool) (hv : (v, b) ∈ path) :
    v ∈ dtCollectInputIndices dt := by
  induction dt generalizing d path with
  | dtLeaf _ => simp [leftmostPathExceedingDepth] at hpath
  | dtNode w left right ih_left ih_right =>
    cases d with
    | zero =>
      simp only [leftmostPathExceedingDepth] at hpath
      rw [Option.some.injEq] at hpath; subst hpath
      simp only [List.mem_cons] at hv
      rcases hv with ⟨rfl, _⟩ | hv_rest
      · simp [dtCollectInputIndices]
      · simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
        exact Or.inl (Or.inr (leftmostPath_vars_in_dt left v b hv_rest))
    | succ d' =>
      simp only [leftmostPathExceedingDepth] at hpath
      match hleft : leftmostPathExceedingDepth left d' with
      | some lpath =>
        rw [hleft] at hpath; rw [Option.some.injEq] at hpath; subst hpath
        simp only [List.mem_cons] at hv
        rcases hv with ⟨rfl, _⟩ | hv_rest
        · simp [dtCollectInputIndices]
        · simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
          exact Or.inl (Or.inr (ih_left d' lpath hleft hv_rest))
      | none =>
        rw [hleft] at hpath
        match hright : leftmostPathExceedingDepth right d' with
        | some rpath =>
          rw [hright] at hpath; rw [Option.some.injEq] at hpath; subst hpath
          simp only [List.mem_cons] at hv
          rcases hv with ⟨rfl, _⟩ | hv_rest
          · simp [dtCollectInputIndices]
          · simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
            exact Or.inr (ih_right d' rpath hright hv_rest)
        | none => rw [hright] at hpath; simp at hpath

/-- `leftmostPath` on a DT with disjoint paths has Nodup first projections. -/
private lemma leftmostPath_nodup_of_disjoint
    (dt : DecisionTree)
    (hdi : DTPathsVarDisjoint dt) :
    ((leftmostPath dt).map Prod.fst).Nodup := by
  induction dt with
  | dtLeaf _ => simp [leftmostPath]
  | dtNode v left _ ih =>
    obtain ⟨hv_nl, _, hdi_l, _⟩ := hdi
    simp only [leftmostPath, List.map_cons]
    exact List.Nodup.cons
      (fun hmem => hv_nl (by
        obtain ⟨⟨w, b⟩, hw_mem, rfl⟩ := List.mem_map.mp hmem
        exact leftmostPath_vars_in_dt left w b hw_mem))
      (ih hdi_l)

/-- `leftmostPathExceedingDepth` on a DT with disjoint paths returns a path
    with Nodup first projections. -/
lemma leftmostPathExceedingDepth_nodup_of_disjoint
    (dt : DecisionTree) (d : Nat)
    (hdi : DTPathsVarDisjoint dt)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth dt d = some path) :
    (path.map Prod.fst).Nodup := by
  induction dt generalizing d path with
  | dtLeaf _ => simp [leftmostPathExceedingDepth] at hpath
  | dtNode v left right ih_left ih_right =>
    obtain ⟨hv_nl, hv_nr, hdi_l, hdi_r⟩ := hdi
    cases d with
    | zero =>
      simp only [leftmostPathExceedingDepth] at hpath
      rw [Option.some.injEq] at hpath; subst hpath
      simp only [List.map_cons]
      exact List.Nodup.cons
        (fun hmem => hv_nl (by
          obtain ⟨⟨w, b⟩, hw_mem, rfl⟩ := List.mem_map.mp hmem
          exact leftmostPath_vars_in_dt left w b hw_mem))
        (leftmostPath_nodup_of_disjoint left hdi_l)
    | succ d' =>
      simp only [leftmostPathExceedingDepth] at hpath
      match hleft : leftmostPathExceedingDepth left d' with
      | some lpath =>
        rw [hleft] at hpath; rw [Option.some.injEq] at hpath; subst hpath
        simp only [List.map_cons]
        exact List.Nodup.cons
          (fun hmem => hv_nl (by
            obtain ⟨⟨w, b⟩, hw_mem, rfl⟩ := List.mem_map.mp hmem
            exact leftmostPath_exceeding_vars_in_dt left d' lpath hleft w b hw_mem))
          (ih_left d' hdi_l lpath hleft)
      | none =>
        rw [hleft] at hpath
        match hright : leftmostPathExceedingDepth right d' with
        | some rpath =>
          rw [hright] at hpath; rw [Option.some.injEq] at hpath; subst hpath
          simp only [List.map_cons]
          exact List.Nodup.cons
            (fun hmem => hv_nr (by
              obtain ⟨⟨w, b⟩, hw_mem, rfl⟩ := List.mem_map.mp hmem
              exact leftmostPath_exceeding_vars_in_dt right d' rpath hright w b hw_mem))
            (ih_right d' hdi_r rpath hright)
        | none => rw [hright] at hpath; simp at hpath

/-- Every variable in a `leftmostPathExceedingDepth` output path
    is a node variable of the decision tree. -/
lemma leftmostPathExceedingDepth_vars_in_collect
    (dt : DecisionTree) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth dt d = some path)
    (w : Nat) (b : Bool) (hw : (w, b) ∈ path) :
    w ∈ dtCollectInputIndices dt := by
  induction dt generalizing d path with
  | dtLeaf _ => simp [leftmostPathExceedingDepth] at hpath
  | dtNode v left right ih_left ih_right =>
    match d with
    | 0 =>
      simp only [leftmostPathExceedingDepth, Option.some.injEq] at hpath
      rw [← hpath] at hw
      simp only [List.mem_cons] at hw
      simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
      rcases hw with ⟨rfl, _⟩ | hmem
      · left; left; rfl
      · left; right
        -- (w, b) ∈ leftmostPath left → w ∈ dtCollectInputIndices left
        suffices ∀ (t : DecisionTree) (x : Nat),
            x ∈ (leftmostPath t).map Prod.fst →
            x ∈ dtCollectInputIndices t from this left w
          (List.mem_map_of_mem (f := Prod.fst) hmem)
        intro t x hx
        induction t with
        | dtLeaf _ => simp [leftmostPath] at hx
        | dtNode v' l _ ih_l _ =>
          simp only [leftmostPath, List.map_cons, List.mem_cons] at hx
          simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
          rcases hx with rfl | hx
          · left; left; rfl
          · left; right; exact ih_l hx
    | d' + 1 =>
      simp only [leftmostPathExceedingDepth] at hpath
      split at hpath
      · -- left branch succeeds
        rename_i hpath_left
        rw [Option.some.injEq] at hpath
        rw [← hpath] at hw
        simp only [List.mem_cons] at hw
        simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
        rcases hw with ⟨rfl, _⟩ | hmem
        · left; left; rfl
        · left; right; exact ih_left d' _ hpath_left hmem
      · -- left branch fails, try right
        rename_i hpath_left
        split at hpath
        · -- right branch succeeds
          rename_i hpath_right
          rw [Option.some.injEq] at hpath
          rw [← hpath] at hw
          simp only [List.mem_cons] at hw
          simp only [dtCollectInputIndices, List.mem_append, List.mem_singleton]
          rcases hw with ⟨rfl, _⟩ | hmem
          · left; left; rfl
          · right; exact ih_right d' _ hpath_right hmem
        · -- both fail
          simp at hpath

/-- Every variable in `canonicalDTVarOrder` of a well-formed DNF
    belongs to `ufiCollectInputIndices`, because `dnfClauses`
    extracts exactly the inputGate indices for a well-formed DNF. -/
lemma canonicalDTVarOrder_subset_inputs (dnf : UnboundedFanInFormula)
    (h : isDNF dnf = true) (v : Nat)
    (hv : v ∈ canonicalDTVarOrder dnf) :
    v ∈ ufiCollectInputIndices dnf := by
  simp only [canonicalDTVarOrder] at hv
  have hv' := mem_dedupFirst.mp hv
  rw [List.mem_flatMap] at hv'
  obtain ⟨clause, hc_mem, hv_in_clause⟩ := hv'
  rw [List.mem_map] at hv_in_clause
  obtain ⟨⟨idx, neg⟩, hlit, rfl⟩ := hv_in_clause
  -- After rfl: idx substituted for v, hlit : (v, neg) ∈ clause
  simp only [dnfClauses] at hc_mem
  match dnf, h with
  | .orGate gates, h =>
    rw [List.mem_map] at hc_mem
    obtain ⟨gate, hgate_mem, hgate_eq⟩ := hc_mem
    -- From isDNF, gate must be isAndOfInputsOnly
    have h_aoi : isAndOfInputsOnly gate = true := by
      simp only [isDNF, List.all_eq_true] at h; exact h gate hgate_mem
    -- Match on gate, carrying dependent hypotheses
    match gate, h_aoi, hgate_mem, hgate_eq with
    | .andGate lits, _, hgate_mem, hgate_eq =>
      -- hgate_eq : lits.filterMap ... = clause
      rw [← hgate_eq] at hlit
      rw [List.mem_filterMap] at hlit
      obtain ⟨lit, hlit_mem, hlit_eq⟩ := hlit
      match lit, hlit_eq with
      | .inputGate i b, hlit_eq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hlit_eq
        obtain ⟨rfl, rfl⟩ := hlit_eq
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        refine ⟨.andGate lits, hgate_mem, ?_⟩
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨_, hlit_mem, by simp [ufiCollectInputIndices]⟩
      | .constant _ _, hlit_eq => simp at hlit_eq
      | .notGate _, hlit_eq => simp at hlit_eq
      | .andGate _, hlit_eq => simp at hlit_eq
      | .orGate _, hlit_eq => simp at hlit_eq
    | .orGate _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi
    | .inputGate _ _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi
    | .constant _ _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi
    | .notGate _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi

/-- Variables in `canonicalDTVarOrder` of a restricted DNF must have `asgn v = none`.
    This follows from: the canonical var order is a subset of the input indices of the
    restricted DNF, and restriction preserves only live variables. -/
lemma canonicalDTVarOrder_asgn_none
    (dnf : UnboundedFanInFormula) (asgn : Nat → Option Bool)
    (hdnf : isDNF dnf = true) (v : Nat)
    (hv : v ∈ canonicalDTVarOrder (simpleRestrictDNF asgn dnf)) :
    asgn v = none := by
  have hinp := canonicalDTVarOrder_subset_inputs
    (simpleRestrictDNF asgn dnf)
    (restrictDNF_preserves_dnf asgn dnf hdnf)
    v hv
  exact restrictDNF_preserves_liveVars_in_assignment asgn dnf hdnf v hinp

-- ────────────────────────────────────────────────────────────────────────
-- §  Full-query DT: vars, disjoint paths, nodup, path_var_none
-- ────────────────────────────────────────────────────────────────────────

/-- Node variables of `deadTree clause` are clause variables. -/
lemma deadTree_vars_subset
    (clause : List (Nat × Bool)) (w : Nat)
    (hw : w ∈ dtCollectInputIndices (deadTree clause)) :
    w ∈ clause.map Prod.fst := by
  induction clause with
  | nil => simp [deadTree, dtCollectInputIndices] at hw
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    simp only [deadTree, dtCollectInputIndices] at hw
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false, List.map_cons] at hw ⊢
    rcases hw with (rfl | h) | h
    · exact Or.inl rfl
    · exact Or.inr (ih h)
    · exact Or.inr (ih h)

/-- Node variables of `clauseToPathTreeFull` are clause variables. -/
lemma clauseToPathTreeFull_vars_subset
    (clause : List (Nat × Bool)) (w : Nat)
    (hw : w ∈ dtCollectInputIndices (clauseToPathTreeFull clause)) :
    w ∈ clause.map Prod.fst := by
  induction clause with
  | nil => simp [clauseToPathTreeFull, dtCollectInputIndices] at hw
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    simp only [clauseToPathTreeFull] at hw
    split at hw <;> {
      simp only [dtCollectInputIndices, List.mem_append,
        List.mem_cons, List.mem_nil_iff, or_false,
        List.map_cons, List.mem_cons] at hw ⊢
      rcases hw with (rfl | h) | h
      · exact Or.inl rfl
      · exact Or.inr (by first | exact ih h | exact deadTree_vars_subset rest w h)
      · exact Or.inr (by first | exact ih h | exact deadTree_vars_subset rest w h)
    }

/-- `deadTree` has disjoint paths when the clause has nodup fst. -/
private lemma deadTree_disjoint
    (clause : List (Nat × Bool))
    (hnd : (clause.map Prod.fst).Nodup) :
    DTPathsVarDisjoint (deadTree clause) := by
  induction clause with
  | nil => exact trivial
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    have hnd_rest := (List.nodup_cons.mp hnd).2
    have hv_not := (List.nodup_cons.mp hnd).1
    simp only [deadTree, DTPathsVarDisjoint]
    exact ⟨fun h => hv_not (deadTree_vars_subset rest v h),
           fun h => hv_not (deadTree_vars_subset rest v h),
           ih hnd_rest, ih hnd_rest⟩

/-- `clauseToPathTreeFull` has disjoint paths when clause has nodup fst. -/
private lemma clauseToPathTreeFull_disjoint
    (clause : List (Nat × Bool))
    (hnd : (clause.map Prod.fst).Nodup) :
    DTPathsVarDisjoint (clauseToPathTreeFull clause) := by
  induction clause with
  | nil => exact trivial
  | cons lit rest ih =>
    have hnd_rest := (List.nodup_cons.mp hnd).2
    have hlit_not := (List.nodup_cons.mp hnd).1
    simp only [clauseToPathTreeFull]
    split
    · exact ⟨fun h => hlit_not (clauseToPathTreeFull_vars_subset rest lit.1 h),
             fun h => hlit_not (deadTree_vars_subset rest lit.1 h),
             ih hnd_rest, deadTree_disjoint rest hnd_rest⟩
    · exact ⟨fun h => hlit_not (deadTree_vars_subset rest lit.1 h),
             fun h => hlit_not (clauseToPathTreeFull_vars_subset rest lit.1 h),
             deadTree_disjoint rest hnd_rest, ih hnd_rest⟩

mutual
/-- Node vars of `graftOnZeroLeavesWithSimplificationFull` come from
    the base tree or the input clauses. -/
lemma graftOnZeroLeavesWithSimplificationFull_vars_in
    (base : DecisionTree) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (w : Nat)
    (hw : w ∈ dtCollectInputIndices
      (graftOnZeroLeavesWithSimplificationFull base clauses fuel)) :
    w ∈ dtCollectInputIndices base ∨ ∃ c ∈ clauses, w ∈ c.map Prod.fst := by
  match base with
  | .dtLeaf .true =>
    simp [graftOnZeroLeavesWithSimplificationFull, dtCollectInputIndices] at hw
  | .dtLeaf .false =>
    simp only [graftOnZeroLeavesWithSimplificationFull] at hw
    exact Or.inr (canonicalDecisionTreeAuxPreciseFull_vars_in fuel clauses w hw)
  | .dtNode v l r =>
    simp only [graftOnZeroLeavesWithSimplificationFull, dtCollectInputIndices,
      List.mem_append, List.mem_singleton] at hw
    rcases hw with (rfl | h) | h
    · exact Or.inl (by simp [dtCollectInputIndices])
    · rcases graftOnZeroLeavesWithSimplificationFull_vars_in
          l (simplifyClausesLeft clauses v) fuel w h with h_l | ⟨c, hc, hvar⟩
      · exact Or.inl (List.mem_append.mpr
            (Or.inl (List.mem_append.mpr (Or.inr h_l))))
      · obtain ⟨⟨_, neg⟩, hmem, rfl⟩ := List.mem_map.mp hvar
        obtain ⟨c_orig, hc_orig_in, hlit_in⟩ :=
          simplifyClausesLeft_vars_subset clauses v _ neg c hc hmem
        exact Or.inr ⟨c_orig, hc_orig_in, List.mem_map.mpr ⟨(_, neg), hlit_in, rfl⟩⟩
    · rcases graftOnZeroLeavesWithSimplificationFull_vars_in
          r (simplifyClausesRight clauses v) fuel w h with h_r | ⟨c, hc, hvar⟩
      · exact Or.inl (List.mem_append.mpr (Or.inr h_r))
      · obtain ⟨⟨_, neg⟩, hmem, rfl⟩ := List.mem_map.mp hvar
        obtain ⟨c_orig, hc_orig_in, hlit_in⟩ :=
          simplifyClausesRight_vars_subset clauses v _ neg c hc hmem
        exact Or.inr ⟨c_orig, hc_orig_in, List.mem_map.mpr ⟨(_, neg), hlit_in, rfl⟩⟩

/-- Node vars of `canonicalDecisionTreeAuxPreciseFull` come from clauses. -/
lemma canonicalDecisionTreeAuxPreciseFull_vars_in
    (fuel : Nat) (clauses : List (List (Nat × Bool)))
    (w : Nat)
    (hw : w ∈ dtCollectInputIndices
      (canonicalDecisionTreeAuxPreciseFull fuel clauses)) :
    ∃ c ∈ clauses, w ∈ c.map Prod.fst := by
  match fuel, clauses with
  | 0, _ => simp [canonicalDecisionTreeAuxPreciseFull, dtCollectInputIndices] at hw
  | _ + 1, [] => simp [canonicalDecisionTreeAuxPreciseFull, dtCollectInputIndices] at hw
  | fuel' + 1, clause :: rest =>
    simp only [canonicalDecisionTreeAuxPreciseFull] at hw
    rcases graftOnZeroLeavesWithSimplificationFull_vars_in
        (clauseToPathTreeFull clause) rest fuel' w hw with h_clause | h_rest
    · exact ⟨clause, List.mem_cons_self ..,
        clauseToPathTreeFull_vars_subset clause w h_clause⟩
    · obtain ⟨c, hc_mem, hc_var⟩ := h_rest
      exact ⟨c, List.mem_cons_of_mem _ hc_mem, hc_var⟩
end

mutual
/-- `graftOnZeroLeavesWithSimplificationFull` preserves disjointness. -/
lemma graftOnZeroLeavesWithSimplificationFull_disjoint
    (base : DecisionTree) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (hb : DTPathsVarDisjoint base)
    (hnodup : ∀ c ∈ clauses, (c.map Prod.fst).Nodup) :
    DTPathsVarDisjoint
      (graftOnZeroLeavesWithSimplificationFull base clauses fuel) := by
  match base with
  | .dtLeaf .true =>
    simp [graftOnZeroLeavesWithSimplificationFull, DTPathsVarDisjoint]
  | .dtLeaf .false =>
    simp only [graftOnZeroLeavesWithSimplificationFull]
    exact canonicalDecisionTreeAuxPreciseFull_disjoint fuel clauses hnodup
  | .dtNode v l r =>
    obtain ⟨hv_nl, hv_nr, hb_l, hb_r⟩ := hb
    simp only [graftOnZeroLeavesWithSimplificationFull, DTPathsVarDisjoint]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hmem
      rcases graftOnZeroLeavesWithSimplificationFull_vars_in
          l (simplifyClausesLeft clauses v) fuel v hmem with h_l | ⟨c, hc, hvar⟩
      · exact hv_nl h_l
      · exact simplifyClausesLeft_removes_var clauses v c hc hvar
    · intro hmem
      rcases graftOnZeroLeavesWithSimplificationFull_vars_in
          r (simplifyClausesRight clauses v) fuel v hmem with h_r | ⟨c, hc, hvar⟩
      · exact hv_nr h_r
      · exact simplifyClausesRight_removes_var clauses v c hc hvar
    · exact graftOnZeroLeavesWithSimplificationFull_disjoint
        l (simplifyClausesLeft clauses v) fuel hb_l
        (simplifyClausesLeft_preserves_nodup clauses v hnodup)
    · exact graftOnZeroLeavesWithSimplificationFull_disjoint
        r (simplifyClausesRight clauses v) fuel hb_r
        (simplifyClausesRight_preserves_nodup clauses v hnodup)

/-- `canonicalDecisionTreeAuxPreciseFull` has disjoint paths. -/
lemma canonicalDecisionTreeAuxPreciseFull_disjoint
    (fuel : Nat) (clauses : List (List (Nat × Bool)))
    (hnodup : ∀ c ∈ clauses, (c.map Prod.fst).Nodup) :
    DTPathsVarDisjoint (canonicalDecisionTreeAuxPreciseFull fuel clauses) := by
  match fuel, clauses with
  | 0, _ =>
    simp [canonicalDecisionTreeAuxPreciseFull, DTPathsVarDisjoint]
  | _ + 1, [] =>
    simp [canonicalDecisionTreeAuxPreciseFull, DTPathsVarDisjoint]
  | fuel' + 1, clause :: rest =>
    simp only [canonicalDecisionTreeAuxPreciseFull]
    exact graftOnZeroLeavesWithSimplificationFull_disjoint
      (clauseToPathTreeFull clause) rest fuel'
      (clauseToPathTreeFull_disjoint clause (hnodup clause (List.mem_cons_self ..)))
      (fun c hc => hnodup c (List.mem_cons_of_mem _ hc))
end

end

/-- Path variables in the full-query DT are not assigned by `asgn`. -/
lemma canonical_dt_path_var_none
    (dnf : UnboundedFanInFormula)
    (asgn : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf asgn)
      d = some path)
    (w : Nat) (b : Bool) (hw : (w, b) ∈ path) :
    (restrictionAsFunction asgn) w = none := by
  set asgn_fn := restrictionAsFunction asgn with hasgn_fn_def
  -- w is a node variable of the full-query DT
  have hw_in_dt := leftmostPathExceedingDepth_vars_in_collect
    (canonicalDecisionTree dnf asgn)
    d path hpath w b hw
  -- Unfold the full-query DT definition
  simp only [canonicalDecisionTree] at hw_in_dt
  set restricted := simpleRestrictDNF asgn_fn dnf
  set r_clauses := dnfClauses restricted
  -- w appears in some clause of the restricted DNF
  obtain ⟨c, hc_mem, hw_in_c⟩ :=
    canonicalDecisionTreeAuxPreciseFull_vars_in r_clauses.length r_clauses w hw_in_dt
  -- w ∈ canonicalDTVarOrder restricted
  have hw_in_order : w ∈ canonicalDTVarOrder restricted := by
    rw [canonicalDTVarOrder, mem_dedupFirst]
    exact List.mem_flatMap.mpr ⟨c, hc_mem, hw_in_c⟩
  -- canonicalDTVarOrder_asgn_none gives asgn_fn w = none
  exact canonicalDTVarOrder_asgn_none dnf asgn_fn hdnf w hw_in_order

/-- The full-query canonical DT has disjoint node variables on paths,
    so the leftmost path has nodup fst. -/
lemma canonical_dt_path_take_nodup_fst
    (dnf : UnboundedFanInFormula)
    (asgn : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf asgn)
      d = some path) :
    ((path.take d).map Prod.fst).Nodup := by
  have hdi := canonicalDecisionTreeAuxPreciseFull_disjoint
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) dnf)).length
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) dnf))
    (restrictDNF_preserves_clause_nodup dnf
      (restrictionAsFunction asgn) hnodup)
  have hpath_nodup := leftmostPathExceedingDepth_nodup_of_disjoint
    (canonicalDecisionTree dnf asgn)
    d hdi path hpath
  exact hpath_nodup.sublist (List.take_sublist d _ |>.map _)

/-- Strengthened version of `canonical_dt_path_take_nodup_fst`:
    the WHOLE path's `.map fst` is `Nodup`, not just the first `d` bits. -/
lemma canonical_dt_path_nodup_fst
    (dnf : UnboundedFanInFormula)
    (asgn : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf asgn)
      d = some path) :
    (path.map Prod.fst).Nodup := by
  have hdi := canonicalDecisionTreeAuxPreciseFull_disjoint
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) dnf)).length
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) dnf))
    (restrictDNF_preserves_clause_nodup dnf
      (restrictionAsFunction asgn) hnodup)
  exact leftmostPathExceedingDepth_nodup_of_disjoint
    (canonicalDecisionTree dnf asgn)
    d hdi path hpath

-- ════════════════════════════════════════════════════════════════════════════
-- §6. Path membership and prefix properties
-- ════════════════════════════════════════════════════════════════════════════

/-- A path through a decision tree: records the variable and direction
    (left = zero, right = one) at each internal node. -/
inductive IsPathIn : DecisionTree → List (Nat × Bool) → Prop where
  | leaf (b : Bool) : IsPathIn (.dtLeaf b) []
  | left (v : Nat) (l r : DecisionTree) (p : List (Nat × Bool))
      (hp : IsPathIn l p) : IsPathIn (.dtNode v l r) ((v, .false) :: p)
  | right (v : Nat) (l r : DecisionTree) (p : List (Nat × Bool))
      (hp : IsPathIn r p) : IsPathIn (.dtNode v l r) ((v, .true) :: p)

/-- `leftmostPath` produces a valid `IsPathIn` path. -/
lemma leftmostPath_isPathIn (dt : DecisionTree) :
    IsPathIn dt (leftmostPath dt) := by
  induction dt with
  | dtLeaf b => exact .leaf b
  | dtNode v left _ ih => exact .left v left _ _ ih

/-- `leftmostPathExceedingDepth` produces a valid `IsPathIn` path. -/
lemma leftmostPathExceedingDepth_isPathIn
    (dt : DecisionTree) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth dt d = some path) :
    IsPathIn dt path := by
  induction dt generalizing d path with
  | dtLeaf _ => simp [leftmostPathExceedingDepth] at hpath
  | dtNode v left right ih_left ih_right =>
    cases d with
    | zero =>
      simp only [leftmostPathExceedingDepth] at hpath
      rw [Option.some.injEq] at hpath; subst hpath
      exact .left v left right _ (leftmostPath_isPathIn left)
    | succ d' =>
      simp only [leftmostPathExceedingDepth] at hpath
      split at hpath
      · rename_i lpath hlpath
        rw [Option.some.injEq] at hpath; subst hpath
        exact .left v left right _ (ih_left d' lpath hlpath)
      · split at hpath
        · rename_i rpath hrpath
          rw [Option.some.injEq] at hpath; subst hpath
          exact .right v left right _ (ih_right d' rpath hrpath)
        · exact absurd hpath (by simp)

-- ────────────────────────────────────────────────────────────────────────
-- §6b. Prefix ordering: first clause vars are a prefix of any path
-- ────────────────────────────────────────────────────────────────────────

/-- Any path through a grafted `deadTree` has the clause variables as a prefix. -/
private lemma graft_deadTree_path_vars_prefix
    (clause : List (Nat × Bool)) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (path : List (Nat × Bool))
    (hp : IsPathIn (graftOnZeroLeavesWithSimplificationFull
      (deadTree clause) clauses fuel) path) :
    clause.map Prod.fst <+: path.map Prod.fst := by
  induction clause generalizing path clauses fuel with
  | nil => exact List.nil_prefix
  | cons lit rest ih =>
    cases lit with | mk w neg =>
    simp only [deadTree, graftOnZeroLeavesWithSimplificationFull] at hp
    cases hp with
    | left _ _ _ p' hp' =>
      simp only [List.map_cons]
      obtain ⟨t, ht⟩ := ih (simplifyClausesLeft clauses w) fuel p' hp'
      exact ⟨t, by simp [ht]⟩
    | right _ _ _ p' hp' =>
      simp only [List.map_cons]
      obtain ⟨t, ht⟩ := ih (simplifyClausesRight clauses w) fuel p' hp'
      exact ⟨t, by simp [ht]⟩

/-- Any path through a grafted `clauseToPathTreeFull` has the clause
    variables as a prefix. -/
private lemma graft_clauseToPathTreeFull_path_vars_prefix
    (clause : List (Nat × Bool)) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (path : List (Nat × Bool))
    (hp : IsPathIn (graftOnZeroLeavesWithSimplificationFull
      (clauseToPathTreeFull clause) clauses fuel) path) :
    clause.map Prod.fst <+: path.map Prod.fst := by
  induction clause generalizing path clauses fuel with
  | nil => exact List.nil_prefix
  | cons lit rest ih =>
    cases lit with | mk w neg =>
    simp only [clauseToPathTreeFull] at hp
    cases hsat : literalSatisfyingBit neg <;> simp only [hsat] at hp
    · simp only [graftOnZeroLeavesWithSimplificationFull] at hp
      cases hp with
      | left _ _ _ p' hp' =>
        simp only [List.map_cons]
        obtain ⟨t, ht⟩ := ih (simplifyClausesLeft clauses w) fuel p' hp'
        exact ⟨t, by simp [ht]⟩
      | right _ _ _ p' hp' =>
        simp only [List.map_cons]
        obtain ⟨t, ht⟩ := graft_deadTree_path_vars_prefix rest
            (simplifyClausesRight clauses w) fuel p' hp'
        exact ⟨t, by simp [ht]⟩
    · simp only [graftOnZeroLeavesWithSimplificationFull] at hp
      cases hp with
      | left _ _ _ p' hp' =>
        simp only [List.map_cons]
        obtain ⟨t, ht⟩ := graft_deadTree_path_vars_prefix rest
            (simplifyClausesLeft clauses w) fuel p' hp'
        exact ⟨t, by simp [ht]⟩
      | right _ _ _ p' hp' =>
        simp only [List.map_cons]
        obtain ⟨t, ht⟩ := ih (simplifyClausesRight clauses w) fuel p' hp'
        exact ⟨t, by simp [ht]⟩

/-- The first clause's variables form a prefix of any path through the
    full-query canonical DT. -/
theorem canonical_dt_first_clause_vars_prefix
    (clauses : List (List (Nat × Bool)))
    (hne : clauses ≠ [])
    (path : List (Nat × Bool))
    (hp : IsPathIn (canonicalDecisionTreeAuxPreciseFull clauses.length clauses) path) :
    (clauses.head hne).map Prod.fst <+: path.map Prod.fst := by
  match clauses, hne with
  | clause :: rest, _ =>
    simp only [List.head_cons, List.length_cons,
               canonicalDecisionTreeAuxPreciseFull] at hp ⊢
    exact graft_clauseToPathTreeFull_path_vars_prefix
      clause rest rest.length path hp

-- ════════════════════════════════════════════════════════════════════════════
-- §7. Path decomposition: splitting paths at clause boundaries
-- ════════════════════════════════════════════════════════════════════════════

/-- Iteratively simplify a clause list according to a path's bits.
    For each `(v, b)` in the path:
    - if `b = .zero`, apply `simplifyClausesLeft` (assign `v := 0`)
    - if `b = .one`, apply `simplifyClausesRight` (assign `v := 1`) -/
def simplifyClausesByPath
    (clauses : List (List (Nat × Bool)))
    (path : List (Nat × Bool)) : List (List (Nat × Bool)) :=
  match path with
  | [] => clauses
  | (v, .false) :: rest => simplifyClausesByPath (simplifyClausesLeft clauses v) rest
  | (v, .true) :: rest => simplifyClausesByPath (simplifyClausesRight clauses v) rest

/-- Each surviving clause in `simplifyClausesByPath clauses path` lifts to
    some original clause in `clauses` whose variable set covers it.

    *Why true*: each step of `simplifyClausesByPath` either drops a clause
    entirely or filters out a literal (whose variable matches the path bit).
    Filtering reduces the variable set; dropping removes the clause. So every
    surviving clause has a variable set that is a subset of some original
    clause's variable set. -/
lemma simplifyClausesByPath_head_lifts
    (clauses : List (List (Nat × Bool))) (path : List (Nat × Bool))
    (head : List (Nat × Bool))
    (hhead : head ∈ simplifyClausesByPath clauses path) :
    ∃ c ∈ clauses, head.map Prod.fst ⊆ c.map Prod.fst := by
  induction path generalizing clauses with
  | nil =>
    simp only [simplifyClausesByPath] at hhead
    exact ⟨head, hhead, fun _ h => h⟩
  | cons vb rest ih =>
    cases vb with
    | mk v b =>
      cases b with
      | false =>
        simp only [simplifyClausesByPath] at hhead
        obtain ⟨c', hc'_mem, hsub⟩ := ih (simplifyClausesLeft clauses v) hhead
        -- c' ∈ simplifyClausesLeft clauses v
        simp only [simplifyClausesLeft, List.mem_map, List.mem_filter] at hc'_mem
        obtain ⟨c, ⟨hc_mem, _⟩, hc'_eq⟩ := hc'_mem
        refine ⟨c, hc_mem, ?_⟩
        intro w hw
        have hw_c' : w ∈ c'.map Prod.fst := hsub hw
        rw [← hc'_eq] at hw_c'
        rw [List.mem_map] at hw_c' ⊢
        obtain ⟨lit, hlit_mem, hlit_eq⟩ := hw_c'
        rw [List.mem_filter] at hlit_mem
        exact ⟨lit, hlit_mem.1, hlit_eq⟩
      | true =>
        simp only [simplifyClausesByPath] at hhead
        obtain ⟨c', hc'_mem, hsub⟩ := ih (simplifyClausesRight clauses v) hhead
        simp only [simplifyClausesRight, List.mem_map, List.mem_filter] at hc'_mem
        obtain ⟨c, ⟨hc_mem, _⟩, hc'_eq⟩ := hc'_mem
        refine ⟨c, hc_mem, ?_⟩
        intro w hw
        have hw_c' : w ∈ c'.map Prod.fst := hsub hw
        rw [← hc'_eq] at hw_c'
        rw [List.mem_map] at hw_c' ⊢
        obtain ⟨lit, hlit_mem, hlit_eq⟩ := hw_c'
        rw [List.mem_filter] at hlit_mem
        exact ⟨lit, hlit_mem.1, hlit_eq⟩

/-- `simplifyClausesByPath` only filters clauses; the result has length
    ≤ original length. -/
lemma simplifyClausesByPath_length_le
    (clauses : List (List (Nat × Bool))) (path : List (Nat × Bool)) :
    (simplifyClausesByPath clauses path).length ≤ clauses.length := by
  induction path generalizing clauses with
  | nil => simp [simplifyClausesByPath]
  | cons vb rest ih =>
    cases vb with
    | mk v b =>
      cases b with
      | false =>
        simp only [simplifyClausesByPath]
        have h1 : (simplifyClausesLeft clauses v).length ≤ clauses.length := by
          simp only [simplifyClausesLeft, List.length_map]
          exact List.length_filter_le _ _
        exact (ih (simplifyClausesLeft clauses v)).trans h1
      | true =>
        simp only [simplifyClausesByPath]
        have h1 : (simplifyClausesRight clauses v).length ≤ clauses.length := by
          simp only [simplifyClausesRight, List.length_map]
          exact List.length_filter_le _ _
        exact (ih (simplifyClausesRight clauses v)).trans h1

/-- `simplifyClausesByPath` distributes over path concatenation. -/
lemma simplifyClausesByPath_append
    (clauses : List (List (Nat × Bool))) (p1 p2 : List (Nat × Bool)) :
    simplifyClausesByPath clauses (p1 ++ p2) =
    simplifyClausesByPath (simplifyClausesByPath clauses p1) p2 := by
  induction p1 generalizing clauses with
  | nil => rfl
  | cons vb rest ih =>
    obtain ⟨v, b⟩ := vb
    cases b with
    | false =>
      change simplifyClausesByPath clauses ((v, .false) :: (rest ++ p2)) =
           simplifyClausesByPath
             (simplifyClausesByPath clauses ((v, .false) :: rest)) p2
      simp only [simplifyClausesByPath]
      exact ih _
    | true =>
      change simplifyClausesByPath clauses ((v, .true) :: (rest ++ p2)) =
           simplifyClausesByPath
             (simplifyClausesByPath clauses ((v, .true) :: rest)) p2
      simp only [simplifyClausesByPath]
      exact ih _

/-! ### Restriction-as-list helpers

    These lemmas recast `simplifyClausesLeft/right/by_path` as the uniform list-level
    operation `restrictClauseList` parameterised by an `asgn : Nat → Option Bool`.
    These helpers feed the canonical-DT iter-split machinery and other
    restriction-based reasoning. -/

/-- Restrict a clause list by a functional assignment: drop killed clauses,
    remove assigned literals from survivors. -/
def restrictClauseList
    (clauses : List (List (Nat × Bool)))
    (asgn : Nat → Option Bool) : List (List (Nat × Bool)) :=
  clauses.filterMap (fun c =>
    if isClauseKilled c asgn then none
    else some (c.filter (fun p => asgn p.1 = none)))

lemma restrictClauseList_cons (c : List (Nat × Bool))
    (cs : List (List (Nat × Bool))) (asgn : Nat → Option Bool) :
    restrictClauseList (c :: cs) asgn =
    if isClauseKilled c asgn then restrictClauseList cs asgn
    else (c.filter (fun p => asgn p.1 = none)) :: restrictClauseList cs asgn := by
  unfold restrictClauseList
  simp only [List.filterMap_cons]
  cases isClauseKilled c asgn <;> simp

/-- Restricting by the trivial (all-none) assignment is the identity. -/
lemma restrictClauseList_none
    (l : List (List (Nat × Bool))) :
    restrictClauseList l (fun _ => none) = l := by
  induction l with
  | nil => simp [restrictClauseList]
  | cons c cs ih =>
    rw [restrictClauseList_cons]
    have : isClauseKilled c (fun _ => none) = false := by
      rw [isClauseKilled, List.any_eq_false]; intro ⟨v, neg⟩ _
      simp
    rw [if_neg (by rw [this]; simp)]
    have hfilt : c.filter (fun p : Nat × Bool => ((fun _ : Nat => @none Bool) p.1 = none)) = c := by
      apply List.filter_eq_self.mpr; intro _ _; simp
    rw [hfilt, ih]

lemma simplifyClausesLeft_cons' (c : List (List (Nat × Bool)))
    (hd : List (Nat × Bool)) (v : Nat) :
    simplifyClausesLeft (hd :: c) v =
    if hd.any (fun lit => lit.1 == v && !lit.2) then simplifyClausesLeft c v
    else (hd.filter (fun lit => !(lit.1 == v && lit.2))) ::
      simplifyClausesLeft c v := by
  unfold simplifyClausesLeft
  simp only [List.filter_cons]
  cases hd.any (fun lit => lit.1 == v && !lit.2) <;> simp [List.map_cons]

lemma simplifyClausesRight_cons' (c : List (List (Nat × Bool)))
    (hd : List (Nat × Bool)) (v : Nat) :
    simplifyClausesRight (hd :: c) v =
    if hd.any (fun lit => lit.1 == v && lit.2) then simplifyClausesRight c v
    else (hd.filter (fun lit => !(lit.1 == v && !lit.2))) ::
      simplifyClausesRight c v := by
  unfold simplifyClausesRight
  simp only [List.filter_cons]
  cases hd.any (fun lit => lit.1 == v && lit.2) <;> simp [List.map_cons]

/-- `simplifyClausesLeft` on a restricted list = restricting by extended assignment. -/
lemma simplifyClausesLeft_eq_restrict
    (l : List (List (Nat × Bool)))
    (asgn : Nat → Option Bool) (v : Nat) (hv : asgn v = none) :
    simplifyClausesLeft (restrictClauseList l asgn) v =
    restrictClauseList l (fun i => if i == v then some .false else asgn i) := by
  induction l with
  | nil => simp [restrictClauseList, simplifyClausesLeft]
  | cons c cs ih =>
    rw [restrictClauseList_cons c cs asgn,
        restrictClauseList_cons c cs (fun i => if i == v then some .false else asgn i)]
    by_cases hk : isClauseKilled c asgn = true
    · rw [if_pos hk]
      have hke : isClauseKilled c (fun i => if i == v then some false else asgn i) = true :=
        killed_clause_stays_killed c asgn _ (fun w hw => by
          by_cases hwv : w = v
          · subst hwv; exact absurd hv hw
          · simp [beq_iff_eq, hwv]) hk
      rw [if_pos hke]; exact ih
    · rw [if_neg hk]
      rw [simplifyClausesLeft_cons']
      by_cases hany : (c.filter fun p => asgn p.1 = none).any
          (fun lit => lit.1 == v && !lit.2) = true
      · rw [if_pos hany]
        have hv_false_in_c : (v, false) ∈ c := by
          rw [List.any_eq_true] at hany
          obtain ⟨⟨w, neg⟩, hmem, hlit⟩ := hany
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hlit
          obtain ⟨rfl, rfl⟩ := hlit
          exact (List.mem_filter.mp hmem).1
        have hke : isClauseKilled c (fun i => if i == v then some false else asgn i) = true := by
          rw [isClauseKilled, List.any_eq_true]
          exact ⟨(v, false), hv_false_in_c, by simp [literalSatisfyingBit]⟩
        rw [if_pos hke]; exact ih
      · rw [if_neg hany]
        have hno_v_false : ∀ neg, (v, neg) ∈ c → neg = true := by
          intro neg hmem
          by_contra hne; push Not at hne
          have : neg = false := by cases neg <;> simp_all
          subst this
          have hmf : (v, false) ∈ c.filter (fun p => asgn p.1 = none) :=
            List.mem_filter.mpr ⟨hmem, by simp [hv]⟩
          have : (c.filter fun p => asgn p.1 = none).any
              (fun lit => lit.1 == v && !lit.2) = true := by
            rw [List.any_eq_true]; exact ⟨(v, false), hmf, by simp⟩
          exact absurd this hany
        have hke : isClauseKilled c (fun i => if i == v then some false else asgn i) = false := by
          rw [Bool.eq_false_iff]; intro habs
          rw [isClauseKilled, List.any_eq_true] at habs
          obtain ⟨⟨w, neg⟩, hmem, hlit⟩ := habs
          by_cases hwv : w = v
          · subst hwv; have := hno_v_false neg hmem; subst this
            simp [literalSatisfyingBit] at hlit
          · simp only [beq_iff_eq, hwv, ↓reduceIte] at hlit
            have : isClauseKilled c asgn = true := by
              rw [isClauseKilled, List.any_eq_true]
              exact ⟨⟨w, neg⟩, hmem, by simpa using hlit⟩
            exact absurd this hk
        rw [if_neg (by rw [hke]; simp)]
        congr 1
        · rw [List.filter_filter]; apply List.filter_congr
          intro ⟨w, neg⟩ hmem; simp only [beq_iff_eq]
          by_cases hwv : w = v
          · subst hwv; have := hno_v_false neg hmem; subst this; simp [hv]
          · simp [hwv]

/-- `simplifyClausesRight` on a restricted list = restricting by extended assignment. -/
lemma simplifyClausesRight_eq_restrict
    (l : List (List (Nat × Bool)))
    (asgn : Nat → Option Bool) (v : Nat) (hv : asgn v = none) :
    simplifyClausesRight (restrictClauseList l asgn) v =
    restrictClauseList l (fun i => if i == v then some .true else asgn i) := by
  induction l with
  | nil => simp [restrictClauseList, simplifyClausesRight]
  | cons c cs ih =>
    rw [restrictClauseList_cons c cs asgn,
        restrictClauseList_cons c cs (fun i => if i == v then some .true else asgn i)]
    by_cases hk : isClauseKilled c asgn = true
    · rw [if_pos hk]
      have hke : isClauseKilled c (fun i => if i == v then some true else asgn i) = true :=
        killed_clause_stays_killed c asgn _ (fun w hw => by
          by_cases hwv : w = v
          · subst hwv; exact absurd hv hw
          · simp [beq_iff_eq, hwv]) hk
      rw [if_pos hke]; exact ih
    · rw [if_neg hk]
      rw [simplifyClausesRight_cons']
      by_cases hany : (c.filter fun p => asgn p.1 = none).any
          (fun lit => lit.1 == v && lit.2) = true
      · rw [if_pos hany]
        have hv_true_in_c : (v, true) ∈ c := by
          rw [List.any_eq_true] at hany
          obtain ⟨⟨w, neg⟩, hmem, hlit⟩ := hany
          simp only [Bool.and_eq_true, beq_iff_eq] at hlit
          obtain ⟨rfl, rfl⟩ := hlit
          exact (List.mem_filter.mp hmem).1
        have hke : isClauseKilled c (fun i => if i == v then some true else asgn i) = true := by
          rw [isClauseKilled, List.any_eq_true]
          exact ⟨(v, true), hv_true_in_c, by simp [literalSatisfyingBit]⟩
        rw [if_pos hke]; exact ih
      · rw [if_neg hany]
        have hno_v_true : ∀ neg, (v, neg) ∈ c → neg = false := by
          intro neg hmem
          by_contra hne; push Not at hne
          have : neg = true := by cases neg <;> simp_all
          subst this
          have hmf : (v, true) ∈ c.filter (fun p => asgn p.1 = none) :=
            List.mem_filter.mpr ⟨hmem, by simp [hv]⟩
          have : (c.filter fun p => asgn p.1 = none).any
              (fun lit => lit.1 == v && lit.2) = true := by
            rw [List.any_eq_true]; exact ⟨(v, true), hmf, by simp⟩
          exact absurd this hany
        have hke : isClauseKilled c (fun i => if i == v then some true else asgn i) = false := by
          rw [Bool.eq_false_iff]; intro habs
          rw [isClauseKilled, List.any_eq_true] at habs
          obtain ⟨⟨w, neg⟩, hmem, hlit⟩ := habs
          by_cases hwv : w = v
          · subst hwv; have := hno_v_true neg hmem; subst this
            simp [literalSatisfyingBit] at hlit
          · simp only [beq_iff_eq, hwv, ↓reduceIte] at hlit
            have : isClauseKilled c asgn = true := by
              rw [isClauseKilled, List.any_eq_true]
              exact ⟨⟨w, neg⟩, hmem, by simpa using hlit⟩
            exact absurd this hk
        rw [if_neg (by rw [hke]; simp)]
        congr 1
        · rw [List.filter_filter]; apply List.filter_congr
          intro ⟨w, neg⟩ hmem; simp only [beq_iff_eq]
          by_cases hwv : w = v
          · subst hwv; have := hno_v_true neg hmem; subst this; simp [hv]
          · simp [hwv]

/-- Convert a path to an assignment function by folding over the base. -/
def pathToAsgn (base : Nat → Option Bool) (path : List (Nat × Bool)) :
    Nat → Option Bool :=
  path.foldl (fun A (vd : Nat × Bool) => fun i => if i == vd.1 then some vd.2 else A i) base

lemma pathToAsgn_cons (base : Nat → Option Bool) (v : Nat) (b : Bool)
    (rest : List (Nat × Bool)) :
    pathToAsgn base ((v, b) :: rest) =
    pathToAsgn (fun i => if i == v then some b else base i) rest := rfl

/-- `pathToAsgn` returns the base for variables not in the path. -/
lemma pathToAsgn_notMem
    (base : Nat → Option Bool) (path : List (Nat × Bool)) (v : Nat)
    (hv : v ∉ path.map Prod.fst) :
    pathToAsgn base path v = base v := by
  induction path generalizing base with
  | nil => rfl
  | cons wb rest ih =>
    obtain ⟨w, b⟩ := wb
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    rw [pathToAsgn_cons, ih _ hv.2]
    simp only [beq_iff_eq, ite_eq_right_iff]
    exact fun h => absurd h hv.1

/-- `pathToAsgn` assigns the given value for members (with nodup). -/
lemma pathToAsgn_mem
    (base : Nat → Option Bool) (path : List (Nat × Bool)) (v : Nat) (b : Bool)
    (hmem : (v, b) ∈ path) (hnodup : (path.map Prod.fst).Nodup) :
    pathToAsgn base path v = some b := by
  induction path generalizing base with
  | nil => simp at hmem
  | cons wb rest ih =>
    obtain ⟨w, bw⟩ := wb
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rw [pathToAsgn_cons]
    rcases List.mem_cons.mp hmem with heq | hmem_rest
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [pathToAsgn_notMem _ rest v hnodup.1]
      simp
    · exact ih _ hmem_rest hnodup.2

/-- `simplifyClausesByPath` on a restricted clause list equals
    restricting by the path-extended assignment.
    Requires that all path variables are unassigned under the base
    and that path variable names are distinct. -/
lemma simplifyClausesByPath_eq_restrict
    (l : List (List (Nat × Bool)))
    (asgn : Nat → Option Bool) (path : List (Nat × Bool))
    (hpath_none : ∀ vb ∈ path, asgn vb.1 = none)
    (hpath_nodup : (path.map Prod.fst).Nodup) :
    simplifyClausesByPath (restrictClauseList l asgn) path =
    restrictClauseList l (pathToAsgn asgn path) := by
  induction path generalizing asgn l with
  | nil => simp [simplifyClausesByPath, pathToAsgn]
  | cons vb rest ih =>
    obtain ⟨v, b⟩ := vb
    have hv_none : asgn v = none := hpath_none (v, b) (.head _)
    simp only [List.map_cons] at hpath_nodup
    have hv_not_rest : v ∉ rest.map Prod.fst := by
      rw [List.nodup_cons] at hpath_nodup; exact hpath_nodup.1
    have hrest_nodup : (rest.map Prod.fst).Nodup := by
      rw [List.nodup_cons] at hpath_nodup; exact hpath_nodup.2
    have hrest_none : ∀ vb' ∈ rest,
        (fun i => if i == v then some b else asgn i) vb'.1 = none := by
      intro ⟨w, bw⟩ hw
      have hwv : w ≠ v := by
        intro heq
        have : w ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(w, bw), hw, rfl⟩
        rw [heq] at this
        exact hv_not_rest this
      simp only [beq_iff_eq, hwv, ↓reduceIte]
      exact hpath_none (w, bw) (.tail _ hw)
    cases b with
    | false =>
      simp only [simplifyClausesByPath, pathToAsgn_cons]
      rw [simplifyClausesLeft_eq_restrict l asgn v hv_none]
      exact ih l (fun i => if i == v then some .false else asgn i) hrest_none hrest_nodup
    | true =>
      simp only [simplifyClausesByPath, pathToAsgn_cons]
      rw [simplifyClausesRight_eq_restrict l asgn v hv_none]
      exact ih l (fun i => if i == v then some .true else asgn i) hrest_none hrest_nodup

/-- **Bridge lemma**: `simplifyClausesByPath l pre` equals `restrictClauseList l A`
    where `A = pathToAsgn (fun _ => none) pre` assigns each path variable to its bit.

    This is an immediate corollary of `simplifyClausesByPath_eq_restrict`
    with the trivial base assignment, using `restrictClauseList_none`. -/
lemma simplifyClausesByPath_as_restrict
    (l : List (List (Nat × Bool))) (pre : List (Nat × Bool))
    (hnodup : (pre.map Prod.fst).Nodup) :
    simplifyClausesByPath l pre =
    restrictClauseList l (pathToAsgn (fun _ => none) pre) := by
  conv_lhs => rw [← restrictClauseList_none l]
  exact simplifyClausesByPath_eq_restrict l (fun _ => none) pre
    (fun _ _ => rfl) hnodup

#print axioms simplifyClausesByPath_as_restrict

/-- If `head` is killed by `pre`, then `simplifyClausesByPath` drops it
    and the result on `head :: rest` agrees with the result on `rest`. -/
lemma simplifyClausesByPath_killed_head
    (head : List (Nat × Bool)) (rest : List (List (Nat × Bool)))
    (pre : List (Nat × Bool))
    (hnodup : (pre.map Prod.fst).Nodup)
    (hkill : isClauseKilled head (pathToAsgn (fun _ => none) pre) = true) :
    simplifyClausesByPath (head :: rest) pre =
    simplifyClausesByPath rest pre := by
  rw [simplifyClausesByPath_as_restrict (head :: rest) pre hnodup,
      simplifyClausesByPath_as_restrict rest pre hnodup,
      restrictClauseList_cons, if_pos hkill]

/- **Truncated iter-split uniqueness**: agreement on leading prefixes.

    Without any non-emptiness hypothesis, two iter-splits of the same
    `path` (with the same clauses, segment provenance, and variable-map
    invariants) agree on
    `take k` for any `k` bounded by both lengths.

    Proof outline (induction on `k`):
    * `k = 0`: both `take 0 = []`.
    * `k → k+1`: by IH, cumulative bits at index `k` agree.
      Then segment provenance at `k` gives `segs1[k].2 = segs2[k].2`
      (heads of the same `simplifyClausesByPath` list).  The variable-map
      invariant then gives
      length agreement on `.1`.  Splitting `path = cum_k ++ s.1 ++ rest`
      via `List.take_append_drop` and `List.append_cancel_left` leaves
      `s1.1 ++ rest1 = s2.1 ++ rest2` with `|s1.1| = |s2.1|`, so
      `s1.1 = s2.1` by `List.append_inj_left`.

    This remains valid with trailing degenerate `([], [])` segments,
    which can occur when the canonical-DT path terminates at a one-leaf. -/
lemma iter_split_first_k_eq
    (clauses : List (List (Nat × Bool)))
    (path : List (Nat × Bool))
    (segs1 segs2 : List (List (Nat × Bool) × List (Nat × Bool)))
    (hpath1 : path = (segs1.map Prod.fst).flatten)
    (hpath2 : path = (segs2.map Prod.fst).flatten)
    (hprov1 : ∀ (j : Nat) (hj : j < segs1.length), ∃ tail,
      simplifyClausesByPath clauses
          (((segs1.take j).map Prod.fst).flatten)
        = (segs1[j]'hj).2 :: tail)
    (hprov2 : ∀ (j : Nat) (hj : j < segs2.length), ∃ tail,
      simplifyClausesByPath clauses
          (((segs2.take j).map Prod.fst).flatten)
        = (segs2[j]'hj).2 :: tail)
    (hvm1 : ∀ p ∈ segs1, p.1.map Prod.fst = p.2.map Prod.fst)
    (hvm2 : ∀ p ∈ segs2, p.1.map Prod.fst = p.2.map Prod.fst)
    (k : Nat) (hk1 : k ≤ segs1.length) (hk2 : k ≤ segs2.length) :
    segs1.take k = segs2.take k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1' : k ≤ segs1.length := Nat.le_of_succ_le hk1
    have hk2' : k ≤ segs2.length := Nat.le_of_succ_le hk2
    have htake_k_eq : segs1.take k = segs2.take k := ih hk1' hk2'
    have hk1_lt : k < segs1.length := hk1
    have hk2_lt : k < segs2.length := hk2
    -- (1) Cumulative bits agree at index k.
    have hcum_eq : ((segs1.take k).map Prod.fst).flatten
                 = ((segs2.take k).map Prod.fst).flatten := by
      rw [htake_k_eq]
    -- (2) heads of simplifyClausesByPath agree, hence segs[k].2 agree.
    obtain ⟨t1, ht1⟩ := hprov1 k hk1_lt
    obtain ⟨t2, ht2⟩ := hprov2 k hk2_lt
    rw [hcum_eq] at ht1
    have hcl_eq : (segs1[k]'hk1_lt).2 :: t1 = (segs2[k]'hk2_lt).2 :: t2 :=
      ht1.symm.trans ht2
    have hsnd_eq : (segs1[k]'hk1_lt).2 = (segs2[k]'hk2_lt).2 :=
      (List.cons.injEq _ _ _ _).mp hcl_eq |>.1
    -- (3) Length agreement on .1 via hvm.
    have hk_in_1 : (segs1[k]'hk1_lt) ∈ segs1 := List.getElem_mem _
    have hk_in_2 : (segs2[k]'hk2_lt) ∈ segs2 := List.getElem_mem _
    have hvm_1 := hvm1 _ hk_in_1
    have hvm_2 := hvm2 _ hk_in_2
    have hlen_eq : (segs1[k]'hk1_lt).1.length = (segs2[k]'hk2_lt).1.length := by
      have h1 := congr_arg List.length hvm_1
      have h2 := congr_arg List.length hvm_2
      simp only [List.length_map] at h1 h2
      rw [hsnd_eq] at h1
      omega
    -- (4) Path-split.  segs1 = segs1.take k ++ segs1[k] :: segs1.drop (k+1).
    have hsplit_segs1 :
        segs1 = segs1.take k ++ ((segs1[k]'hk1_lt) :: segs1.drop (k+1)) := by
      have h1 := (List.take_append_drop k segs1).symm
      have h2 : segs1.drop k = (segs1[k]'hk1_lt) :: segs1.drop (k+1) :=
        List.drop_eq_getElem_cons hk1_lt
      rw [h2] at h1
      exact h1
    have hsplit_segs2 :
        segs2 = segs2.take k ++ ((segs2[k]'hk2_lt) :: segs2.drop (k+1)) := by
      have h1 := (List.take_append_drop k segs2).symm
      have h2 : segs2.drop k = (segs2[k]'hk2_lt) :: segs2.drop (k+1) :=
        List.drop_eq_getElem_cons hk2_lt
      rw [h2] at h1
      exact h1
    -- Flatten both decompositions.
    have hflat1 : path = ((segs1.take k).map Prod.fst).flatten
                       ++ (segs1[k]'hk1_lt).1
                       ++ ((segs1.drop (k+1)).map Prod.fst).flatten := by
      have h := hpath1
      conv_rhs at h => rw [hsplit_segs1]
      rw [List.map_append, List.map_cons, List.flatten_append,
        List.flatten_cons, ← List.append_assoc] at h
      exact h
    have hflat2 : path = ((segs2.take k).map Prod.fst).flatten
                       ++ (segs2[k]'hk2_lt).1
                       ++ ((segs2.drop (k+1)).map Prod.fst).flatten := by
      have h := hpath2
      conv_rhs at h => rw [hsplit_segs2]
      rw [List.map_append, List.map_cons, List.flatten_append,
        List.flatten_cons, ← List.append_assoc] at h
      exact h
    -- Reassociate: cum_k ++ (s.1 ++ rest)
    have hflat1' : path = ((segs1.take k).map Prod.fst).flatten
                ++ ((segs1[k]'hk1_lt).1
                  ++ ((segs1.drop (k+1)).map Prod.fst).flatten) := by
      rw [hflat1, List.append_assoc]
    have hflat2' : path = ((segs2.take k).map Prod.fst).flatten
                ++ ((segs2[k]'hk2_lt).1
                  ++ ((segs2.drop (k+1)).map Prod.fst).flatten) := by
      rw [hflat2, List.append_assoc]
    have hcat_eq :
        ((segs1.take k).map Prod.fst).flatten
          ++ ((segs1[k]'hk1_lt).1
            ++ ((segs1.drop (k+1)).map Prod.fst).flatten)
        = ((segs2.take k).map Prod.fst).flatten
          ++ ((segs2[k]'hk2_lt).1
            ++ ((segs2.drop (k+1)).map Prod.fst).flatten) := by
      rw [← hflat1', hflat2']
    rw [hcum_eq] at hcat_eq
    have hrest_eq :
        (segs1[k]'hk1_lt).1
          ++ ((segs1.drop (k+1)).map Prod.fst).flatten
        = (segs2[k]'hk2_lt).1
          ++ ((segs2.drop (k+1)).map Prod.fst).flatten :=
      List.append_cancel_left hcat_eq
    have hfst_eq : (segs1[k]'hk1_lt).1 = (segs2[k]'hk2_lt).1 :=
      List.append_inj_left hrest_eq hlen_eq
    -- (5) Combine to segs1[k] = segs2[k].
    have hpair_eq : (segs1[k]'hk1_lt) = (segs2[k]'hk2_lt) := by
      apply Prod.ext hfst_eq hsnd_eq
    -- (6) Conclude via take_succ (= take_add_one).
    have hgi1 : segs1[k]?.toList = [(segs1[k]'hk1_lt)] := by
      rw [List.getElem?_eq_getElem hk1_lt]; rfl
    have hgi2 : segs2[k]?.toList = [(segs2[k]'hk2_lt)] := by
      rw [List.getElem?_eq_getElem hk2_lt]; rfl
    calc segs1.take (k+1)
        = segs1.take k ++ segs1[k]?.toList := List.take_add_one
      _ = segs2.take k ++ [(segs1[k]'hk1_lt)] := by rw [htake_k_eq, hgi1]
      _ = segs2.take k ++ [(segs2[k]'hk2_lt)] := by rw [hpair_eq]
      _ = segs2.take k ++ segs2[k]?.toList := by rw [hgi2]
      _ = segs2.take (k+1) := List.take_add_one.symm


/- **Sub-bridge #1 — term-vs-clause filterMap identity**.

    For an `orGate` DNF, `dnfClauses ∘ simpleRestrictDNF σ` factors
    as a `filterMap` over `dnfClauses dnf`: each original clause is
    either dropped (if `σ` kills it) or has its `σ`-assigned literals
    stripped (preserving the surviving-literal order).

    The killing predicate matches `isClauseKilled _ σ`:
    a clause is killed iff some literal `(v, neg)` has `σ v = some b`
    with `b ≠ literalSatisfyingBit neg`.

    The strip predicate matches the live-var filter on the clause:
    keep `(v, _)` iff `σ v = none`.

    *Required for*: identifying the LHS list of clauses in
    `r_of_combined_eq_restricted_simplify_head` with a `filterMap` of
    the original DNF clauses, so first-survivor index can be tracked.

    -/
private lemma dnfClauses_simple_restrict_extract_aux
    (lits : List UnboundedFanInFormula)
    (hin : lits.all isInput = true)
    (σ : Nat → Option Bool) :
    let c : List (Nat × Bool) := lits.filterMap (fun lit =>
      match lit with
      | .inputGate i b => some (i, b)
      | _ => none)
    (Option.map (fun g => match g with
        | .andGate lits' => lits'.filterMap (fun lit =>
            match lit with
            | .inputGate i b => some (i, b)
            | _ => none)
        | _ => ([] : List (Nat × Bool)))
      (simpleRestrictTerm σ (.andGate lits)))
    = (if isClauseKilled c σ then none
       else some (c.filter (fun p => σ p.1 == none))) := by
  change Option.map _ (
    if (lits.map (simpleRestrictLiteral σ)).any
      (fun l => match l with | .constant false _ => true | _ => false) then none
    else some (UnboundedFanInFormula.andGate ((lits.map (simpleRestrictLiteral σ)).filter
      (fun l => match l with | .constant _ _ => false | _ => true)))) = _
  have r1 : (lits.map (simpleRestrictLiteral σ)).any
      (fun l => match l with | .constant false _ => true | _ => false)
    = isClauseKilled (lits.filterMap (fun lit =>
        match lit with | .inputGate i b => some (i, b) | _ => none)) σ := by
    induction lits with
    | nil => simp [isClauseKilled]
    | cons lit rest ih =>
      have hlit_in : isInput lit = true := by
        rw [List.all_cons] at hin; exact (Bool.and_eq_true _ _).mp hin |>.1
      have hrest_in : rest.all isInput = true := by
        rw [List.all_cons] at hin; exact (Bool.and_eq_true _ _).mp hin |>.2
      match lit, hlit_in with
      | .inputGate i neg, _ =>
      simp only [List.map_cons, List.any_cons, List.filterMap_cons, ih hrest_in,
        isClauseKilled]
      simp only [simpleRestrictLiteral]
      cases hσi : σ i with
      | none => rfl
      | some b =>
        cases hneg : neg with
        | false => simp only [literalSatisfyingBit]; cases b <;> simp
        | true => simp only [literalSatisfyingBit, Bool.not]; cases b <;> simp
  rw [r1]
  by_cases hk : isClauseKilled (lits.filterMap (fun lit =>
      match lit with | .inputGate i b => some (i, b) | _ => none)) σ = true
  · rw [if_pos hk, if_pos hk]; rfl
  · rw [Bool.not_eq_true] at hk
    rw [if_neg (by rw [hk]; decide), if_neg (by rw [hk]; decide)]
    simp only [Option.map_some]
    clear hk r1
    induction lits with
    | nil => simp
    | cons lit rest ih =>
      have hlit_in : isInput lit = true := by
        rw [List.all_cons] at hin; exact (Bool.and_eq_true _ _).mp hin |>.1
      have hrest_in : rest.all isInput = true := by
        rw [List.all_cons] at hin; exact (Bool.and_eq_true _ _).mp hin |>.2
      match lit, hlit_in with
      | .inputGate i neg, _ =>
      simp only [List.map_cons, List.filter_cons, List.filterMap_cons]
      simp only [simpleRestrictLiteral]
      by_cases hσi : σ i = none
      · simp only [hσi]
        simp only [↓reduceIte, List.filterMap_cons, beq_self_eq_true]
        have ih' := ih hrest_in
        simp only [Option.some.injEq] at ih' ⊢
        rw [ih']
      · obtain ⟨b, hσi'⟩ := Option.ne_none_iff_exists'.mp hσi
        simp only [hσi']
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih hrest_in

lemma dnfClauses_simple_restrict_eq_filterMap
    (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true)
    (σ : Nat → Option Bool) :
    dnfClauses (simpleRestrictDNF σ dnf)
    = (dnfClauses dnf).filterMap (fun c =>
        if isClauseKilled c σ then none
        else some (c.filter (fun p => σ p.1 == none))) := by
  match dnf, hdnf with
  | .orGate gates, hdnf =>
    have hgates : ∀ g ∈ gates, isAndOfInputsOnly g = true := by
      simp only [isDNF, List.all_eq_true] at hdnf; exact hdnf
    change dnfClauses (.orGate (gates.filterMap (simpleRestrictTerm σ))) =
      (gates.map _).filterMap _
    simp only [dnfClauses]
    rw [List.map_filterMap, List.filterMap_map]
    apply List.filterMap_congr
    intro g hg
    have hg_aoi := hgates g hg
    match g, hg_aoi with
    | .andGate lits, hg_aoi =>
      have hin : lits.all isInput = true := by
        simp only [isAndOfInputsOnly] at hg_aoi; exact hg_aoi
      exact dnfClauses_simple_restrict_extract_aux lits hin σ

/- **Sub-bridge #2 — iterated-strip = one-shot strip on the same list**.

    `simplifyClausesByPath` applied to a *restricted* clause list
    (already stripped of `asgn` assignments) by `cum` equals one-shot
    `restrictClauseList` of the *original* clause list by the
    combined assignment `restrictionAsFunction (asgn ++ cum)`.

    Existing infrastructure:
    - `simplifyClausesByPath_as_restrict` (proved): equates
      `simplifyClausesByPath l cum` with `restrictClauseList l
      (pathToAsgn _ cum)` when `cum.fst.Nodup`.
    - Folding the outer `restrictClauseList … (restrictionAsFunction asgn)`
      into the inner restriction gives `restrictClauseList orig
      (pathToAsgn (restrictionAsFunction asgn) cum)`, and finally relate the
      `pathToAsgn (restrictionAsFunction asgn) cum` lookup function with
      `restrictionAsFunction (asgn ++ cum)` (both produce the same `Nat → Option Bool`
      under disjointness).

    *Required for*: bridging the LHS of `R_of_combined_…` (iterated
    simplify) to a one-shot restrict of the original DNF.

    Hypotheses:
    - `cum.map fst).Nodup` — cum bits don't repeat vars (path nodup).
    - `(cum.map fst).Disjoint (asgn.map fst)` — encoder invariant.

    -/
private lemma restrictClauseList_eq_filterMap_beq
    (l : List (List (Nat × Bool))) (σ : Nat → Option Bool) :
    restrictClauseList l σ
    = l.filterMap (fun c =>
        if isClauseKilled c σ then none
        else some (c.filter (fun p => σ p.1 == none))) := by
  unfold restrictClauseList
  apply List.filterMap_congr
  intro c _
  by_cases hk : isClauseKilled c σ = true
  · rw [if_pos hk, if_pos hk]
  · rw [Bool.not_eq_true] at hk
    rw [if_neg (by rw [hk]; decide), if_neg (by rw [hk]; decide)]
    congr 1
    apply List.filter_congr
    intro p _
    cases hpv : σ p.1 with
    | none => simp
    | some b => simp

private lemma pathToAsgn_eq_cr_none_append
    (asgn cum : List (Nat × Bool))
    (hcum_nodup : (cum.map Prod.fst).Nodup)
    (hdisj : ∀ v ∈ cum.map Prod.fst,
      (asgn.any fun p => p.1 == v) = false) :
    ∀ v, pathToAsgn (restrictionAsFunction asgn) cum v
        = restrictionAsFunction (asgn ++ cum) v := by
  intro v
  by_cases hv_cum : v ∈ cum.map Prod.fst
  · obtain ⟨b, hvb_cum⟩ : ∃ b, (v, b) ∈ cum := by
      rcases List.mem_map.mp hv_cum with ⟨⟨w, b⟩, hmem, hw⟩
      simp only at hw; subst hw; exact ⟨b, hmem⟩
    rw [pathToAsgn_mem _ cum v b hvb_cum hcum_nodup]
    unfold restrictionAsFunction
    have hasgn_none : asgn.find? (fun p => p.1 == v) = none := by
      rw [List.find?_eq_none]
      intro p hp
      have hany := hdisj v hv_cum
      rw [List.any_eq_false] at hany
      exact hany p hp
    rw [List.find?_append, hasgn_none, Option.none_or]
    have hcum_eq : cum.find? (fun p => p.1 == v) = some (v, b) := by
      clear hasgn_none
      induction cum with
      | nil => simp at hvb_cum
      | cons p rest ih =>
        rcases List.mem_cons.mp hvb_cum with heq | hmem_rest
        · subst heq; simp
        · simp only [List.find?_cons]
          by_cases hpv : (p.1 == v) = true
          · exfalso
            simp only [List.map_cons, List.nodup_cons] at hcum_nodup
            apply hcum_nodup.1
            rw [beq_iff_eq] at hpv
            rw [hpv]
            exact List.mem_map_of_mem hmem_rest
          · simp only [hpv]
            apply ih
            · simp only [List.map_cons, List.nodup_cons] at hcum_nodup
              exact hcum_nodup.2
            · intro w hw; exact hdisj w (List.mem_cons_of_mem _ hw)
            · exact List.mem_map.mpr ⟨(v, b), hmem_rest, rfl⟩
            · exact hmem_rest
    rw [hcum_eq]
  · rw [pathToAsgn_notMem _ cum v hv_cum]
    unfold restrictionAsFunction
    have hcum_none : cum.find? (fun p => p.1 == v) = none := by
      rw [List.find?_eq_none]
      intro p hp hpv
      apply hv_cum
      rw [beq_iff_eq] at hpv
      rw [← hpv]
      exact List.mem_map_of_mem hp
    rw [List.find?_append, hcum_none, Option.or_none]

lemma iterated_strip_eq_one_shot_strip
    (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true)
    (asgn cum : List (Nat × Bool))
    (hcum_nodup : (cum.map Prod.fst).Nodup)
    (hcum_disj_asgn : ∀ v ∈ cum.map Prod.fst,
      (asgn.any fun p => p.1 == v) = false) :
    simplifyClausesByPath
      (dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) dnf)) cum
    = (dnfClauses dnf).filterMap (fun c =>
        if isClauseKilled c (restrictionAsFunction
            (asgn ++ cum)) then none
        else some (c.filter (fun p =>
          restrictionAsFunction (asgn ++ cum) p.1 == none))) := by
  rw [dnfClauses_simple_restrict_eq_filterMap dnf hdnf]
  rw [← restrictClauseList_eq_filterMap_beq]
  have hpath_none : ∀ vb ∈ cum,
      restrictionAsFunction asgn vb.1 = none := by
    intro vb hvb
    have hv_cum : vb.1 ∈ cum.map Prod.fst := List.mem_map_of_mem hvb
    have hany := hcum_disj_asgn vb.1 hv_cum
    unfold restrictionAsFunction
    have hfind : asgn.find? (fun p => p.1 == vb.1) = none := by
      rw [List.find?_eq_none]
      intro p hp
      rw [List.any_eq_false] at hany
      exact hany p hp
    rw [hfind]
  rw [simplifyClausesByPath_eq_restrict (dnfClauses dnf)
        (restrictionAsFunction asgn) cum hpath_none hcum_nodup]
  have hfun_eq : pathToAsgn (restrictionAsFunction asgn) cum
      = restrictionAsFunction (asgn ++ cum) := by
    funext v
    exact pathToAsgn_eq_cr_none_append asgn cum hcum_nodup hcum_disj_asgn v
  rw [hfun_eq]
  rw [restrictClauseList_eq_filterMap_beq]

/- **Sub-bridge #3 — first-survivor index commutes with structural filterMap**.

    Given `g : α → Option α` whose action on each element is either
    "drop" (none) or "keep modified by `f : α → α`" (some (f x)), AND
    given that the killing-predicate for the first-survivor search agrees
    on the original and the modified element, the first-survivor index
    on `l.filterMap g` equals the index (after position-translation) of
    the first survivor in `l`.

    Specialised form needed here: if `c` is asgn-survivor (so
    `simpleRestrictTerm σ_asgn c = some c'` with `c' = strip_assigned c`),
    then `isClauseKilled c (asgn ++ cum)` ↔ `isClauseKilled c' cum`,
    so `firstTermNotKilledByList` on the filterMap equals the strip of
    the first non-killed clause in the original.

    *Required for*: aligning the head of the LHS list (filterMap'd)
    with `restrictionOfFirstTermNotKilledByList` on the original DNF under
    the combined assignment and cumulative path.

    -/
private lemma isClauseKilled_cr_none_eq
    (c : List (Nat × Bool)) (A : List (Nat × Bool)) :
    isClauseKilled c (restrictionAsFunction A)
    = c.any fun (vneg : Nat × Bool) =>
        match A.find? (fun p => p.1 == vneg.1) with
        | none => false
        | some (_, b) => !(b == literalSatisfyingBit vneg.2) := by
  unfold isClauseKilled
  congr 1
  funext ⟨v, neg⟩
  change (match (restrictionAsFunction A) v with
        | none => false
        | some b => !(b == literalSatisfyingBit neg))
      = match A.find? (fun p => p.1 == v) with
        | none => false
        | some (_, b) => !(b == literalSatisfyingBit neg)
  unfold restrictionAsFunction
  cases A.find? (fun p => p.1 == v) with
  | none => rfl
  | some pair => cases pair; rfl

private lemma ftnkb_cons_killed
    (c : List (Nat × Bool)) (rest : List (List (Nat × Bool))) (A : List (Nat × Bool))
    (hk : isClauseKilled c (restrictionAsFunction A) = true) :
    firstTermNotKilledByList (c :: rest) A = firstTermNotKilledByList rest A := by
  unfold firstTermNotKilledByList
  have h_is : isClauseKilledBy c A = true := by
    calc
      isClauseKilledBy c A =
          c.any fun vneg =>
            match A.find? (fun p => p.1 == vneg.1) with
            | none => false
            | some (_, b) => !(b == literalSatisfyingBit vneg.2) := rfl
      _ = isClauseKilled c (restrictionAsFunction A) :=
        (isClauseKilled_cr_none_eq c A).symm
      _ = true := hk
  have hp : (!isClauseKilledBy c A) = false := by simp [h_is]
  rw [List.findIdx?_cons]
  simp only [hp, Bool.false_eq_true, if_false]
  cases h : List.findIdx? (fun c => !isClauseKilledBy c A) rest <;>
    simp

private lemma ftnkb_cons_alive
    (c : List (Nat × Bool)) (rest : List (List (Nat × Bool))) (A : List (Nat × Bool))
    (hnk : isClauseKilled c (restrictionAsFunction A) = false) :
    firstTermNotKilledByList (c :: rest) A = c := by
  unfold firstTermNotKilledByList
  have h_is : isClauseKilledBy c A = false := by
    calc
      isClauseKilledBy c A =
          c.any fun vneg =>
            match A.find? (fun p => p.1 == vneg.1) with
            | none => false
            | some (_, b) => !(b == literalSatisfyingBit vneg.2) := rfl
      _ = isClauseKilled c (restrictionAsFunction A) :=
        (isClauseKilled_cr_none_eq c A).symm
      _ = false := hnk
  have hp : (!isClauseKilledBy c A) = true := by simp [h_is]
  rw [List.findIdx?_cons]
  simp [hp]

lemma isClauseKilledBy_eq_isClauseKilled
    (c : List (Nat × Bool)) (A : List (Nat × Bool)) :
    isClauseKilledBy c A =
      isClauseKilled c (restrictionAsFunction A) := by
  calc
    isClauseKilledBy c A =
        c.any fun vneg =>
          match A.find? (fun p => p.1 == vneg.1) with
          | none => false
          | some (_, b) => !(b == literalSatisfyingBit vneg.2) := rfl
    _ = isClauseKilled c (restrictionAsFunction A) :=
      (isClauseKilled_cr_none_eq c A).symm

lemma firstTermNotKilledByList_self
    (clauses : List (List (Nat × Bool))) (A : List (Nat × Bool)) :
    isClauseKilledBy (firstTermNotKilledByList clauses A) A = false := by
  induction clauses with
  | nil => simp [firstTermNotKilledByList, isClauseKilledBy]
  | cons c rest ih =>
      cases hk : isClauseKilled c (restrictionAsFunction A) with
      | false =>
          rw [ftnkb_cons_alive c rest A hk]
          calc
            isClauseKilledBy c A =
                c.any fun vneg =>
                  match A.find? (fun p => p.1 == vneg.1) with
                  | none => false
                  | some (_, b) =>
                      !(b == literalSatisfyingBit vneg.2) := rfl
            _ = isClauseKilled c (restrictionAsFunction A) :=
              (isClauseKilled_cr_none_eq c A).symm
            _ = false := hk
      | true =>
          rw [ftnkb_cons_killed c rest A hk]
          exact ih

lemma firstTermNotKilledByList_eq
    (clauses : List (List (Nat × Bool))) (A₁ A₂ : List (Nat × Bool))
    (hagree : ∀ w, restrictionAsFunction A₁ w ≠ none →
      restrictionAsFunction A₂ w = restrictionAsFunction A₁ w)
    (hfirst_alive :
      isClauseKilledBy (firstTermNotKilledByList clauses A₁) A₂ = false) :
    firstTermNotKilledByList clauses A₂ =
      firstTermNotKilledByList clauses A₁ := by
  induction clauses with
  | nil => simp [firstTermNotKilledByList]
  | cons c rest ih =>
      by_cases hk₁ : isClauseKilledBy c A₁ = true
      · have hk₁' : isClauseKilled c (restrictionAsFunction A₁) = true := by
          rwa [← isClauseKilledBy_eq_isClauseKilled]
        have hk₂' := killed_clause_stays_killed c
          (restrictionAsFunction A₁) (restrictionAsFunction A₂) hagree hk₁'
        rw [ftnkb_cons_killed c rest A₁ hk₁',
          ftnkb_cons_killed c rest A₂ hk₂']
        rw [ftnkb_cons_killed c rest A₁ hk₁'] at hfirst_alive
        exact ih hfirst_alive
      · have hnk₁ : isClauseKilledBy c A₁ = false := by
          cases h : isClauseKilledBy c A₁ <;> simp_all
        have hnk₁' : isClauseKilled c (restrictionAsFunction A₁) = false := by
          rwa [← isClauseKilledBy_eq_isClauseKilled]
        rw [ftnkb_cons_alive c rest A₁ hnk₁']
        rw [ftnkb_cons_alive c rest A₁ hnk₁'] at hfirst_alive
        have hnk₂' : isClauseKilled c (restrictionAsFunction A₂) = false := by
          rwa [← isClauseKilledBy_eq_isClauseKilled]
        rw [ftnkb_cons_alive c rest A₂ hnk₂']

lemma firstTermNotKilledByList_mem_or_nil
    (clauses : List (List (Nat × Bool))) (A : List (Nat × Bool)) :
    firstTermNotKilledByList clauses A ∈ clauses ∨
      firstTermNotKilledByList clauses A = [] := by
  unfold firstTermNotKilledByList
  cases hidx : clauses.findIdx? (fun c => !isClauseKilledBy c A) with
  | none => right; simp
  | some i =>
      left
      obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma firstTermNotKilledByList_eq_of_cr_none_eq
    (clauses : List (List (Nat × Bool))) (A₁ A₂ : List (Nat × Bool))
    (heq : ∀ v, restrictionAsFunction A₁ v =
      restrictionAsFunction A₂ v) :
    firstTermNotKilledByList clauses A₁ =
      firstTermNotKilledByList clauses A₂ := by
  have hfun : restrictionAsFunction A₁ =
      restrictionAsFunction A₂ := funext heq
  have hkilled : ∀ c, isClauseKilledBy c A₁ =
      isClauseKilledBy c A₂ := by
    intro c
    rw [isClauseKilledBy_eq_isClauseKilled,
      isClauseKilledBy_eq_isClauseKilled, hfun]
  unfold firstTermNotKilledByList
  simp_rw [hkilled]

lemma restrictClauseByListAssignment_subset
    (clause : List (Nat × Bool)) (A : List (Nat × Bool))
    (p : Nat × Bool) (hp : p ∈ restrictClauseByListAssignment clause A) :
    p ∈ clause := by
  unfold restrictClauseByListAssignment at hp
  split at hp
  · exact absurd hp List.not_mem_nil
  · exact List.mem_of_mem_filter hp

lemma restrictClauseByListAssignment_mem_of_unassigned
    (clause : List (Nat × Bool)) (A : List (Nat × Bool))
    (v : Nat) (neg : Bool)
    (hmem : (v, neg) ∈ clause)
    (hunassigned : (A.any fun (w, _) => w == v) = false)
    (hnk : isClauseKilledBy clause A = false) :
    (v, neg) ∈ restrictClauseByListAssignment clause A := by
  unfold restrictClauseByListAssignment
  rw [hnk]
  exact List.mem_filter.mpr ⟨hmem, by simp [hunassigned]⟩

lemma restrictionOfFirstTermNotKilledByList_vars_notMem_asgn
    (clauses : List (List (Nat × Bool))) (A : List (Nat × Bool))
    (p : Nat × Bool)
    (hp : p ∈ restrictionOfFirstTermNotKilledByList clauses A) :
    (A.any fun (w, _) => w == p.1) = false := by
  unfold restrictionOfFirstTermNotKilledByList restrictClauseByListAssignment at hp
  split at hp
  · exact absurd hp List.not_mem_nil
  · have hlive := (List.mem_filter.mp hp).2
    cases h : A.any fun (w, _) => w == p.1
    · rfl
    · simp [h] at hlive

lemma firstTermNotKilledByList_filterMap_strip
    (dnf : UnboundedFanInFormula) (asgn cum : List (Nat × Bool))
    (head : List (Nat × Bool)) (tail : List (List (Nat × Bool)))
    (h_eq :
      (dnfClauses dnf).filterMap (fun c =>
          if isClauseKilled c (restrictionAsFunction
              (asgn ++ cum)) then none
          else some (c.filter (fun p =>
            restrictionAsFunction (asgn ++ cum) p.1 == none)))
        = head :: tail) :
    (firstTermNotKilledByList (dnfClauses dnf) (asgn ++ cum)).filter
      (fun p =>
        restrictionAsFunction (asgn ++ cum) p.1 == none)
    = head := by
  set A := asgn ++ cum with h_a
  generalize hcs : dnfClauses dnf = cs at h_eq
  clear hcs h_a
  induction cs with
  | nil => simp [List.filterMap_nil] at h_eq
  | cons c rest ih =>
    rw [List.filterMap_cons] at h_eq
    by_cases hk : isClauseKilled c (restrictionAsFunction A) = true
    · rw [if_pos hk] at h_eq
      simp only at h_eq
      rw [ftnkb_cons_killed c rest A hk]
      exact ih h_eq
    · rw [Bool.not_eq_true] at hk
      rw [if_neg (by rw [hk]; decide)] at h_eq
      simp only [List.cons.injEq] at h_eq
      rw [ftnkb_cons_alive c rest A hk]
      exact h_eq.1

/- Sub-lemma: `restrictClauseByListAssignment c A` reduces to `c.filter`
   when `c` is alive
    under `restrictionAsFunction A`.  Bridges the asgn-list-based filter form
    `(v,_) => !A.any (·.1 == v)` with `restrictionAsFunction A v == none`. -/
private lemma restrictClauseByListAssignment_eq_filter_alive
    (c : List (Nat × Bool)) (A : List (Nat × Bool))
    (hnk : isClauseKilled c (restrictionAsFunction A) = false) :
    restrictClauseByListAssignment c A
    = c.filter (fun p => restrictionAsFunction A p.1 == none) := by
  unfold restrictClauseByListAssignment
  -- Translate `hnk` to the pattern used by
  -- `restrictClauseByListAssignment`'s condition.
  have hk : (c.any fun (vneg : Nat × Bool) =>
        match A.find? (fun p => p.1 == vneg.1) with
        | none => false
        | some (_, b) => !(b == literalSatisfyingBit vneg.2)) = false := by
    rw [← isClauseKilled_cr_none_eq, hnk]
  -- The if-condition uses `fun (v, neg) => match …` (anonymous-constructor
  -- pattern). Convert via `show`.
  have hk' : (c.any fun (vneg : Nat × Bool) =>
        match vneg with
        | (v, neg) =>
          match A.find? (fun p => p.1 == v) with
          | none => false
          | some (_, b) => !(b == literalSatisfyingBit neg)) = false := by
    convert hk using 2
  change (if (c.any fun (vneg : Nat × Bool) =>
            match vneg with
            | (v, neg) =>
              match A.find? (fun p => p.1 == v) with
              | none => false
              | some (_, b) => !(b == literalSatisfyingBit neg)) = true
        then ([] : List (Nat × Bool))
        else c.filter fun (vneg : Nat × Bool) =>
          match vneg with
          | (v, _) => !A.any fun (wneg : Nat × Bool) =>
            match wneg with
            | (w, _) => w == v)
      = c.filter (fun p => restrictionAsFunction A p.1 == none)
  rw [hk']
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply List.filter_congr
  intro p _
  cases p with
  | mk v _ =>
    change (!A.any fun (wneg : Nat × Bool) => match wneg with | (w, _) => w == v)
        = (restrictionAsFunction A v == none)
    unfold restrictionAsFunction
    cases hf : A.find? (fun q => q.1 == v) with
    | none =>
      have hany : (A.any fun (q : Nat × Bool) => match q with | (w, _) => w == v) = false := by
        rw [List.any_eq_false]
        intro q hq
        cases q with
        | mk w b =>
          change ¬ (w == v) = true
          intro hwv
          exact List.find?_eq_none.mp hf (w, b) hq hwv
      rw [hany]; rfl
    | some pair =>
      cases pair with
      | mk w b =>
        have hwv : w == v := by
          have hsat := List.find?_some hf
          simpa using hsat
        have hany : (A.any fun (q : Nat × Bool) => match q with | (w, _) => w == v) = true := by
          rw [List.any_eq_true]
          exact ⟨(w, b), List.mem_of_find?_eq_some hf, hwv⟩
        rw [hany]; rfl

/-- The cumulative restriction is exactly the head of the running
    simplification. -/
lemma r_of_combined_eq_restricted_simplify_head_exact
    (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true)
    (asgn cum : List (Nat × Bool))
    (hcum_nodup : (cum.map Prod.fst).Nodup)
    (hcum_disj_asgn : ∀ v ∈ cum.map Prod.fst,
      (asgn.any fun p => p.1 == v) = false)
    (head : List (Nat × Bool)) (tail : List (List (Nat × Bool)))
    (h_eq :
      simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) dnf))
        cum = head :: tail) :
    restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
      (asgn ++ cum) = head := by
  -- Step 1: rewrite the iterated restriction as a one-shot restriction.
  rw [iterated_strip_eq_one_shot_strip dnf hdnf asgn cum hcum_nodup hcum_disj_asgn] at h_eq
  -- Step 2: identify the first surviving clause with `head`.
  have hf := firstTermNotKilledByList_filterMap_strip dnf asgn cum head tail h_eq
  -- Step 3: show the selected clause is alive.
  set A := asgn ++ cum with h_a
  set σ := restrictionAsFunction A with hσ
  have h_alive : ∀ (cs : List (List (Nat × Bool))) (h tl)
      (he : cs.filterMap (fun c =>
          if isClauseKilled c σ then none
          else some (c.filter (fun p => σ p.1 == none))) = h :: tl),
      isClauseKilled (firstTermNotKilledByList cs A) σ = false := by
    intro cs
    induction cs with
    | nil => intro h tl he; simp at he
    | cons c rest ih =>
      intro h tl he
      rw [List.filterMap_cons] at he
      by_cases hk : isClauseKilled c σ = true
      · rw [if_pos hk] at he
        simp only at he
        rw [ftnkb_cons_killed c rest A hk]
        exact ih h tl he
      · rw [Bool.not_eq_true] at hk
        rw [ftnkb_cons_alive c rest A hk]
        exact hk
  have hnk := h_alive (dnfClauses dnf) head tail h_eq
  -- Step 4: `restrictClauseByListAssignment` reduces to the live-literal filter.
  unfold restrictionOfFirstTermNotKilledByList
  rw [restrictClauseByListAssignment_eq_filter_alive _ A hnk, hf]

/-- Map the exact restricted-head equality over literal variables. -/
lemma r_of_combined_eq_restricted_simplify_head
    (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true)
    (asgn cum : List (Nat × Bool))
    (hcum_nodup : (cum.map Prod.fst).Nodup)
    (hcum_disj_asgn : ∀ v ∈ cum.map Prod.fst,
      (asgn.any fun p => p.1 == v) = false)
    (head : List (Nat × Bool)) (tail : List (List (Nat × Bool)))
    (h_eq :
      simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) dnf))
        cum = head :: tail) :
    (restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
      (asgn ++ cum)).map Prod.fst = head.map Prod.fst :=
  congrArg (List.map Prod.fst)
    (r_of_combined_eq_restricted_simplify_head_exact dnf hdnf asgn cum
      hcum_nodup hcum_disj_asgn head tail h_eq)

/-- Strengthened dead tree path split: `simplified = simplifyClausesByPath clauses pre`. -/
private lemma graft_deadTree_path_split_simplified
    (clause : List (Nat × Bool)) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (path : List (Nat × Bool))
    (hp : IsPathIn (graftOnZeroLeavesWithSimplificationFull
      (deadTree clause) clauses fuel) path) :
    ∃ (pre suf : List (Nat × Bool))
      (simplified : List (List (Nat × Bool))),
      path = pre ++ suf ∧
      pre.map Prod.fst = clause.map Prod.fst ∧
      simplified = simplifyClausesByPath clauses pre ∧
      IsPathIn (canonicalDecisionTreeAuxPreciseFull fuel simplified) suf := by
  induction clause generalizing path clauses fuel with
  | nil =>
    simp only [deadTree, graftOnZeroLeavesWithSimplificationFull] at hp
    exact ⟨[], path, clauses, by simp, by simp, by simp [simplifyClausesByPath], hp⟩
  | cons lit rest ih =>
    cases lit with | mk w neg =>
    simp only [deadTree, graftOnZeroLeavesWithSimplificationFull] at hp
    cases hp with
    | left _ _ _ p' hp' =>
      obtain ⟨pref, suf, simpl, hcat, hpref_eq, hsimp_eq, hsuf_path⟩ :=
        ih (simplifyClausesLeft clauses w) fuel p' hp'
      exact ⟨(w, .false) :: pref, suf, simpl,
        by simp [hcat], by simp [hpref_eq],
        by simp [simplifyClausesByPath, hsimp_eq], hsuf_path⟩
    | right _ _ _ p' hp' =>
      obtain ⟨pref, suf, simpl, hcat, hpref_eq, hsimp_eq, hsuf_path⟩ :=
        ih (simplifyClausesRight clauses w) fuel p' hp'
      exact ⟨(w, .true) :: pref, suf, simpl,
        by simp [hcat], by simp [hpref_eq],
        by simp [simplifyClausesByPath, hsimp_eq], hsuf_path⟩

/-- Strengthened path split for `clauseToPathTreeFull`:
    additionally shows `simplified = simplifyClausesByPath clauses pre`. -/
lemma graft_clauseToPathTreeFull_path_split_simplified
    (clause : List (Nat × Bool)) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (path : List (Nat × Bool))
    (hp : IsPathIn (graftOnZeroLeavesWithSimplificationFull
      (clauseToPathTreeFull clause) clauses fuel) path) :
    ∃ (pre suf : List (Nat × Bool))
      (simplified : List (List (Nat × Bool))),
      path = pre ++ suf ∧
      pre.map Prod.fst = clause.map Prod.fst ∧
      simplified = simplifyClausesByPath clauses pre ∧
      (suf = [] ∨
       IsPathIn (canonicalDecisionTreeAuxPreciseFull fuel simplified) suf) := by
  induction clause generalizing path clauses fuel with
  | nil =>
    simp only [clauseToPathTreeFull, graftOnZeroLeavesWithSimplificationFull] at hp
    cases hp
    exact ⟨[], [], clauses, by simp, by simp, by simp [simplifyClausesByPath], Or.inl rfl⟩
  | cons lit rest ih =>
    cases lit with | mk w neg =>
    simp only [clauseToPathTreeFull] at hp
    cases hsat : literalSatisfyingBit neg <;> simp only [hsat] at hp
    · -- sat = .zero: left = clauseToPathTreeFull rest, right = deadTree rest
      simp only [graftOnZeroLeavesWithSimplificationFull] at hp
      cases hp with
      | left _ _ _ p' hp' =>
        -- Satisfying direction: recurse into clauseToPathTreeFull rest
        obtain ⟨pref, suf, simpl, hcat, hpref_eq, hsimp_eq, hsuf⟩ :=
          ih (simplifyClausesLeft clauses w) fuel p' hp'
        exact ⟨(w, .false) :: pref, suf, simpl,
          by simp [hcat], by simp [hpref_eq],
          by simp [simplifyClausesByPath, hsimp_eq], hsuf⟩
      | right _ _ _ p' hp' =>
        -- Dead direction: all rest vars then graft
        obtain ⟨pref, suf, simpl, hcat, hpref_eq, hsimp_eq, hsuf_path⟩ :=
          graft_deadTree_path_split_simplified rest
            (simplifyClausesRight clauses w) fuel p' hp'
        exact ⟨(w, .true) :: pref, suf, simpl,
          by simp [hcat], by simp [hpref_eq],
          by simp [simplifyClausesByPath, hsimp_eq], Or.inr hsuf_path⟩
    · -- sat = .one: left = deadTree rest, right = clauseToPathTreeFull rest
      simp only [graftOnZeroLeavesWithSimplificationFull] at hp
      cases hp with
      | left _ _ _ p' hp' =>
        -- Dead direction
        obtain ⟨pref, suf, simpl, hcat, hpref_eq, hsimp_eq, hsuf_path⟩ :=
          graft_deadTree_path_split_simplified rest
            (simplifyClausesLeft clauses w) fuel p' hp'
        exact ⟨(w, .false) :: pref, suf, simpl,
          by simp [hcat], by simp [hpref_eq],
          by simp [simplifyClausesByPath, hsimp_eq], Or.inr hsuf_path⟩
      | right _ _ _ p' hp' =>
        -- Satisfying direction
        obtain ⟨pref, suf, simpl, hcat, hpref_eq, hsimp_eq, hsuf⟩ :=
          ih (simplifyClausesRight clauses w) fuel p' hp'
        exact ⟨(w, .true) :: pref, suf, simpl,
          by simp [hcat], by simp [hpref_eq],
          by simp [simplifyClausesByPath, hsimp_eq], hsuf⟩

/-- If a path through a grafted `clauseToPathTreeFull` continues
    past the clause into later clauses (`suf ≠ []`), then some literal
    in the path prefix was assigned a non-satisfying bit.

    This is the direct (non-contrapositive) form of the structural
    property: a path exiting a clause's subtree MUST take a
    non-satisfying direction at some variable. -/
lemma graft_clauseToPathTreeFull_suf_ne_imp_non_sat
    (clause : List (Nat × Bool)) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (pre suf : List (Nat × Bool))
    (hp : IsPathIn (graftOnZeroLeavesWithSimplificationFull
      (clauseToPathTreeFull clause) clauses fuel) (pre ++ suf))
    (hpre_eq : pre.map Prod.fst = clause.map Prod.fst)
    (hsuf_ne : suf ≠ []) :
    ∃ (v : Nat) (neg : Bool) (b : Bool),
      (v, neg) ∈ clause ∧ (v, b) ∈ pre ∧ b ≠ literalSatisfyingBit neg := by
  induction clause generalizing pre clauses fuel with
  | nil =>
    -- clause = [] → pre = [] → graft(dtLeaf .one) → suf = [] → contradiction
    cases pre with
    | nil =>
      simp only [clauseToPathTreeFull, graftOnZeroLeavesWithSimplificationFull,
        List.nil_append] at hp
      cases hp; exact absurd rfl hsuf_ne
    | cons => simp at hpre_eq
  | cons lit rest ih =>
    cases lit with | mk v neg =>
    cases pre with
    | nil => simp at hpre_eq
    | cons phd ptl =>
      cases phd with | mk w b =>
      simp only [List.map_cons, List.cons.injEq] at hpre_eq
      -- Save membership facts before rfl (which replaces w) and cases hp
      have hlit_mem : (w, neg) ∈ (w, neg) :: rest := List.mem_cons_self
      have hpre_hd_zero : (w, false) ∈ (w, false) :: ptl := List.mem_cons_self
      have hpre_hd_one : (w, true) ∈ (w, true) :: ptl := List.mem_cons_self
      obtain ⟨rfl, hpre_eq_tail⟩ := hpre_eq
      simp only [clauseToPathTreeFull] at hp
      cases hsat : literalSatisfyingBit neg <;> simp only [hsat, List.cons_append] at hp
      · -- sat = .zero: left = clauseToPathTreeFull, right = deadTree
        simp only [graftOnZeroLeavesWithSimplificationFull] at hp
        cases hp with
        | left _ _ _ p hp' =>
          -- b = .zero (satisfying direction), recurse into rest
          obtain ⟨v', neg', b', hv_in, hb_in, hne⟩ := ih _ _ _ hp' hpre_eq_tail
          exact ⟨v', neg', b', List.mem_cons_of_mem _ hv_in,
            List.mem_cons_of_mem _ hb_in, hne⟩
        | right _ _ _ p hp' =>
          -- b = .one ≠ .zero = sat: non-satisfying witness found
          exact ⟨_, neg, .true, hlit_mem, hpre_hd_one, by simp [hsat]⟩
      · -- sat = .one: left = deadTree, right = clauseToPathTreeFull
        simp only [graftOnZeroLeavesWithSimplificationFull] at hp
        cases hp with
        | left _ _ _ p hp' =>
          -- b = .zero ≠ .one = sat: non-satisfying witness found
          exact ⟨_, neg, .false, hlit_mem, hpre_hd_zero, by simp [hsat]⟩
        | right _ _ _ p hp' =>
          -- b = .one (satisfying direction), recurse into rest
          obtain ⟨v', neg', b', hv_in, hb_in, hne⟩ := ih _ _ _ hp' hpre_eq_tail
          exact ⟨v', neg', b', List.mem_cons_of_mem _ hv_in,
            List.mem_cons_of_mem _ hb_in, hne⟩

/-- **Graft exit-direction lemma** (piece (b) of the iter-split classification).

    If a path through a grafted `clauseToPathTreeFull` continues past
    the clause into later clauses (`suf ≠ []`), and the prefix's variables
    are distinct, then the head clause is **killed** by the assignment
    `pathToAsgn (fun _ => none) pre` induced by the path prefix.

    This says concretely that path bits within a segment kill the segment's
    head — the structural fact powering iter-split's per-segment
    classification. -/
lemma graft_clauseToPathTreeFull_suf_ne_imp_head_killed
    (clause : List (Nat × Bool)) (clauses : List (List (Nat × Bool))) (fuel : Nat)
    (pre suf : List (Nat × Bool))
    (hp : IsPathIn (graftOnZeroLeavesWithSimplificationFull
      (clauseToPathTreeFull clause) clauses fuel) (pre ++ suf))
    (hpre_eq : pre.map Prod.fst = clause.map Prod.fst)
    (hpre_nodup : (pre.map Prod.fst).Nodup)
    (hsuf_ne : suf ≠ []) :
    isClauseKilled clause (pathToAsgn (fun _ => none) pre) = true := by
  obtain ⟨v, neg, b, hv_in_clause, hvb_in_pre, hb_ne⟩ :=
    graft_clauseToPathTreeFull_suf_ne_imp_non_sat
      clause clauses fuel pre suf hp hpre_eq hsuf_ne
  -- pathToAsgn (none) pre v = some b (via membership + nodup).
  have hpath_v : pathToAsgn (fun _ => none) pre v = some b :=
    pathToAsgn_mem (fun _ => none) pre v b hvb_in_pre hpre_nodup
  -- Witness the killing literal (v, neg) ∈ clause.
  rw [isClauseKilled, List.any_eq_true]
  refine ⟨(v, neg), hv_in_clause, ?_⟩
  -- Goal (after destructuring the match on (v, neg)): the literal evaluates falsely.
  change (match pathToAsgn (fun _ => none) pre v with
        | none => false
        | some b' => !(b' == literalSatisfyingBit neg)) = true
  rw [hpath_v]
  -- Goal: !(b == literalSatisfyingBit neg) = true, i.e. b ≠ literalSatisfyingBit neg.
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  exact hb_ne

/-! ### Iterative path decomposition through `k` clauses

    The decomposition walks `k` clauses, peeling off
    one clause-segment at a time and accumulating the consumed path prefix.

    This is the structural backbone needed to bound `path.length` against the
    *number* of clauses traversed rather than just the first one.

    The lemma is stated with `k` as an arbitrary parameter; the proof goes by
    induction on `k`, with the base case `k = 0` trivial and the inductive
    step continuing on the suffix returned by the hypothesis. -/

/-- `simplifyClausesByPath` preserves the Nodup-fst invariant on each
    surviving clause. Follows by induction on the path using the
    left/right preservation lemmas. -/
lemma simplifyClausesByPath_preserves_nodup
    (clauses : List (List (Nat × Bool))) (path : List (Nat × Bool))
    (hnd : ∀ c ∈ clauses, (c.map Prod.fst).Nodup) :
    ∀ c ∈ simplifyClausesByPath clauses path, (c.map Prod.fst).Nodup := by
  induction path generalizing clauses with
  | nil => simpa [simplifyClausesByPath] using hnd
  | cons hd tl ih =>
    cases hd with
    | mk v b =>
      cases b with
      | false =>
        simp only [simplifyClausesByPath]
        exact ih _ (simplifyClausesLeft_preserves_nodup clauses v hnd)
      | true =>
        simp only [simplifyClausesByPath]
        exact ih _ (simplifyClausesRight_preserves_nodup clauses v hnd)

/-- **Iter-split with per-segment paths.** Exposes for each segment `j`
    a graft-tree `IsPathIn`
    whose path is `segments[j].1 ++ (continuation past segment j)`,
    along with Nodup-fst of every segment's head clause.

    With this data, callers can immediately invoke
    `graft_clauseToPathTreeFull_suf_ne_imp_head_killed` (when
    the continuation is non-empty) to conclude that segment `j`'s head
    is killed by `pathToAsgn (fun _ => none) segments[j].1`.

    The "continuation past segment `j`" is
    `((segments.drop (j+1)).map Prod.fst).flatten ++ suf`, i.e. all
    path bits from segments after `j` plus the residual `suf`. -/
lemma canonical_dt_path_split_iter_with_heads_per_seg
    (clauses : List (List (Nat × Bool)))
    (hnodup_clauses : ∀ c ∈ clauses, (c.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hp : IsPathIn (canonicalDecisionTreeAuxPreciseFull clauses.length clauses) path)
    (k : Nat) :
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool)))
      (suf : List (Nat × Bool)),
      path = (segments.map Prod.fst).flatten ++ suf ∧
      segments.length ≤ k ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ p ∈ segments, ∃ c ∈ clauses, p.2.map Prod.fst ⊆ c.map Prod.fst) ∧
      (∀ p ∈ segments, (p.2.map Prod.fst).Nodup) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ (rest_j : List (List (Nat × Bool))) (fuel_j : Nat),
          IsPathIn (graftOnZeroLeavesWithSimplificationFull
            (clauseToPathTreeFull segments[j].2) rest_j fuel_j)
            (segments[j].1 ++
              (((segments.drop (j+1)).map Prod.fst).flatten ++ suf))) ∧
      -- At iteration `j`, `segments[j].2` is the head of the running simplification
      -- of `clauses` by the path bits accumulated through the first `j` segments.
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ (tail_j : List (List (Nat × Bool))),
          simplifyClausesByPath clauses (((segments.take j).map Prod.fst).flatten) =
            segments[j].2 :: tail_j) ∧
      (suf = [] ∨
        ∃ (simplified : List (List (Nat × Bool))) (fuel' : Nat),
          (∀ c ∈ simplified, ∃ c' ∈ clauses, c.map Prod.fst ⊆ c'.map Prod.fst) ∧
          (∀ c ∈ simplified, (c.map Prod.fst).Nodup) ∧
          simplified.length + segments.length ≤ clauses.length ∧
          segments.length = k ∧
          -- When iteration continues, `simplified` is the cumulative
          -- simplify-by-path of `clauses`.
          simplified =
            simplifyClausesByPath clauses ((segments.map Prod.fst).flatten) ∧
          IsPathIn (canonicalDecisionTreeAuxPreciseFull fuel' simplified) suf) := by
  induction k with
  | zero =>
    refine ⟨[], path, by simp, le_refl 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp_mem; simp at hp_mem
    · intro p hp_mem; simp at hp_mem
    · intro p hp_mem; simp at hp_mem
    · intro j hj; simp at hj
    · intro j hj; simp at hj
    · by_cases hpath_nil : path = []
      · exact Or.inl hpath_nil
      · refine Or.inr ⟨clauses, clauses.length, ?_, ?_, ?_, ?_, ?_, hp⟩
        · intro c hc; exact ⟨c, hc, fun _ h => h⟩
        · exact hnodup_clauses
        · simp
        · simp
        · simp [simplifyClausesByPath]
  | succ k ih =>
    obtain ⟨segments, suf, hcat, hlen, hcov, hheads, hnd_seg, hperseg, hcum_a, hsuf⟩ := ih
    cases hsuf with
    | inl hsuf_nil =>
      refine ⟨segments, suf, hcat, Nat.le_succ_of_le hlen, hcov, hheads,
              hnd_seg, hperseg, hcum_a, Or.inl hsuf_nil⟩
    | inr hsuf_path =>
      obtain ⟨simplified, fuel', hlift_simp, hnd_simp, hlen_inv, hseg_eq, hsimp_cum, hp_suf⟩ :=
        hsuf_path
      by_cases hsimp_ne : simplified = []
      · subst hsimp_ne
        cases fuel' with
        | zero =>
          simp only [canonicalDecisionTreeAuxPreciseFull] at hp_suf
          cases hp_suf
          refine ⟨segments, [], by simp [hcat], Nat.le_succ_of_le hlen, hcov, hheads,
                  hnd_seg, ?_, hcum_a, Or.inl rfl⟩
          intro j hj
          obtain ⟨rest_j, fuel_j, hpsj⟩ := hperseg j hj
          exact ⟨rest_j, fuel_j, by simpa using hpsj⟩
        | succ fuel'' =>
          simp only [canonicalDecisionTreeAuxPreciseFull] at hp_suf
          cases hp_suf
          refine ⟨segments, [], by simp [hcat], Nat.le_succ_of_le hlen, hcov, hheads,
                  hnd_seg, ?_, hcum_a, Or.inl rfl⟩
          intro j hj
          obtain ⟨rest_j, fuel_j, hpsj⟩ := hperseg j hj
          exact ⟨rest_j, fuel_j, by simpa using hpsj⟩
      · cases fuel' with
        | zero =>
          simp only [canonicalDecisionTreeAuxPreciseFull] at hp_suf
          cases hp_suf
          refine ⟨segments, [], by simp [hcat], Nat.le_succ_of_le hlen, hcov, hheads,
                  hnd_seg, ?_, hcum_a, Or.inl rfl⟩
          intro j hj
          obtain ⟨rest_j, fuel_j, hpsj⟩ := hperseg j hj
          exact ⟨rest_j, fuel_j, by simpa using hpsj⟩
        | succ fuel'' =>
          match simplified, hsimp_ne, hlift_simp, hnd_simp, hlen_inv with
          | head_clause :: rest, _, hlift_simp, hnd_simp, hlen_inv =>
            simp only [canonicalDecisionTreeAuxPreciseFull] at hp_suf
            obtain ⟨pre₂, suf₂, simpl₂, hcat₂, hpref_eq₂, hsimp_eq₂, hsuf₂⟩ :=
              graft_clauseToPathTreeFull_path_split_simplified
                head_clause rest fuel'' suf hp_suf
            have hhead_lift : ∃ c' ∈ clauses,
                head_clause.map Prod.fst ⊆ c'.map Prod.fst :=
              hlift_simp head_clause (by simp)
            have hrest_lift : ∀ c ∈ rest, ∃ c' ∈ clauses,
                c.map Prod.fst ⊆ c'.map Prod.fst :=
              fun c hc => hlift_simp c (by simp [hc])
            have hhead_nodup : (head_clause.map Prod.fst).Nodup :=
              hnd_simp head_clause (by simp)
            have hrest_nodup : ∀ c ∈ rest, (c.map Prod.fst).Nodup :=
              fun c hc => hnd_simp c (by simp [hc])
            have hpre₂_nodup : (pre₂.map Prod.fst).Nodup := by
              rw [hpref_eq₂]; exact hhead_nodup
            -- New segments and new suf
            set newsegs := segments ++ [(pre₂, head_clause)] with hns
            -- per-iteration IsPathIn for the freshly added last segment
            have hnew_perseg_last :
                IsPathIn (graftOnZeroLeavesWithSimplificationFull
                  (clauseToPathTreeFull head_clause) rest fuel'') (pre₂ ++ suf₂) := by
              rw [← hcat₂]; exact hp_suf
            refine ⟨newsegs, suf₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hcat, hcat₂]; simp [hns, List.append_assoc]
            · simp [hns]; omega
            · intro p hp_mem
              simp only [hns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp_mem
              cases hp_mem with
              | inl h => exact hcov p h
              | inr h => rw [h]; exact hpref_eq₂
            · intro p hp_mem
              simp only [hns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp_mem
              cases hp_mem with
              | inl h => exact hheads p h
              | inr h => rw [h]; exact hhead_lift
            · intro p hp_mem
              simp only [hns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp_mem
              cases hp_mem with
              | inl h => exact hnd_seg p h
              | inr h => rw [h]; exact hhead_nodup
            · -- Per-segment IsPathIn for new segments list.
              intro j hj
              by_cases hjlt : j < segments.length
              · -- Existing segment: transfer `IsPathIn` using suffix rearrangement.
                obtain ⟨rest_j, fuel_j, hpsj⟩ := hperseg j hjlt
                refine ⟨rest_j, fuel_j, ?_⟩
                -- newsegs[j] = segments[j] when j < segments.length
                have hidx : newsegs[j]'(by simp [hns]; omega) = segments[j]'hjlt := by
                  simp [hns, List.getElem_append_left hjlt]
                -- Suf rearrangement:
                -- The prior suffix is rearranged after appending the new segment:
                -- `segments[j].1 ++ ((segments.drop (j+1)).map fst).flatten ++ suf`
                -- becomes `newsegs[j].1 ++ ((newsegs.drop (j+1)).map fst).flatten ++ suf₂`,
                --   where newsegs.drop (j+1) = segments.drop (j+1) ++ [(pre₂, head_clause)]
                --   so the flatten = (segments.drop (j+1)).map fst).flatten ++ pre₂
                --   and suf = pre₂ ++ suf₂ ⇒ they match.
                have hdrop :
                    (newsegs.drop (j+1)).map Prod.fst =
                    (segments.drop (j+1)).map Prod.fst ++ [pre₂] := by
                  simp [hns, List.drop_append_of_le_length (by omega : j + 1 ≤ segments.length)]
                have hsuf_rearr :
                    ((segments.drop (j+1)).map Prod.fst).flatten ++ suf =
                    (((newsegs.drop (j+1)).map Prod.fst).flatten ++ suf₂) := by
                  rw [hdrop]
                  simp [List.flatten_append, hcat₂, List.append_assoc]
                rw [hidx, ← hsuf_rearr]
                exact hpsj
              · -- New segment: j = segments.length.
                have hjeq : j = segments.length := by
                  simp [hns] at hj; omega
                refine ⟨rest, fuel'', ?_⟩
                have hidx : newsegs[j]'hj = (pre₂, head_clause) := by
                  subst hjeq
                  simp [hns, List.getElem_append_right (by omega : segments.length ≤ segments.length)]
                have hdrop_nil : (newsegs.drop (j+1)).map Prod.fst = [] := by
                  subst hjeq
                  simp [hns]
                rw [hidx]
                simp only
                rw [show (((newsegs.drop (j+1)).map Prod.fst).flatten ++ suf₂) = suf₂ by
                      rw [hdrop_nil]; simp]
                exact hnew_perseg_last
            · -- Per-iteration cumulative-simplify identity.
              intro j hj
              by_cases hjlt : j < segments.length
              · -- Existing segment: the cumulative prefix is unchanged.
                obtain ⟨tail_j, htail_j⟩ := hcum_a j hjlt
                have hidx : newsegs[j]'(by simp [hns]; omega) = segments[j]'hjlt := by
                  simp [hns, List.getElem_append_left hjlt]
                have htake_eq :
                    ((newsegs.take j).map Prod.fst).flatten =
                    ((segments.take j).map Prod.fst).flatten := by
                  have : newsegs.take j = segments.take j := by
                    simp [hns,
                      List.take_append_of_le_length (by omega : j ≤ segments.length)]
                  rw [this]
                rw [hidx, htake_eq]
                exact ⟨tail_j, htail_j⟩
              · -- New segment: j = segments.length. Use B from IH.
                have hjeq : j = segments.length := by
                  simp [hns] at hj; omega
                have hidx : newsegs[j]'hj = (pre₂, head_clause) := by
                  subst hjeq
                  simp [hns, List.getElem_append_right (by omega : segments.length ≤ segments.length)]
                have htake_eq :
                    ((newsegs.take j).map Prod.fst).flatten =
                    (segments.map Prod.fst).flatten := by
                  subst hjeq
                  simp [hns]
                refine ⟨rest, ?_⟩
                rw [hidx, htake_eq, hsimp_cum]
            · -- **suf₂ branch**: split on whether suf₂ is empty.
              by_cases hsuf2_nil : suf₂ = []
              · exact Or.inl hsuf2_nil
              · -- suf₂ ≠ [] ⟹ hsuf₂ must be Or.inr (Or.inl gives suf₂ = []).
                have hsuf₂_path : IsPathIn
                    (canonicalDecisionTreeAuxPreciseFull fuel'' simpl₂) suf₂ :=
                  hsuf₂.resolve_left hsuf2_nil
                refine Or.inr ⟨simpl₂, fuel'', ?_, ?_, ?_, ?_, ?_, hsuf₂_path⟩
                · intro c hc
                  rw [hsimp_eq₂] at hc
                  obtain ⟨c', hc'_rest, hsub'⟩ :=
                    simplifyClausesByPath_head_lifts rest pre₂ c hc
                  obtain ⟨c'', hc''_clauses, hsub''⟩ := hrest_lift c' hc'_rest
                  exact ⟨c'', hc''_clauses, fun v hv => hsub'' (hsub' hv)⟩
                · intro c hc
                  rw [hsimp_eq₂] at hc
                  exact simplifyClausesByPath_preserves_nodup rest pre₂ hrest_nodup c hc
                · rw [hsimp_eq₂]
                  have h1 : (simplifyClausesByPath rest pre₂).length ≤ rest.length :=
                    simplifyClausesByPath_length_le rest pre₂
                  have hlen_new : newsegs.length = segments.length + 1 := by
                    simp [hns]
                  rw [hlen_new]
                  simp only [List.length_cons] at hlen_inv
                  omega
                · have hlen_new : newsegs.length = segments.length + 1 := by
                    simp [hns]
                  rw [hlen_new]; omega
                · -- `simpl₂ = simplifyClausesByPath clauses cum_path`.
                  -- where cum_path = (segments.flatten) ++ pre₂ = (newsegs.flatten).
                  have hkill : isClauseKilled head_clause
                      (pathToAsgn (fun _ => none) pre₂) = true := by
                    apply graft_clauseToPathTreeFull_suf_ne_imp_head_killed
                      head_clause rest fuel'' pre₂ suf₂ hnew_perseg_last hpref_eq₂ hpre₂_nodup
                    exact hsuf2_nil
                  -- (newsegs.map fst).flatten = (segments.map fst).flatten ++ pre₂.
                  have hflat :
                      (newsegs.map Prod.fst).flatten =
                      (segments.map Prod.fst).flatten ++ pre₂ := by
                    simp [hns, List.flatten_append]
                  rw [hsimp_eq₂, hflat, simplifyClausesByPath_append, ← hsimp_cum]
                  exact (simplifyClausesByPath_killed_head head_clause rest pre₂
                    hpre₂_nodup hkill).symm


/-- **Per-segment killed-head formulation.**

    Decomposes any path through the CDT into a sequence of clause-segments,
    where each segment corresponds to traversing one clause's variables.
    For every NON-LAST segment `j`, the segment's head clause is killed by
    the assignment derived from segment `j`'s OWN prefix bits (not the
    global cumulative restriction).

    Concretely, returns a list of `(prefix_j, head_clause_j)` pairs such that:
    1. `path = (segments.map fst).flatten`  (segments tile the path)
    2. `segments.length ≤ |restricted_clauses|`  (at most one segment per
        surviving clause)
    3. Each segment's prefix exactly covers its head clause's variables
        (`prefix.map fst = head.map fst`), so `|prefix| = |head|`.
    4. Each segment's head clause is a sublist (variable-wise) of some
        clause in the original restricted DNF.
    5. **(Killing property.)** For every `j < segments.length - 1`, the
        head clause `segments[j].2` is killed by
        `pathToAsgn (fun _ => none) segments[j].1`.

    *Why this is the right formulation.* The killing literal in segment `j`'s
    head appears in `segments[j].1` (the path bits within segment `j`), not in
    the cumulative `path.take d`. The original lemma assumed the cumulative
    bits killed every clause, but missed that `clauseToPathTreeFull` adds
    `deadTree` padding that extends the path past the killing depth.

    The killing claim is triggered by the continuation past segment `j` being
    non-empty. (When all later segments have empty prefixes — which happens
    when their head clauses are all `[]` — segment `j` may end at a 1-leaf
    instead of being killed, so we cannot conclude killing in that edge
    case.)

    *Use for path-length bounds.* By (3), `path.length = Σ |head_j|`. Bounds
    on individual clause widths (e.g. `≤ w`) and number of surviving clauses
    then give `path.length ≤ w * segments.length ≤ w * |restricted_clauses|`. -/
lemma cdt_full_query_per_segment_killed
    {n : Nat} (f : UnboundedFanInDNF n) (asgn : List (Nat × Bool))
    (hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hpath : IsPathIn (canonicalDecisionTree f.val asgn) path) :
    let restricted_clauses :=
      dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val)
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))),
      path = (segments.map Prod.fst).flatten ∧
      segments.length ≤ restricted_clauses.length ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ p ∈ segments, ∃ c ∈ restricted_clauses,
        p.2.map Prod.fst ⊆ c.map Prod.fst) ∧
      (∀ p ∈ segments, (p.2.map Prod.fst).Nodup) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ((segments.drop (j + 1)).map Prod.fst).flatten ≠ [] →
        isClauseKilled segments[j].2
          (pathToAsgn (fun _ => none) segments[j].1) = true) ∧
      -- At iteration `j`, `segments[j].2` is the head of the running simplification of
      -- `restricted_clauses` by the path bits of the first `j` segments.
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ (tail_j : List (List (Nat × Bool))),
          simplifyClausesByPath restricted_clauses
              (((segments.take j).map Prod.fst).flatten) =
            segments[j].2 :: tail_j) := by
  -- Step 1: unfold the CDT to expose the iter-split target.
  simp only [canonicalDecisionTree] at hpath
  set restricted :=
    dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) f.val) with hrestr_def
  -- Step 2: invoke the per-segment iter-split with k = restricted.length.
  obtain ⟨segments, suf, hcat, hlen, hcov, hheads, hnd_seg, hperseg, hcum_a, hsuf⟩ :=
    canonical_dt_path_split_iter_with_heads_per_seg
      restricted hnodup_restricted path hpath restricted.length
  -- Step 3: force suf = []. Either it's already [], or the inr case gives
  -- segments.length = restricted.length AND simplified.length + segments.length
  -- ≤ restricted.length, forcing simplified = [], hence suf = [].
  have hsuf_nil : suf = [] := by
    cases hsuf with
    | inl h => exact h
    | inr h =>
      obtain ⟨simplified, fuel', _, _, hlen_inv, hseg_eq, _hsimp_cum, hp_suf⟩ := h
      have hsimp_zero : simplified.length = 0 := by omega
      have hsimp_nil : simplified = [] := List.length_eq_zero_iff.mp hsimp_zero
      subst hsimp_nil
      cases fuel' with
      | zero =>
        simp only [canonicalDecisionTreeAuxPreciseFull] at hp_suf
        cases hp_suf; rfl
      | succ fuel'' =>
        simp only [canonicalDecisionTreeAuxPreciseFull] at hp_suf
        cases hp_suf; rfl
  -- Step 4: assemble.
  refine ⟨segments, ?_, hlen, hcov, hheads, hnd_seg, ?_, hcum_a⟩
  · rw [hcat, hsuf_nil]; simp
  -- Step 5: discharge the killing claim per segment via
  -- `graft_clauseToPathTreeFull_suf_ne_imp_head_killed`.
  intro j hj hcont_ne
  obtain ⟨rest_j, fuel_j, hps_j⟩ := hperseg j hj
  -- Specialize the IsPathIn from per_seg using suf = [] to drop the trailing ++ [].
  have hps_j' :
      IsPathIn (graftOnZeroLeavesWithSimplificationFull
        (clauseToPathTreeFull segments[j].2) rest_j fuel_j)
        (segments[j].1 ++ ((segments.drop (j + 1)).map Prod.fst).flatten) := by
    have := hps_j
    rw [hsuf_nil] at this
    simpa using this
  -- The head's vars are Nodup, and the prefix's vars equal the head's.
  have hhead_nodup : (segments[j].2.map Prod.fst).Nodup :=
    hnd_seg segments[j] (List.getElem_mem hj)
  have hpre_eq : segments[j].1.map Prod.fst = segments[j].2.map Prod.fst :=
    hcov segments[j] (List.getElem_mem hj)
  have hpre_nodup : (segments[j].1.map Prod.fst).Nodup := by
    rw [hpre_eq]; exact hhead_nodup
  exact graft_clauseToPathTreeFull_suf_ne_imp_head_killed
    segments[j].2 rest_j fuel_j segments[j].1
    ((segments.drop (j + 1)).map Prod.fst).flatten
    hps_j' hpre_eq hpre_nodup hcont_ne

/-- **Killed heads are covered by their segment prefix.**

    For any iter-split decomposition of a CDT path (as produced by
    `cdt_full_query_per_segment_killed`), every variable appearing in any
    segment's head clause has a witness bit in that segment's prefix path
    bits. In particular, every head-variable lies in `path` (since each
    segment's prefix is a sublist of `path`).

    This is an immediate consequence of the iter-split invariant
    `pre.map fst = head.map fst` (conjunct 3 of
    `cdt_full_query_per_segment_killed`), packaged here for use as a
    direct bridge from a segment-head variable to a concrete path bit. -/
lemma cdt_full_query_killed_heads_covered_by_prefix
    {n : Nat} (f : UnboundedFanInDNF n) (asgn : List (Nat × Bool))
    (hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hpath : IsPathIn (canonicalDecisionTree f.val asgn) path) :
    let restricted_clauses :=
      dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val)
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))),
      path = (segments.map Prod.fst).flatten ∧
      segments.length ≤ restricted_clauses.length ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ p ∈ segments, ∃ c ∈ restricted_clauses,
        p.2.map Prod.fst ⊆ c.map Prod.fst) ∧
      (∀ p ∈ segments, (p.2.map Prod.fst).Nodup) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ((segments.drop (j + 1)).map Prod.fst).flatten ≠ [] →
        isClauseKilled segments[j].2
          (pathToAsgn (fun _ => none) segments[j].1) = true) ∧
      -- Every variable in any segment's head has a witness bit in that
      -- segment's prefix path bits.
      (∀ (i : Nat) (hi : i < segments.length) (v : Nat),
        v ∈ (segments[i]'hi).2.map Prod.fst →
        ∃ b, (v, b) ∈ (segments[i]'hi).1) ∧
      -- At iteration `j`, `segments[j].2` is the head of the running simplification of
      -- `restricted_clauses` by the path bits of the first `j` segments.
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ (tail_j : List (List (Nat × Bool))),
          simplifyClausesByPath restricted_clauses
              (((segments.take j).map Prod.fst).flatten) =
            segments[j].2 :: tail_j) := by
  obtain ⟨segments, hcat, hlen, hcov, hheads, hnd, hkill, hcum_a⟩ :=
    cdt_full_query_per_segment_killed f asgn hnodup_restricted path hpath
  refine ⟨segments, hcat, hlen, hcov, hheads, hnd, hkill, ?_, hcum_a⟩
  intro i hi v hv
  -- pre.map fst = head.map fst, so v ∈ pre.map fst, hence ∃ b, (v, b) ∈ pre.
  have hpre_eq : (segments[i]'hi).1.map Prod.fst = (segments[i]'hi).2.map Prod.fst :=
    hcov (segments[i]'hi) (List.getElem_mem hi)
  have hv_pre : v ∈ (segments[i]'hi).1.map Prod.fst := by
    rw [hpre_eq]; exact hv
  rw [List.mem_map] at hv_pre
  obtain ⟨⟨v', b⟩, hvb_mem, hvb_eq⟩ := hv_pre
  simp only at hvb_eq
  subst hvb_eq
  exact ⟨b, hvb_mem⟩

/- **Non-last iter-split segments are non-empty.**

    For any iter-split decomposition of a CDT path produced by
    `cdt_full_query_per_segment_killed`, every non-last segment's prefix
    `segments[j].1` is non-empty.

    *Why true.*  The 6th conjunct of `cdt_full_query_per_segment_killed`
    gives `isClauseKilled segments[j].2 (pathToAsgn None segments[j].1) = true`
    for all `j < length - 1` (precisely: when `((segs.drop (j+1)).map fst).flatten ≠ []`).
    Killing requires at least one literal in `segments[j].2` to have a
    matching kill-bit in `segments[j].1`.  Hence `segments[j].2 ≠ []`,
    and via vars-match (3rd conjunct), `segments[j].1 ≠ []`.

    *Why a "for ALL j" version is FALSE.*  When the canonical-DT path
    terminates at a 1-leaf (because some clause becomes satisfied),
    the final segment is the degenerate `([], [])` produced by
    `graft_clauseToPathTreeFull_path_split_simplified`'s nil case.
    See `clauseToPathTreeFull [] = dtLeaf .one` and the per-iter
    `graftOnZeroLeavesWithSimplificationFull (dtLeaf .one) _ _ = dtLeaf .one`.

    -/
lemma cdt_segment_pre_ne_nil_except_last
    {n : Nat} (f : UnboundedFanInDNF n) (asgn : List (Nat × Bool))
    (_hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (_hpath : IsPathIn (canonicalDecisionTree f.val asgn) path)
    (segments : List (List (Nat × Bool) × List (Nat × Bool)))
    (_hseg_cat : path = (segments.map Prod.fst).flatten)
    (hseg_pre_eq : ∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst)
    (hseg_killed : ∀ (j : Nat) (hj : j < segments.length),
      ((segments.drop (j + 1)).map Prod.fst).flatten ≠ [] →
      isClauseKilled (segments[j]'hj).2
        (pathToAsgn (fun _ => none) (segments[j]'hj).1) = true)
    (j : Nat) (hj : j < segments.length)
    (hj_not_last : ((segments.drop (j + 1)).map Prod.fst).flatten ≠ []) :
    (segments[j]'hj).1 ≠ [] := by
  -- Apply the killed claim at j.
  have hkill := hseg_killed j hj hj_not_last
  -- A killed clause must be non-empty (kill requires ≥1 literal).
  have hseg_j_2_ne : (segments[j]'hj).2 ≠ [] := by
    intro h_empty
    rw [h_empty] at hkill
    -- isClauseKilled [] _ = false (empty .any)
    simp [isClauseKilled] at hkill
  -- Via vars-match, segments[j].1.fst.length = segments[j].2.fst.length > 0.
  have hvm := hseg_pre_eq (segments[j]'hj) (List.getElem_mem hj)
  intro h_pre_empty
  have h_fst_empty : (segments[j]'hj).1.map Prod.fst = [] := by
    rw [h_pre_empty]; rfl
  rw [hvm] at h_fst_empty
  have h_seg_2_empty : (segments[j]'hj).2 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hxfst : x.1 ∈ (segments[j]'hj).2.map Prod.fst :=
      List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [h_fst_empty] at hxfst
    exact List.not_mem_nil hxfst
  exact hseg_j_2_ne h_seg_2_empty

#print axioms cdt_segment_pre_ne_nil_except_last

/- **Within-depth iter-split segments are non-empty.**

    Specialisation of `cdt_segment_pre_ne_nil_except_last` to the encoder
    bundle setting: when the path comes from `leftmostPathExceedingDepth`
    (so `path.length > d`), any iter-split segment `j` whose cumulative
    path-bits-through-index-`j` end at position `≤ d` is automatically
    non-last (more bits remain in path).  Hence `segments[j].1 ≠ []`.

    *Why this matters.*  In the encoder bundle, all segments referenced via
    `hρ_segments_consumed`'s `segments.take k` are within depth `d` (since
    ρ extends asgn by at most depth-`d` bits). This excludes the trailing degenerate
    `([], [])` segment that may exist past depth `d` when the canonical
    DT 1-leaf-terminates (see `clauseToPathTreeFull [] = dtLeaf .one`). -/
lemma cdt_segment_pre_ne_nil_within_depth
    {n : Nat} (f : UnboundedFanInDNF n) (asgn : List (Nat × Bool))
    (hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (segments : List (List (Nat × Bool) × List (Nat × Bool)))
    (hseg_cat : path = (segments.map Prod.fst).flatten)
    (hseg_pre_eq : ∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst)
    (hseg_killed : ∀ (j : Nat) (hj : j < segments.length),
      ((segments.drop (j + 1)).map Prod.fst).flatten ≠ [] →
      isClauseKilled (segments[j]'hj).2
        (pathToAsgn (fun _ => none) (segments[j]'hj).1) = true)
    (j : Nat) (hj : j < segments.length)
    (h_within_d :
      ((segments.take (j + 1)).map Prod.fst).flatten.length ≤ d) :
    (segments[j]'hj).1 ≠ [] := by
  -- Step 1: path = take(j+1).flatten ++ drop(j+1).flatten.
  have hsplit :
      path = ((segments.take (j+1)).map Prod.fst).flatten ++
             ((segments.drop (j+1)).map Prod.fst).flatten := by
    rw [hseg_cat]
    conv_lhs =>
      rw [show segments = segments.take (j+1) ++ segments.drop (j+1) from
        (List.take_append_drop (j+1) segments).symm]
    rw [List.map_append, List.flatten_append]
  -- Step 2: path.length > d.
  have hpath_len_gt :=
    leftmostPathExceedingDepth_some_path_length_gt _ _ _ hpath
  -- Step 3: drop(j+1).flatten.length > 0, hence ≠ [].
  have hdrop_ne :
      ((segments.drop (j + 1)).map Prod.fst).flatten ≠ [] := by
    intro h_empty
    rw [hsplit, h_empty, List.append_nil] at hpath_len_gt
    omega
  -- Step 4: segment j is non-last. Reconstruct `IsPathIn` from `hpath` and
  -- apply the existing lemma.
  have hpath_isin :
      IsPathIn (canonicalDecisionTree f.val asgn) path :=
    leftmostPathExceedingDepth_isPathIn _ _ _ hpath
  exact cdt_segment_pre_ne_nil_except_last f asgn hnodup_restricted path
    hpath_isin segments hseg_cat hseg_pre_eq hseg_killed j hj hdrop_ne

#print axioms cdt_segment_pre_ne_nil_within_depth


/-- **Main head bridge.** The encoder's restricted first surviving clause
    equals the head of the iter-split's running simplification when the
    latter is nonempty. -/
lemma roftnkb_eq_simplify_path_head
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool)) (π : List (Nat × Bool))
    (hdisj : ∀ vb ∈ π, ¬ (asgn.any fun (w, _) => w == vb.1))
    (hnd : (π.map Prod.fst).Nodup)
    (hne : simplifyClausesByPath
      (dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val)) π ≠ []) :
    restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions asgn π) =
    (simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) f.val)) π).head hne := by
  have hπ_disj : ∀ v ∈ π.map Prod.fst,
      (asgn.any fun (w, _) => w == v) = false := by
    intro v hv
    obtain ⟨vb, hvb, rfl⟩ := List.mem_map.mp hv
    have hd := hdisj vb hvb
    cases h : asgn.any fun (w, _) => w == vb.1
    · rfl
    · exact absurd h hd
  have hcombine : combineRestrictions asgn π = asgn ++ π := by
    unfold combineRestrictions
    congr 1
    apply List.filter_eq_self.mpr
    intro vb hvb
    have hv_mem : vb.1 ∈ π.map Prod.fst :=
      List.mem_map_of_mem (f := Prod.fst) hvb
    simp [hπ_disj vb.1 hv_mem]
  obtain ⟨head, tail, hs⟩ : ∃ head tail,
      simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) f.val)) π = head :: tail := by
    cases hs : simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) f.val)) π with
    | nil => exact absurd hs hne
    | cons head tail => exact ⟨head, tail, rfl⟩
  have hhead :
      (simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) f.val)) π).head hne = head := by
    have h_head : ∀ (l₁ l₂ : List (List (Nat × Bool))) (heq : l₁ = l₂)
        (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), l₁.head h₁ = l₂.head h₂ := by
      intro l₁ l₂ heq h₁ h₂
      subst heq
      rfl
    exact h_head _ _ hs hne (List.cons_ne_nil head tail)
  rw [hhead]
  simpa [hcombine] using
    r_of_combined_eq_restricted_simplify_head_exact f.val f.property.2
      asgn π hnd hπ_disj head tail hs


/- **Canonical-prefix segment-head equality.** At the canonical
    iter-split prefix `prefix_i := ((segments.take i).map fst).flatten`,
    `segments[i].2` has the same variables as the first clause of `dnf` not
    killed by `combineRestrictions asgn prefix_i`.
    No subset hypothesis is needed; this is unconditional given the
    iter-split provenance and a `prefix_i`-disjoint-from-asgn condition
    (which holds because canonical-DT path bits are unassigned by `asgn`
    — see `canonical_dt_path_var_none`).

    *Proof.*  Direct application of `roftnkb_eq_simplify_path_head` with
    `π = prefix_i`, then `_hseg_prov i`'s head-equation gives
    `simplify(C, prefix_i).head = segments[i].2`. -/
lemma iter_split_seg_eq_rtnkb_at_canonical_prefix
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (segments : List (List (Nat × Bool) × List (Nat × Bool)))
    (hpath_eq : path = (segments.map Prod.fst).flatten)
    (hseg_prov :
      ∀ (j : Nat) (hj : j < segments.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segments.take j).map Prod.fst).flatten)
          = (segments[j]'hj).2 :: tail_j)
    (i : Nat) (hi : i < segments.length) :
    let prefix_i : List (Nat × Bool) := ((segments.take i).map Prod.fst).flatten
    (segments[i]'hi).2.map Prod.fst =
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions asgn prefix_i)).map Prod.fst := by
  intro prefix_i
  /- prefix_i is a prefix of path, hence each bit of prefix_i is on path. -/
  have hprefix_path : prefix_i <+: path := by
    rw [hpath_eq]
    exact List.IsPrefix.flatten (List.IsPrefix.map _ (List.take_prefix _ _))
  /- Each var in prefix_i is unassigned by asgn (canonical-DT invariant). -/
  have hdisj : ∀ vb ∈ prefix_i, ¬ (asgn.any fun (w, _) => w == vb.1) := by
    intro vb hvb habs
    have hvb_path : vb ∈ path := hprefix_path.subset hvb
    have hnone :=
      canonical_dt_path_var_none f.val asgn f.property.2 d path
        hpath vb.1 vb.2 hvb_path
    /- `asgn.any z==vb.1 = true` ⇒ asgn has (vb.1, _) ⇒ restrictionAsFunction asgn vb.1 ≠ none. -/
    rw [List.any_eq_true] at habs
    obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := habs
    simp only [beq_iff_eq] at hw'_eq
    subst hw'_eq
    simp only [restrictionAsFunction] at hnone
    have hfind : asgn.find? (fun q => q.1 == vb.1) ≠ none := by
      rw [Ne, List.find?_eq_none]; push Not
      exact ⟨(vb.1, b'), hw'_mem, by simp⟩
    rcases hfind_eq : asgn.find? (fun q => q.1 == vb.1) with _ | ⟨_, _⟩
    · exact hfind hfind_eq
    · rw [hfind_eq] at hnone; cases hnone
  /- prefix_i.fst.Nodup since path.fst.Nodup and prefix_i is a prefix. -/
  have hpath_nodup : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
  have hpfx_nodup : (prefix_i.map Prod.fst).Nodup := by
    have : prefix_i.map Prod.fst <+: path.map Prod.fst :=
      List.IsPrefix.map _ hprefix_path
    exact this.sublist.nodup hpath_nodup
  /- _hseg_prov i gives the head-equation. -/
  obtain ⟨tail_i, hseg_eq⟩ := hseg_prov i hi
  /- The simplified-by-prefix list is nonempty. -/
  have hne :
      simplifyClausesByPath
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) f.val)) prefix_i ≠ [] := by
    rw [hseg_eq]; intro h; cases h
  /- Bridge B: the first non-killed clause is the head of the simplified list. -/
  have hbridge :=
    roftnkb_eq_simplify_path_head f asgn prefix_i hdisj hpfx_nodup hne
  /- Compute the head explicitly via hseg_eq, side-stepping the dependent
     `hne` motive issue with a generic helper. -/
  have h_head : ∀ (l : List (List (Nat × Bool))) (head : List (Nat × Bool))
      (tail : List (List (Nat × Bool))) (heq : l = head :: tail) (h : l ≠ []),
      l.head h = head := by
    intro l head tail heq h; subst heq; rfl
  have hhead := h_head _ _ _ hseg_eq hne
  rw [hbridge, hhead]

#print axioms iter_split_seg_eq_rtnkb_at_canonical_prefix

/- **Identification of `πI` in the alive case.**

    Under the bundle's alive-case discriminant
    `ρ = asgn ++ ((segs.take k).map fst).flatten`,
    `remaining_π = (((segs.drop k).map fst).flatten).filter window`,
    filtering `remaining_π` by the variables in
    `restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ` yields exactly the
    `k`-th segment's path bits:

        πI = segs[k].1.

    Once `πI = segs[k].1` as lists, the bundle relation lifts to
    `combineRestrictions ρ πI = asgn ++ prefix_{k+1}`.

    *Proof outline.*
    1. `combineRestrictions asgn prefix_k = asgn ++ prefix_k = ρ`
       (assignment-disjoint via
       `canonical_dt_path_var_none`).
    2. The selected clause variables equal `segs[k].2.map Prod.fst` by
       `iter_split_seg_eq_rtnkb_at_canonical_prefix`, which equals
       `segs[k].1.map Prod.fst` by `hvm`.
    3. `segs.drop k = segs[k] :: segs.drop (k+1)`, so
       `((segs.drop k).map fst).flatten = segs[k].1 ++ rest`.
    4. `remaining_π = (segs[k].1 ++ rest).filter window
                    = segs[k].1 ++ rest.filter window` (by `hwindow`).
    5. `πI = (segs[k].1 ++ rest_filtered).filter (segs[k].1.fst.contains)
            = segs[k].1` (rest_filtered's fsts disjoint from segs[k].1.fst by
       path nodup-fst).
    -/
lemma pi_eq_segments_k_alive
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (segs : List (List (Nat × Bool) × List (Nat × Bool)))
    (hpath_eq : path = (segs.map Prod.fst).flatten)
    (hseg_prov :
      ∀ (j : Nat) (hj : j < segs.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segs.take j).map Prod.fst).flatten)
          = (segs[j]'hj).2 :: tail_j)
    (hvm : ∀ p ∈ segs, p.1.map Prod.fst = p.2.map Prod.fst)
    (k : Nat) (hk_lt : k < segs.length)
    (hwindow : ∀ p ∈ (segs[k]'hk_lt).1, p ∈ path.take d)
    (ρ : List (Nat × Bool))
    (hρ_eq : ρ = asgn ++ ((segs.take k).map Prod.fst).flatten) :
    let remaining_π := (((segs.drop k).map Prod.fst).flatten).filter
      (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2))
    remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        |>.contains x.1)
      = (segs[k]'hk_lt).1 := by
  intro remaining_π
  -- Path nodup-fst (used throughout for disjointness arguments).
  have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
  -- prefix_k abbreviation.
  set prefix_k : List (Nat × Bool) := ((segs.take k).map Prod.fst).flatten with hprefix_k_def
  -- Steps 1 and 2: the selected clause under ρ has the variables of `segs[k].2`.
  -- Apply `iter_split_seg_eq_rtnkb_at_canonical_prefix` at i = k.
  have h_r_ρ_eq_segk2 :
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        = (segs[k]'hk_lt).2.map Prod.fst := by
    -- The lemma identifies `segs[k].2` with the selected clause under the
    -- assignment extended by `prefix_k`.
    have h := iter_split_seg_eq_rtnkb_at_canonical_prefix f asgn hnodup d path
      hpath segs hpath_eq hseg_prov k hk_lt
    -- combineRestrictions asgn prefix_k = asgn ++ prefix_k = ρ (path bits asgn-disjoint).
    have hprefix_disj_asgn : ∀ vb ∈ prefix_k,
        (asgn.any fun (w, _) => w == vb.1) = false := by
      intro vb hvb
      -- vb ∈ prefix_k ⊆ path
      have hvb_path : vb ∈ path := by
        rw [hpath_eq]; rw [hprefix_k_def] at hvb
        exact (List.IsPrefix.flatten
          (List.IsPrefix.map _ (List.take_prefix _ _))).subset hvb
      have hnone := canonical_dt_path_var_none f.val asgn f.property.2 d
        path hpath vb.1 vb.2 hvb_path
      -- restrictionAsFunction asgn vb.1 = none ⇒ no asgn entry has fst = vb.1.
      cases hany : asgn.any fun (w, _) => w == vb.1
      · rfl
      · exfalso
        rw [List.any_eq_true] at hany
        obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
        simp only [beq_iff_eq] at hw'_eq
        subst hw'_eq
        simp only [restrictionAsFunction] at hnone
        have hfind : asgn.find? (fun q => q.1 == vb.1) ≠ none := by
          rw [Ne, List.find?_eq_none]; push Not
          exact ⟨(vb.1, b'), hw'_mem, by simp⟩
        rcases hfind_eq : asgn.find? (fun q => q.1 == vb.1) with _ | ⟨_, _⟩
        · exact hfind hfind_eq
        · rw [hfind_eq] at hnone; cases hnone
    -- combineRestrictions asgn prefix_k = asgn ++ prefix_k.
    have h_combined_eq : combineRestrictions asgn prefix_k = asgn ++ prefix_k := by
      simp only [combineRestrictions]
      congr 1
      rw [List.filter_eq_self.mpr]
      intro p hp
      rw [Bool.not_eq_true', hprefix_disj_asgn p hp]
    -- ρ = asgn ++ prefix_k = combineRestrictions asgn prefix_k.
    have hρ_eq_combined : ρ = combineRestrictions asgn prefix_k := by
      rw [hρ_eq, h_combined_eq, hprefix_k_def]
    -- Conclude.
    rw [hρ_eq_combined]; exact h.symm
  -- Step 3: segs.drop k = segs[k] :: segs.drop (k+1) (when k < length).
  have hdrop_k_eq : segs.drop k = (segs[k]'hk_lt) :: segs.drop (k + 1) :=
    List.drop_eq_getElem_cons hk_lt
  -- (segs.drop k).map fst).flatten = segs[k].1 ++ ((segs.drop (k+1)).map fst).flatten.
  set rest_flat : List (Nat × Bool) :=
    ((segs.drop (k + 1)).map Prod.fst).flatten with hrest_flat_def
  have hdrop_flat_eq :
      ((segs.drop k).map Prod.fst).flatten = (segs[k]'hk_lt).1 ++ rest_flat := by
    rw [hdrop_k_eq, List.map_cons, List.flatten_cons]
  -- Step 4: remaining_π = segs[k].1 ++ rest_flat.filter window.
  --   (since segs[k].1 ⊆ path.take d ⇒ segs[k].1.filter window = segs[k].1).
  set window : (Nat × Bool) → Bool :=
    fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)
    with hwindow_def
  have hsegk1_filter_id : (segs[k]'hk_lt).1.filter window = (segs[k]'hk_lt).1 := by
    apply List.filter_eq_self.mpr
    intro p hp
    rw [hwindow_def]
    rw [List.any_eq_true]
    refine ⟨p, hwindow p hp, ?_⟩
    simp
  have hrem_decomp :
      remaining_π = (segs[k]'hk_lt).1 ++ rest_flat.filter window := by
    change ((segs.drop k).map Prod.fst).flatten.filter window = _
    rw [hdrop_flat_eq, List.filter_append, hsegk1_filter_id]
  -- Step 5: the selected clause under ρ has the variables of `segs[k].1`.
  have h_r_ρ_eq_segk1 :
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        = (segs[k]'hk_lt).1.map Prod.fst := by
    rw [h_r_ρ_eq_segk2]
    exact (hvm (segs[k]'hk_lt) (List.getElem_mem hk_lt)).symm
  -- Step 6: rewrite the filter using the variable equality from Step 5.
  set Q : (Nat × Bool) → Bool := fun x =>
    (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
      |>.contains x.1 with h_q_def
  set Q' : (Nat × Bool) → Bool := fun x =>
    (segs[k]'hk_lt).1.map Prod.fst |>.contains x.1 with h_q'_def
  have h_q_eq_q' : Q = Q' := by
    funext x
    rw [h_q_def, h_q'_def, h_r_ρ_eq_segk1]
  -- The goal (remaining_π.filter Q = segs[k].1) is on the binder remaining_π
  -- which simp would unfold; transform via hrem_decomp.
  change remaining_π.filter Q = (segs[k]'hk_lt).1
  rw [hrem_decomp, h_q_eq_q', List.filter_append]
  -- Goal: segs[k].1.filter Q' ++ (rest_flat.filter window).filter Q' = segs[k].1.
  -- First part: segs[k].1.filter Q' = segs[k].1 (every elem's fst is in segs[k].1.fst).
  have hsegk1_filter_q' : (segs[k]'hk_lt).1.filter Q' = (segs[k]'hk_lt).1 := by
    apply List.filter_eq_self.mpr
    intro p hp
    rw [h_q'_def]
    apply List.elem_eq_true_of_mem
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  -- Second part: (rest_flat.filter window).filter Q' = [] (rest's fsts disjoint
  -- from segs[k].1.fst by path nodup-fst).
  have hrest_filter_q' : (rest_flat.filter window).filter Q' = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp_filter h_q'_p
    -- p ∈ rest_flat.filter window ⊆ rest_flat = ((segs.drop (k+1)).map fst).flatten.
    have hp_rest : p ∈ rest_flat := List.mem_of_mem_filter hp_filter
    -- p.1 ∈ segs[k].1.fst from h_q'_p.
    have hp1_in_segk1 : p.1 ∈ (segs[k]'hk_lt).1.map Prod.fst := by
      rw [h_q'_def] at h_q'_p
      exact List.mem_of_elem_eq_true h_q'_p
    -- p.1 ∈ rest_flat.fst.
    have hp1_in_rest : p.1 ∈ rest_flat.map Prod.fst :=
      List.mem_map.mpr ⟨p, hp_rest, rfl⟩
    -- Path nodup-fst: segs[k].1.fst and rest_flat.fst are disjoint.
    -- path.fst = ((segs.take k).map fst).flatten.fst ++ segs[k].1.fst ++ rest_flat.fst.
    have hpath_fst_split :
        path.map Prod.fst =
          (prefix_k.map Prod.fst) ++ (segs[k]'hk_lt).1.map Prod.fst
            ++ rest_flat.map Prod.fst := by
      rw [hpath_eq]
      have hsplit : segs = segs.take k ++ segs.drop k := (List.take_append_drop k segs).symm
      conv_lhs => rw [hsplit]
      rw [hdrop_k_eq, List.map_append, List.map_cons,
        List.flatten_append, List.flatten_cons,
        List.map_append, List.map_append]
      rw [hprefix_k_def, hrest_flat_def]
      ac_rfl
    rw [hpath_fst_split] at hpath_nodup_fst
    -- The rightmost append: (prefix_k.fst ++ segk.fst) and rest_flat.fst disjoint.
    have hndp := hpath_nodup_fst
    have hdisj_outer :=
      List.disjoint_of_nodup_append hndp
    -- p.1 ∈ (prefix_k.fst ++ segs[k].1.fst) (via right summand)
    have hp1_in_left : p.1 ∈ prefix_k.map Prod.fst ++ (segs[k]'hk_lt).1.map Prod.fst :=
      List.mem_append_right _ hp1_in_segk1
    exact hdisj_outer hp1_in_left hp1_in_rest
  rw [hsegk1_filter_q', hrest_filter_q', List.append_nil]

#print axioms pi_eq_segments_k_alive

/- **The combined alive-state restriction is the next canonical prefix.**

    Under the alive-case bundle discriminant
    `ρ = asgn ++ ((segs.take k).map fst).flatten`,
    feeding `segs[k].1` (which equals `πI` by the preceding lemma) into
    `combineRestrictions ρ` yields
    exactly the `(k+1)`-canonical prefix:

        combineRestrictions ρ (segs[k].1) =
          asgn ++ ((segs.take (k+1)).map fst).flatten.

    This is the literal-list equality (not just function equality), and
    lets both sides of the bridge use the same combined assignment.

    *Proof.* Unfold `combineRestrictions`. The filter is a
    no-op because `segs[k].1`'s vars are disjoint from both `asgn`
    (`canonical_dt_path_var_none`) and the earlier `prefix_k`
    bits (path nodup-fst on disjoint segments).  Then
    `prefix_{k+1} = prefix_k ++ segs[k].1` by `List.take_succ`. -/
lemma combined_alive_eq_canonical_prefix_succ
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (segs : List (List (Nat × Bool) × List (Nat × Bool)))
    (hpath_eq : path = (segs.map Prod.fst).flatten)
    (k : Nat) (hk_lt : k < segs.length)
    (ρ : List (Nat × Bool))
    (hρ_eq : ρ = asgn ++ ((segs.take k).map Prod.fst).flatten) :
    combineRestrictions ρ (segs[k]'hk_lt).1 =
      asgn ++ ((segs.take (k+1)).map Prod.fst).flatten := by
  set prefix_k : List (Nat × Bool) := ((segs.take k).map Prod.fst).flatten
    with hprefix_k_def
  -- Path nodup-fst (for the disjointness arguments).
  have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
  -- prefix_{k+1} = prefix_k ++ segs[k].1.
  have hprefix_succ_eq :
      ((segs.take (k+1)).map Prod.fst).flatten = prefix_k ++ (segs[k]'hk_lt).1 := by
    have htake_eq : segs.take (k + 1) = segs.take k ++ [segs[k]'hk_lt] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt]; rfl
    rw [htake_eq, List.map_append, List.flatten_append, hprefix_k_def]
    simp
  -- Goal becomes: combineRestrictions ρ segs[k].1 = asgn ++ prefix_k ++ segs[k].1.
  rw [hprefix_succ_eq, ← List.append_assoc, ← hρ_eq]
  -- Unfold combineRestrictions.  Goal: ρ ++ segs[k].1.filter(¬ρ.any) = ρ ++ segs[k].1.
  unfold combineRestrictions
  congr 1
  -- segs[k].1.filter(¬ρ.any) = segs[k].1: each p ∈ segs[k].1 has p.1 ∉ ρ.fst.
  apply List.filter_eq_self.mpr
  intro p hp
  rw [Bool.not_eq_true']
  rw [hρ_eq, List.any_append, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · -- (a) asgn.any (z == p.1) = false: p ∈ segs[k].1 ⊆ path; via canonical-DT.
    have hp_path : p ∈ path := by
      rw [hpath_eq, List.mem_flatten]
      exact ⟨(segs[k]'hk_lt).1,
        List.mem_map.mpr ⟨segs[k]'hk_lt, List.getElem_mem hk_lt, rfl⟩, hp⟩
    have hnone := canonical_dt_path_var_none f.val asgn f.property.2 d
      path hpath p.1 p.2 hp_path
    cases hany : asgn.any fun (z, _) => z == p.1
    · rfl
    · exfalso
      rw [List.any_eq_true] at hany
      obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
      simp only [beq_iff_eq] at hw'_eq
      subst hw'_eq
      simp only [restrictionAsFunction] at hnone
      have hfind : asgn.find? (fun q => q.1 == p.1) ≠ none := by
        rw [Ne, List.find?_eq_none]; push Not
        exact ⟨(p.1, b'), hw'_mem, by simp⟩
      rcases hfind_eq : asgn.find? (fun q => q.1 == p.1) with _ | ⟨_, _⟩
      · exact hfind hfind_eq
      · rw [hfind_eq] at hnone; cases hnone
  · -- (b) prefix_k.any (z == p.1) = false: path nodup-fst + disjoint segments.
    cases hany : prefix_k.any fun (z, _) => z == p.1
    · rfl
    · exfalso
      rw [List.any_eq_true] at hany
      obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
      simp only [beq_iff_eq] at hw'_eq
      subst hw'_eq
      have hp1_in_prefix : p.1 ∈ prefix_k.map Prod.fst :=
        List.mem_map.mpr ⟨(p.1, b'), hw'_mem, rfl⟩
      have hp1_in_segk : p.1 ∈ (segs[k]'hk_lt).1.map Prod.fst :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      have hsegs_eq : segs = segs.take k ++ (segs[k]'hk_lt) :: segs.drop (k+1) := by
        have h1 := (List.take_append_drop k segs).symm
        rw [List.drop_eq_getElem_cons hk_lt] at h1
        exact h1
      have hpath_split : path.map Prod.fst =
          prefix_k.map Prod.fst ++ ((segs[k]'hk_lt).1.map Prod.fst ++
          ((segs.drop (k+1)).map Prod.fst).flatten.map Prod.fst) := by
        have hflat_eq : (segs.map Prod.fst).flatten =
            prefix_k ++ ((segs[k]'hk_lt).1 ++ ((segs.drop (k+1)).map Prod.fst).flatten) := by
          conv_lhs => rw [hsegs_eq]
          rw [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]
        rw [hpath_eq, hflat_eq, List.map_append, List.map_append]
      rw [hpath_split] at hpath_nodup_fst
      have hdisj := List.disjoint_of_nodup_append hpath_nodup_fst
      have hp1_in_right :
          p.1 ∈ (segs[k]'hk_lt).1.map Prod.fst ++
            ((segs.drop (k+1)).map Prod.fst).flatten.map Prod.fst :=
        List.mem_append_left _ hp1_in_segk
      exact hdisj hp1_in_prefix hp1_in_right

#print axioms combined_alive_eq_canonical_prefix_succ


/- **Straddler-exhaustion — `remaining_π` equals exactly the truncated segment.**

    Setting.  In the bundle's alive state with the canonical witness
    `(segs, k, partial_seg = [])`, the loop's `remaining_π` is fixed by
    the bundle invariant to be
        `remaining_π = ((segs.drop k).map fst).flatten.filter window`,
    where `window = path.take d`-membership.  In the **straddler regime**
    (`prefix_k.length ≤ d < prefix_{k+1}.length`), we claim more: the
    filter cuts away EVERYTHING except the truncated head of `segs[k].1`:

        `remaining_π = (segs[k].1).take (d - prefix_k.length)`.

    *Why this matters for the encoder step.*  At the encoder level, the next
    iteration's `remaining' = remaining_π.filter (¬πI.any)` where
    `πI ⊆ remaining_π`.  Combined with the straddler equality
    `πI = truncated`
    and this lemma's `remaining_π = truncated`, we get `remaining' = []`,
    so the recursive encoder call hits the base case immediately.  Thus
    the bridge's straddler-case obligation never needs to construct a
    valid `hloop'` — it's harmlessly discarded.

    *Proof outline (~60 lines).*
      Step 1.  Decompose `(segs.drop k) = segs[k] :: segs.drop (k+1)`,
               so `((segs.drop k).map fst).flatten = segs[k].1 ++ rest_flat`
               where `rest_flat = ((segs.drop (k+1)).map fst).flatten`.
      Step 2.  `List.filter_append`: `remaining_π = segs[k].1.filter window
                                                   ++ rest_flat.filter window`.
      Step 3.  `rest_flat.filter window = []`.
               Bits in rest_flat sit at positions ≥ prefix_{k+1}.length
               in path; since `prefix_{k+1}.length > d` (straddler hyp),
               these positions are ≥ d+1 > d.  Path-nodup-fst tells us
               `path.take d` and `path.drop d` have disjoint vars, so
               no rest_flat bit can satisfy `(path.take d).any (q.fst==p.fst
               ∧ q.snd==p.snd)`.  Conclude window p = false ∀ p ∈ rest_flat.
      Step 4.  `segs[k].1.filter window = (segs[k].1).take (d - prefix_k.length)`.
               This is the KEY straddler observation.  Using the path-bit
               positional structure:
                 path = prefix_k ++ segs[k].1 ++ rest_flat
                 path.take d = prefix_k ++ (segs[k].1).take (d - prefix_k.length)
                              (by splitting `List.take` across the append and
                               using `List.take_of_length_le h_prefix_k_le`).
               So bits of `(segs[k].1).take (d - prefix_k.length)` are in
               `path.take d` (window passes), and bits of
               `(segs[k].1).drop (d - prefix_k.length)` are at path
               positions ≥ d (window fails by path-nodup-fst).
               Apply `List.filter` on the take ++ drop decomposition.
      Step 5.  Combine: `remaining_π = trunc ++ [] = trunc`.

    The argument is purely positional, using path nodup-fst and take/drop
    arithmetic rather than clause-selection simplification. -/
lemma remaining_π_eq_truncated_at_alive_straddler
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (segs : List (List (Nat × Bool) × List (Nat × Bool)))
    (hpath_eq : path = (segs.map Prod.fst).flatten)
    (k : Nat) (hk_lt : k < segs.length)
    (h_prefix_k_le :
      ((segs.take k).map Prod.fst).flatten.length ≤ d)
    (h_straddler :
      d < ((segs.take (k + 1)).map Prod.fst).flatten.length) :
    let prefix_k : List (Nat × Bool) := ((segs.take k).map Prod.fst).flatten
    let truncated : List (Nat × Bool) :=
      (segs[k]'hk_lt).1.take (d - prefix_k.length)
    let window : (Nat × Bool) → Bool :=
      fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)
    (((segs.drop k).map Prod.fst).flatten).filter window = truncated := by
  -- Path nodup-fst.
  have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
  -- Local abbreviations (NOT via `set` — avoids motive shadowing of let-binders).
  let prefix_k : List (Nat × Bool) := ((segs.take k).map Prod.fst).flatten
  let seg_k : List (Nat × Bool) := (segs[k]'hk_lt).1
  let rest_flat : List (Nat × Bool) := ((segs.drop (k+1)).map Prod.fst).flatten
  let m : Nat := d - prefix_k.length
  let truncated : List (Nat × Bool) := seg_k.take m
  let window : (Nat × Bool) → Bool :=
    fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)
  change (((segs.drop k).map Prod.fst).flatten).filter window = truncated
  -- (segs.drop k) split.
  have hdrop_k_eq : segs.drop k = (segs[k]'hk_lt) :: segs.drop (k + 1) :=
    List.drop_eq_getElem_cons hk_lt
  have hdrop_flat_eq :
      ((segs.drop k).map Prod.fst).flatten = seg_k ++ rest_flat := by
    change ((segs.drop k).map Prod.fst).flatten =
         (segs[k]'hk_lt).1 ++ ((segs.drop (k+1)).map Prod.fst).flatten
    rw [hdrop_k_eq, List.map_cons, List.flatten_cons]
  -- prefix_{k+1} = prefix_k ++ seg_k (as flatten).
  have hprefix_succ_flat :
      ((segs.take (k+1)).map Prod.fst).flatten = prefix_k ++ seg_k := by
    change ((segs.take (k+1)).map Prod.fst).flatten =
         ((segs.take k).map Prod.fst).flatten ++ (segs[k]'hk_lt).1
    have htake_eq : segs.take (k + 1) = segs.take k ++ [segs[k]'hk_lt] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt]; rfl
    rw [htake_eq, List.map_append, List.flatten_append]; simp
  -- Derive a length fact bridging the let-defs to omega-visible form.
  have hpfx_len_eq :
      prefix_k.length = ((segs.take k).map Prod.fst).flatten.length := rfl
  have hseg_k_len_eq : seg_k.length = (segs[k]'hk_lt).1.length := rfl
  have hprefix_succ_len :
      ((segs.take (k+1)).map Prod.fst).flatten.length =
        prefix_k.length + seg_k.length := by
    rw [hprefix_succ_flat, List.length_append]
  -- m bounds: m < seg_k.length (from h_straddler).
  have hm_lt_seg_k : m < seg_k.length := by
    change d - prefix_k.length < seg_k.length
    have h := h_straddler
    rw [hprefix_succ_len] at h
    omega
  -- path = prefix_k ++ seg_k ++ rest_flat.
  have hpath_split : path = prefix_k ++ seg_k ++ rest_flat := by
    change path = ((segs.take k).map Prod.fst).flatten ++ (segs[k]'hk_lt).1 ++
                ((segs.drop (k+1)).map Prod.fst).flatten
    have hsegs_split : segs = segs.take k ++ (segs[k]'hk_lt) :: segs.drop (k+1) := by
      have h1 := (List.take_append_drop k segs).symm
      rw [hdrop_k_eq] at h1; exact h1
    rw [hpath_eq]
    conv_lhs => rw [hsegs_split]
    rw [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons,
        ← List.append_assoc]
  -- path.take d = prefix_k ++ truncated.
  have hpath_take_d : path.take d = prefix_k ++ truncated := by
    change path.take d = prefix_k ++ seg_k.take m
    rw [hpath_split]
    have hd_lt : d < (prefix_k ++ seg_k).length := by
      rw [List.length_append]
      have h := h_straddler
      rw [hprefix_succ_len] at h; exact h
    rw [List.take_append_of_le_length (le_of_lt hd_lt)]
    -- Goal: (prefix_k ++ seg_k).take d = prefix_k ++ seg_k.take m.
    have hd_eq : d = prefix_k.length + m := by
      change d = prefix_k.length + (d - prefix_k.length); omega
    rw [hd_eq, List.take_append]
    -- Goal: prefix_k.take (prefix_k.length + m) ++ seg_k.take (prefix_k.length + m - prefix_k.length)
    --     = prefix_k ++ seg_k.take m.
    congr 1
    · exact List.take_of_length_le (Nat.le_add_right _ _)
    · congr 1; omega
  -- Path-nodup-fst on the regrouped path = prefix_k ++ truncated ++ (seg_k.drop m ++ rest_flat).
  have hsplit_drop : seg_k ++ rest_flat = truncated ++ (seg_k.drop m ++ rest_flat) := by
    change (segs[k]'hk_lt).1 ++ ((segs.drop (k+1)).map Prod.fst).flatten =
         (segs[k]'hk_lt).1.take (d - ((segs.take k).map Prod.fst).flatten.length) ++
         ((segs[k]'hk_lt).1.drop (d - ((segs.take k).map Prod.fst).flatten.length) ++
          ((segs.drop (k+1)).map Prod.fst).flatten)
    rw [← List.append_assoc, List.take_append_drop]
  have hpath_split2 : path = prefix_k ++ truncated ++ (seg_k.drop m ++ rest_flat) := by
    rw [hpath_split, List.append_assoc, hsplit_drop, ← List.append_assoc]
  have hpath_nodup_fst2 :
      ((prefix_k ++ truncated ++ (seg_k.drop m ++ rest_flat)).map Prod.fst).Nodup := by
    rw [← hpath_split2]; exact hpath_nodup_fst
  have hdisj_outer :
      ((prefix_k ++ truncated).map Prod.fst).Disjoint
        ((seg_k.drop m ++ rest_flat).map Prod.fst) := by
    rw [List.map_append] at hpath_nodup_fst2
    exact List.disjoint_of_nodup_append hpath_nodup_fst2
  -- Filter computation.
  rw [hdrop_flat_eq, hsplit_drop, List.filter_append]
  -- Claim 1: truncated.filter window = truncated.
  have hfilt_trunc : truncated.filter window = truncated := by
    apply List.filter_eq_self.mpr
    intro p hp
    show window p = true
    have hp_in_take_d : p ∈ path.take d := by
      rw [hpath_take_d]; exact List.mem_append_right _ hp
    rw [List.any_eq_true]
    exact ⟨p, hp_in_take_d, by simp⟩
  -- Claim 2: (seg_k.drop m ++ rest_flat).filter window = [].
  have hfilt_rest : (seg_k.drop m ++ rest_flat).filter window = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp_mem hwin
    rw [List.any_eq_true] at hwin
    obtain ⟨q, hq_mem, hq_eq⟩ := hwin
    simp only [Bool.and_eq_true, beq_iff_eq] at hq_eq
    obtain ⟨hq1, _hq2⟩ := hq_eq
    have hq_in_pref : q ∈ prefix_k ++ truncated := by
      rw [← hpath_take_d]; exact hq_mem
    have hq1_in : q.1 ∈ (prefix_k ++ truncated).map Prod.fst :=
      List.mem_map.mpr ⟨q, hq_in_pref, rfl⟩
    have hp1_in : p.1 ∈ (seg_k.drop m ++ rest_flat).map Prod.fst :=
      List.mem_map.mpr ⟨p, hp_mem, rfl⟩
    rw [← hq1] at hp1_in
    exact hdisj_outer hq1_in hp1_in
  rw [hfilt_trunc, hfilt_rest, List.append_nil]

#print axioms remaining_π_eq_truncated_at_alive_straddler


end Circuits.CnfDnf.Restrictions
