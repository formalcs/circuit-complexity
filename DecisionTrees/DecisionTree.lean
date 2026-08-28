import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import Formulas.CnfDnf.CnfDnfBasic

namespace DecisionTrees
open Circuits
open Circuits.CnfDnf

inductive DecisionTree where
  | dtLeaf : Bool -> DecisionTree
  | dtNode : Nat -> DecisionTree -> DecisionTree -> DecisionTree
  deriving Repr

open DecisionTree

def decisionTreeNodeCount (tree : DecisionTree) : Nat :=
  match tree with
  | dtLeaf _ => 1
  | dtNode _ left right =>
      1 + (decisionTreeNodeCount left) + (decisionTreeNodeCount right)

def decisionTreeDepth (tree : DecisionTree) : Nat :=
  match tree with
  | dtLeaf _ => 0
  | dtNode _ left right =>
      1 + (max (decisionTreeDepth left) (decisionTreeDepth right))

def evalDecisionTree (tree : DecisionTree) (inputs : List Bool) : Bool :=
  match tree with
  | dtLeaf bit => bit
  | dtNode i left right =>
      match inputs[i]? with
      | none => false
      | some input =>
          match input with
          | false => evalDecisionTree left inputs
          | true => evalDecisionTree right inputs

-- Convert a DecisionTree to a DNF (OR of ANDs) as an UnboundedFanInFormula.
-- Each root-to-1-leaf path becomes an AND clause of literals.
-- dtNode i left right: going left means input i is 0 (negated), right means input i is 1.

open UnboundedFanInFormula

def decisionTreeToDNFClauses (tree : DecisionTree)
    (path : List UnboundedFanInFormula) : List UnboundedFanInFormula :=
  match tree with
  | dtLeaf true => [andGate path]
  | dtLeaf false => []
  | dtNode i left right =>
      (decisionTreeToDNFClauses left (path ++ [(inputGate i true)])) ++
      (decisionTreeToDNFClauses right (path ++ [inputGate i false]))

def decisionTreeToDNF (tree : DecisionTree) : UnboundedFanInFormula :=
  orGate (decisionTreeToDNFClauses tree [])

-- Collect all input indices from a DecisionTree
def dtCollectInputIndices (tree : DecisionTree) : List Nat :=
  match tree with
  | dtLeaf _ => []
  | dtNode i left right =>
      [i] ++ dtCollectInputIndices left ++ dtCollectInputIndices right

-- Collect input indices from a path (list of circuit gates)
def collectPathIndices (path : List UnboundedFanInFormula) : List Nat :=
  path.flatMap ufiCollectInputIndices

-- ============================================================
-- Direction 1: DNF inputs ⊆ DT inputs (unconditional)
-- ============================================================

-- Helper: any index in the clauses comes from the path or the tree
theorem dt_to_dnfClauses_indices_sub (tree : DecisionTree)
    (path : List UnboundedFanInFormula) (x : Nat)
    (h : x ∈ (decisionTreeToDNFClauses tree path).flatMap ufiCollectInputIndices) :
    x ∈ collectPathIndices path ∨ x ∈ dtCollectInputIndices tree := by
  induction tree generalizing path with
  | dtLeaf b =>
    cases b with
    | true =>
      simp only [decisionTreeToDNFClauses, List.flatMap_cons, List.flatMap_nil,
                  List.append_nil] at h
      unfold ufiCollectInputIndices at h
      exact Or.inl h
    | false =>
      simp [decisionTreeToDNFClauses, List.flatMap_nil] at h
  | dtNode i left right ih_left ih_right =>
    simp only [decisionTreeToDNFClauses, List.flatMap_append] at h
    rw [List.mem_append] at h
    cases h with
    | inl h_left =>
      have := ih_left (path ++ [inputGate i true]) h_left
      cases this with
      | inl h_path =>
        rw [collectPathIndices, List.flatMap_append, List.mem_append] at h_path
        simp only [List.flatMap_cons, List.flatMap_nil, ufiCollectInputIndices,
                    List.append_nil] at h_path
        cases h_path with
        | inl h_orig => exact Or.inl h_orig
        | inr h_new =>
          right; simp only [dtCollectInputIndices, List.cons_append, List.nil_append,
            List.mem_cons, List.mem_append]
          left; simp only [List.mem_cons, List.not_mem_nil, or_false] at h_new; exact h_new
      | inr h_tree =>
        right; simp only [dtCollectInputIndices, List.cons_append, List.nil_append,
          List.mem_cons, List.mem_append]; right; left; exact h_tree
    | inr h_right =>
      have := ih_right (path ++ [inputGate i false]) h_right
      cases this with
      | inl h_path =>
        rw [collectPathIndices, List.flatMap_append, List.mem_append] at h_path
        simp only [List.flatMap_cons, List.flatMap_nil, ufiCollectInputIndices,
                    List.append_nil] at h_path
        cases h_path with
        | inl h_orig => exact Or.inl h_orig
        | inr h_new =>
          right; simp only [dtCollectInputIndices, List.cons_append, List.nil_append,
            List.mem_cons, List.mem_append]
          left; simp only [List.mem_cons, List.not_mem_nil, or_false] at h_new; exact h_new
      | inr h_tree =>
        right; simp only [dtCollectInputIndices, List.cons_append, List.nil_append,
          List.mem_cons, List.mem_append]; right; right; exact h_tree

-- DNF inputs ⊆ DT inputs (unconditional)
theorem dnf_inputs_sub_dt_inputs (tree : DecisionTree) (x : Nat)
    (h : x ∈ ufiCollectInputIndices (decisionTreeToDNF tree)) :
    x ∈ dtCollectInputIndices tree := by
  unfold decisionTreeToDNF ufiCollectInputIndices at h
  have := dt_to_dnfClauses_indices_sub tree [] x h
  simp only [collectPathIndices, List.flatMap_nil, List.not_mem_nil, false_or] at this
  exact this

-- Helper: andGate over append factors as conjunction
private theorem ufi_eval_andGate_append (xs ys : List UnboundedFanInFormula)
    (inputs : List Bool) :
    ufiFormulaEval (andGate (xs ++ ys)) inputs =
    match (ufiFormulaEval (andGate xs) inputs, ufiFormulaEval (andGate ys) inputs) with
    | (true, true) => true
    | _ => false := by
  induction xs with
  | nil =>
    simp only [List.nil_append, ufiFormulaEval]
    cases ufiFormulaEval (andGate ys) inputs <;> rfl
  | cons x xs ih =>
    simp only [List.cons_append, ufiFormulaEval]
    cases ufiFormulaEval x inputs with
    | false => rfl
    | true =>
      exact ih

-- Helper: orGate over append is disjunction
private theorem ufi_eval_orGate_append (xs ys : List UnboundedFanInFormula)
    (inputs : List Bool) :
    ufiFormulaEval (orGate (xs ++ ys)) inputs =
    match ufiFormulaEval (orGate xs) inputs with
    | true => true
    | false => ufiFormulaEval (orGate ys) inputs := by
  induction xs with
  | nil => simp only [List.nil_append, ufiFormulaEval]
  | cons x xs ih =>
    simp only [List.cons_append, ufiFormulaEval]
    cases ufiFormulaEval x inputs with
    | true => rfl
    | false => exact ih

-- Helper: andGate [single] evaluates the same as the single gate
private theorem ufi_eval_andGate_singleton (g : UnboundedFanInFormula)
    (inputs : List Bool) :
    ufiFormulaEval (andGate [g]) inputs = ufiFormulaEval g inputs := by
  simp only [ufiFormulaEval]
  cases ufiFormulaEval g inputs <;> simp_all

-- Helper: eval of inputGate gate with out-of-range index.

private theorem ufi_eval_input_some (i : Nat) (negated : Bool) (inputs : List Bool) (v : Bool)
    (h : inputs[i]? = some v) :
    ufiFormulaEval (inputGate i negated) inputs =
    match negated with | true => Bool.not v | false => v := by
  rw [ufiFormulaEval_input_some i negated v inputs h]
  cases negated <;> rfl

-- Generalized lemma: the orGate of clauses = (path satisfied) AND (tree result).
-- Requires that every input index occurring in the tree is within `inputs`.
private theorem decisionTreeToDNFClauses_eval
    (tree : DecisionTree) (path : List UnboundedFanInFormula)
    (inputs : List Bool)
    (h_range : ∀ i ∈ dtCollectInputIndices tree, i < inputs.length) :
    ufiFormulaEval (orGate (decisionTreeToDNFClauses tree path)) inputs =
    match (ufiFormulaEval (andGate path) inputs, evalDecisionTree tree inputs) with
    | (true, true) => true
    | _ => false := by
  induction tree generalizing path with
  | dtLeaf b =>
    cases b with
    | true =>
      simp only [decisionTreeToDNFClauses, evalDecisionTree, ufiFormulaEval]
      cases ufiFormulaEval (andGate path) inputs <;> rfl
    | false =>
      simp only [decisionTreeToDNFClauses, evalDecisionTree, ufiFormulaEval]
      cases ufiFormulaEval (andGate path) inputs <;> rfl
  | dtNode i left right ih_left ih_right =>
    -- Derive sub-range hypotheses for children
    have h_i_in : i ∈ dtCollectInputIndices (dtNode i left right) := by
      change i ∈ [i] ++ dtCollectInputIndices left ++ dtCollectInputIndices right
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
    have hi_lt : i < inputs.length := h_range i h_i_in
    have h_l_range : ∀ j ∈ dtCollectInputIndices left, j < inputs.length := by
      intro j hj
      apply h_range
      change j ∈ [i] ++ dtCollectInputIndices left ++ dtCollectInputIndices right
      exact List.mem_append_left _ (List.mem_append_right [i] hj)
    have h_r_range : ∀ j ∈ dtCollectInputIndices right, j < inputs.length := by
      intro j hj
      apply h_range
      change j ∈ [i] ++ dtCollectInputIndices left ++ dtCollectInputIndices right
      exact List.mem_append_right _ hj
    simp only [decisionTreeToDNFClauses]
    rw [ufi_eval_orGate_append, ih_left _ h_l_range, ih_right _ h_r_range]
    -- Case-split on path and input bit
    cases hp : ufiFormulaEval (andGate path) inputs with
    | false =>
      -- Path not satisfied ⇒ any extension also not satisfied
      have h_ext : ∀ g, ufiFormulaEval (andGate (path ++ [g])) inputs = false := by
        intro g; rw [ufi_eval_andGate_append]; simp [hp]
      rw [h_ext, h_ext]
    | true =>
      -- Path satisfied, split on input bit at position i
      cases hg : inputs[i]? with
      | none =>
        -- The index is in range, so `inputs[i]?` cannot be `none` — contradiction.
        exfalso
        have hsome : inputs[i]? = some (inputs[i]'hi_lt) := by
          exact List.getElem?_eq_some_iff.mpr ⟨hi_lt, rfl⟩
        rw [hg] at hsome
        exact absurd hsome (by intro h; cases h)
      | some bit =>
        cases bit with
        | false =>
          -- inputGate i = 0: inputGate i true gives one (negated), inputGate i false gives zero
          have hg' : inputs[i]? = some false := by
            exact hg
          have h_ext_true : ufiFormulaEval (andGate (path ++ [inputGate i true])) inputs = true :=
          by
            rw [ufi_eval_andGate_append, ufi_eval_andGate_singleton,
                ufi_eval_input_some i true inputs false hg]
            simp [hp, Bool.not]
          have h_ext_false : ufiFormulaEval (andGate (path ++ [inputGate i false])) inputs = false
          := by
            rw [ufi_eval_andGate_append, ufi_eval_andGate_singleton,
                ufi_eval_input_some i false inputs false hg]
            simp [hp]
          rw [h_ext_true, h_ext_false]
          -- DT goes left when input i = 0
          simp only [evalDecisionTree, hg']
          cases evalDecisionTree left inputs <;> rfl
        | true =>
          -- inputGate i = 1: inputGate i true gives zero (negated), inputGate i false gives one
          have hg' : inputs[i]? = some true := by
            exact hg
          have h_ext_true : ufiFormulaEval (andGate (path ++ [inputGate i true])) inputs = false :=
          by
            rw [ufi_eval_andGate_append, ufi_eval_andGate_singleton,
                ufi_eval_input_some i true inputs true hg]
            simp [hp, Bool.not]
          have h_ext_false : ufiFormulaEval (andGate (path ++ [inputGate i false]))
                                              inputs = true := by
            rw [ufi_eval_andGate_append, ufi_eval_andGate_singleton,
                ufi_eval_input_some i false inputs true hg]
            simp [hp]
          rw [h_ext_true, h_ext_false]
          -- DT goes right when input i = 1
          simp only [evalDecisionTree, hg']

theorem decisionTreeToDNF_eval_equiv (tree : DecisionTree)
    (inputs : List Bool)
    (h_range : ∀ i ∈ dtCollectInputIndices tree, i < inputs.length) :
  evalDecisionTree tree inputs = ufiFormulaEval (decisionTreeToDNF tree) inputs
  := by
  unfold decisionTreeToDNF
  rw [decisionTreeToDNFClauses_eval _ _ _ h_range]
  simp only [ufiFormulaEval]
  cases evalDecisionTree tree inputs <;> rfl

-- Extract (variable_index, is_negated) pairs from an AND-of-inputs gate
def extractAndLiterals (gate : UnboundedFanInFormula) : List (Nat × Bool) :=
  match gate with
  | andGate gates => gates.filterMap fun g =>
      match g with
      | inputGate i b => some (i, b)
      | _ => none
  | _ => []

/-- Remove duplicates keeping the first occurrence of each element.
    Unlike `List.dedup` (which keeps the last occurrence via `List.pwFilter`),
    this preserves the clause-by-clause ordering needed for the canonical DT:
    when applied to `(clauses.flatMap (fun c => c.map Prod.fst))`, all variables
    of clause 0 appear first, then new variables of clause 1, etc.

    Example: `dedupFirst [1, 3, 2, 3] = [1, 3, 2]` (not `[1, 2, 3]`). -/
def dedupFirst [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.any (· == x) then acc else acc ++ [x]) []

private theorem dedupFirst_foldl_mem [BEq α] [LawfulBEq α]
    (l : List α) (acc : List α) (x : α) :
    x ∈ l.foldl (fun acc x =>
      if acc.any (· == x) then acc else acc ++ [x]) acc ↔
    x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp [List.foldl]
  | cons a t ih =>
    simp only [List.foldl, List.mem_cons]
    by_cases ha : (acc.any (· == a)) = true
    · rw [if_pos ha, ih]
      have ha_in_acc : a ∈ acc := by
        rw [List.any_eq_true] at ha
        obtain ⟨y, hy, hbeq⟩ := ha
        exact eq_of_beq hbeq ▸ hy
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl ha_in_acc
        · exact Or.inr h
    · rw [if_neg ha, ih]
      simp [List.mem_append]
      tauto

theorem mem_dedupFirst [BEq α] [LawfulBEq α] {l : List α} {x : α} :
    x ∈ dedupFirst l ↔ x ∈ l := by
  simp only [dedupFirst]
  rw [dedupFirst_foldl_mem]
  simp

-- Simplify clauses assuming variable i is zero (left branch in decision tree)
-- Literal (i, true) = negated: not(0) = 1, satisfied → remove from clause
-- Literal (i, false) = non-negated: 0, not satisfied → remove entire clause
def simplifyClausesLeft (clauses : List (List (Nat × Bool))) (i : Nat) :
    List (List (Nat × Bool)) :=
  (clauses.filter (fun c => !c.any (fun lit => lit.1 == i && !lit.2))).map
    (fun c => c.filter (fun lit => !(lit.1 == i && lit.2)))

-- Simplify clauses assuming variable i is one (right branch in decision tree)
-- Literal (i, false) = non-negated: 1, satisfied → remove from clause
-- Literal (i, true) = negated: not(1) = 0, not satisfied → remove entire clause
def simplifyClausesRight (clauses : List (List (Nat × Bool))) (i : Nat) :
    List (List (Nat × Bool)) :=
  (clauses.filter (fun c => !c.any (fun lit => lit.1 == i && lit.2))).map
    (fun c => c.filter (fun lit => !(lit.1 == i && !lit.2)))

-- Evaluate a single literal: (variable_index, is_negated) pair.
-- Aligns with `ufiFormulaEval` on `inputGate`: an out-of-range literal is false,
-- independently of its polarity.
def evalLiteral (inputs : List Bool) (lit : Nat × Bool) : Bool :=
  match inputs[lit.1]? with
  | none => false
  | some v =>
    match lit.2 with
    | true => Bool.not v
    | false => v

-- Evaluate a clause: conjunction of all literals
def evalClause (inputs : List Bool) : List (Nat × Bool) → Bool
  | [] => true
  | lit :: rest =>
    match evalLiteral inputs lit with
    | false => false
    | true => evalClause inputs rest

-- Evaluate clauses: disjunction of all clauses
def evalClauses (inputs : List Bool) : List (List (Nat × Bool)) → Bool
  | [] => false
  | c :: rest =>
    match evalClause inputs c with
    | true => true
    | false => evalClauses inputs rest

-- evalLiteral matches ufiFormulaEval of inputGate
private theorem evalLiteral_eq_input (inputs : List Bool) (j : Nat) (neg : Bool) :
    evalLiteral inputs (j, neg) = ufiFormulaEval (inputGate j neg) inputs := by
  unfold evalLiteral ufiFormulaEval
  cases inputs[j]? <;> cases neg <;> rfl

-- Evaluating extracted literals agrees with evaluating their `andGate`.
private theorem evalClause_eq_andGate_inputs (inputs : List Bool)
    (gates : List UnboundedFanInFormula)
    (h : gates.all isInput = true) :
    evalClause inputs (extractAndLiterals (andGate gates)) =
    ufiFormulaEval (andGate gates) inputs := by
  simp only [extractAndLiterals]
  induction gates with
  | nil => simp [List.filterMap, evalClause, ufiFormulaEval]
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hg, hgs⟩ := h
    cases g with
    | inputGate i b =>
      simp only [List.filterMap_cons, evalClause]
      rw [evalLiteral_eq_input, ih hgs]
      -- The RHS unfolds via the andGate cons equation
      conv_rhs => unfold ufiFormulaEval
      rfl
    | _ => simp [isInput] at hg

-- evalClause for extracted literals equals ufiFormulaEval for isAndOfInputsOnly gate
private theorem evalClause_eq_gate (inputs : List Bool)
    (gate : UnboundedFanInFormula)
    (h : isAndOfInputsOnly gate = true) :
    evalClause inputs (extractAndLiterals gate) = ufiFormulaEval gate inputs := by
  cases gate with
  | andGate gates =>
    simp only [isAndOfInputsOnly] at h
    exact evalClause_eq_andGate_inputs inputs gates h
  | _ => simp [isAndOfInputsOnly] at h

-- evalClauses for extracted clause lists equals ufiFormulaEval for orGate of DNF
theorem evalClauses_eq_dnf (inputs : List Bool)
    (gates : List UnboundedFanInFormula)
    (h : gates.all isAndOfInputsOnly = true) :
    evalClauses inputs (gates.map extractAndLiterals) =
    ufiFormulaEval (orGate gates) inputs := by
  induction gates with
  | nil => simp [evalClauses, List.map, ufiFormulaEval]
  | cons g gs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hg, hgs⟩ := h
    simp only [List.map_cons, evalClauses, ufiFormulaEval]
    rw [evalClause_eq_gate inputs g hg]
    cases ufiFormulaEval g inputs <;> simp [ih hgs]

-- ============================================================
-- Simplification lemmas
-- ============================================================

-- When input i = zero: a clause is satisfied after simplify_left iff it was satisfied before
private theorem evalClause_simplify_left (inputs : List Bool) (c : List (Nat × Bool)) (i : Nat)
    (hg : inputs[i]? = some false) :
    evalClause inputs (c.filter (fun lit => !(lit.1 == i && lit.2))) =
    (if c.any (fun lit => lit.1 == i && !lit.2) then false
     else evalClause inputs c) := by
  induction c with
  | nil => rfl
  | cons lit rest ih =>
    simp only [List.any_cons, List.filter_cons]
    by_cases h_elim : (lit.1 == i && !lit.2) = true
    · simp only [h_elim, Bool.true_or, ite_true]
      have hliti : lit.1 = i := by
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h_elim; exact h_elim.1
      have hlitn : lit.2 = false := by
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h_elim; exact h_elim.2
      have heval : evalLiteral inputs lit = false := by
        change evalLiteral inputs (lit.1, lit.2) = _
        rw [hliti, hlitn]; simp only [evalLiteral, hg]
      have hkeep : (!(lit.1 == i && lit.2)) = true := by simp [hlitn]
      simp only [hkeep, ite_true, evalClause, heval]
    · simp only [h_elim, Bool.false_or]
      by_cases h_remove : (lit.1 == i && lit.2) = true
      · simp only [h_remove, Bool.not_true]
        have hliti : lit.1 = i := by
          simp only [Bool.and_eq_true, beq_iff_eq] at h_remove; exact h_remove.1
        have hlitn : lit.2 = true := by
          simp only [Bool.and_eq_true, beq_iff_eq] at h_remove; exact h_remove.2
        have heval : evalLiteral inputs lit = true := by
          change evalLiteral inputs (lit.1, lit.2) = _
          rw [hliti, hlitn]; simp only [evalLiteral, hg, Bool.not]
        simp only [evalClause, heval]
        exact ih
      · simp only [h_remove, Bool.not_false, ite_true, evalClause]
        cases heval : evalLiteral inputs lit with
        | false => simp
        | true => exact ih

-- When input i = one: a clause is satisfied after simplify_right iff it was satisfied before
private theorem evalClause_simplify_right (inputs : List Bool) (c : List (Nat × Bool)) (i : Nat)
    (hg : inputs[i]? = some true) :
    evalClause inputs (c.filter (fun lit => !(lit.1 == i && !lit.2))) =
    (if c.any (fun lit => lit.1 == i && lit.2) then false
     else evalClause inputs c) := by
  induction c with
  | nil => rfl
  | cons lit rest ih =>
    simp only [List.any_cons, List.filter_cons]
    by_cases h_elim : (lit.1 == i && lit.2) = true
    · simp only [h_elim, Bool.true_or, ite_true]
      have hliti : lit.1 = i := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h_elim; exact h_elim.1
      have hlitn : lit.2 = true := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h_elim; exact h_elim.2
      have heval : evalLiteral inputs lit = false := by
        change evalLiteral inputs (lit.1, lit.2) = _
        rw [hliti, hlitn]; simp only [evalLiteral, hg, Bool.not]
      have hkeep : (!(lit.1 == i && !lit.2)) = true := by simp [hlitn]
      simp only [hkeep, ite_true, evalClause, heval]
    · simp only [h_elim, Bool.false_or]
      by_cases h_remove : (lit.1 == i && !lit.2) = true
      · simp only [h_remove, Bool.not_true]
        have hliti : lit.1 = i := by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h_remove; exact h_remove.1
        have hlitn : lit.2 = false := by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h_remove; exact h_remove.2
        have heval : evalLiteral inputs lit = true := by
          change evalLiteral inputs (lit.1, lit.2) = _
          rw [hliti, hlitn]; simp only [evalLiteral, hg]
        simp only [evalClause, heval]
        exact ih
      · simp only [h_remove, Bool.not_false, ite_true, evalClause]
        cases heval : evalLiteral inputs lit with
        | false => simp
        | true => exact ih

-- Helper: clause evaluates to zero when it contains a falsified literal
private theorem evalClause_zero_of_any (inputs : List Bool) (c : List (Nat × Bool))
    (lit : Nat × Bool) (hlit_mem : lit ∈ c) (hlit_eval : evalLiteral inputs lit = false) :
    evalClause inputs c = false := by
  induction c with
  | nil => simp at hlit_mem
  | cons l ls ihl =>
    simp only [evalClause]
    rcases List.mem_cons.mp hlit_mem with rfl | hmem
    · rw [hlit_eval]
    · cases evalLiteral inputs l with
      | false => rfl
      | true => exact ihl hmem

-- evalClauses respects simplifyClausesLeft
theorem evalClauses_simplify_left (inputs : List Bool)
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (hg : inputs[i]? = some false) :
    evalClauses inputs (simplifyClausesLeft clauses i) =
    evalClauses inputs clauses := by
  induction clauses with
  | nil => rfl
  | cons c rest ih =>
    simp only [simplifyClausesLeft, List.filter_cons]
    by_cases h_elim : c.any (fun lit => lit.1 == i && !lit.2) = true
    · simp only [h_elim, Bool.not_true]
      have hc : evalClause inputs c = false := by
        simp only [List.any_eq_true] at h_elim
        obtain ⟨lit, hlit_mem, hlit_cond⟩ := h_elim
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hlit_cond
        apply evalClause_zero_of_any inputs c lit hlit_mem
        change evalLiteral inputs (lit.1, lit.2) = _
        rw [hlit_cond.1, hlit_cond.2]; simp only [evalLiteral, hg]
      simp only [evalClauses, hc]
      exact ih
    · simp only [h_elim, Bool.not_false, ite_true, List.map_cons, evalClauses]
      rw [evalClause_simplify_left inputs c i hg, if_neg (by simpa using h_elim)]
      cases evalClause inputs c with
      | true => rfl
      | false => exact ih

-- evalClauses respects simplifyClausesRight
theorem evalClauses_simplify_right (inputs : List Bool)
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (hg : inputs[i]? = some true) :
    evalClauses inputs (simplifyClausesRight clauses i) =
    evalClauses inputs clauses := by
  induction clauses with
  | nil => rfl
  | cons c rest ih =>
    simp only [simplifyClausesRight, List.filter_cons]
    by_cases h_elim : c.any (fun lit => lit.1 == i && lit.2) = true
    · simp only [h_elim, Bool.not_true]
      have hc : evalClause inputs c = false := by
        simp only [List.any_eq_true] at h_elim
        obtain ⟨lit, hlit_mem, hlit_cond⟩ := h_elim
        simp only [Bool.and_eq_true, beq_iff_eq] at hlit_cond
        apply evalClause_zero_of_any inputs c lit hlit_mem
        change evalLiteral inputs (lit.1, lit.2) = _
        rw [hlit_cond.1, hlit_cond.2]; simp only [evalLiteral, hg, Bool.not]
      simp only [evalClauses, hc]
      exact ih
    · simp only [h_elim, Bool.not_false, ite_true, List.map_cons, evalClauses]
      rw [evalClause_simplify_right inputs c i hg, if_neg (by simpa using h_elim)]
      cases evalClause inputs c with
      | true => rfl
      | false => exact ih

/-- A DT has "disjoint paths" if the root variable doesn't appear in any subtree,
    and subtrees also have disjoint paths. -/
def DTPathsVarDisjoint : DecisionTree → Prop
  | .dtLeaf _ => True
  | .dtNode v left right =>
      v ∉ dtCollectInputIndices left ∧
      v ∉ dtCollectInputIndices right ∧
      DTPathsVarDisjoint left ∧
      DTPathsVarDisjoint right

-- ────────────────────────────────────────────────────────────────────────
-- §  simplifyClausesLeft / right: variable removal, nodup, subset
-- ────────────────────────────────────────────────────────────────────────

/-- `simplifyClausesLeft clauses i` removes variable `i` from all output clauses. -/
lemma simplifyClausesLeft_removes_var
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (c : List (Nat × Bool))
    (hc : c ∈ simplifyClausesLeft clauses i) :
    i ∉ c.map Prod.fst := by
  simp only [simplifyClausesLeft] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hc'_in, hc'_outer⟩ := List.mem_filter.mp hc'_mem
  intro hi
  obtain ⟨⟨w, neg⟩, hw_mem, (hw_eq : w = i)⟩ := List.mem_map.mp hi
  rw [hw_eq] at hw_mem
  obtain ⟨hw_in_c', hw_kept⟩ := List.mem_filter.mp hw_mem
  cases neg with
  | false =>
    have h_any : c'.any (fun lit => lit.1 == i && !lit.2) = true :=
      List.any_eq_true.mpr ⟨(i, false), hw_in_c', by simp⟩
    simp [h_any] at hc'_outer
  | true => simp at hw_kept

/-- `simplifyClausesRight clauses i` removes variable `i` from all output clauses. -/
lemma simplifyClausesRight_removes_var
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (c : List (Nat × Bool))
    (hc : c ∈ simplifyClausesRight clauses i) :
    i ∉ c.map Prod.fst := by
  simp only [simplifyClausesRight] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hc'_in, hc'_outer⟩ := List.mem_filter.mp hc'_mem
  intro hi
  obtain ⟨⟨w, neg⟩, hw_mem, (hw_eq : w = i)⟩ := List.mem_map.mp hi
  rw [hw_eq] at hw_mem
  obtain ⟨hw_in_c', hw_kept⟩ := List.mem_filter.mp hw_mem
  cases neg with
  | true =>
    have h_any : c'.any (fun lit => lit.1 == i && lit.2) = true :=
      List.any_eq_true.mpr ⟨(i, true), hw_in_c', by simp⟩
    simp [h_any] at hc'_outer
  | false => simp at hw_kept

/-- `simplifyClausesLeft` preserves Nodup on clause variables. -/
lemma simplifyClausesLeft_preserves_nodup
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (hnd : ∀ c ∈ clauses, (c.map Prod.fst).Nodup) :
    ∀ c ∈ simplifyClausesLeft clauses i, (c.map Prod.fst).Nodup := by
  intro c hc
  simp only [simplifyClausesLeft] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hc'_in, _⟩ := List.mem_filter.mp hc'_mem
  exact (hnd c' hc'_in).sublist (List.filter_sublist.map _)

/-- `simplifyClausesRight` preserves Nodup on clause variables. -/
lemma simplifyClausesRight_preserves_nodup
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (hnd : ∀ c ∈ clauses, (c.map Prod.fst).Nodup) :
    ∀ c ∈ simplifyClausesRight clauses i, (c.map Prod.fst).Nodup := by
  intro c hc
  simp only [simplifyClausesRight] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hc'_in, _⟩ := List.mem_filter.mp hc'_mem
  exact (hnd c' hc'_in).sublist (List.filter_sublist.map _)

/-- Variables in `simplifyClausesLeft` output come from the input clauses. -/
lemma simplifyClausesLeft_vars_subset
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (w : Nat) (neg : Bool) (c : List (Nat × Bool))
    (hc : c ∈ simplifyClausesLeft clauses i)
    (hw : (w, neg) ∈ c) :
    ∃ c' ∈ clauses, (w, neg) ∈ c' := by
  simp only [simplifyClausesLeft] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hc'_in, _⟩ := List.mem_filter.mp hc'_mem
  exact ⟨c', hc'_in, List.mem_of_mem_filter hw⟩

/-- Variables in `simplifyClausesRight` output come from the input clauses. -/
lemma simplifyClausesRight_vars_subset
    (clauses : List (List (Nat × Bool))) (i : Nat)
    (w : Nat) (neg : Bool) (c : List (Nat × Bool))
    (hc : c ∈ simplifyClausesRight clauses i)
    (hw : (w, neg) ∈ c) :
    ∃ c' ∈ clauses, (w, neg) ∈ c' := by
  simp only [simplifyClausesRight] at hc
  obtain ⟨c', hc'_mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hc'_in, _⟩ := List.mem_filter.mp hc'_mem
  exact ⟨c', hc'_in, List.mem_of_mem_filter hw⟩

end DecisionTrees
