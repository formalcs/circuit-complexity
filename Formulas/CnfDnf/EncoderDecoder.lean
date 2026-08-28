import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import DecisionTrees.DecisionTree
import Formulas.CnfDnf.CnfDnfBasic
import Formulas.CnfDnf.CnfDnfFamilies
import Formulas.CnfDnf.RandomRestriction
import Formulas.CnfDnf.SwitchingLemmaBasic
import Formulas.CnfDnf.SwitchingLemmaCore
import Formulas.CnfDnf.SwitchingLemmaCanonicalDT
import Mathlib.Data.List.TakeWhile

namespace Circuits.CnfDnf.Restrictions

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.flexible false
open Circuits.CnfDnf.Families
open DecisionTrees
open Lists.ListLemmas


/-- Encode a chunk by replacing each variable with its position in T_i. -/
def encoderChunk
    (T_i : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    : List (Nat × Bool) :=
  chunk.map fun (v, dir) =>
    let pos := findPositionInClause' T_i v
    (pos, dir)

/-- Auxiliary for the iterative encoder.  The final dead-variable
    assignment is the first component and the encoded chunks are the second. -/
def beameEncoderAux
    (fuel : Nat)
    (remaining_π : List (Nat × Bool))
    (clauses : List (List (Nat × Bool)))
    (ρ : List (Nat × Bool))
    (dead_acc : List (Nat × Bool))
    : List (Nat × Bool) × List (List (Nat × Bool)) :=
  match fuel with
  | 0         => (dead_acc, [])
  | fuel' + 1 =>
    if remaining_π = [] then
      (dead_acc, [])
    else
      let Tᵢ := firstTermNotKilledByList clauses ρ
      let U_i := restrictClauseByListAssignment Tᵢ ρ
      let U_vars := U_i.map Prod.fst
      let πI := remaining_π.filter fun x => U_vars.contains x.1
      let γ_i := (gammaBitsForClause U_i).take πI.length
      let dead_acc' := dead_acc ++ γ_i
      if πI.length = 0 then
        (dead_acc', [])
      else
        let chunk := encoderChunk Tᵢ πI
        let remaining' := remaining_π.filter fun (w, _) => !πI.any fun (w', _) => w' == w
        let ρ' := combineRestrictions ρ πI
        let (final_dead, restEncoder) :=
          beameEncoderAux fuel' remaining' clauses ρ' dead_acc'
        (final_dead, chunk :: restEncoder)

/-- Beame encoder using the full-query canonical DT (`canonicalDecisionTree`).

    The full-query DT queries ALL clause variables on every path (including
    non-satisfying branches), matching the Beame switching lemma construction.
    This guarantees: if `πI ≠ remaining_π` then `πI` sets all variables
    in the currently selected clause `U_i`. -/
private def encodeRestrictionFromFormula
    (d : Nat)
    (dnf : UnboundedFanInFormula)
    (asgn : List (Nat × Bool))
    : List (Nat × Bool) × List (List (Nat × Bool)) :=
  let dt := canonicalDecisionTree dnf asgn
  let clauses := dnfClauses dnf
  match leftmostPathExceedingDepth dt d with
  | none => (asgn, [])
  | some path =>
    let π := path.take d
    beameEncoderAux π.length π clauses asgn asgn

def encoderRestriction (d : Nat)
                            (dnf : UnboundedFanInProperDNF n)
                            (ρ : AssignedRandomRestriction σ n)
    : List (Nat × Bool) × List (List (Nat × Bool)) :=
  let asgn := mkAssignmentList ρ.starAssignment.val.val
                                 ρ.varAssignments
                                 n
  let dt := properDNFCanonicalDecisionTree dnf ρ
  let clauses := dnfClauses dnf.val
  match leftmostPathExceedingDepth dt d with
  | none => (asgn, [])
  | some path =>
    let π := path.take d
    beameEncoderAux π.length π clauses asgn asgn

/-- Iterative decoder that recovers path variables from chunks by repeatedly
    selecting the first clause not killed by the accumulated assignment. -/
def beameDecoder
    (dnf : UnboundedFanInFormula)
    (B : List (Nat × Bool))
    (aux_info : List (List (Nat × Bool)))
    : List (Nat × Bool) :=
  let clauses := dnfClauses dnf
  let (_, recovered) := aux_info.foldl (fun (B_cur, vars_acc) chunk =>
    let T_i := firstTermNotKilledByList clauses B_cur
    chunk.foldl (fun (B_inner, vars_inner) (pos, π_bit) =>
      let v := (T_i.getD pos (0, false)).1
      ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner)
    ) (B_cur, vars_acc)
  ) (B, ([] : List (Nat × Bool)))
  recovered.reverse


/-- The remaining (unassigned) variables of `firstTermNotKilledByList` appear
    as a prefix of any root-to-leaf path of the full-query canonical DT,
    preserving their original clause order.

    The conclusion preserves their order via `List.IsPrefix`. -/
theorem ftnkb_remaining_vars_prefix_in_dt_path
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (path : List (Nat × Bool))
    (hp : IsPathIn (canonicalDecisionTree f.val asgn) path)
    (h_ne : dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) f.val) ≠ []) :
    (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) asgn).map Prod.fst
      <+: path.map Prod.fst := by
  obtain ⟨head, tail, hr⟩ : ∃ head tail,
      dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val) = head :: tail := by
    cases hr : dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val) with
    | nil => exact absurd hr h_ne
    | cons head tail => exact ⟨head, tail, rfl⟩
  have hprefix := canonical_dt_first_clause_vars_prefix
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) f.val)) (by rw [hr]; simp) path
    (by simpa [canonicalDecisionTree] using hp)
  have hhead :
      (dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val)).head (by rw [hr]; simp) =
      head := by
    have h_head : ∀ (l₁ l₂ : List (List (Nat × Bool))) (heq : l₁ = l₂)
        (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), l₁.head h₁ = l₂.head h₂ := by
      intro l₁ l₂ heq h₁ h₂
      subst heq
      rfl
    exact h_head _ _ hr (by rw [hr]; simp) (List.cons_ne_nil head tail)
  rw [hhead] at hprefix
  have h_r := r_of_combined_eq_restricted_simplify_head_exact
    f.val f.property.2 asgn [] (by simp) (by simp) head tail hr
  have h_r' : restrictionOfFirstTermNotKilledByList
      (dnfClauses f.val) asgn = head := by simpa using h_r
  rw [h_r']
  exact hprefix

/-- If the full-query canonical DT has a path exceeding depth d, then the
    restricted clauses are non-empty and have a non-empty head clause.
    Equivalently, `restrictionOfFirstTermNotKilledByList clauses asgn ≠ []`. -/
private lemma roftnkb_ne_of_long_path
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path) :
    (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) asgn) ≠ [] ∧
    dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) f.val) ≠ [] := by
  set asgn_fn := restrictionAsFunction asgn
  -- Extract orGate structure
  have hdnf := f.property.2
  have ⟨terms, hterms⟩ : ∃ terms, f.val = .orGate terms := by
    cases hv : f.val with
    | orGate terms => exact ⟨terms, rfl⟩
    | _ => rw [hv] at hdnf; simp [isDNF] at hdnf
  rw [hterms] at hpath ⊢
  simp only [canonicalDecisionTree,
    simpleRestrictDNF, dnfClauses_eq_extractAndLiterals] at hpath ⊢
  set r_terms := terms.filterMap (simpleRestrictTerm asgn_fn)
  have hall : terms.all isAndOfInputsOnly = true := by
    rw [hterms] at hdnf; simp only [isDNF] at hdnf; exact hdnf
  -- Step 1: `r_terms ≠ []`; otherwise the tree is a `false` leaf and has no long path.
  have hne : r_terms ≠ [] := by
    intro h
    rw [show r_terms.map extractAndLiterals = [] from by simp [h]] at hpath
    simp [canonicalDecisionTreeAuxPreciseFull, leftmostPathExceedingDepth] at hpath
  -- Step 2: the first restricted term is nonempty; otherwise the tree starts
  -- with a `true` leaf.
  have hhead_ne : extractAndLiterals (r_terms.head hne) ≠ [] := by
    intro h
    -- Rewrite r_terms as head :: tail in hpath
    conv at hpath => rw [show r_terms = r_terms.head hne :: r_terms.tail from
      (List.cons_head_tail hne).symm]
    simp only [List.map_cons, List.length_cons] at hpath
    rw [h] at hpath
    simp [canonicalDecisionTreeAuxPreciseFull,
      clauseToPathTreeFull,
      graftOnZeroLeavesWithSimplificationFull,
      leftmostPathExceedingDepth] at hpath
  -- Step 3: r_clauses ≠ []
  have hr_ne : r_terms.map extractAndLiterals ≠ [] := by simp [List.map_eq_nil_iff, hne]
  have hr_cons : r_terms.map extractAndLiterals =
      extractAndLiterals (r_terms.head hne) ::
        r_terms.tail.map extractAndLiterals := by
    rw [← List.map_cons, List.cons_head_tail hne]
  have h_r := r_of_combined_eq_restricted_simplify_head_exact
    (.orGate terms) (by simpa [isDNF] using hall) asgn [] (by simp) (by simp)
    (extractAndLiterals (r_terms.head hne))
    (r_terms.tail.map extractAndLiterals) hr_cons
  constructor
  · intro h
    apply hhead_ne
    have h_r' : restrictionOfFirstTermNotKilledByList
        (terms.map extractAndLiterals) asgn =
        extractAndLiterals (r_terms.head hne) := by
      rw [dnfClauses_eq_extractAndLiterals] at h_r
      simp only [List.append_nil] at h_r
      exact h_r
    rw [← h_r', h]
  · -- r_clauses ≠ []
    exact hr_ne


/- **Canonical-DT termination at a vacuous head**.  If for some `k`
    the `k`-th iter-split segment's head clause has empty variable set
    (i.e. `segments[k].2.fst = []`, meaning `simplifyClausesByPath`
    has produced the empty/vacuous head clause), then **every subsequent
    segment** has both `.1 = []` and `.2 = []`.

    *Why true.*  By the iter-split provenance,
    `simplifyClausesByPath clauses ((segments.take (j+1)).flatten)
       = segments[j+1].2 :: tail_{j+1}`.
    But `(segments.take (j+1)).flatten = (segments.take j).flatten ++ segments[j].1`,
    and inductively `segments[j].1 = []`, so the LHS equals
    `simplifyClausesByPath clauses ((segments.take j).flatten)
       = segments[j].2 :: tail_j` (by `hcum_a j`).  Cons-injectivity gives
    `segments[j+1].2 = segments[j].2 = []`, hence by `hcov` also
    `segments[j+1].1 = []`.

    Consequently, once an aligned restricted head is empty, every later
    segment is empty as well. -/
private lemma iter_split_segments_empty_after_nil_simplified_head
    (clauses : List (List (Nat × Bool)))
    (segments : List (List (Nat × Bool) × List (Nat × Bool)))
    (hcum_a : ∀ (j : Nat) (hj : j < segments.length),
      ∃ tail_j,
        simplifyClausesByPath clauses
          (((segments.take j).map Prod.fst).flatten)
        = (segments[j]'hj).2 :: tail_j)
    (hcov : ∀ (j : Nat) (hj : j < segments.length),
      (segments[j]'hj).1.map Prod.fst = (segments[j]'hj).2.map Prod.fst)
    (k : Nat) (hk_lt : k < segments.length)
    (hk_nil_fst : (segments[k]'hk_lt).2.map Prod.fst = []) :
    ∀ (j : Nat) (hj : j < segments.length), k ≤ j →
      (segments[j]'hj).1 = [] ∧ (segments[j]'hj).2 = [] := by
  -- Reformulate to enable plain `Nat` induction on `n := j - k`.
  suffices h : ∀ (n : Nat) (hjlt : k + n < segments.length),
      (segments[k + n]'hjlt).1 = [] ∧ (segments[k + n]'hjlt).2 = [] by
    intro j hj hkj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkj
    exact h n hj
  intro n
  induction n with
  | zero =>
    -- Base: n = 0, i.e. j = k.
    intro hjlt
    have hk_2_nil : (segments[k]'hjlt).2 = [] := List.map_eq_nil_iff.mp hk_nil_fst
    have hk_1_fst_nil : ((segments[k]'hjlt).1.map Prod.fst) = [] := by
      rw [hcov k hjlt]; rw [hk_2_nil]; rfl
    have hk_1_nil : (segments[k]'hjlt).1 = [] := List.map_eq_nil_iff.mp hk_1_fst_nil
    exact ⟨hk_1_nil, hk_2_nil⟩
  | succ n ih =>
    -- Step: assume property at j = k + n; prove at j = k + (n + 1).
    intro hjlt
    -- Need predecessor index in range to invoke ih.
    have hpred_lt : k + n < segments.length := by
      have hjlt' : k + n + 1 < segments.length := by
        have heq : k + (n + 1) = k + n + 1 := by ring
        rw [heq] at hjlt; exact hjlt
      omega
    -- Re-derive ih at the predecessor.
    obtain ⟨h1_pred, h2_pred⟩ := ih hpred_lt
    -- Provenance at j = k + n + 1.
    have hjlt' : k + n + 1 < segments.length := by
      have : k + (n + 1) = k + n + 1 := by ring
      rw [this] at hjlt; exact hjlt
    obtain ⟨tail_succ, hsucc⟩ := hcum_a (k + n + 1) hjlt'
    -- Provenance at j = k + n.
    obtain ⟨tail_pred, hpred⟩ := hcum_a (k + n) hpred_lt
    -- (segments.take (k+n+1)).flatten = (segments.take (k+n)).flatten ++ segments[k+n].1
    --                                  = (segments.take (k+n)).flatten ++ []
    --                                  = (segments.take (k+n)).flatten.
    have htake_succ_eq :
        ((segments.take (k + n + 1)).map Prod.fst).flatten =
        ((segments.take (k + n)).map Prod.fst).flatten := by
      have hsplit : segments.take (k + n + 1) =
          segments.take (k + n) ++ [segments[k + n]'hpred_lt] := by
        rw [show k + n + 1 = (k + n) + 1 from rfl]
        rw [List.take_add_one]
        congr 1
        rw [List.getElem?_eq_getElem hpred_lt]
        rfl
      rw [hsplit]
      simp only [List.map_append, List.flatten_append, List.map_cons,
        List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [h1_pred]
      simp
    -- Substitute and apply cons-injectivity.
    rw [htake_succ_eq] at hsucc
    have heq : (segments[k + n + 1]'hjlt').2 :: tail_succ =
        (segments[k + n]'hpred_lt).2 :: tail_pred := by
      rw [← hsucc, hpred]
    have h2_succ : (segments[k + n + 1]'hjlt').2 = (segments[k + n]'hpred_lt).2 :=
      (List.cons.injEq _ _ _ _).mp heq |>.1
    rw [h2_pred] at h2_succ
    -- Now derive .1 = [] via hcov + h2_succ.
    have h1_succ_fst : ((segments[k + n + 1]'hjlt').1.map Prod.fst) = [] := by
      rw [hcov (k + n + 1) hjlt', h2_succ]; rfl
    have h1_succ : (segments[k + n + 1]'hjlt').1 = [] :=
      List.map_eq_nil_iff.mp h1_succ_fst
    -- Convert k + n + 1 = k + (n + 1) for the goal.
    have heqi : k + (n + 1) = k + n + 1 := by ring
    refine ⟨?_, ?_⟩
    · simp_rw [heqi]; exact h1_succ
    · simp_rw [heqi]; exact h2_succ

/- Given the canonical iter-split of `path` and the encoder's halt index
    `k_canonical` (where `consumed = ((segs.take k).fst).flatten`), derive
    the selected clause under `combineRestrictions asgn consumed` is nonempty:
      1. Suppose it is empty. Apply `iter_split_seg_eq_rtnkb_at_canonical_prefix`
         at index `k_canonical` to get `segs[k_canonical].2.fst = []`.
      2. Apply `iter_split_segments_empty_after_nil_simplified_head` to
         conclude `segs[j].1 = []` for every `j ≥ k_canonical`.
      3. Hence `path = consumed` (drop part is empty).
      4. Combined with `consumed ⊆ path.take d` (encoder-faithful invariant),
         deduce `path ⊆ path.take d`, hence `path.length ≤ d`.
      5. Contradicts `leftmostPathExceedingDepth ... = some path`
         (which forces `d < path.length`). -/
private lemma r_ne_nil_via_canonical_iter_split
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (segs_canon : List (List (Nat × Bool) × List (Nat × Bool)))
    (k_canonical : Nat)
    (hpath_canon : path = (segs_canon.map Prod.fst).flatten)
    (_hk_le : k_canonical ≤ segs_canon.length)
    (hcanon_prov :
      ∀ (j : Nat) (hj : j < segs_canon.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segs_canon.take j).map Prod.fst).flatten)
          = (segs_canon[j]'hj).2 :: tail_j)
    (hvm_canon :
      ∀ (j : Nat) (hj : j < segs_canon.length),
        (segs_canon[j]'hj).1.map Prod.fst = (segs_canon[j]'hj).2.map Prod.fst)
    (consumed : List (Nat × Bool))
    (hcons_prefix :
      consumed = ((segs_canon.take k_canonical).map Prod.fst).flatten)
    (hcons_in_window : ∀ p ∈ consumed, p ∈ path.take d) :
    restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions asgn consumed) ≠ [] := by
  intro h_r_nil
  -- **Step A**: deduce `(segs_canon.drop k_canonical).fst.flatten = []`.
  have hdrop_nil :
      ((segs_canon.drop k_canonical).map Prod.fst).flatten = [] := by
    rcases Nat.lt_or_ge k_canonical segs_canon.length with hk_lt | hk_ge
    · have hkeq :=
        iter_split_seg_eq_rtnkb_at_canonical_prefix
          f asgn hnodup d path hpath segs_canon hpath_canon hcanon_prov
          k_canonical hk_lt
      simp only at hkeq
      rw [← hcons_prefix] at hkeq
      have hk_2_fst_nil : (segs_canon[k_canonical]'hk_lt).2.map Prod.fst = [] := by
        rw [hkeq, h_r_nil]; rfl
      have hempty :=
        iter_split_segments_empty_after_nil_simplified_head
          (dnfClauses (simpleRestrictDNF
            (restrictionAsFunction asgn) f.val))
          segs_canon hcanon_prov
          (fun j hj => hvm_canon j hj)
          k_canonical hk_lt hk_2_fst_nil
      apply List.flatten_eq_nil_iff.mpr
      intro l hl
      rw [List.mem_map] at hl
      obtain ⟨q, hq_mem, hq_eq⟩ := hl
      obtain ⟨i, hi, hq_get⟩ := List.getElem_of_mem hq_mem
      rw [List.getElem_drop] at hq_get
      have hidx_lt : k_canonical + i < segs_canon.length := by
        rw [List.length_drop] at hi; omega
      have hi1 : (segs_canon[k_canonical + i]'hidx_lt).1 = [] :=
        (hempty (k_canonical + i) hidx_lt (Nat.le_add_right _ _)).1
      rw [← hq_eq, ← hq_get]; exact hi1
    · have hdrop_eq : segs_canon.drop k_canonical = [] := List.drop_eq_nil_of_le hk_ge
      rw [hdrop_eq]; rfl
  -- **Step B**: `path = consumed`.
  have hpath_eq_consumed : path = consumed := by
    have hsplit : segs_canon =
        segs_canon.take k_canonical ++ segs_canon.drop k_canonical :=
      (List.take_append_drop _ _).symm
    calc path
        = (segs_canon.map Prod.fst).flatten := hpath_canon
      _ = ((segs_canon.take k_canonical ++ segs_canon.drop k_canonical).map
            Prod.fst).flatten := by rw [← hsplit]
      _ = ((segs_canon.take k_canonical).map Prod.fst).flatten ++
          ((segs_canon.drop k_canonical).map Prod.fst).flatten := by
            rw [List.map_append, List.flatten_append]
      _ = ((segs_canon.take k_canonical).map Prod.fst).flatten ++ [] := by
            rw [hdrop_nil]
      _ = ((segs_canon.take k_canonical).map Prod.fst).flatten :=
            List.append_nil _
      _ = consumed := hcons_prefix.symm
  -- **Step C**: derive `path.length ≤ d`, contradicting `hpath`.
  have hpath_in_take : ∀ p ∈ path, p ∈ path.take d := by
    intro p hp; rw [hpath_eq_consumed] at hp; exact hcons_in_window p hp
  have hpath_nodup_fst :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
  have hpath_nodup : path.Nodup := List.Nodup.of_map _ hpath_nodup_fst
  have h_subset : path ⊆ path.take d := hpath_in_take
  have h_len_le : path.length ≤ (path.take d).length :=
    (hpath_nodup.subperm h_subset).length_le
  have h_take_le_d : (path.take d).length ≤ d := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  have hpath_len_gt :=
    leftmostPathExceedingDepth_some_path_length_gt _ _ _ hpath
  omega

#print axioms r_ne_nil_via_canonical_iter_split


-- ════════════════════════════════════════════════════════════════════════════
-- §  Bridge from the first non-killed clause to `simplifyClausesByPath`
-- ════════════════════════════════════════════════════════════════════════════
--
-- The encoder calls `restrictionOfFirstTermNotKilledByList (dnfClauses
-- f.val) (combineRestrictions asgn π)` (a list-based, original-DNF
-- operation). The iter-split
-- (`canonical_dt_path_split_iter_with_heads_per_seg`)
-- works on `simplifyClausesByPath (dnfClauses (simpleRestrictDNF
-- (restrictionAsFunction asgn) f.val)) π` (a function-based, restricted-DNF operation).
--
-- The following identity connects each iter-split segment head with the
-- corresponding running simplification.

/-- **Iter-split segment-head identity.** The iter-split's `segments[j].2`
    equals the head of the running simplification of the restricted DNF
    by the segment-prefix path bits.

    *Why this is true.* The iter-split is constructed by repeatedly
    extracting the head of the simplified clause list at each step (via
    `clauseToPathTreeFull segments[j].2`) and then running
    `graftOnZeroLeavesWithSimplificationFull ... rest_j fuel_j` to
    consume the segment's prefix bits, producing the next simplified list.
    Hence `segments[j].2` is precisely
    `(simplifyClausesByPath simplified_0 ((segments.take j).map fst).flatten).head`. -/
private lemma iter_split_segment_head_eq_simplify_path_head
    {n : Nat} (f : UnboundedFanInDNF n) (asgn : List (Nat × Bool))
    (hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hp : IsPathIn (canonicalDecisionTree f.val asgn) path) :
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))),
      path = (segments.map Prod.fst).flatten ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ p ∈ segments, ∃ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        p.2.map Prod.fst ⊆ c.map Prod.fst) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ (hne : simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segments.take j).map Prod.fst).flatten) ≠ []),
          (segments[j]'hj).2 =
          (simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segments.take j).map Prod.fst).flatten)).head hne) := by
  -- Unfold the grafting decision tree to its iter-split form.
  simp only [canonicalDecisionTree] at hp
  set restricted :=
    dnfClauses (simpleRestrictDNF
      (restrictionAsFunction asgn) f.val) with hrestr_def
  obtain ⟨segments, suf, hcat, _hlen, hcov, hheads, _hnd_seg, _hperseg, hcum_a, hsuf⟩ :=
    canonical_dt_path_split_iter_with_heads_per_seg
      restricted hnodup_restricted path hp restricted.length
  -- Force suf = [] (same argument as in `cdt_full_query_per_segment_killed`).
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
        simp [canonicalDecisionTreeAuxPreciseFull] at hp_suf
        cases hp_suf; rfl
      | succ fuel'' =>
        simp [canonicalDecisionTreeAuxPreciseFull] at hp_suf
        cases hp_suf; rfl
  refine ⟨segments, ?_, hcov, hheads, ?_⟩
  · rw [hcat, hsuf_nil]; simp
  -- Conjunct 4: per-iteration cumulative-simplify head equality.
  intro j hj
  obtain ⟨tail_j, htail_j⟩ := hcum_a j hj
  have hne : simplifyClausesByPath restricted
      (((segments.take j).map Prod.fst).flatten) ≠ [] := by
    rw [htail_j]; simp
  refine ⟨hne, ?_⟩
  -- Both sides reduce to `(segments[j].2 :: tail_j).head` via htail_j.
  have h_head : ∀ (l₁ l₂ : List (List (Nat × Bool))) (heq : l₁ = l₂)
      (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), l₁.head h₁ = l₂.head h₂ := by
    intro l₁ l₂ heq h₁ h₂; subst heq; rfl
  have hne' : (segments[j]'hj).2 :: tail_j ≠ [] := by simp
  have := h_head _ _ htail_j hne hne'
  rw [this]
  rfl

#print axioms iter_split_segment_head_eq_simplify_path_head

-- ════════════════════════════════════════════════════════════════════════════
-- §  Main theorem: encoder_dead_length
-- ════════════════════════════════════════════════════════════════════════════

/- **Encoder first-non-killed-clause alignment with iter-split segment heads.**

    The encoder's per-step `restrictionOfFirstTermNotKilledByList`
    calls (run on the ORIGINAL `dnfClauses f.val` under cumulative
    `combineRestrictions asgn consumed`) coincide with the head clauses
    `segments[j].2` produced by
    `cdt_full_query_per_segment_killed`/`cdt_full_query_killed_heads_covered_by_prefix`
    (which are obtained via running `simplifyClausesByPath` on the
    `simpleRestrictDNF`-restricted DNF).

    **Existential form.** We existentially quantify over `segments` so the
    polarity invariant comes from the iter-split's construction (rather
    than being assumed via a too-weak `.map fst ⊆` hypothesis, which
    admits the trivial polarity-flipped counterexample
    `f = orGate [andGate [inputGate 0 false]]`, `asgn = []`,
    `segments = [([(0,.zero)], [(0, true)])]`).

    Together with the matching filter identity, this is the
    `h_align` premise of `encoder_aux_dead_length_via_segments` at the
    call site `ρ = asgn`, where `consumed` is
    `((segments.take j).map fst).flatten`.

    In the inductive step, after consuming
      `pre_j = ((segments.take j).map fst).flatten`, the encoder uses
      `combineRestrictions asgn (pre_j ++ segments[j].1)` while the iter-split
      advances `simplified` via `simplifyClausesByPath`. Both
      operations agree on:
      (i) which clauses are now killed (both scans select the same survivor);
      (ii) which vars are removed from the surviving head.
      Bridge via `simplifyClausesByPath` ↔ `simpleRestrictDNF` after
      assignment-extension, plus the iter-split's structural conjunct
      `segments[j].1.map fst = segments[j].2.map fst`.
-/
private lemma encoder_roftnkb_eq_segment_head
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool))
    (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path) :
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))),
      path = (segments.map Prod.fst).flatten ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ p ∈ segments, ∃ c ∈ dnfClauses (simpleRestrictDNF
          (restrictionAsFunction asgn) f.val),
        p.2.map Prod.fst ⊆ c.map Prod.fst) ∧
      (∀ p ∈ segments, p.1 ≠ []) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions asgn (((segments.take j).map Prod.fst).flatten)) =
          (segments[j]'hj).2) := by
  -- Extract IsPathIn from the leftmost-path hypothesis.
  have hp_isin : IsPathIn
      (canonicalDecisionTree f.val asgn) path :=
    leftmostPathExceedingDepth_isPathIn _ _ _ hpath
  -- Bridge: original-DNF Nodup ⟹ restricted-DNF Nodup.
  have hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup :=
    restrictDNF_preserves_clause_nodup f.val _ hnodup
  -- Use the iter-split lemma (which provides conjuncts 1-3 plus the
  -- simplify_path head equality needed for conjunct 4).
  obtain ⟨raw_segs, hraw_path_eq, hraw_cov, hraw_heads, h_iter⟩ :=
    iter_split_segment_head_eq_simplify_path_head f asgn hnodup_restricted path hp_isin
  -- Prove `h_align` for the raw segments.
  have hraw_align : ∀ (j : Nat) (hj : j < raw_segs.length),
      restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions asgn (((raw_segs.take j).map Prod.fst).flatten)) =
        (raw_segs[j]'hj).2 := by
    intro j hj
    -- Set up π_j := cumulative prefix of the first j segments.
    set π_j := ((raw_segs.take j).map Prod.fst).flatten with hπj_def
    -- Path bits in π_j are also bits of `path`.
    have hπj_sub_path : ∀ vb ∈ π_j, vb ∈ path := by
      intro vb hvb
      rw [hraw_path_eq]
      have htake_sub : List.Sublist ((raw_segs.take j).map Prod.fst)
          (raw_segs.map Prod.fst) :=
        List.Sublist.map _ (List.take_sublist j _)
      exact htake_sub.flatten.subset hvb
    -- Disjointness: π_j vars are not in asgn.
    have hdisj : ∀ vb ∈ π_j, ¬ (asgn.any fun (w, _) => w == vb.1) := by
      intro vb hvb
      have hvb_path := hπj_sub_path vb hvb
      have hnone := canonical_dt_path_var_none
        f.val asgn f.property.2 d path hpath vb.1 vb.2 hvb_path
      have heq := not_list_any_iff_cr_none_eq_none asgn vb.1
      rw [hnone] at heq
      simp only [beq_self_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at heq
      intro habs
      rw [habs] at heq
      exact Bool.noConfusion heq
    -- Nodup-fst for π_j.
    have hpath_nodup : (path.map Prod.fst).Nodup :=
      canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
    have hπj_nd : (π_j.map Prod.fst).Nodup := by
      have hsub : List.Sublist (π_j.map Prod.fst) (path.map Prod.fst) := by
        rw [hraw_path_eq]
        have hsub1 : List.Sublist π_j ((raw_segs.map Prod.fst).flatten) := by
          rw [hπj_def]
          exact (List.Sublist.map _ (List.take_sublist j _)).flatten
        exact List.Sublist.map _ hsub1
      exact hpath_nodup.sublist hsub
    obtain ⟨hne_simp, hseg_eq⟩ := h_iter j hj
    have hbridge :=
      roftnkb_eq_simplify_path_head f asgn π_j hdisj hπj_nd hne_simp
    rw [hbridge, ← hseg_eq]
  -- Length-alignment for raw segments (from fst-eq in hraw_cov).
  have hraw_len : ∀ p ∈ raw_segs, p.1.length = p.2.length := fun p hp => by
    have := congrArg List.length (hraw_cov p hp); simpa using this
  -- ── Suffix-empties propagation: empty .1 implies empty .1 in successor. ──
  have h_succ_empty : ∀ j (hj : j + 1 < raw_segs.length),
      (raw_segs[j]'(by omega)).1 = [] →
      (raw_segs[j+1]'hj).1 = [] := by
    intro j hj hempty
    have hj0 : j < raw_segs.length := by omega
    have h2_empty : (raw_segs[j]'hj0).2 = [] := by
      have hl := hraw_len _ (List.getElem_mem hj0)
      rw [hempty] at hl
      exact List.length_eq_zero_iff.mp hl.symm
    have hcum_eq : ((raw_segs.take (j+1)).map Prod.fst).flatten =
        ((raw_segs.take j).map Prod.fst).flatten := by
      rw [show raw_segs.take (j+1) = raw_segs.take j ++ [raw_segs[j]'hj0] from
            List.take_succ_eq_append_getElem hj0]
      rw [List.map_append, List.flatten_append]
      simp [hempty]
    have h_a_j := hraw_align j hj0
    have h_a_j1 := hraw_align (j+1) hj
    rw [hcum_eq, h_a_j] at h_a_j1
    have h21_empty : (raw_segs[j+1]'hj).2 = [] := by
      rw [← h_a_j1]; exact h2_empty
    have hl1 := hraw_len _ (List.getElem_mem hj)
    rw [h21_empty] at hl1
    exact List.length_eq_zero_iff.mp hl1
  -- Generalize: if some j₀ has empty .1, then all k ≥ j₀ have empty .1.
  have h_suffix_empties : ∀ j₀ k (hk : k < raw_segs.length),
      j₀ ≤ k →
      (∀ (hj : j₀ < raw_segs.length), (raw_segs[j₀]'hj).1 = []) →
      (raw_segs[k]'hk).1 = [] := by
    intro j₀ k hk hjk hempty
    induction k with
    | zero =>
      have : j₀ = 0 := by omega
      subst this; exact hempty (by omega)
    | succ k ih =>
      by_cases hjeq : j₀ = k + 1
      · subst hjeq; exact hempty hk
      · have hjk' : j₀ ≤ k := by omega
        have hk' : k < raw_segs.length := by omega
        exact h_succ_empty k hk (ih hk' hjk')
  -- ── Define segments via case analysis on whether all .1 are nonempty. ──
  classical
  by_cases hall : ∀ (k : Nat) (hk : k < raw_segs.length), (raw_segs[k]'hk).1 ≠ []
  · -- All raw_segs already have nonempty .1; use them directly.
    refine ⟨raw_segs, hraw_path_eq, hraw_cov, hraw_heads, ?_, hraw_align⟩
    intro p hp
    obtain ⟨k, hk, hpk⟩ := List.mem_iff_getElem.mp hp
    rw [← hpk]; exact hall k hk
  · -- Some raw_seg has empty .1; find the smallest such index.
    push Not at hall
    obtain ⟨k₀, hk₀_lt, hk₀_emp⟩ := hall
    let P : Nat → Prop := fun k => ∃ (hk : k < raw_segs.length), (raw_segs[k]'hk).1 = []
    have h_p_ex : ∃ k, P k := ⟨k₀, hk₀_lt, hk₀_emp⟩
    let N := Nat.find h_p_ex
    have h_n_spec : P N := Nat.find_spec h_p_ex
    have h_n_lt : N < raw_segs.length := h_n_spec.fst
    have h_n_emp : (raw_segs[N]'h_n_lt).1 = [] := h_n_spec.snd
    have h_n_min : ∀ m < N, ∀ (hm : m < raw_segs.length),
        (raw_segs[m]'hm).1 ≠ [] := by
      intro m hm_n hm h_emp
      exact Nat.find_min h_p_ex hm_n ⟨hm, h_emp⟩
    -- Suffix from N onwards is all empty .1.
    have h_suf_emp : ∀ k (hk : k < raw_segs.length), N ≤ k →
        (raw_segs[k]'hk).1 = [] :=
      fun k hk hge => h_suffix_empties N k hk hge (fun _ => h_n_emp)
    set segments := raw_segs.take N with hseg_def
    have h_n_le : N ≤ raw_segs.length := le_of_lt h_n_lt
    have hsc_len : segments.length = N := by
      rw [hseg_def]; exact List.length_take_of_le h_n_le
    refine ⟨segments, ?_, ?_, ?_, ?_, ?_⟩
    · -- path = (segments.map fst).flatten
      have hsplit : raw_segs = segments ++ raw_segs.drop N := by
        rw [hseg_def]; exact (List.take_append_drop N raw_segs).symm
      rw [hraw_path_eq]
      conv_lhs => rw [hsplit]
      rw [List.map_append, List.flatten_append]
      rw [show ((raw_segs.drop N).map Prod.fst).flatten = [] by
        apply List.flatten_eq_nil_iff.mpr
        intro l hl
        rw [List.mem_map] at hl
        obtain ⟨p, hp_drop, hp_eq⟩ := hl
        rw [List.mem_iff_getElem] at hp_drop
        obtain ⟨i, hi, hpidx⟩ := hp_drop
        rw [List.getElem_drop] at hpidx
        have hi' : N + i < raw_segs.length := by
          rw [List.length_drop] at hi; omega
        have hemp_i := h_suf_emp (N + i) hi' (Nat.le_add_right _ _)
        rw [hpidx] at hemp_i
        rw [← hp_eq, hemp_i]]
      rw [List.append_nil]
    · -- alignment (sublist of raw_segs)
      intro p hp
      have hsub : segments.Sublist raw_segs := by
        rw [hseg_def]; exact List.take_sublist N raw_segs
      exact hraw_cov p (hsub.subset hp)
    · -- head ⊆ clause (sublist of raw_segs)
      intro p hp
      have hsub : segments.Sublist raw_segs := by
        rw [hseg_def]; exact List.take_sublist N raw_segs
      exact hraw_heads p (hsub.subset hp)
    · -- nonemptiness
      intro p hp
      obtain ⟨k, hk_lt, hpk⟩ := List.mem_iff_getElem.mp hp
      have hk_n : k < N := by rw [hsc_len] at hk_lt; exact hk_lt
      have hk_raw : k < raw_segs.length := lt_of_lt_of_le hk_n h_n_le
      have h_idx : segments[k]'hk_lt = raw_segs[k]'hk_raw := by
        simp only [hseg_def, List.getElem_take]
      rw [← hpk, h_idx]
      exact h_n_min k hk_n hk_raw
    · -- h_align
      intro j hj
      have hj_n : j < N := by rw [hsc_len] at hj; exact hj
      have hj_raw : j < raw_segs.length := lt_of_lt_of_le hj_n h_n_le
      have h_idx : segments[j]'hj = raw_segs[j]'hj_raw := by
        simp only [hseg_def, List.getElem_take]
      have hcum : ((segments.take j).map Prod.fst).flatten =
          ((raw_segs.take j).map Prod.fst).flatten := by
        have hsg_take : segments.take j = raw_segs.take j := by
          rw [hseg_def, List.take_take, min_eq_left (le_of_lt hj_n)]
        rw [hsg_take]
      rw [h_idx, hcum]
      exact hraw_align j hj_raw

#print axioms encoder_roftnkb_eq_segment_head

/-- **Segment-induction helper for `encoder_dead_length`.**

    Inducts directly on the iter-split `segments` produced by
    `cdt_full_query_killed_heads_covered_by_prefix`.

    Per-step alignment `h_align` (indexed by `j`) gives the encoder/segments
    bridge: at the encoder iteration with restriction
    `combineRestrictions ρ consumed` (where `consumed` is the cumulative prefix of
    earlier segment .1's), the selected clause equals `segments[j].2`
    and the filter equals `segments[j].1`.

    The remaining structural hypotheses (Nodup, ρ-disjointness,
    segment-non-emptiness) are needed to prove the encoder's filter step
    matches the segment decomposition.
-/
private lemma encoder_aux_dead_length_via_segments
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (segments : List (List (Nat × Bool) × List (Nat × Bool)))
    (hfuel : segments.length ≤ fuel)
    (hsegs_eq : remaining_π = (segments.map Prod.fst).flatten)
    (hnodup_rem : (remaining_π.map Prod.fst).Nodup)
    (hdisj_ρ : ∀ w b, (w, b) ∈ remaining_π →
      (ρ.any fun (z, _) => z == w) = false)
    (hsegs_align : ∀ p ∈ segments, p.1.length ≤ p.2.length)
    (h_seg_nonempty : ∀ p ∈ segments, p.1 ≠ [])
    (h_align : ∀ (j : Nat) (hj : j < segments.length),
      restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
        (combineRestrictions ρ (((segments.take j).map Prod.fst).flatten)) =
        (segments[j]'hj).2 ∧
      (remaining_π.filter (fun (w : Nat × Bool) =>
        !(((segments.take j).map Prod.fst).flatten).any
          (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
        (fun x => ((restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
          (combineRestrictions ρ
            (((segments.take j).map Prod.fst).flatten))).map
          Prod.fst).contains x.1) =
        (segments[j]'hj).1) :
    (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1.length =
      dead_acc.length + remaining_π.length := by
  induction segments generalizing fuel remaining_π ρ dead_acc with
  | nil =>
    have hrem_nil : remaining_π = [] := by simp [hsegs_eq]
    subst hrem_nil
    cases fuel <;> simp [beameEncoderAux]
  | cons seg0 rest ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      -- ── Step 1: Apply h_align(0) to identify the first encoder step ──
      have h_align_0_raw := h_align 0 (Nat.succ_pos _)
      simp only [List.take_zero, List.map_nil, List.flatten_nil, List.any_nil,
        Bool.not_false, List.filter_true, combineRestrictions,
        List.filter_nil, List.append_nil, List.getElem_cons_zero]
        at h_align_0_raw
      obtain ⟨h_u_eq, hπi_eq⟩ := h_align_0_raw
      -- Encoder local abbreviations
      set clauses := dnfClauses dnf with hcl_def
      set U_i := restrictClauseByListAssignment (firstTermNotKilledByList clauses ρ) ρ with h_u_def
      set U_vars := U_i.map Prod.fst with h_uv_def
      set p_pred : (Nat × Bool) → Bool := fun x => U_vars.contains x.1 with hp_def
      set πI := remaining_π.filter p_pred with hπi_def
      have hπi_eq_seg : πI = seg0.1 := hπi_eq
      -- ── Step 2: Show seg0.1 ≠ [], remaining_π ≠ [], πI.length ≠ 0 ──
      have hseg0_ne : seg0.1 ≠ [] := h_seg_nonempty _ List.mem_cons_self
      have hrem_ne : remaining_π ≠ [] := by
        rw [hsegs_eq, List.map_cons, List.flatten_cons]
        intro hcontra
        exact hseg0_ne (List.append_eq_nil_iff.mp hcontra).1
      have hπi_len_ne : πI.length ≠ 0 := by
        rw [hπi_eq_seg]; exact fun h => hseg0_ne (List.length_eq_zero_iff.mp h)
      -- ── Step 3: Length facts ──
      have hseg0_len : seg0.1.length ≤ seg0.2.length :=
        hsegs_align seg0 List.mem_cons_self
      have h_u_len : U_i.length = seg0.2.length := by
        change (restrictionOfFirstTermNotKilledByList clauses ρ).length =
          seg0.2.length
        rw [h_u_eq]
      have hπi_le_u : πI.length ≤ U_i.length := by
        rw [hπi_eq_seg, h_u_len]; exact hseg0_len
      have hγ_len : ((gammaBitsForClause U_i).take πI.length).length = πI.length := by
        rw [List.length_take]
        have hgamma_len : (gammaBitsForClause U_i).length = U_i.length := by
          simp [gammaBitsForClause]
        omega
      -- ── Step 4: Unfold encoder, take recursive branch ──
      simp only [beameEncoderAux]
      rw [if_neg hrem_ne, if_neg hπi_len_ne]
      set ρ' := combineRestrictions ρ πI with hρ'_def
      set remaining' := remaining_π.filter
        (fun (w : Nat × Bool) => !πI.any (fun (w' : Nat × Bool) => w'.1 == w.1))
        with hrem'_def
      set dead_acc' := dead_acc ++ (gammaBitsForClause U_i).take πI.length
        with hda'_def
      show (beameEncoderAux fuel'
        (remaining_π.filter (fun (w : Nat × Bool) =>
          !πI.any (fun (w' : Nat × Bool) => w'.1 == w.1)))
        (dnfClauses dnf) ρ' dead_acc').1.length = dead_acc.length + remaining_π.length
      change (beameEncoderAux fuel' remaining' (dnfClauses dnf) ρ' dead_acc').1.length =
        dead_acc.length + remaining_π.length
      -- ── Step 5: Show remaining' = (rest.map fst).flatten via Nodup disjointness ──
      have hnodup_split :
          (seg0.1.map Prod.fst).Disjoint (((rest.map Prod.fst).flatten).map Prod.fst) := by
        have hraw : (((seg0 :: rest).map Prod.fst).flatten.map Prod.fst).Nodup := by
          rw [← hsegs_eq]; exact hnodup_rem
        rw [List.map_cons, List.flatten_cons, List.map_append] at hraw
        intro a ha hb
        exact (List.nodup_append.mp hraw).2.2 a ha a hb rfl
      have hrem'_eq : remaining' = (rest.map Prod.fst).flatten := by
        rw [hrem'_def, hπi_eq_seg, hsegs_eq, List.map_cons, List.flatten_cons,
          List.filter_append]
        have h_seg0_part :
            seg0.1.filter (fun (w : Nat × Bool) =>
              !seg0.1.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ⟨w, b⟩ hwb
          simp only [Bool.not_eq_true', Bool.not_eq_false]
          rw [List.any_eq_true]
          exact ⟨(w, b), hwb, by simp⟩
        have h_rest_part :
            ((rest.map Prod.fst).flatten).filter (fun (w : Nat × Bool) =>
              !seg0.1.any (fun (w' : Nat × Bool) => w'.1 == w.1)) =
            (rest.map Prod.fst).flatten := by
          apply List.filter_eq_self.mpr
          intro ⟨w, b⟩ hwb
          simp only [Bool.not_eq_true']
          rw [List.any_eq_false]
          intro ⟨z, bz⟩ hz_seg0
          simp only [beq_iff_eq]; intro heq
          have hz_fst : z ∈ seg0.1.map Prod.fst :=
            List.mem_map.mpr ⟨(z, bz), hz_seg0, rfl⟩
          have hw_fst : w ∈ ((rest.map Prod.fst).flatten).map Prod.fst :=
            List.mem_map.mpr ⟨(w, b), hwb, rfl⟩
          rw [heq] at hz_fst
          exact hnodup_split hz_fst hw_fst
        rw [h_seg0_part, h_rest_part]
        simp
      -- ── Step 6: Build the IH preconditions ──
      have hfuel' : rest.length ≤ fuel' := by
        have h := hfuel; simp [List.length_cons] at h; omega
      have hnodup_rem' : (remaining'.map Prod.fst).Nodup :=
        List.Pairwise.sublist (List.filter_sublist.map _) hnodup_rem
      have hπi_disj_ρ : ∀ x ∈ πI, (ρ.any fun (z, _) => z == x.1) = false := by
        intro x hx
        exact hdisj_ρ x.1 x.2 (List.mem_of_mem_filter hx)
      have hdisj_ρ' : ∀ w b, (w, b) ∈ remaining' →
          (ρ'.any fun (z, _) => z == w) = false := by
        intro w b hw_rem'
        have hw_rπ : (w, b) ∈ remaining_π := List.mem_of_mem_filter hw_rem'
        have hρ_none := hdisj_ρ w b hw_rπ
        show (combineRestrictions ρ πI).any (fun (z, _) => z == w) = false
        rw [combineRestrictions, List.any_append, hρ_none, Bool.false_or]
        rw [List.any_eq_false]
        intro ⟨z, bz⟩ hz_filt
        simp only [beq_iff_eq]; intro heq
        have hz_πi := List.mem_of_mem_filter hz_filt
        have hw_in_πi : πI.any (fun (w', _) => w' == w) = true := by
          rw [List.any_eq_true]
          exact ⟨(z, bz), hz_πi, by simp [heq]⟩
        have hw_nc := (List.mem_filter.mp hw_rem').2
        simp only [Bool.not_eq_true'] at hw_nc
        exact absurd hw_in_πi (by rw [hw_nc]; exact Bool.false_ne_true)
      -- ── Step 7: Build h_align' for rest by shifting index ──
      have h_align' : ∀ (j : Nat) (hj : j < rest.length),
          restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
            (combineRestrictions ρ' (((rest.take j).map Prod.fst).flatten)) =
            (rest[j]'hj).2 ∧
          (remaining'.filter (fun (w : Nat × Bool) =>
            !(((rest.take j).map Prod.fst).flatten).any
              (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
            (fun x => ((restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
              (combineRestrictions ρ'
                (((rest.take j).map Prod.fst).flatten))).map
              Prod.fst).contains x.1) =
            (rest[j]'hj).1 := by
        intro j hj
        have hj1 : j + 1 < (seg0 :: rest).length := by simp; omega
        have h_outer := h_align (j + 1) hj1
        set inner := ((rest.take j).map Prod.fst).flatten with h_inner_def
        have h_take_succ : (seg0 :: rest).take (j + 1) = seg0 :: rest.take j := by
          rfl
        have h_consumed_eq : (((seg0 :: rest).take (j + 1)).map Prod.fst).flatten =
            seg0.1 ++ inner := by
          rw [h_take_succ]; simp [h_inner_def]
        have h_inner_sub_rest : ∀ x ∈ inner, x ∈ (rest.map Prod.fst).flatten := by
          intro x hx
          rw [h_inner_def, List.mem_flatten] at hx
          obtain ⟨l, hl_in, hx_in_l⟩ := hx
          rw [List.mem_map] at hl_in
          obtain ⟨seg, hseg_in, rfl⟩ := hl_in
          rw [List.mem_flatten]
          exact ⟨seg.1, List.mem_map.mpr ⟨seg, List.mem_of_mem_take hseg_in, rfl⟩, hx_in_l⟩
        have h_inner_disj_seg0 : ∀ x ∈ inner,
            (seg0.1.any fun (z, _) => z == x.1) = false := by
          intro x hx
          have hx_rest := h_inner_sub_rest x hx
          rw [List.any_eq_false]
          intro ⟨z, bz⟩ hz_seg0
          simp only [beq_iff_eq]; intro heq
          have hz_fst : z ∈ seg0.1.map Prod.fst :=
            List.mem_map.mpr ⟨(z, bz), hz_seg0, rfl⟩
          have hx_fst : x.1 ∈ ((rest.map Prod.fst).flatten).map Prod.fst :=
            List.mem_map.mpr ⟨x, hx_rest, rfl⟩
          rw [heq] at hz_fst
          exact hnodup_split hz_fst hx_fst
        have h_inner_disj_πi : ∀ x ∈ inner,
            (πI.any fun (z, _) => z == x.1) = false := by
          intro x hx
          rw [hπi_eq_seg]; exact h_inner_disj_seg0 x hx
        have h_inner_disj_ρ : ∀ x ∈ inner, (ρ.any fun (z, _) => z == x.1) = false := by
          intro x hx
          have hx_rest := h_inner_sub_rest x hx
          have : x ∈ remaining_π := by
            rw [hsegs_eq, List.map_cons, List.flatten_cons]
            exact List.mem_append_right _ hx_rest
          exact hdisj_ρ x.1 x.2 this
        have h_seg0_disj_ρ : ∀ x ∈ seg0.1, (ρ.any fun (z, _) => z == x.1) = false := by
          intro x hx
          have : x ∈ remaining_π := by
            rw [hsegs_eq, List.map_cons, List.flatten_cons]
            exact List.mem_append_left _ hx
          exact hdisj_ρ x.1 x.2 this
        have h_πi_disj_ρ' : ∀ x ∈ πI, (ρ.any fun (z, _) => z == x.1) = false := by
          intro x hx; rw [hπi_eq_seg] at hx; exact h_seg0_disj_ρ x hx
        -- Associativity of assignment extension moves `seg0.1` into ρ'.
        have h_combined_split : combineRestrictions ρ (seg0.1 ++ inner) =
            combineRestrictions ρ' inner := by
          rw [hρ'_def, ← hπi_eq_seg]
          rw [combineRestrictions_append_eq_nested ρ πI inner h_πi_disj_ρ' h_inner_disj_ρ
            h_inner_disj_πi]
        rw [h_consumed_eq, h_combined_split] at h_outer
        have h_idx_eq : (seg0 :: rest)[j + 1]'hj1 = rest[j]'hj := by
          simp [List.getElem_cons_succ]
        rw [h_idx_eq] at h_outer
        -- Massage filter on remaining_π = seg0.1 ++ flatten rest to filter on remaining'
        have h_filt_eq : remaining_π.filter (fun (w : Nat × Bool) =>
            !(seg0.1 ++ inner).any (fun (w' : Nat × Bool) => w'.1 == w.1)) =
            remaining'.filter (fun (w : Nat × Bool) =>
              !inner.any (fun (w' : Nat × Bool) => w'.1 == w.1)) := by
          rw [hrem'_eq, hsegs_eq, List.map_cons, List.flatten_cons,
            List.filter_append]
          have h_seg0_zero : seg0.1.filter (fun (w : Nat × Bool) =>
              !(seg0.1 ++ inner).any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro ⟨w, b⟩ hwb
            simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_append,
              Bool.or_eq_true]
            left
            rw [List.any_eq_true]
            exact ⟨(w, b), hwb, by simp⟩
          have h_rest_drop : ((rest.map Prod.fst).flatten).filter
              (fun (w : Nat × Bool) =>
                !(seg0.1 ++ inner).any (fun (w' : Nat × Bool) => w'.1 == w.1)) =
              ((rest.map Prod.fst).flatten).filter
                (fun (w : Nat × Bool) =>
                  !inner.any (fun (w' : Nat × Bool) => w'.1 == w.1)) := by
            apply List.filter_congr
            intro ⟨w, b⟩ hwb
            simp only [List.any_append, Bool.not_or]
            have h_seg0_no : seg0.1.any (fun (w', _) => w' == w) = false := by
              rw [List.any_eq_false]
              intro ⟨z, bz⟩ hz_seg0
              simp only [beq_iff_eq]; intro heq
              have hz_fst : z ∈ seg0.1.map Prod.fst :=
                List.mem_map.mpr ⟨(z, bz), hz_seg0, rfl⟩
              have hw_fst : w ∈ ((rest.map Prod.fst).flatten).map Prod.fst :=
                List.mem_map.mpr ⟨(w, b), hwb, rfl⟩
              rw [heq] at hz_fst
              exact hnodup_split hz_fst hw_fst
            rw [h_seg0_no]
            simp
          rw [h_seg0_zero, h_rest_drop]
          simp
        rw [h_filt_eq] at h_outer
        exact h_outer
      -- ── Step 8: Apply IH ──
      have hsegs_align' : ∀ p ∈ rest, p.1.length ≤ p.2.length :=
        fun p hp => hsegs_align p (List.mem_cons_of_mem _ hp)
      have h_seg_nonempty' : ∀ p ∈ rest, p.1 ≠ [] :=
        fun p hp => h_seg_nonempty p (List.mem_cons_of_mem _ hp)
      have h_ih := ih fuel' remaining' ρ' dead_acc'
        hfuel' hrem'_eq hnodup_rem' hdisj_ρ' hsegs_align' h_seg_nonempty' h_align'
      rw [h_ih]
      -- ── Step 9: Close arithmetic ──
      have hrem'_len : remaining'.length = (rest.map Prod.fst).flatten.length := by
        rw [hrem'_eq]
      have hrem_len : remaining_π.length = seg0.1.length +
          (rest.map Prod.fst).flatten.length := by
        rw [hsegs_eq, List.map_cons, List.flatten_cons, List.length_append]
      rw [hda'_def, List.length_append, hγ_len, hπi_eq_seg, hrem'_len, hrem_len]
      omega

/-- **Mid-segment tiling: the truncation `path.take d` only chops the LAST
    segment.**

    Given the iter-split `segments_full` of the full path (from
    `encoder_roftnkb_eq_segment_head`), `π = path.take d` is obtained by
    keeping a prefix of `segments_full` whole and possibly truncating the
    next segment in the middle. In particular, every segment **strictly
    before** the cut-point is contained entirely in `π`, and only the
    final (boundary) segment may be partially consumed.

    Concretely we produce:
    - `k` (the number of fully-tiled segments),
    - a prefix of the next segment, possibly `[]`,
      such that
        `π = ((segments_full.take k).map fst).flatten ++ partial`,
        `partial <+: (segments_full[k]?.map fst).getD []`.

    *Why this holds.* `path = (segments_full.map fst).flatten`. Truncating
    `path` at index `d` either lands at a segment boundary (`partial = []`,
    `k = #segments fully consumed`) or strictly inside one segment (then
    `partial = segments_full[k].1.take r` for some `0 < r <
    segments_full[k].1.length`). All segments `< k` are fully contained
    because their cumulative length is `≤ d`.

    The proof decomposes `List.flatten` by cumulative segment lengths. -/
private lemma path_take_d_segment_truncation
    (path : List (Nat × Bool)) (d : Nat)
    (segments_full : List (List (Nat × Bool) × List (Nat × Bool)))
    (hpath_eq : path = (segments_full.map Prod.fst).flatten) :
    ∃ (k : Nat) (partial_last : List (Nat × Bool)),
      k ≤ segments_full.length ∧
      path.take d =
        ((segments_full.take k).map Prod.fst).flatten ++ partial_last ∧
      (∀ (hk : k < segments_full.length),
        partial_last <+: (segments_full[k]'hk).1) ∧
      (∀ (hk : k < segments_full.length),
        partial_last = (segments_full[k]'hk).1 → False) := by
  subst hpath_eq
  induction segments_full generalizing d with
  | nil =>
    refine ⟨0, [], by simp, by simp, ?_, ?_⟩ <;> intro hk <;> simp at hk
  | cons s rest ih =>
    by_cases hd_lt : d < s.1.length
    · -- Cut inside the very first segment.
      refine ⟨0, s.1.take d, by simp, ?_, ?_, ?_⟩
      · simp only [List.take_zero, List.map_nil, List.flatten_nil,
          List.nil_append, List.map_cons, List.flatten_cons]
        rw [List.take_append_of_le_length (le_of_lt hd_lt)]
      · intro _; exact List.take_prefix _ _
      · intro _ hpart
        have hlen : (s.1.take d).length = ((s :: rest)[0]'(by simp)).1.length := by
          rw [hpart]
        simp only [List.length_take, List.getElem_cons_zero] at hlen
        rw [min_eq_left (le_of_lt hd_lt)] at hlen
        omega
    · -- Consume the first segment whole, recurse on the rest.
      push Not at hd_lt
      obtain ⟨k', partial_last, hk'_le, hpath_eq', hpref, hstrict⟩ :=
        ih (d - s.1.length)
      refine ⟨k' + 1, partial_last, ?_, ?_, ?_, ?_⟩
      · simp; omega
      · rw [List.map_cons, List.flatten_cons, List.take_append,
            List.take_of_length_le hd_lt, hpath_eq',
            List.take_succ_cons, List.map_cons, List.flatten_cons,
            List.append_assoc]
      · intro hk
        have hk' : k' < rest.length := by
          simp at hk; omega
        simpa [List.getElem_cons_succ] using hpref hk'
      · intro hk hpart
        have hk' : k' < rest.length := by
          simp at hk; omega
        apply hstrict hk'
        simpa [List.getElem_cons_succ] using hpart

/-- **Path-segment decomposition under truncation (with nodup-fst).**

    Given segments `segs` whose flattened `.1` projection equals `path`,
    with per-segment alignment `p.1.fst = p.2.fst` and nonempty `.1`,
    truncating `path` at depth `d` yields a structurally-aligned segment
    decomposition of `path.take d`:

    `trunc := segs.take k ++ (if partial = [] then [] else
                              [(partial, (segs[k]'_).2.take partial.length)])`

    where `(k, partial)` come from `path_take_d_segment_truncation`.

    The lemma packages all properties needed by `h_truncated_segments`:
    1. `trunc.length ≤ (path.take d).length` — Each `.1` is nonempty so
       `trunc.length ≤ Σ |.1| = |path.take d|`.
    2. `path.take d = (trunc.map fst).flatten` — From the truncation eqn.
    3. `∀ p ∈ trunc, p.1.length ≤ p.2.length` — Full segs use alignment;
       partial uses `partial <+: segs[k].1` plus alignment.
    4. `∀ p ∈ trunc, p.1 ≠ []` — Full segs by hyp; partial nonempty by
       construction (we drop the partial entry when empty).
    5. **Bridge to full segments.** For `j < trunc.length`:
         `((trunc.take j).map fst).flatten = ((segs.take j).map fst).flatten`.
       This is the key `nodup-fst`-flavored prefix identity that lets
       `h_align` for `trunc` inherit from `h_align` for `segs`.
    6. **Per-segment recovery.** For `j < trunc.length`:
         `(trunc[j]).1 <+: (segs[j]).1`  and  `(trunc[j]).2 = (segs[j]).2`
       when `j < k` (full match), and the partial slot satisfies the
       `<+:` and `.2 = (segs[k]).2.take partial.length` relations. -/
private lemma path_take_segments_truncate
    (path : List (Nat × Bool)) (d : Nat)
    (segs : List (List (Nat × Bool) × List (Nat × Bool)))
    (hflat : path = (segs.map Prod.fst).flatten)
    (halgn : ∀ p ∈ segs, p.1.map Prod.fst = p.2.map Prod.fst)
    (hne : ∀ p ∈ segs, p.1 ≠ []) :
    ∃ (trunc : List (List (Nat × Bool) × List (Nat × Bool))) (k : Nat),
      k ≤ segs.length ∧
      trunc.length ≤ (path.take d).length ∧
      path.take d = (trunc.map Prod.fst).flatten ∧
      (∀ p ∈ trunc, p.1.length ≤ p.2.length) ∧
      (∀ p ∈ trunc, p.1 ≠ []) ∧
      k ≤ trunc.length ∧
      trunc.length ≤ k + 1 ∧
      (∀ (j : Nat) (hj : j < trunc.length),
        ∃ (hj_full : j < segs.length),
          ((trunc.take j).map Prod.fst).flatten =
            ((segs.take j).map Prod.fst).flatten ∧
          (trunc[j]'hj).2 = (segs[j]'hj_full).2 ∧
          (trunc[j]'hj).1 <+: (segs[j]'hj_full).1) := by
  -- Length-alignment from fst-equality.
  have hlen_align : ∀ p ∈ segs, p.1.length = p.2.length := fun p hp => by
    have := congrArg List.length (halgn p hp); simpa using this
  -- Helper: if all .1 are nonempty, then |xs| ≤ |flatten of .1|.
  have hlen_le_flat : ∀ (xs : List (List (Nat × Bool) × List (Nat × Bool))),
      (∀ q ∈ xs, q.1 ≠ []) → xs.length ≤ ((xs.map Prod.fst).flatten).length := by
    intro xs hne_xs
    induction xs with
    | nil => simp
    | cons a rest ih =>
      simp [List.length_flatten]
      have ha_pos : 1 ≤ a.1.length :=
        Nat.one_le_iff_ne_zero.mpr (fun h0 =>
          hne_xs a (by simp) (List.length_eq_zero_iff.mp h0))
      have hrest := ih (fun q hq => hne_xs q (by simp [hq]))
      simp [List.length_flatten] at hrest
      omega
  -- Apply path truncation.
  obtain ⟨k, partial_last, hk_le, hpath_eq, hpref_part, hstrict_part⟩ :=
    path_take_d_segment_truncation path d segs hflat
  -- Decide whether to include the partial slot.
  by_cases hpart_nil : partial_last = []
  · -- Boundary cut; trunc := segs.take k.
    refine ⟨segs.take k, k, hk_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- length bound: trunc.length ≤ |path.take d|
      have h_eq : path.take d = ((segs.take k).map Prod.fst).flatten := by
        rw [hpath_eq, hpart_nil, List.append_nil]
      rw [h_eq]
      exact hlen_le_flat _ (fun q hq =>
        hne q ((List.take_sublist k segs).subset hq))
    · -- path.take d = flatten
      rw [hpath_eq, hpart_nil, List.append_nil]
    · -- alignment p.1.length ≤ p.2.length
      intro p hp
      have hp_segs : p ∈ segs := (List.take_sublist k segs).subset hp
      exact le_of_eq (hlen_align p hp_segs)
    · -- nonemptiness
      intro p hp
      exact hne p ((List.take_sublist k segs).subset hp)
    · -- k ≤ trunc.length
      exact (List.length_take_of_le hk_le).symm.le
    · -- trunc.length ≤ k + 1
      have := List.length_take_le k segs
      omega
    · -- bridge to full segments (j < k)
      intro j hj
      have hj_le_k : j < k := by
        rw [List.length_take_of_le hk_le] at hj; exact hj
      have hj_full : j < segs.length := lt_of_lt_of_le hj_le_k hk_le
      refine ⟨hj_full, ?_, ?_, ?_⟩
      · -- ((trunc.take j).map fst).flatten = ((segs.take j).map fst).flatten
        have h_take_take : (segs.take k).take j = segs.take j := by
          rw [List.take_take, min_eq_left (le_of_lt hj_le_k)]
        rw [h_take_take]
      · -- trunc[j].2 = segs[j].2
        simp [List.getElem_take]
      · -- trunc[j].1 <+: segs[j].1
        have h_idx : (segs.take k)[j]'hj = segs[j]'hj_full := by
          simp [List.getElem_take]
        rw [h_idx]
  · -- Strict cut inside (k+1)-th segment; trunc := segs.take k ++ [(partial, segs[k].2.take |partial|)].
    -- partial nonempty implies k < segs.length (otherwise partial ≤ [] = remaining).
    have hk_lt : k < segs.length := by
      rcases Nat.lt_or_ge k segs.length with h | h
      · exact h
      · -- k = segs.length: then segs.take k = segs, flatten = path, so path.take d = path ++ partial.
        -- This means partial is "beyond" path, but path.take d ⊆ path ⟹ partial = [].
        have hk_eq : k = segs.length := le_antisymm hk_le h
        rw [hk_eq, List.take_length] at hpath_eq
        -- path.take d = (segs.map fst).flatten ++ partial = path ++ partial
        rw [← hflat] at hpath_eq
        have hpart_len : partial_last.length = 0 := by
          have hle : (path.take d).length ≤ path.length := List.length_take_le' d path
          have heq : (path.take d).length = path.length + partial_last.length := by
            rw [hpath_eq]; simp
          omega
        exact absurd (List.length_eq_zero_iff.mp hpart_len) hpart_nil
    have hpref : partial_last <+: (segs[k]'hk_lt).1 := hpref_part hk_lt
    have hstrict : ¬ partial_last = (segs[k]'hk_lt).1 := fun h =>
      hstrict_part hk_lt h
    have hpart_lt : partial_last.length < (segs[k]'hk_lt).1.length :=
      lt_of_le_of_ne hpref.length_le (fun heq => hstrict (hpref.eq_of_length heq))
    set tail_seg : List (Nat × Bool) × List (Nat × Bool) :=
      (partial_last, (segs[k]'hk_lt).2) with htail_def
    refine ⟨segs.take k ++ [tail_seg], k, hk_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- length bound
      have h_eq : path.take d =
          (((segs.take k ++ [tail_seg]).map Prod.fst).flatten) := by
        rw [hpath_eq, List.map_append, List.flatten_append]
        simp [htail_def]
      rw [h_eq]
      apply hlen_le_flat
      intro q hq
      rw [List.mem_append] at hq
      rcases hq with hq_full | hq_tail
      · exact hne q ((List.take_sublist k segs).subset hq_full)
      · simp at hq_tail; rw [hq_tail, htail_def]; exact hpart_nil
    · -- path.take d = flatten
      rw [hpath_eq]
      rw [List.map_append, List.flatten_append]
      simp [htail_def]
    · -- alignment p.1.length ≤ p.2.length
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp_full | hp_tail
      · have hp_segs : p ∈ segs := (List.take_sublist k segs).subset hp_full
        exact le_of_eq (hlen_align p hp_segs)
      · simp at hp_tail
        rw [hp_tail, htail_def]
        have hk_align := hlen_align _ (List.getElem_mem hk_lt)
        exact le_of_lt (lt_of_lt_of_le hpart_lt (le_of_eq hk_align))
    · -- nonemptiness
      intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp_full | hp_tail
      · exact hne p ((List.take_sublist k segs).subset hp_full)
      · simp at hp_tail
        rw [hp_tail, htail_def]
        exact hpart_nil
    · -- k ≤ trunc.length
      simp [List.length_take_of_le hk_le]
    · -- trunc.length ≤ k + 1
      simp [List.length_take_of_le hk_le]
    · -- bridge to full segments
      intro j hj
      simp at hj
      rcases Nat.lt_or_ge j k with hj_lt | hj_ge
      · -- j < k: full segment slot
        have hj_full : j < segs.length := lt_of_lt_of_le hj_lt hk_le
        have h_le_take_k : j ≤ (segs.take k).length := by
          rw [List.length_take_of_le hk_le]; omega
        refine ⟨hj_full, ?_, ?_, ?_⟩
        · -- prefix sums equal
          have h1 : (segs.take k ++ [tail_seg]).take j = (segs.take k).take j :=
            List.take_append_of_le_length h_le_take_k
          have h2 : (segs.take k).take j = segs.take j := by
            rw [List.take_take, min_eq_left (le_of_lt hj_lt)]
          rw [h1, h2]
        · -- .2 equality
          have h_idx_lt : j < (segs.take k).length := by
            rw [List.length_take_of_le hk_le]; exact hj_lt
          have h_idx : (segs.take k ++ [tail_seg])[j]'(by
              rw [List.length_append]; omega) =
              (segs.take k)[j]'h_idx_lt :=
            List.getElem_append_left h_idx_lt
          rw [h_idx]; simp [List.getElem_take]
        · -- .1 prefix
          have h_idx_lt : j < (segs.take k).length := by
            rw [List.length_take_of_le hk_le]; exact hj_lt
          have h_idx : (segs.take k ++ [tail_seg])[j]'(by
              rw [List.length_append]; omega) =
              (segs.take k)[j]'h_idx_lt :=
            List.getElem_append_left h_idx_lt
          rw [h_idx]; simp [List.getElem_take]
      · -- j = k: partial slot
        have hj_eq : j = k := by omega
        have h_eq_take : (List.take k segs).length = k := List.length_take_of_le hk_le
        have h_le_take_k : k ≤ (List.take k segs).length := h_eq_take.symm.le
        have h_idx_t : (segs.take k ++ [tail_seg])[j]'(by
            rw [List.length_append, h_eq_take]; simp; omega) = tail_seg := by
          have hge : (segs.take k).length ≤ j := by rw [h_eq_take]; omega
          rw [List.getElem_append_right hge]
          have hsub : j - (segs.take k).length = 0 := by rw [h_eq_take]; omega
          simp []
        have hj_full : j < segs.length := hj_eq ▸ hk_lt
        have h_seg_idx_eq : segs[j]'hj_full = segs[k]'hk_lt := by
          cases hj_eq; rfl
        refine ⟨hj_full, ?_, ?_, ?_⟩
        · -- ((trunc.take j).map fst).flatten = ((segs.take j).map fst).flatten
          rw [hj_eq]
          have h_take : (segs.take k ++ [tail_seg]).take k = segs.take k := by
            rw [List.take_append_of_le_length h_le_take_k, List.take_take]
            simp []
          rw [h_take]
        · -- (trunc[j]).2 = (segs[j]).2
          rw [h_idx_t, htail_def, h_seg_idx_eq]
        · -- (trunc[j]).1 <+: (segs[j]).1
          rw [h_idx_t, htail_def, h_seg_idx_eq]
          exact hpref

/-- The encoder produces exactly `asgn.length + d` dead variables
    when a path of depth ≥ d exists in the full-query canonical DT.

    The proof obtains the iter-split `segments` of `path` from
    `cdt_full_query_killed_heads_covered_by_prefix` and discharges the
    encoder-step bridge via segment alignment. -/
private lemma encoder_dead_length
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool))
    (d : Nat)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path) :
    (encodeRestrictionFromFormula d f.val asgn).1.length = asgn.length + d := by
  simp only [encodeRestrictionFromFormula]
  rw [hpath]
  set π := path.take d with hπ_def
  -- π.length = d.
  have hpath_len := leftmostPathExceedingDepth_some_path_length_gt
    (canonicalDecisionTree f.val asgn) d path hpath
  have htake_len : π.length = d := List.length_take_of_le (by omega)
  -- Restricted DNF nodup-fst (needed for the segments lemma).
  have hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup :=
    restrictDNF_preserves_clause_nodup f.val
      (restrictionAsFunction asgn) hnodup
  -- IsPathIn for the full path through the asgn-grafted CDT.
  have hp_isin :
      IsPathIn (canonicalDecisionTree f.val asgn) path :=
    leftmostPathExceedingDepth_isPathIn _ _ _ hpath
  -- Get the iter-split segments of `path` with the killed-heads-covered conjunct.
  obtain ⟨_segments_full, _hpath_eq, _hlen, _hcov, _hheads, _hnd_seg, _hkill,
            _hkilled_covered, _hcum_a⟩ :=
    cdt_full_query_killed_heads_covered_by_prefix f asgn hnodup_restricted
      path hp_isin
  -- π has nodup fst.
  have hnodup_π : (π.map Prod.fst).Nodup :=
    canonical_dt_path_take_nodup_fst f.val asgn hnodup d path hpath
  -- Path vars are unassigned in asgn.
  have hpath_var_none : ∀ w b, (w, b) ∈ π →
      restrictionAsFunction asgn w = none := fun w b hw =>
    canonical_dt_path_var_none f.val asgn f.property.2 d path hpath
      w b (List.mem_of_mem_take hw)
  have hπ_disj_asgn : ∀ w b, (w, b) ∈ π →
      (asgn.any fun (z, _) => z == w) = false := by
    intro w b hw
    rw [list_any_eq_cr_none_isSome, hpath_var_none w b hw]; rfl
  -- ── Structural bridge: truncate the full segments to cover exactly π. ──
  -- Produce `segments` such that `π = (segments.map fst).flatten`,
  -- `segments.length ≤ π.length`, segment-heads have aligned fst-projections,
  -- segment prefixes are non-empty, and at each step the encoder's selected clause
  -- equals the segment head and the filter-prefix equals the segment prefix.
  --
  -- This walks `_segments_full`, summing prefix lengths to carve out a
  -- tiling of `π` and align encoder iterations with segment indices.
  have h_truncated_segments :
      ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))),
        segments.length ≤ π.length ∧
        π = (segments.map Prod.fst).flatten ∧
        (∀ p ∈ segments, p.1.length ≤ p.2.length) ∧
        (∀ p ∈ segments, p.1 ≠ []) ∧
        (∀ (j : Nat) (hj : j < segments.length),
          restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
            (combineRestrictions asgn
              (((segments.take j).map Prod.fst).flatten)) =
            (segments[j]'hj).2 ∧
          (π.filter (fun (w : Nat × Bool) =>
            !(((segments.take j).map Prod.fst).flatten).any
              (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
            (fun x => ((restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
              (combineRestrictions asgn
                (((segments.take j).map Prod.fst).flatten))).map
              Prod.fst).contains x.1) =
            (segments[j]'hj).1) := by
    -- Step 1: get full segments via encoder_roftnkb_eq_segment_head.
    obtain ⟨segs_full, hsf_path, hsf_align, _hsf_heads, hsf_ne, hsf_roftnkb⟩ :=
      encoder_roftnkb_eq_segment_head f hnodup asgn d path hpath
    -- Step 2: truncate to depth d.
    obtain ⟨trunc, k, _hk_le, htrunc_len, htrunc_path, htrunc_align,
            htrunc_ne, _hk_le_t, _ht_le_k1, htrunc_bridge⟩ :=
      path_take_segments_truncate path d segs_full hsf_path hsf_align hsf_ne
    -- Path-fst nodup, used for the filter equation.
    have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
      canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
    refine ⟨trunc, htrunc_len, htrunc_path, htrunc_align, htrunc_ne, ?_⟩
    intro j hj
    obtain ⟨hj_full, hcum_eq, hidx2_eq, hidx1_pref⟩ := htrunc_bridge j hj
    -- First conjunct: align the first non-killed clause via the bridge.
    have h_first :
        restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions asgn
            (((trunc.take j).map Prod.fst).flatten)) =
          (trunc[j]'hj).2 := by
      rw [hcum_eq, hidx2_eq]
      exact hsf_roftnkb j hj_full
    refine ⟨h_first, ?_⟩
    -- Second conjunct: filter equation.
    -- Rewrite the inner selected clause to `(trunc[j]).2` via `h_first`, then
    -- to `(segs_full[j]).2`.
    rw [h_first, hidx2_eq]
    -- Now goal: (π.filter (∉ cum_j(trunc))).filter (∈ segs_full[j].2.fst) = trunc[j].1.
    -- Step A: π = cum_j ++ rest_of_π where cum_j = ((segs_full.take j).map fst).flatten.
    --   rest_of_π = (bits in segs_full[j..k-1].1) ++ partial = bits indexed ≥ cum_j.length in π.
    -- Step B: by π.fst.Nodup (sublist of path.fst.Nodup), filter (∉ cum_j) keeps rest_of_π.
    -- Step C: filter (∈ segs_full[j].2.fst) on rest_of_π = filter (∈ segs_full[j].1.fst) =
    --   (since segs_full[j].1 is the first chunk of rest_of_π, and remaining bits have
    --    distinct vars by nodup) just keeps the bits whose var is in segs_full[j].1.fst.
    -- For full slot (j < k): trunc[j].1 = segs_full[j].1, and the filter keeps exactly that.
    -- For partial slot (j = k): trunc[j].1 = partial <+: segs_full[k].1, and rest_of_π = partial,
    --   so filter keeps all of partial = trunc[j].1.
    -- We prove this by reusing path_filter_segment_eq applied to a custom segment list.
    --
    -- Concretely: π = (trunc.map fst).flatten. trunc[j].2 = segs_full[j].2.
    -- Use path_filter_segment_eq on `trunc` if alignment held. But trunc[k].2 = segs_full[k].2
    -- while trunc[k].1 = partial, with partial.fst <+: segs_full[k].1.fst = segs_full[k].2.fst.
    -- So path_filter_segment_eq does NOT directly apply (alignment is only fst-prefix,
    -- not equality). We do the filter computation directly.
    --
    -- π.fst.Nodup
    have hπ_nodup_fst : (π.map Prod.fst).Nodup := hnodup_π
    -- Decompose π = cum_j ++ rest_j using htrunc_path and trunc structure.
    set cum_j := ((trunc.take j).map Prod.fst).flatten with hcumj_def
    set rest_j := ((trunc.drop j).map Prod.fst).flatten with hrest_def
    have hπ_split : π = cum_j ++ rest_j := by
      rw [hπ_def, htrunc_path, hcumj_def, hrest_def]
      rw [show (List.map Prod.fst (List.take j trunc)).flatten ++
              (List.map Prod.fst (List.drop j trunc)).flatten =
            (List.map Prod.fst (List.take j trunc) ++
              List.map Prod.fst (List.drop j trunc)).flatten from
              List.flatten_append.symm,
          ← List.map_append, List.take_append_drop]
    -- π.fst = cum_j.fst ++ rest_j.fst, both Nodup with disjoint vars.
    have hcum_rest_nd : ((cum_j.map Prod.fst) ++ (rest_j.map Prod.fst)).Nodup := by
      have := hπ_nodup_fst
      rw [hπ_split, List.map_append] at this
      exact this
    have hcum_rest_disj : ∀ a ∈ cum_j.map Prod.fst,
        ∀ b ∈ rest_j.map Prod.fst, a ≠ b :=
      (List.nodup_append.mp hcum_rest_nd).2.2
    -- Step A: filter (∉ cum_j) on π yields rest_j.
    have hfilter_not_cum : π.filter (fun (w : Nat × Bool) =>
        !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = rest_j := by
      rw [hπ_split, List.filter_append]
      have h_cum_drop : cum_j.filter (fun (w : Nat × Bool) =>
          !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro w hw _
        have : cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1) = true := by
          rw [List.any_eq_true]; exact ⟨w, hw, by simp⟩
        simp [this] at *
      have h_rest_keep : rest_j.filter (fun (w : Nat × Bool) =>
          !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = rest_j := by
        apply List.filter_eq_self.mpr
        intro w hw
        simp only [Bool.not_eq_true']
        rw [List.any_eq_false]
        intro ⟨z, bz⟩ hz_cum
        simp only [beq_iff_eq]
        intro heq
        have hz_fst : z ∈ cum_j.map Prod.fst :=
          List.mem_map.mpr ⟨(z, bz), hz_cum, rfl⟩
        have hw_fst : w.1 ∈ rest_j.map Prod.fst :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact hcum_rest_disj z hz_fst w.1 hw_fst heq
      rw [h_cum_drop, h_rest_keep, List.nil_append]
    -- Decompose rest_j = trunc[j].1 ++ tail_j where tail_j = ((trunc.drop (j+1)).map fst).flatten
    set tail_j := ((trunc.drop (j+1)).map Prod.fst).flatten with htail_def
    have hrest_split : rest_j = (trunc[j]'hj).1 ++ tail_j := by
      rw [hrest_def, htail_def]
      have h_drop_succ : trunc.drop j = (trunc[j]'hj) :: trunc.drop (j+1) := by
        rw [← List.getElem_cons_drop hj]
      rw [h_drop_succ, List.map_cons, List.flatten_cons]
    -- rest_j.fst.Nodup (sublist of π.fst).
    have hrest_nodup : (rest_j.map Prod.fst).Nodup :=
      (List.nodup_append.mp hcum_rest_nd).2.1
    have hsplit_nd : ((trunc[j]'hj).1.map Prod.fst ++ tail_j.map Prod.fst).Nodup := by
      have := hrest_nodup; rw [hrest_split, List.map_append] at this; exact this
    have hseg_tail_disj : ∀ a ∈ (trunc[j]'hj).1.map Prod.fst,
        ∀ b ∈ tail_j.map Prod.fst, a ≠ b :=
      (List.nodup_append.mp hsplit_nd).2.2
    -- Step B: filter (∈ segs_full[j].2.fst) on rest_j.
    -- Key: trunc[j].1.fst ⊆ segs_full[j].1.fst (via prefix) ⊆ segs_full[j].2.fst (via halgn).
    -- And tail_j.fst ⊆ rest_j.fst, disjoint from trunc[j].1.fst by hsplit_nd.
    -- Tail vars: each in some trunc[j'].1.fst with j' > j.
    -- Whether tail vars belong to segs_full[j].2.fst: by overall path-nodup, since
    -- trunc[j'].1 (j' > j) has vars in some segs_full[j'].1, with j' ≥ j (or partial of segs_full[k]).
    -- All these segs_full[j'].1 (j' > j) and segs_full[k].1 have vars distinct from segs_full[j].1
    -- (by path-nodup). And segs_full[j].2.fst = segs_full[j].1.fst (via hsf_align).
    -- So tail_j vars are NOT in segs_full[j].2.fst.
    have hsf_align_j : (segs_full[j]'hj_full).1.map Prod.fst =
        (segs_full[j]'hj_full).2.map Prod.fst :=
      hsf_align _ (List.getElem_mem hj_full)
    have htrj_fst_sub : ∀ v ∈ (trunc[j]'hj).1.map Prod.fst,
        v ∈ (segs_full[j]'hj_full).1.map Prod.fst := by
      intro v hv
      rw [List.mem_map] at hv
      obtain ⟨w, hw, hw_eq⟩ := hv
      have := hidx1_pref.subset hw
      exact List.mem_map.mpr ⟨w, this, hw_eq⟩
    rw [hfilter_not_cum, hrest_split, List.filter_append]
    have h_seg_keep : (trunc[j]'hj).1.filter
        (fun x => ((segs_full[j]'hj_full).2.map Prod.fst).contains x.1) =
        (trunc[j]'hj).1 := by
      apply List.filter_eq_self.mpr
      intro w hw
      rw [List.contains_iff_mem, ← hsf_align_j]
      exact htrj_fst_sub w.1 (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have h_tail_drop : tail_j.filter
        (fun x => ((segs_full[j]'hj_full).2.map Prod.fst).contains x.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw hcontra
      rw [List.contains_iff_mem, ← hsf_align_j] at hcontra
      -- Full slots agree with their untruncated segment, while the boundary
      -- slot has an empty tail. In either case `hcontra` conflicts with the
      -- duplicate-free split at `j`.
      have hw_tail_fst : w.1 ∈ tail_j.map Prod.fst :=
        List.mem_map.mpr ⟨w, hw, rfl⟩
      -- Split between a full slot and the boundary slot.
      have hk_le_t : k ≤ trunc.length := _hk_le_t
      by_cases hjk : j < k
      · -- Full slot: trunc[j] = segs_full[j], so trunc[j].1.fst = segs_full[j].1.fst.
        have hj_lt_k : j < k := hjk
        -- For a full slot, prove equality via the adjacent cumulative prefixes:
        -- ((trunc.take (j+1)).map fst).flatten = ((segs_full.take (j+1)).map fst).flatten
        -- (using bridge with j+1). Combined with hcum_eq (bridge for j), get
        -- trunc[j].1 = segs_full[j].1 by cancellation.
        have hj1_lt : j + 1 < trunc.length ∨ j + 1 = trunc.length := by
          rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        -- Always j + 1 ≤ k (since j < k), so hj+1 < trunc.length (since k ≤ trunc.length).
        have hj1_lt_t : j + 1 ≤ trunc.length :=
          le_trans (Nat.succ_le_of_lt hjk) hk_le_t
        rcases Nat.lt_or_eq_of_le hj1_lt_t with hj1_lt' | hj1_eq
        · -- j + 1 < trunc.length: use bridge at j+1.
          obtain ⟨_hj1_full, hcum_eq_j1, _, _⟩ := htrunc_bridge (j+1) hj1_lt'
          -- ((trunc.take (j+1)).map fst).flatten = cum_j ++ trunc[j].1.fst-ish.
          have hcum_trunc_succ : ((trunc.take (j+1)).map Prod.fst).flatten =
              cum_j ++ (trunc[j]'hj).1 := by
            rw [show trunc.take (j+1) = trunc.take j ++ [trunc[j]'hj] from
                List.take_succ_eq_append_getElem hj,
              List.map_append, List.flatten_append]
            simp [hcumj_def]
          have hcum_segs_succ : ((segs_full.take (j+1)).map Prod.fst).flatten =
              ((segs_full.take j).map Prod.fst).flatten ++ (segs_full[j]'hj_full).1 := by
            rw [show segs_full.take (j+1) = segs_full.take j ++ [segs_full[j]'hj_full] from
                List.take_succ_eq_append_getElem hj_full,
              List.map_append, List.flatten_append]
            simp
          rw [hcum_trunc_succ, hcum_segs_succ, ← hcum_eq] at hcum_eq_j1
          have htrj1_eq : (trunc[j]'hj).1 = (segs_full[j]'hj_full).1 :=
            List.append_cancel_left hcum_eq_j1
          have hw_in_segj : w.1 ∈ (trunc[j]'hj).1.map Prod.fst := by
            rw [htrj1_eq]; exact hcontra
          exact hseg_tail_disj w.1 hw_in_segj w.1 hw_tail_fst rfl
        · -- j + 1 = trunc.length: tail_j = [].
          have htail_nil : tail_j = [] := by
            rw [htail_def]
            have : trunc.drop (j+1) = [] := List.drop_eq_nil_of_le (le_of_eq hj1_eq.symm)
            rw [this]; simp
          rw [htail_nil] at hw_tail_fst
          simp at hw_tail_fst
      · -- Partial slot (j = k): tail_j = [] since j = trunc.length - 1.
        push Not at hjk
        have hj_eq_k : j = k := le_antisymm (by omega) hjk
        -- trunc.length ≤ k + 1, so j = k means j + 1 ≥ trunc.length.
        have ht_le : trunc.length ≤ k + 1 := _ht_le_k1
        have hj1_ge : j + 1 ≥ trunc.length := by omega
        have htail_nil : tail_j = [] := by
          rw [htail_def]
          have : trunc.drop (j+1) = [] := List.drop_eq_nil_of_le hj1_ge
          rw [this]; simp
        rw [htail_nil] at hw_tail_fst
        simp at hw_tail_fst
    rw [h_seg_keep, h_tail_drop, List.append_nil]
  obtain ⟨segments, hsegs_len, hπ_eq, hsegs_align, h_seg_nonempty, h_align⟩ :=
    h_truncated_segments
  -- Apply the segment-induction helper.
  have haux := encoder_aux_dead_length_via_segments
    π.length π f.val asgn asgn segments hsegs_len hπ_eq hnodup_π
    hπ_disj_asgn hsegs_align h_seg_nonempty h_align
  rw [haux, htake_len]

#print axioms encoder_dead_length

-- ════════════════════════════════════════════════════════════════════════════
-- §  Dead variable nodup fst for encoder
-- ════════════════════════════════════════════════════════════════════════════

/-- Per-step trace predicate for `encoder_aux_dead_nodup_fst` (truncation-aware).

    Mirrors the encoder's own fuel-indexed recursion.  At every fuel-step
    until exhaustion, the trace requires that the **filtered** πI lines
    up with a prefix of the current selected clause's variables:

      `πI.map fst = U_vars.take πI.length` and `πI.length ≤ U_i.length`.

    These two facts together are exactly what the proof needs to conclude
    `γ_i.map fst = πI.map fst` (via `gamma_bits_map_fst_eq` + `List.map_take`).

    Both directions of prefix-comparability between `U_vars` and
    `remaining_π.map fst` produce this:
    * If `U_vars <+: remaining_π.map fst` (non-truncated): `πI =
      remaining_π.take U_vars.length`, so `πI.fst = U_vars`.
    * If `remaining_π.map fst <+: U_vars` (truncated final segment):
      `πI = remaining_π`, so `πI.fst = remaining_π.fst = U_vars.take
      remaining_π.length`. -/
private def EncoderNodupTrace (clauses : List (List (Nat × Bool))) :
    Nat → List (Nat × Bool) → List (Nat × Bool) → Prop
  | 0, _, _ => True
  | n + 1, ρ, rem =>
      let U_i := restrictionOfFirstTermNotKilledByList clauses ρ
      let U_vars := U_i.map Prod.fst
      let πI := rem.filter (fun x => U_vars.contains x.1)
      πI.map Prod.fst = U_vars.take πI.length ∧
      πI.length ≤ U_i.length ∧
      EncoderNodupTrace clauses n (combineRestrictions ρ πI)
        (rem.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w)))

/-- Aux lemma: `beameEncoderAux` preserves nodup on dead_acc.map fst,
    given a per-step trace witnessing the encoder/segment alignment at every
    fuel-step.

    Invariant: `dead_acc.map Prod.fst` is Nodup, and every var in
    `dead_acc.map Prod.fst` is in `ρ` (so disjoint from γ_i vars which are
    in `πI ⊆ remaining_π`, hence NOT in ρ). -/
private lemma encoder_aux_dead_nodup_fst
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (_hnodup_clauses : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (hnodup_acc : (dead_acc.map Prod.fst).Nodup)
    (hacc_in_ρ : ∀ w ∈ dead_acc.map Prod.fst,
      (ρ.any fun (w', _) => w' == w) = true)
    (hnodup_rem : (remaining_π.map Prod.fst).Nodup)
    (hdisj_ρ : ∀ w b, (w, b) ∈ remaining_π →
      (ρ.any fun (z, _) => z == w) = false)
    (h_trace : EncoderNodupTrace (dnfClauses dnf) fuel ρ remaining_π) :
    ((beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1.map Prod.fst).Nodup := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero => simp [beameEncoderAux]; exact hnodup_acc
  | succ n ih =>
    -- Destructure the trace: πI.fst = U_vars.take πI.length + length bound + tail trace
    obtain ⟨hπi_fst_take, _hπi_len_le, h_trace_next⟩ := h_trace
    simp only [beameEncoderAux]
    split
    · exact hnodup_acc
    · rename_i hne
      set clauses := dnfClauses dnf
      set U_i := restrictionOfFirstTermNotKilledByList clauses ρ
      set U_vars := U_i.map Prod.fst
      set p_fn : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
      set πI := remaining_π.filter p_fn
      set γ_i := (gammaBitsForClause U_i).take πI.length
      set dead_acc' := dead_acc ++ γ_i
      set ρ' := combineRestrictions ρ πI
      set remaining' := remaining_π.filter fun (w, _) => !πI.any fun (w', _) => w' == w
      -- πI.fst nodup (from rem nodup via filter sublist)
      have hπi_nodup : (πI.map Prod.fst).Nodup :=
        List.Pairwise.sublist (List.filter_sublist.map _) hnodup_rem
      -- γ_i.map fst = πI.map fst (from trace + gamma_bits_map_fst_eq + List.map_take)
      have hγ_fst_eq : γ_i.map Prod.fst = πI.map Prod.fst := by
        show ((gammaBitsForClause U_i).take πI.length).map Prod.fst = πI.map Prod.fst
        rw [List.map_take, gamma_bits_map_fst_eq]
        exact hπi_fst_take.symm
      -- γ_i has nodup fst
      have hnodup_γ : (γ_i.map Prod.fst).Nodup := hγ_fst_eq ▸ hπi_nodup
      -- γ_i vars are NOT in ρ (γ_i.fst = πI.fst, πI ⊆ rem, rem disjoint ρ)
      have hγ_not_ρ : ∀ w ∈ γ_i.map Prod.fst,
          (ρ.any fun (w', _) => w' == w) = false := by
        intro w hw
        rw [hγ_fst_eq] at hw
        obtain ⟨⟨w', b'⟩, hw'_πi, rfl⟩ := List.mem_map.mp hw
        exact hdisj_ρ w' b' (List.mem_of_mem_filter hw'_πi)
      -- dead_acc and γ_i are fst-disjoint
      have hdisjoint : ∀ a ∈ dead_acc.map Prod.fst,
          ∀ b ∈ γ_i.map Prod.fst, a ≠ b := by
        intro a ha b hb hab
        have : (ρ.any fun (w', _) => w' == a) = true := hacc_in_ρ a ha
        rw [hab] at this
        exact absurd this (by rw [hγ_not_ρ b hb]; decide)
      have hnodup_acc' : (dead_acc'.map Prod.fst).Nodup := by
        show ((dead_acc ++ γ_i).map Prod.fst).Nodup
        rw [List.map_append]
        exact List.nodup_append.mpr ⟨hnodup_acc, hnodup_γ, hdisjoint⟩
      -- Every variable in `dead_acc'` is assigned by ρ'.
      have hacc_in_ρ' : ∀ w ∈ dead_acc'.map Prod.fst,
          (ρ'.any fun (w', _) => w' == w) = true := by
        intro w hw
        show (combineRestrictions ρ πI).any (fun (w', _) => w' == w) = true
        rw [show dead_acc' = dead_acc ++ γ_i from rfl, List.map_append,
            List.mem_append] at hw
        rw [combineRestrictions, List.any_append]
        cases hw with
        | inl hw_acc =>
          exact Bool.or_eq_true_iff.mpr (Or.inl (hacc_in_ρ w hw_acc))
        | inr hw_γ =>
          rw [hγ_fst_eq] at hw_γ
          obtain ⟨⟨w', b'⟩, hw'_πi, rfl⟩ := List.mem_map.mp hw_γ
          have hw'_ρ_none := hdisj_ρ w' b' (List.mem_of_mem_filter hw'_πi)
          rw [Bool.or_eq_true_iff]
          right; rw [List.any_eq_true]
          exact ⟨(w', b'),
            List.mem_filter.mpr ⟨hw'_πi, by simp [hw'_ρ_none]⟩,
            by simp⟩
      split
      · exact hnodup_acc'
      · -- Recursive case
        have hnodup_rem' : (remaining'.map Prod.fst).Nodup :=
          List.Pairwise.sublist (List.filter_sublist.map _) hnodup_rem
        have hdisj_ρ' : ∀ w' b', (w', b') ∈ remaining' →
            (ρ'.any fun (z, _) => z == w') = false := by
          intro w' b' hw_rem'
          have hw_rπ : (w', b') ∈ remaining_π := List.mem_of_mem_filter hw_rem'
          have hρ_none := hdisj_ρ w' b' hw_rπ
          show (combineRestrictions ρ πI).any (fun (z, _) => z == w') = false
          rw [combineRestrictions, List.any_append, hρ_none, Bool.false_or]
          rw [List.any_eq_false]
          intro ⟨z, bz⟩ hz_filt
          simp only [beq_iff_eq]; intro heq
          have hz_πi := List.mem_of_mem_filter hz_filt
          have hw'_in_πi : πI.any (fun (w'', _) => w'' == w') = true := by
            rw [List.any_eq_true]
            exact ⟨(z, bz), hz_πi, by simp [heq]⟩
          have hw_nc := (List.mem_filter.mp hw_rem').2
          simp only [Bool.not_eq_true'] at hw_nc
          exact absurd hw'_in_πi (by rw [hw_nc]; exact Bool.false_ne_true)
        exact ih remaining' ρ' dead_acc' hnodup_acc' hacc_in_ρ'
          hnodup_rem' hdisj_ρ' h_trace_next

#print axioms encoder_aux_dead_nodup_fst

/-- The empty-remaining trace: at every fuel-step, πI collapses to `[]`,
    and `combineRestrictions ρ [] = ρ`, so the trace is satisfied
    vacuously by structural recursion on fuel. -/
private lemma encoder_nodup_trace_empty_rem
    (clauses : List (List (Nat × Bool))) (ρ : List (Nat × Bool)) (fuel : Nat) :
    EncoderNodupTrace clauses fuel ρ [] := by
  induction fuel generalizing ρ with
  | zero => trivial
  | succ n ih =>
    simp only [EncoderNodupTrace, List.filter_nil, List.map_nil, List.length_nil,
      ]
    refine ⟨rfl, Nat.zero_le _, ?_⟩
    have h_combined : combineRestrictions ρ [] = ρ := by
      simp [combineRestrictions]
    rw [h_combined]
    exact ih ρ

/-- Build `EncoderNodupTrace` from segment alignment, mirroring
    `encoder_aux_dead_length_via_segments` but threading the trace's
    `πI.fst = U_vars.take πI.length ∧ πI.length ≤ U_i.length` triple
    instead of the encoder's length output. -/
private lemma encoder_nodup_trace_of_segments
    (clauses : List (List (Nat × Bool)))
    (segments : List (List (Nat × Bool) × List (Nat × Bool)))
    (asgn rem : List (Nat × Bool))
    (fuel : Nat)
    (hsegs_eq : rem = (segments.map Prod.fst).flatten)
    (hnodup_rem : (rem.map Prod.fst).Nodup)
    (hdisj_ρ : ∀ w b, (w, b) ∈ rem →
      (asgn.any fun (z, _) => z == w) = false)
    (hsegs_align : ∀ p ∈ segments, p.1.length ≤ p.2.length)
    (hsegs_align_fst : ∀ p ∈ segments,
      p.1.map Prod.fst = (p.2.map Prod.fst).take p.1.length)
    (h_seg_nonempty : ∀ p ∈ segments, p.1 ≠ [])
    (h_align : ∀ (j : Nat) (hj : j < segments.length),
      restrictionOfFirstTermNotKilledByList clauses
        (combineRestrictions asgn (((segments.take j).map Prod.fst).flatten)) =
        (segments[j]'hj).2 ∧
      (rem.filter (fun (w : Nat × Bool) =>
        !(((segments.take j).map Prod.fst).flatten).any
          (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
        (fun x => ((restrictionOfFirstTermNotKilledByList clauses
          (combineRestrictions asgn
            (((segments.take j).map Prod.fst).flatten))).map
          Prod.fst).contains x.1) =
        (segments[j]'hj).1) :
    EncoderNodupTrace clauses fuel asgn rem := by
  induction segments generalizing fuel asgn rem with
  | nil =>
    have hrem_nil : rem = [] := by simp [hsegs_eq]
    subst hrem_nil
    exact encoder_nodup_trace_empty_rem clauses asgn fuel
  | cons seg0 rest ih =>
    cases fuel with
    | zero => trivial
    | succ fuel' =>
      -- ── Step 1: Apply h_align(0) to identify the first encoder step ──
      have h_align_0_raw := h_align 0 (Nat.succ_pos _)
      simp only [List.take_zero, List.map_nil, List.flatten_nil, List.any_nil,
        Bool.not_false, List.filter_true, combineRestrictions,
        List.filter_nil, List.append_nil, List.getElem_cons_zero]
        at h_align_0_raw
      obtain ⟨h_u_eq, hπi_eq⟩ := h_align_0_raw
      -- Local abbreviations matching the trace's recursion.
      set U_i := restrictionOfFirstTermNotKilledByList clauses asgn with h_u_def
      set U_vars := U_i.map Prod.fst with h_uv_def
      set p_pred : (Nat × Bool) → Bool := fun x => U_vars.contains x.1 with hp_def
      set πI := rem.filter p_pred with hπi_def
      have hπi_eq_seg : πI = seg0.1 := hπi_eq
      have h_u_eq_seg : U_i = seg0.2 := h_u_eq
      -- ── Step 2: Length facts ──
      have hπi_fst_take : πI.map Prod.fst = U_vars.take πI.length := by
        have h_align_fst := hsegs_align_fst seg0 List.mem_cons_self
        rw [hπi_eq_seg, h_uv_def, h_u_eq_seg]
        exact h_align_fst
      have hπi_len_le : πI.length ≤ U_i.length := by
        rw [hπi_eq_seg, h_u_eq_seg]
        exact hsegs_align seg0 List.mem_cons_self
      -- ── Step 3: Goal unfolding ──
      show πI.map Prod.fst = U_vars.take πI.length ∧
           πI.length ≤ U_i.length ∧
           EncoderNodupTrace clauses fuel' (combineRestrictions asgn πI)
             (rem.filter fun (w, _) => !πI.any fun (w', _) => w' == w)
      refine ⟨hπi_fst_take, hπi_len_le, ?_⟩
      -- ── Step 4: Set up the inner state and its invariants ──
      set ρ' := combineRestrictions asgn πI with hρ'_def
      set remaining' := rem.filter
        (fun (w : Nat × Bool) => !πI.any (fun (w' : Nat × Bool) => w'.1 == w.1))
        with hrem'_def
      -- Disjointness of seg0.1 and rest_flat from `rem`'s nodup.
      have hnodup_split :
          (seg0.1.map Prod.fst).Disjoint
            (((rest.map Prod.fst).flatten).map Prod.fst) := by
        have hraw : (((seg0 :: rest).map Prod.fst).flatten.map Prod.fst).Nodup := by
          rw [← hsegs_eq]; exact hnodup_rem
        rw [List.map_cons, List.flatten_cons, List.map_append] at hraw
        intro a ha hb
        exact (List.nodup_append.mp hraw).2.2 a ha a hb rfl
      -- remaining' = (rest.map fst).flatten
      have hrem'_eq : remaining' = (rest.map Prod.fst).flatten := by
        rw [hrem'_def, hπi_eq_seg, hsegs_eq, List.map_cons, List.flatten_cons,
          List.filter_append]
        have h_seg0_part :
            seg0.1.filter (fun (w : Nat × Bool) =>
              !seg0.1.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ⟨w, b⟩ hwb
          simp only [Bool.not_eq_true', Bool.not_eq_false]
          rw [List.any_eq_true]
          exact ⟨(w, b), hwb, by simp⟩
        have h_rest_part :
            ((rest.map Prod.fst).flatten).filter (fun (w : Nat × Bool) =>
              !seg0.1.any (fun (w' : Nat × Bool) => w'.1 == w.1)) =
            (rest.map Prod.fst).flatten := by
          apply List.filter_eq_self.mpr
          intro ⟨w, b⟩ hwb
          simp only [Bool.not_eq_true']
          rw [List.any_eq_false]
          intro ⟨z, bz⟩ hz_seg0
          simp only [beq_iff_eq]; intro heq
          have hz_fst : z ∈ seg0.1.map Prod.fst :=
            List.mem_map.mpr ⟨(z, bz), hz_seg0, rfl⟩
          have hw_fst : w ∈ ((rest.map Prod.fst).flatten).map Prod.fst :=
            List.mem_map.mpr ⟨(w, b), hwb, rfl⟩
          rw [heq] at hz_fst
          exact hnodup_split hz_fst hw_fst
        rw [h_seg0_part, h_rest_part]
        simp
      have hnodup_rem' : (remaining'.map Prod.fst).Nodup :=
        List.Pairwise.sublist (List.filter_sublist.map _) hnodup_rem
      have hπi_disj_ρ : ∀ x ∈ πI, (asgn.any fun (z, _) => z == x.1) = false := by
        intro x hx
        exact hdisj_ρ x.1 x.2 (List.mem_of_mem_filter hx)
      have hdisj_ρ' : ∀ w b, (w, b) ∈ remaining' →
          (ρ'.any fun (z, _) => z == w) = false := by
        intro w b hw_rem'
        have hw_rπ : (w, b) ∈ rem := List.mem_of_mem_filter hw_rem'
        have hρ_none := hdisj_ρ w b hw_rπ
        show (combineRestrictions asgn πI).any (fun (z, _) => z == w) = false
        rw [combineRestrictions, List.any_append, hρ_none, Bool.false_or]
        rw [List.any_eq_false]
        intro ⟨z, bz⟩ hz_filt
        simp only [beq_iff_eq]; intro heq
        have hz_πi := List.mem_of_mem_filter hz_filt
        have hw_in_πi : πI.any (fun (w', _) => w' == w) = true := by
          rw [List.any_eq_true]
          exact ⟨(z, bz), hz_πi, by simp [heq]⟩
        have hw_nc := (List.mem_filter.mp hw_rem').2
        simp only [Bool.not_eq_true'] at hw_nc
        exact absurd hw_in_πi (by rw [hw_nc]; exact Bool.false_ne_true)
      -- ── Step 5: Build h_align' for rest by index-shifting ──
      have h_align' : ∀ (j : Nat) (hj : j < rest.length),
          restrictionOfFirstTermNotKilledByList clauses
            (combineRestrictions ρ' (((rest.take j).map Prod.fst).flatten)) =
            (rest[j]'hj).2 ∧
          (remaining'.filter (fun (w : Nat × Bool) =>
            !(((rest.take j).map Prod.fst).flatten).any
              (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
            (fun x => ((restrictionOfFirstTermNotKilledByList clauses
              (combineRestrictions ρ'
                (((rest.take j).map Prod.fst).flatten))).map
              Prod.fst).contains x.1) =
            (rest[j]'hj).1 := by
        intro j hj
        have hj1 : j + 1 < (seg0 :: rest).length := by simp; omega
        have h_outer := h_align (j + 1) hj1
        set inner := ((rest.take j).map Prod.fst).flatten with h_inner_def
        have h_take_succ : (seg0 :: rest).take (j + 1) = seg0 :: rest.take j := by
          rfl
        have h_consumed_eq : (((seg0 :: rest).take (j + 1)).map Prod.fst).flatten =
            seg0.1 ++ inner := by
          rw [h_take_succ]; simp [h_inner_def]
        have h_inner_sub_rest : ∀ x ∈ inner, x ∈ (rest.map Prod.fst).flatten := by
          intro x hx
          rw [h_inner_def, List.mem_flatten] at hx
          obtain ⟨l, hl_in, hx_in_l⟩ := hx
          rw [List.mem_map] at hl_in
          obtain ⟨seg, hseg_in, rfl⟩ := hl_in
          rw [List.mem_flatten]
          exact ⟨seg.1,
            List.mem_map.mpr ⟨seg, List.mem_of_mem_take hseg_in, rfl⟩, hx_in_l⟩
        have h_inner_disj_seg0 : ∀ x ∈ inner,
            (seg0.1.any fun (z, _) => z == x.1) = false := by
          intro x hx
          have hx_rest := h_inner_sub_rest x hx
          rw [List.any_eq_false]
          intro ⟨z, bz⟩ hz_seg0
          simp only [beq_iff_eq]; intro heq
          have hz_fst : z ∈ seg0.1.map Prod.fst :=
            List.mem_map.mpr ⟨(z, bz), hz_seg0, rfl⟩
          have hx_fst : x.1 ∈ ((rest.map Prod.fst).flatten).map Prod.fst :=
            List.mem_map.mpr ⟨x, hx_rest, rfl⟩
          rw [heq] at hz_fst
          exact hnodup_split hz_fst hx_fst
        have h_inner_disj_πi : ∀ x ∈ inner,
            (πI.any fun (z, _) => z == x.1) = false := by
          intro x hx
          rw [hπi_eq_seg]; exact h_inner_disj_seg0 x hx
        have h_inner_disj_asgn : ∀ x ∈ inner,
            (asgn.any fun (z, _) => z == x.1) = false := by
          intro x hx
          have hx_rest := h_inner_sub_rest x hx
          have : x ∈ rem := by
            rw [hsegs_eq, List.map_cons, List.flatten_cons]
            exact List.mem_append_right _ hx_rest
          exact hdisj_ρ x.1 x.2 this
        have h_seg0_disj_asgn : ∀ x ∈ seg0.1,
            (asgn.any fun (z, _) => z == x.1) = false := by
          intro x hx
          have : x ∈ rem := by
            rw [hsegs_eq, List.map_cons, List.flatten_cons]
            exact List.mem_append_left _ hx
          exact hdisj_ρ x.1 x.2 this
        have h_πi_disj_asgn : ∀ x ∈ πI,
            (asgn.any fun (z, _) => z == x.1) = false := by
          intro x hx; rw [hπi_eq_seg] at hx; exact h_seg0_disj_asgn x hx
        have h_combined_split : combineRestrictions asgn (seg0.1 ++ inner) =
            combineRestrictions ρ' inner := by
          rw [hρ'_def, ← hπi_eq_seg]
          rw [combineRestrictions_append_eq_nested asgn πI inner h_πi_disj_asgn h_inner_disj_asgn
            h_inner_disj_πi]
        rw [h_consumed_eq, h_combined_split] at h_outer
        have h_idx_eq : (seg0 :: rest)[j + 1]'hj1 = rest[j]'hj := by
          simp [List.getElem_cons_succ]
        rw [h_idx_eq] at h_outer
        have h_filt_eq : rem.filter (fun (w : Nat × Bool) =>
            !(seg0.1 ++ inner).any (fun (w' : Nat × Bool) => w'.1 == w.1)) =
            remaining'.filter (fun (w : Nat × Bool) =>
              !inner.any (fun (w' : Nat × Bool) => w'.1 == w.1)) := by
          rw [hrem'_eq, hsegs_eq, List.map_cons, List.flatten_cons,
            List.filter_append]
          have h_seg0_zero : seg0.1.filter (fun (w : Nat × Bool) =>
              !(seg0.1 ++ inner).any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro ⟨w, b⟩ hwb
            simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_append,
              Bool.or_eq_true]
            left
            rw [List.any_eq_true]
            exact ⟨(w, b), hwb, by simp⟩
          have h_rest_drop : ((rest.map Prod.fst).flatten).filter
              (fun (w : Nat × Bool) =>
                !(seg0.1 ++ inner).any (fun (w' : Nat × Bool) => w'.1 == w.1)) =
              ((rest.map Prod.fst).flatten).filter
                (fun (w : Nat × Bool) =>
                  !inner.any (fun (w' : Nat × Bool) => w'.1 == w.1)) := by
            apply List.filter_congr
            intro ⟨w, b⟩ hwb
            simp only [List.any_append, Bool.not_or]
            have h_seg0_no : seg0.1.any (fun (w', _) => w' == w) = false := by
              rw [List.any_eq_false]
              intro ⟨z, bz⟩ hz_seg0
              simp only [beq_iff_eq]; intro heq
              have hz_fst : z ∈ seg0.1.map Prod.fst :=
                List.mem_map.mpr ⟨(z, bz), hz_seg0, rfl⟩
              have hw_fst : w ∈ ((rest.map Prod.fst).flatten).map Prod.fst :=
                List.mem_map.mpr ⟨(w, b), hwb, rfl⟩
              rw [heq] at hz_fst
              exact hnodup_split hz_fst hw_fst
            rw [h_seg0_no]
            simp
          rw [h_seg0_zero, h_rest_drop]
          simp
        rw [h_filt_eq] at h_outer
        exact h_outer
      -- ── Step 6: Apply IH ──
      have hsegs_align' : ∀ p ∈ rest, p.1.length ≤ p.2.length :=
        fun p hp => hsegs_align p (List.mem_cons_of_mem _ hp)
      have hsegs_align_fst' : ∀ p ∈ rest,
          p.1.map Prod.fst = (p.2.map Prod.fst).take p.1.length :=
        fun p hp => hsegs_align_fst p (List.mem_cons_of_mem _ hp)
      have h_seg_nonempty' : ∀ p ∈ rest, p.1 ≠ [] :=
        fun p hp => h_seg_nonempty p (List.mem_cons_of_mem _ hp)
      exact ih ρ' remaining' fuel' hrem'_eq hnodup_rem' hdisj_ρ'
        hsegs_align' hsegs_align_fst' h_seg_nonempty' h_align'

#print axioms encoder_nodup_trace_of_segments

/-- Dead variables from the encoder have nodup on first components.
    The proof follows the canonical path's segment decomposition. -/
private lemma encoder_dead_nodup_fst
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool))
    (hnodup_asgn : (asgn.map Prod.fst).Nodup)
    (d : Nat)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path) :
    ((encodeRestrictionFromFormula d f.val asgn).1.map Prod.fst).Nodup := by
  -- ── Pull in killed-heads-covered iter-split of `path`. ──────────────────
  have hp_isin :
      IsPathIn (canonicalDecisionTree f.val asgn) path :=
    leftmostPathExceedingDepth_isPathIn _ _ _ hpath
  have hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val),
        (c.map Prod.fst).Nodup :=
    restrictDNF_preserves_clause_nodup f.val
      (restrictionAsFunction asgn) hnodup
  obtain ⟨_segments_full, _hpath_eq, _hlen, _hcov, _hheads, _hnd_seg, _hkill,
            _hkilled_covered, _hcum_a⟩ :=
    cdt_full_query_killed_heads_covered_by_prefix f asgn hnodup_restricted
      path hp_isin
  simp only [encodeRestrictionFromFormula]
  rw [hpath]
  set π := path.take d
  -- asgn has nodup and asgn vars are in asgn (tautology for self-any)
  have hasgn_in_asgn : ∀ w ∈ asgn.map Prod.fst,
      (asgn.any fun (w', _) => w' == w) = true := by
    intro w hw
    rw [List.any_eq_true]
    obtain ⟨⟨v, b⟩, hv, rfl⟩ := List.mem_map.mp hw
    exact ⟨(v, b), hv, by simp⟩
  -- Path vars nodup
  have hnodup_fst : (π.map Prod.fst).Nodup :=
    canonical_dt_path_take_nodup_fst f.val asgn hnodup d path hpath
  -- Path vars are unassigned by asgn
  have hdisj_ρ : ∀ w b, (w, b) ∈ π →
      (asgn.any fun (z, _) => z == w) = false := by
    intro w b hw
    rw [list_any_eq_cr_none_isSome,
        canonical_dt_path_var_none f.val asgn f.property.2 d path hpath
          w b (List.mem_of_mem_take hw)]
    rfl
  -- ── Per-step trace via segment alignment. ──
  -- Get full segments of `path` from `encoder_roftnkb_eq_segment_head`,
  -- truncate them to depth d via `path_take_segments_truncate`, then feed
  -- the truncated bridge into `encoder_nodup_trace_of_segments`.
  obtain ⟨segs_full, hsf_path, hsf_align, _hsf_heads, hsf_ne, hsf_roftnkb⟩ :=
    encoder_roftnkb_eq_segment_head f hnodup asgn d path hpath
  obtain ⟨trunc, _k, _hk_le, _htrunc_len, htrunc_path, htrunc_align,
          htrunc_ne, _hk_le_t, _ht_le_k1, htrunc_bridge⟩ :=
    path_take_segments_truncate path d segs_full hsf_path hsf_align hsf_ne
  -- Per-segment fst alignment for trunc: prefix + length-le ⇒ take-equal.
  have htrunc_align_fst : ∀ p ∈ trunc,
      p.1.map Prod.fst = (p.2.map Prod.fst).take p.1.length := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
    obtain ⟨hj_full, _hcum, hidx2_eq, hidx1_pref⟩ := htrunc_bridge j hj
    have hsf_align_j := hsf_align (segs_full[j]'hj_full) (List.getElem_mem _)
    have hpref_fst : ((trunc[j]'hj).1.map Prod.fst) <+:
        ((segs_full[j]'hj_full).1.map Prod.fst) :=
      hidx1_pref.map _
    have hpref_fst' : ((trunc[j]'hj).1.map Prod.fst) <+:
        ((trunc[j]'hj).2.map Prod.fst) := by
      rw [hidx2_eq]; rw [hsf_align_j] at hpref_fst; exact hpref_fst
    rw [← hpj]
    rw [List.prefix_iff_eq_take.mp hpref_fst', List.length_map]
  -- Per-segment bridge for trunc, derived from segs_full's bridge.
  have htrunc_h_align : ∀ (j : Nat) (hj : j < trunc.length),
      restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions asgn (((trunc.take j).map Prod.fst).flatten)) =
        (trunc[j]'hj).2 ∧
      (π.filter (fun (w : Nat × Bool) =>
        !(((trunc.take j).map Prod.fst).flatten).any
          (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
        (fun x => ((restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions asgn
            (((trunc.take j).map Prod.fst).flatten))).map
          Prod.fst).contains x.1) =
        (trunc[j]'hj).1 := by
    intro j hj
    obtain ⟨hj_full, hcum_eq, hidx2_eq, hidx1_pref⟩ := htrunc_bridge j hj
    have h_first :
        restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions asgn
            (((trunc.take j).map Prod.fst).flatten)) =
          (trunc[j]'hj).2 := by
      rw [hcum_eq, hidx2_eq]
      exact hsf_roftnkb j hj_full
    refine ⟨h_first, ?_⟩
    rw [h_first]
    -- It remains to identify the doubly filtered path with `trunc[j].1`.
    -- Decompose π = cum_j ++ rest_j using htrunc_path; then case-split on
    -- whether j is a "full" slot or the partial-tail slot.
    -- π.fst nodup
    have hπ_nodup_fst : (π.map Prod.fst).Nodup :=
      canonical_dt_path_take_nodup_fst f.val asgn hnodup d path hpath
    set cum_j := ((trunc.take j).map Prod.fst).flatten with hcumj_def
    set rest_j := ((trunc.drop j).map Prod.fst).flatten with hrest_def
    have hπ_split : π = cum_j ++ rest_j := by
      show path.take d = _
      rw [htrunc_path, hcumj_def, hrest_def]
      rw [show (List.map Prod.fst (List.take j trunc)).flatten ++
              (List.map Prod.fst (List.drop j trunc)).flatten =
            (List.map Prod.fst (List.take j trunc) ++
              List.map Prod.fst (List.drop j trunc)).flatten from
              List.flatten_append.symm,
          ← List.map_append, List.take_append_drop]
    have hcum_rest_nd : ((cum_j.map Prod.fst) ++ (rest_j.map Prod.fst)).Nodup := by
      have h := hπ_nodup_fst
      rw [hπ_split, List.map_append] at h; exact h
    have hcum_rest_disj : ∀ a ∈ cum_j.map Prod.fst,
        ∀ b ∈ rest_j.map Prod.fst, a ≠ b :=
      (List.nodup_append.mp hcum_rest_nd).2.2
    -- Filter (∉ cum_j) on π yields rest_j.
    have hfilter_not_cum : π.filter (fun (w : Nat × Bool) =>
        !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = rest_j := by
      rw [hπ_split, List.filter_append]
      have h_cum_drop : cum_j.filter (fun (w : Nat × Bool) =>
          !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro w hw _
        have : cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1) = true := by
          rw [List.any_eq_true]; exact ⟨w, hw, by simp⟩
        simp [this] at *
      have h_rest_keep : rest_j.filter (fun (w : Nat × Bool) =>
          !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = rest_j := by
        apply List.filter_eq_self.mpr
        intro w hw
        simp only [Bool.not_eq_true']
        rw [List.any_eq_false]
        intro ⟨z, bz⟩ hz_cum
        simp only [beq_iff_eq]; intro heq
        have hz_fst : z ∈ cum_j.map Prod.fst :=
          List.mem_map.mpr ⟨(z, bz), hz_cum, rfl⟩
        have hw_fst : w.1 ∈ rest_j.map Prod.fst :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact hcum_rest_disj z hz_fst w.1 hw_fst heq
      rw [h_cum_drop, h_rest_keep, List.nil_append]
    rw [hfilter_not_cum]
    -- rest_j = trunc[j].1 ++ tail_j.
    set tail_j := ((trunc.drop (j+1)).map Prod.fst).flatten with htail_def
    have hrest_split : rest_j = (trunc[j]'hj).1 ++ tail_j := by
      rw [hrest_def, htail_def]
      have h_drop_succ : trunc.drop j = (trunc[j]'hj) :: trunc.drop (j+1) := by
        rw [← List.getElem_cons_drop hj]
      rw [h_drop_succ, List.map_cons, List.flatten_cons]
    -- Now: trunc[j].2.fst = segs_full[j].2.fst = segs_full[j].1.fst (alignment).
    -- trunc[j].1.fst <+: segs_full[j].1.fst (prefix) — but trunc[j].1's vars ARE
    -- in trunc[j].2.fst (since prefix), and the OTHER segments' vars are NOT in
    -- trunc[j].2.fst (= segs_full[j].2.fst), by Nodup of path.fst combined with
    -- the fact that segs_full[j].1.fst = segs_full[j].2.fst lies in path.fst.
    --
    -- We rely on hsf_align_j to relate trunc[j].2.fst to segs_full[j].1.fst.
    have hsf_align_j := hsf_align (segs_full[j]'hj_full) (List.getElem_mem _)
    have htrunc2_fst_eq : (trunc[j]'hj).2.map Prod.fst =
        (segs_full[j]'hj_full).1.map Prod.fst := by
      rw [hidx2_eq]; exact hsf_align_j.symm
    -- segs_full[j].1 ⊆ path (because segs_full tiles path).
    have hsegfull_sub_path : ∀ x ∈ (segs_full[j]'hj_full).1, x ∈ path := by
      intro x hx
      rw [hsf_path]
      rw [List.mem_flatten]
      refine ⟨(segs_full[j]'hj_full).1, ?_, hx⟩
      rw [List.mem_map]
      exact ⟨segs_full[j]'hj_full, List.getElem_mem _, rfl⟩
    -- trunc[j].1 ⊆ rest_j ⊆ π ⊆ path (so trunc[j].1.fst ⊆ path.fst, used for nodup).
    have htrunc1_sub_π : ∀ x ∈ (trunc[j]'hj).1, x ∈ π := by
      intro x hx
      rw [hπ_split]
      apply List.mem_append_right
      rw [hrest_split]
      exact List.mem_append_left _ hx
    -- tail_j vars are NOT in trunc[j].2.fst.
    -- Reason: tail_j ⊆ rest_j ⊆ π, and rest_j.fst.Nodup gives trunc[j].1.fst
    -- disjoint from tail_j.fst. But trunc[j].2.fst = segs_full[j].1.fst, which
    -- *might* share vars with later segs of segs_full — no, segs_full tiles
    -- path with .1.fst's all distinct (path.fst nodup, segs_full[j].1.fst <+:
    -- path.fst's chunk j). So trunc[j].2.fst (= segs_full[j].1.fst) is
    -- disjoint from segs_full[k].1.fst for k > j; but tail_j may include
    -- partial of segs_full[k].1, still disjoint.
    have hrest_nodup : (rest_j.map Prod.fst).Nodup :=
      (List.nodup_append.mp hcum_rest_nd).2.1
    have hsplit_nd : ((trunc[j]'hj).1.map Prod.fst ++ tail_j.map Prod.fst).Nodup := by
      have := hrest_nodup; rw [hrest_split, List.map_append] at this; exact this
    -- It remains to show that `tail_j` is variable-disjoint from `trunc[j].2`.
    -- trunc[j].2.fst = segs_full[j].1.fst. tail_j ⊆ trunc.drop(j+1).flatten.
    -- All trunc.drop(j+1) entries' .1's are in segs_full[k].1 for some k > j.
    -- Path nodup ⇒ segs_full[j].1.fst disjoint from segs_full[k].1.fst (k > j).
    -- Hence disjoint from `tail_j.fst`.
    have htail_disj_t2 : ∀ x ∈ tail_j,
        ((trunc[j]'hj).2.map Prod.fst).contains x.1 = false := by
      intro x hx_tail
      by_contra hcontra
      rw [Bool.not_eq_false] at hcontra
      rw [List.contains_iff_mem, htrunc2_fst_eq] at hcontra
      obtain ⟨y, hy_seg, hy_eq⟩ := List.mem_map.mp hcontra
      -- Locate x in tail_j: tail_j = ((trunc.drop (j+1)).map fst).flatten
      rw [htail_def, List.mem_flatten] at hx_tail
      obtain ⟨xs, hxs_in, hx_in_xs⟩ := hx_tail
      rw [List.mem_map] at hxs_in
      obtain ⟨seg_i, hsegi_drop, hxs_eq⟩ := hxs_in
      -- seg_i = trunc[j+1+idx] for some idx
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hsegi_drop
      rw [List.length_drop] at hidx_lt
      have hi_idx : j + 1 + idx < trunc.length := by omega
      have hsegi_at : seg_i = trunc[j + 1 + idx]'hi_idx := by
        rw [← hidx_eq, List.getElem_drop]
      obtain ⟨hi_full, _, _, hi_idx1_pref⟩ := htrunc_bridge (j+1+idx) hi_idx
      -- x ∈ segs_full[j+1+idx].1 (via prefix)
      have hx_in_segi_full : x ∈ (segs_full[j+1+idx]'hi_full).1 := by
        have hx_in_seg_i_1 : x ∈ seg_i.1 := hxs_eq ▸ hx_in_xs
        rw [hsegi_at] at hx_in_seg_i_1
        exact hi_idx1_pref.subset hx_in_seg_i_1
      -- path.fst.Nodup ⇒ pairwise disjoint segments via flatten
      have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
        canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
      have hflat_eq : path.map Prod.fst =
          (segs_full.map (fun p => p.1.map Prod.fst)).flatten := by
        rw [hsf_path, List.map_flatten, List.map_map]
        rfl
      have hpath_nodup_fst' :
          ((segs_full.map (fun p => p.1.map Prod.fst)).flatten).Nodup := by
        rw [← hflat_eq]; exact hpath_nodup_fst
      obtain ⟨_, hpw⟩ := List.nodup_flatten.mp hpath_nodup_fst'
      rw [List.pairwise_map] at hpw
      have hjlt : j < j + 1 + idx := by omega
      have hdisj := List.pairwise_iff_getElem.mp hpw j (j+1+idx) hj_full hi_full hjlt
      have hy_fst : y.1 ∈ (segs_full[j]'hj_full).1.map Prod.fst :=
        List.mem_map.mpr ⟨y, hy_seg, rfl⟩
      have hx_fst : x.1 ∈ (segs_full[j+1+idx]'hi_full).1.map Prod.fst :=
        List.mem_map.mpr ⟨x, hx_in_segi_full, rfl⟩
      rw [hy_eq] at hy_fst
      exact hdisj hy_fst hx_fst
    have htrunc1_in_t2 : ∀ x ∈ (trunc[j]'hj).1,
        ((trunc[j]'hj).2.map Prod.fst).contains x.1 = true := by
      intro x hx
      have h_align_fst := htrunc_align_fst (trunc[j]'hj) (List.getElem_mem _)
      have hx_fst : x.1 ∈ (trunc[j]'hj).1.map Prod.fst :=
        List.mem_map.mpr ⟨x, hx, rfl⟩
      rw [h_align_fst] at hx_fst
      rw [List.contains_iff_mem]
      exact List.mem_of_mem_take hx_fst
    rw [hrest_split, List.filter_append]
    have h_trunc1_keep : (trunc[j]'hj).1.filter
        (fun x => ((trunc[j]'hj).2.map Prod.fst).contains x.1) =
        (trunc[j]'hj).1 := by
      apply List.filter_eq_self.mpr
      exact htrunc1_in_t2
    have h_tail_drop : tail_j.filter
        (fun x => ((trunc[j]'hj).2.map Prod.fst).contains x.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx h_pos
      have := htail_disj_t2 x hx
      rw [this] at h_pos
      exact Bool.false_ne_true h_pos
    rw [h_trunc1_keep, h_tail_drop, List.append_nil]
  have h_trace : EncoderNodupTrace (dnfClauses f.val) π.length asgn π := by
    have hrem_eq : π = (trunc.map Prod.fst).flatten := htrunc_path
    have hnodup_π : (π.map Prod.fst).Nodup :=
      canonical_dt_path_take_nodup_fst f.val asgn hnodup d path hpath
    exact encoder_nodup_trace_of_segments (dnfClauses f.val) trunc asgn π
      π.length hrem_eq hnodup_π hdisj_ρ htrunc_align htrunc_align_fst htrunc_ne
      htrunc_h_align
  exact encoder_aux_dead_nodup_fst π.length π f.val asgn asgn
    hnodup hnodup_asgn hasgn_in_asgn
    hnodup_fst hdisj_ρ h_trace

#print axioms encoder_dead_nodup_fst

/-- **Aux: encoder dead vars are bounded by `dead_acc ∪ remaining_π`** (trace form).

    Given the same `EncoderNodupTrace` invariant used by
    `encoder_aux_dead_nodup_fst`, every fst-projection of a dead var produced
    by `beameEncoderAux` is either already in `dead_acc.fst`
    or in `remaining_π.fst`.  Direct induction on fuel: at each step the
    encoder appends `γ_i = take πI.length (gammaBitsForClause U_i)`,
    whose fst-projection equals `πI.fst ⊆ remaining_π.fst` by the trace. -/
private lemma encoder_aux_dead_fst_subset
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (h_trace : EncoderNodupTrace (dnfClauses dnf) fuel ρ remaining_π) :
    ∀ w ∈ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1.map Prod.fst,
      w ∈ dead_acc.map Prod.fst ∨ w ∈ remaining_π.map Prod.fst := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero =>
    intro w hw
    simp only [beameEncoderAux] at hw
    exact Or.inl hw
  | succ n ih =>
    obtain ⟨hπi_fst_take, _hπi_len_le, h_trace_next⟩ := h_trace
    intro w hw
    simp only [beameEncoderAux] at hw
    split at hw
    · exact Or.inl hw
    · set clauses := dnfClauses dnf
      set U_i := restrictionOfFirstTermNotKilledByList clauses ρ
      set U_vars := U_i.map Prod.fst
      set p_fn : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
      set πI := remaining_π.filter p_fn
      set γ_i := (gammaBitsForClause U_i).take πI.length
      set dead_acc' := dead_acc ++ γ_i
      set ρ' := combineRestrictions ρ πI
      set remaining' := remaining_π.filter fun (w, _) => !πI.any fun (w', _) => w' == w
      have hγ_fst : γ_i.map Prod.fst = πI.map Prod.fst := by
        show ((gammaBitsForClause U_i).take πI.length).map Prod.fst =
          πI.map Prod.fst
        rw [List.map_take, gamma_bits_map_fst_eq]
        exact hπi_fst_take.symm
      -- Helper: γ_i.fst membership ⇒ remaining_π.fst membership.
      have hγ_sub_rem : ∀ w ∈ γ_i.map Prod.fst, w ∈ remaining_π.map Prod.fst := by
        intro w hw
        rw [hγ_fst] at hw
        obtain ⟨⟨w', b'⟩, hw'_πi, hw'_eq⟩ := List.mem_map.mp hw
        exact List.mem_map.mpr ⟨(w', b'), List.mem_of_mem_filter hw'_πi, hw'_eq⟩
      split at hw
      · -- πI.length = 0 branch: encoder returns dead_acc'.
        rw [List.map_append, List.mem_append] at hw
        cases hw with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (hγ_sub_rem w h)
      · -- Recursive branch.
        have ih_res := ih remaining' ρ' dead_acc' h_trace_next w hw
        cases ih_res with
        | inl h_in_dead' =>
          rw [show dead_acc' = dead_acc ++ γ_i from rfl, List.map_append,
              List.mem_append] at h_in_dead'
          cases h_in_dead' with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (hγ_sub_rem w h)
        | inr h_in_rem' =>
          obtain ⟨⟨w', b'⟩, hw'_rem, hw'_eq⟩ := List.mem_map.mp h_in_rem'
          exact Or.inr (List.mem_map.mpr
            ⟨(w', b'), List.mem_of_mem_filter hw'_rem, hw'_eq⟩)

/-- **Encoder dead vars (newly killed) lie in `path.take d`.**

    Wrapper for `encoder_aux_dead_fst_subset`: at the encoder's seed
    instance (`ρ = dead_acc = asgn`, `remaining_π = path.take d`), every
    var `w` in the encoder's dead-vars output that is **not** one of the
    seeded `asgn` variables (`hw_asgn`) lies in `path.take d`.

    Reuses the segment-alignment trace built inside `encoder_dead_nodup_fst`. -/
private lemma encoder_dead_vars_subset_path
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool))
    (_hnodup_asgn : (asgn.map Prod.fst).Nodup)
    (d : Nat)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (w : Nat)
    (hw_asgn : (asgn.any fun (z, _) => z == w) = false)
    (hw : w ∈ (encodeRestrictionFromFormula d f.val asgn).1.map Prod.fst) :
    w ∈ (path.take d).map Prod.fst := by
  -- Use the trace-builder logic implicitly by routing through nodup_fst's
  -- precondition machinery.  We reuse `encoder_nodup_trace_of_segments` on
  -- the same `trunc` produced by `path_take_segments_truncate`.
  simp only [encodeRestrictionFromFormula] at hw
  rw [hpath] at hw
  set π := path.take d with hπ_def
  -- Path vars are unassigned by asgn (used to feed the trace).
  have hdisj_ρ : ∀ w b, (w, b) ∈ π →
      (asgn.any fun (z, _) => z == w) = false := by
    intro w b hw_π
    rw [list_any_eq_cr_none_isSome,
        canonical_dt_path_var_none f.val asgn f.property.2 d path hpath
          w b (List.mem_of_mem_take hw_π)]
    rfl
  -- Build the trace via the same segment-alignment construction as
  -- `encoder_dead_nodup_fst`.
  obtain ⟨segs_full, hsf_path, hsf_align, _hsf_heads, hsf_ne, hsf_roftnkb⟩ :=
    encoder_roftnkb_eq_segment_head f hnodup asgn d path hpath
  obtain ⟨trunc, _k, _hk_le, _htrunc_len, htrunc_path, htrunc_align,
          htrunc_ne, _hk_le_t, _ht_le_k1, htrunc_bridge⟩ :=
    path_take_segments_truncate path d segs_full hsf_path hsf_align hsf_ne
  -- Per-segment fst alignment for trunc: prefix + length-le ⇒ take-equal.
  have htrunc_align_fst : ∀ p ∈ trunc,
      p.1.map Prod.fst = (p.2.map Prod.fst).take p.1.length := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
    obtain ⟨hj_full, _hcum, hidx2_eq, hidx1_pref⟩ := htrunc_bridge j hj
    have hsf_align_j := hsf_align (segs_full[j]'hj_full) (List.getElem_mem _)
    have hpref_fst : ((trunc[j]'hj).1.map Prod.fst) <+:
        ((segs_full[j]'hj_full).1.map Prod.fst) :=
      hidx1_pref.map _
    have hpref_fst' : ((trunc[j]'hj).1.map Prod.fst) <+:
        ((trunc[j]'hj).2.map Prod.fst) := by
      rw [hidx2_eq]; rw [hsf_align_j] at hpref_fst; exact hpref_fst
    rw [← hpj]
    rw [List.prefix_iff_eq_take.mp hpref_fst', List.length_map]
  have hnodup_π : (π.map Prod.fst).Nodup :=
    canonical_dt_path_take_nodup_fst f.val asgn hnodup d path hpath
  -- Per-segment bridge for trunc, derived from segs_full's bridge.
  -- (This is the ~150 LOC `htrunc_h_align` block from `encoder_dead_nodup_fst`.)
  have htrunc_h_align : ∀ (j : Nat) (hj : j < trunc.length),
      restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions asgn (((trunc.take j).map Prod.fst).flatten)) =
        (trunc[j]'hj).2 ∧
      (π.filter (fun (w : Nat × Bool) =>
        !(((trunc.take j).map Prod.fst).flatten).any
          (fun (w' : Nat × Bool) => w'.1 == w.1))).filter
        (fun x => ((restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions asgn
            (((trunc.take j).map Prod.fst).flatten))).map
          Prod.fst).contains x.1) =
        (trunc[j]'hj).1 := by
    intro j hj
    obtain ⟨hj_full, hcum_eq, hidx2_eq, hidx1_pref⟩ := htrunc_bridge j hj
    have h_first :
        restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions asgn
            (((trunc.take j).map Prod.fst).flatten)) =
          (trunc[j]'hj).2 := by
      rw [hcum_eq, hidx2_eq]
      exact hsf_roftnkb j hj_full
    refine ⟨h_first, ?_⟩
    rw [h_first]
    set cum_j := ((trunc.take j).map Prod.fst).flatten with hcumj_def
    set rest_j := ((trunc.drop j).map Prod.fst).flatten with hrest_def
    have hπ_split : π = cum_j ++ rest_j := by
      show path.take d = _
      rw [htrunc_path, hcumj_def, hrest_def]
      rw [show (List.map Prod.fst (List.take j trunc)).flatten ++
              (List.map Prod.fst (List.drop j trunc)).flatten =
            (List.map Prod.fst (List.take j trunc) ++
              List.map Prod.fst (List.drop j trunc)).flatten from
              List.flatten_append.symm,
          ← List.map_append, List.take_append_drop]
    have hcum_rest_nd : ((cum_j.map Prod.fst) ++ (rest_j.map Prod.fst)).Nodup := by
      have h := hnodup_π
      rw [hπ_split, List.map_append] at h; exact h
    have hcum_rest_disj : ∀ a ∈ cum_j.map Prod.fst,
        ∀ b ∈ rest_j.map Prod.fst, a ≠ b :=
      (List.nodup_append.mp hcum_rest_nd).2.2
    have hfilter_not_cum : π.filter (fun (w : Nat × Bool) =>
        !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = rest_j := by
      rw [hπ_split, List.filter_append]
      have h_cum_drop : cum_j.filter (fun (w : Nat × Bool) =>
          !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro w hw _
        have : cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1) = true := by
          rw [List.any_eq_true]; exact ⟨w, hw, by simp⟩
        simp [this] at *
      have h_rest_keep : rest_j.filter (fun (w : Nat × Bool) =>
          !cum_j.any (fun (w' : Nat × Bool) => w'.1 == w.1)) = rest_j := by
        apply List.filter_eq_self.mpr
        intro w hw
        simp only [Bool.not_eq_true']
        rw [List.any_eq_false]
        intro ⟨z, bz⟩ hz_cum
        simp only [beq_iff_eq]; intro heq
        have hz_fst : z ∈ cum_j.map Prod.fst :=
          List.mem_map.mpr ⟨(z, bz), hz_cum, rfl⟩
        have hw_fst : w.1 ∈ rest_j.map Prod.fst :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        exact hcum_rest_disj z hz_fst w.1 hw_fst heq
      rw [h_cum_drop, h_rest_keep, List.nil_append]
    rw [hfilter_not_cum]
    set tail_j := ((trunc.drop (j+1)).map Prod.fst).flatten with htail_def
    have hrest_split : rest_j = (trunc[j]'hj).1 ++ tail_j := by
      rw [hrest_def, htail_def]
      have h_drop_succ : trunc.drop j = (trunc[j]'hj) :: trunc.drop (j+1) := by
        rw [← List.getElem_cons_drop hj]
      rw [h_drop_succ, List.map_cons, List.flatten_cons]
    have hsf_align_j := hsf_align (segs_full[j]'hj_full) (List.getElem_mem _)
    have htrunc2_fst_eq : (trunc[j]'hj).2.map Prod.fst =
        (segs_full[j]'hj_full).1.map Prod.fst := by
      rw [hidx2_eq]; exact hsf_align_j.symm
    have hrest_nodup : (rest_j.map Prod.fst).Nodup :=
      (List.nodup_append.mp hcum_rest_nd).2.1
    have _hsplit_nd : ((trunc[j]'hj).1.map Prod.fst ++ tail_j.map Prod.fst).Nodup := by
      have := hrest_nodup; rw [hrest_split, List.map_append] at this; exact this
    have htail_disj_t2 : ∀ x ∈ tail_j,
        ((trunc[j]'hj).2.map Prod.fst).contains x.1 = false := by
      intro x hx_tail
      by_contra hcontra
      rw [Bool.not_eq_false] at hcontra
      rw [List.contains_iff_mem, htrunc2_fst_eq] at hcontra
      obtain ⟨y, hy_seg, hy_eq⟩ := List.mem_map.mp hcontra
      rw [htail_def, List.mem_flatten] at hx_tail
      obtain ⟨xs, hxs_in, hx_in_xs⟩ := hx_tail
      rw [List.mem_map] at hxs_in
      obtain ⟨seg_i, hsegi_drop, hxs_eq⟩ := hxs_in
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hsegi_drop
      rw [List.length_drop] at hidx_lt
      have hi_idx : j + 1 + idx < trunc.length := by omega
      have hsegi_at : seg_i = trunc[j + 1 + idx]'hi_idx := by
        rw [← hidx_eq, List.getElem_drop]
      obtain ⟨hi_full, _, _, hi_idx1_pref⟩ := htrunc_bridge (j+1+idx) hi_idx
      have hx_in_segi_full : x ∈ (segs_full[j+1+idx]'hi_full).1 := by
        have hx_in_seg_i_1 : x ∈ seg_i.1 := hxs_eq ▸ hx_in_xs
        rw [hsegi_at] at hx_in_seg_i_1
        exact hi_idx1_pref.subset hx_in_seg_i_1
      have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
        canonical_dt_path_nodup_fst f.val asgn hnodup d path hpath
      have hflat_eq : path.map Prod.fst =
          (segs_full.map (fun p => p.1.map Prod.fst)).flatten := by
        rw [hsf_path, List.map_flatten, List.map_map]
        rfl
      have hpath_nodup_fst' :
          ((segs_full.map (fun p => p.1.map Prod.fst)).flatten).Nodup := by
        rw [← hflat_eq]; exact hpath_nodup_fst
      obtain ⟨_, hpw⟩ := List.nodup_flatten.mp hpath_nodup_fst'
      rw [List.pairwise_map] at hpw
      have hjlt : j < j + 1 + idx := by omega
      have hdisj := List.pairwise_iff_getElem.mp hpw j (j+1+idx) hj_full hi_full hjlt
      have hy_fst : y.1 ∈ (segs_full[j]'hj_full).1.map Prod.fst :=
        List.mem_map.mpr ⟨y, hy_seg, rfl⟩
      have hx_fst : x.1 ∈ (segs_full[j+1+idx]'hi_full).1.map Prod.fst :=
        List.mem_map.mpr ⟨x, hx_in_segi_full, rfl⟩
      rw [hy_eq] at hy_fst
      exact hdisj hy_fst hx_fst
    have htrunc1_in_t2 : ∀ x ∈ (trunc[j]'hj).1,
        ((trunc[j]'hj).2.map Prod.fst).contains x.1 = true := by
      intro x hx
      have h_align_fst := htrunc_align_fst (trunc[j]'hj) (List.getElem_mem _)
      have hx_fst : x.1 ∈ (trunc[j]'hj).1.map Prod.fst :=
        List.mem_map.mpr ⟨x, hx, rfl⟩
      rw [h_align_fst] at hx_fst
      rw [List.contains_iff_mem]
      exact List.mem_of_mem_take hx_fst
    rw [hrest_split, List.filter_append]
    have h_trunc1_keep : (trunc[j]'hj).1.filter
        (fun x => ((trunc[j]'hj).2.map Prod.fst).contains x.1) =
        (trunc[j]'hj).1 := by
      apply List.filter_eq_self.mpr
      exact htrunc1_in_t2
    have h_tail_drop : tail_j.filter
        (fun x => ((trunc[j]'hj).2.map Prod.fst).contains x.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx h_pos
      have := htail_disj_t2 x hx
      rw [this] at h_pos
      exact Bool.false_ne_true h_pos
    rw [h_trunc1_keep, h_tail_drop, List.append_nil]
  have h_trace : EncoderNodupTrace (dnfClauses f.val) π.length asgn π := by
    have hrem_eq : π = (trunc.map Prod.fst).flatten := htrunc_path
    exact encoder_nodup_trace_of_segments (dnfClauses f.val) trunc asgn π
      π.length hrem_eq hnodup_π hdisj_ρ htrunc_align htrunc_align_fst htrunc_ne
      htrunc_h_align
  -- Apply aux: w ∈ asgn.fst ∨ w ∈ π.fst; rule out asgn via hw_asgn.
  have haux := encoder_aux_dead_fst_subset π.length π f.val asgn asgn h_trace w hw
  cases haux with
  | inl h_in_asgn =>
    exfalso
    obtain ⟨⟨a, ba⟩, ha_mem, rfl⟩ := List.mem_map.mp h_in_asgn
    have : (asgn.any fun (z, _) => z == a) = true := by
      apply List.any_eq_true.mpr
      exact ⟨(a, ba), ha_mem, by simp⟩
    exact Bool.false_ne_true (hw_asgn.symm.trans this)
  | inr h_in_π => exact h_in_π

#print axioms encoder_dead_vars_subset_path


-- ════════════════════════════════════════════════════════════════════════════
-- §  Decoder foldl plumbing
-- ════════════════════════════════════════════════════════════════════════════

/-- Inner step for decoding one position-and-direction pair. -/
private def decoderInnerStep (T : List (Nat × Bool)) :
    (List (Nat × Bool) × List (Nat × Bool)) → (Nat × Bool) →
    (List (Nat × Bool) × List (Nat × Bool)) :=
  fun (B_inner, vars_inner) (pos, π_bit) =>
    let v := (T.getD pos (0, false)).1
    ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner)

/-- Outer step for decoding one encoded chunk. -/
private def decoderOuterStep (clauses : List (List (Nat × Bool))) :
    (List (Nat × Bool) × List (Nat × Bool)) → List (Nat × Bool) →
    (List (Nat × Bool) × List (Nat × Bool)) :=
  fun (B_cur, vars_acc) chunk =>
    let T_i := firstTermNotKilledByList clauses B_cur
    chunk.foldl (decoderInnerStep T_i) (B_cur, vars_acc)

/-- Decoding a well-positioned encoded chunk recovers its entries. -/
private lemma decoder_encoderChunk_decode_eq
    (T : List (Nat × Bool))
    (entries : List (Nat × Bool))
    (h_u : ∀ v d, (v, d) ∈ entries → T.any (fun lit => lit.1 == v) = true) :
    (encoderChunk T entries).map (fun (pos, bit) =>
      ((T.getD pos (0, false)).1, bit)) = entries := by
  induction entries with
  | nil => simp [encoderChunk]
  | cons hd tl ih =>
    obtain ⟨v₀, d₀⟩ := hd
    simp only [encoderChunk, List.map_map, List.map_cons]
    congr 1
    · exact Prod.ext
        (findPositionInClause'_roundtrip T v₀ (h_u v₀ d₀ List.mem_cons_self))
        rfl
    · have ih' := ih (fun v d hm => h_u v d (List.mem_cons_of_mem _ hm))
      simp only [encoderChunk, List.map_map] at ih'
      exact ih'

/-- First component of the inner decoder fold. -/
private lemma decoder_list_inner_foldl_fst_eq
    (T : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    (B : List (Nat × Bool))
    (vars_acc : List (Nat × Bool)) :
    (chunk.foldl (decoderInnerStep T) (B, vars_acc)).1 =
    (chunk.map fun (pos, bit) => ((T.getD pos (0, false)).1, bit)).reverse ++ B := by
  induction chunk generalizing B vars_acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, decoderInnerStep, List.map_cons, List.reverse_cons]
    rw [ih]
    simp [List.append_assoc]

/-- Analog of `decoder_list_inner_foldl_fst_eq` for the `.2` (vars_acc) component. -/
private lemma decoder_list_inner_foldl_snd_eq
    (T : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    (B : List (Nat × Bool))
    (vars_acc : List (Nat × Bool)) :
    (chunk.foldl (decoderInnerStep T) (B, vars_acc)).2 =
    (chunk.map fun (pos, bit) => ((T.getD pos (0, false)).1, bit)).reverse ++ vars_acc := by
  induction chunk generalizing B vars_acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, decoderInnerStep, List.map_cons, List.reverse_cons]
    rw [ih]
    simp [List.append_assoc]

/-- The inner decoder fold preserves entries already in its accumulator. -/
private lemma decoder_list_inner_foldl_acc_mono
    (T : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    (B : List (Nat × Bool))
    (vars_acc : List (Nat × Bool))
    (w : Nat)
    (hw : w ∈ vars_acc.map Prod.fst) :
    w ∈ (chunk.foldl (fun (B_inner, vars_inner) (pos, π_bit) =>
      let v := (T.getD pos (0, false)).1
      ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner)
    ) (B, vars_acc)).2.map Prod.fst := by
  induction chunk generalizing B vars_acc with
  | nil => exact hw
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih _ _ (List.mem_cons.mpr (Or.inr hw))

/-- Every decoded chunk entry appears in the inner fold's output. -/
private lemma decoder_list_inner_foldl_produces
    (T : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    (B : List (Nat × Bool))
    (vars_acc : List (Nat × Bool))
    (pos : Nat) (bit : Bool)
    (hmem : (pos, bit) ∈ chunk) :
    (T.getD pos (0, false)).1 ∈ (chunk.foldl (fun (B_inner, vars_inner) (p, π_bit) =>
      let v := (T.getD p (0, false)).1
      ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner)
    ) (B, vars_acc)).2.map Prod.fst := by
  induction chunk generalizing B vars_acc with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact decoder_list_inner_foldl_acc_mono T tl _ _ _
        (List.mem_cons.mpr (Or.inl rfl))
    · exact ih _ _ htl

/-- Entries in the inner fold output come from the accumulator or decoded chunk. -/
private lemma decoder_list_inner_foldl_subset
    (T : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    (B : List (Nat × Bool))
    (vars_acc : List (Nat × Bool))
    (w : Nat)
    (hw : w ∈ (chunk.foldl (fun (B_inner, vars_inner) (pos, π_bit) =>
      let v := (T.getD pos (0, false)).1
      ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner)) (B, vars_acc)).2.map Prod.fst) :
    w ∈ vars_acc.map Prod.fst ∨
    ∃ (pos : Nat) (bit : Bool), (pos, bit) ∈ chunk ∧
      w = (T.getD pos (0, false)).1 := by
  induction chunk generalizing B vars_acc with
  | nil =>
    simp only [List.foldl_nil] at hw
    exact Or.inl hw
  | cons hd tl ih =>
    have : (hd :: tl).foldl (fun (B_inner, vars_inner) (pos, π_bit) =>
        let v := (T.getD pos (0, false)).1
        ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner))
      (B, vars_acc) =
      tl.foldl (fun (B_inner, vars_inner) (pos, π_bit) =>
        let v := (T.getD pos (0, false)).1
        ((v, π_bit) :: B_inner, (v, π_bit) :: vars_inner))
      (((T.getD hd.1 (0, false)).1, hd.2) :: B,
       ((T.getD hd.1 (0, false)).1, hd.2) :: vars_acc) := by
      simp only [List.foldl_cons]
    rw [this] at hw
    rcases ih _ _ hw with h_acc | ⟨pos, bit, hmem, heq⟩
    · rcases List.mem_cons.mp h_acc with heq' | horig
      · refine Or.inr ⟨hd.1, hd.2, ?_, ?_⟩
        · exact List.mem_cons.mpr (Or.inl (Prod.ext rfl rfl))
        · exact heq'
      · exact Or.inl horig
    · exact Or.inr ⟨pos, bit, List.mem_cons.mpr (Or.inr hmem), heq⟩

/-- Express `beameDecoder` as the reversed outer-fold accumulator. -/
private lemma decoder_eq_foldl_reverse
    (dnf : UnboundedFanInFormula) (B : List (Nat × Bool))
    (chunks : List (List (Nat × Bool))) :
    beameDecoder dnf B chunks =
    (chunks.foldl (decoderOuterStep (dnfClauses dnf))
      (B, [])).2.reverse := by
  simp only [beameDecoder]
  rfl


/- Prefix-preservation step relating the current restriction to the remaining
   canonical-decision-tree path. -/
private lemma ftnkb_prefix_after_consume_encoder_step
    {n : Nat} (f : UnboundedFanInDNF n)
    (ρ : List (Nat × Bool))
    (remaining_π : List (Nat × Bool))
    (πI : List (Nat × Bool))
    (hrem_ne : remaining_π.filter (fun (w, _) =>
      !πI.any (fun (w', _) => w' == w)) ≠ [])
    -- Nonempty restricted head after consuming `πI`.
    (h_r_combined_ne :
      remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w)) ≠ [] →
      restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions ρ πI) ≠ [])
    -- Prefix comparability after consuming `πI`. The reverse direction is
    -- needed in the β-straddler case, where segment
    -- `k_bundle+1` itself straddles depth `d`, so `remaining' = β.take m` is
    -- a strict prefix of the selected clause's variable list, not the other
    -- way around. This mirrors the disjunction in the wrapper's return type.
    (h_r_combined_pref :
      remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w)) ≠ [] →
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions ρ πI)).map Prod.fst
        <+: (remaining_π.filter (fun (w, _) =>
          !πI.any (fun (w', _) => w' == w))).map Prod.fst ∨
      (remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w))).map Prod.fst
        <+: (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions ρ πI)).map Prod.fst) :
    let remaining_πInner := remaining_π.filter (fun (w, _) =>
      !πI.any (fun (w', _) => w' == w))
    (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions ρ πI)).map Prod.fst
      <+: remaining_πInner.map Prod.fst ∧
    (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions ρ πI)) ≠ [] ∨
    remaining_πInner.map Prod.fst
      <+: (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions ρ πI)).map Prod.fst := by
  intro remaining_πInner
  -- Both prefix directions feed directly into the disjunctive conclusion.
  rcases h_r_combined_pref hrem_ne with hpref | hrev
  · exact Or.inl ⟨hpref, h_r_combined_ne hrem_ne⟩
  · exact Or.inr hrev

/-- **Path-prefix propagation for one encoder step.** The inductive step of
    `encoder_aux_decode_gen_iff_mp` invokes this bridge to propagate `hpfx_ρ`
    from level *k* to level *k+1*.

    Its side conditions bridge the outer-level invariants
    `(hρ_sub_orig, hρ_extends_fn_orig, …)` to the restriction extended by
    `πI`. -/
private lemma encoder_path_prefix_after_one_step
    {n : Nat} (f : UnboundedFanInDNF n)
    (asgn : List (Nat × Bool))
    (d : Nat) (path : List (Nat × Bool))
    -- Loop-level state at level k:
    (ρ remaining_π : List (Nat × Bool))
    -- Invariants at level k:
    (hρ_sub_orig : ∀ w b, (w, b) ∈ ρ →
      (w, b) ∈ asgn ∨ (w, b) ∈ path.take d)
    (hρ_extends_fn_orig : ∀ w,
      restrictionAsFunction asgn w ≠ none →
      restrictionAsFunction ρ w =
      restrictionAsFunction asgn w)
    (hnodup_rem_outer : (remaining_π.map Prod.fst).Nodup)
    (hρ_disj_orig : ∀ w b, (w, b) ∈ remaining_π →
      (ρ.any fun (z, _) => z == w) = false)
    (hrem_sub_outer : ∀ x ∈ remaining_π, x ∈ path.take d)
    (hrem_complete_orig : ∀ x ∈ path.take d,
      (ρ.any fun (z, _) => z == x.1) = false → x ∈ remaining_π)
    -- The restricted head remains nonempty whenever variables remain.
    (h_r_combined_ne :
      let πI := remaining_π.filter (fun x =>
        (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
          |>.contains x.1)
      remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w)) ≠ [] →
      restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions ρ πI) ≠ [])
    -- Conditional on `remaining' ≠ []`, the selected clause's variable list
    -- and `remaining'` are prefix-comparable. The reverse direction is the
    -- β-straddler case.
    (h_r_combined_pref :
      let πI := remaining_π.filter (fun x =>
        (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
          |>.contains x.1)
      remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w)) ≠ [] →
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions ρ πI)).map Prod.fst
        <+: (remaining_π.filter (fun (w, _) =>
          !πI.any (fun (w', _) => w' == w))).map Prod.fst ∨
      (remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w))).map Prod.fst
        <+: (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
          (combineRestrictions ρ πI)).map Prod.fst) :
    let U_ρ := restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ
    let U_vars := U_ρ.map Prod.fst
    let πI := remaining_π.filter (fun x => U_vars.contains x.1)
    let ρ' := combineRestrictions ρ πI
    let remaining' := remaining_π.filter
      (fun (w, _) => !πI.any (fun (w', _) => w' == w))
    -- Conclusion: prefix invariant at level k+1 (or `remaining' = []`).
    ((restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ').map Prod.fst
        <+: remaining'.map Prod.fst ∧
      restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ' ≠ []) ∨
    remaining'.map Prod.fst <+:
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ').map Prod.fst := by
  intro U_ρ U_vars πI ρ' remaining'
  -- πI is by definition the filter against U_ρ.fst.
  have hπ_def : πI = remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        |>.contains x.1) := rfl
  -- πI ⊆ remaining_π ⊆ path.take d
  have hπ_sub_path : ∀ x ∈ πI, x ∈ path.take d := fun x hx =>
    hrem_sub_outer x (List.mem_of_mem_filter hx)
  -- ρ' = ρ ++ πI ⊆ asgn ∨ path.take d
  have hρ_sub_step : ∀ w b, (w, b) ∈ combineRestrictions ρ πI →
      (w, b) ∈ asgn ∨ (w, b) ∈ path.take d := by
    intro w b hwb
    simp only [combineRestrictions, List.mem_append] at hwb
    rcases hwb with hwb | hwb
    · exact hρ_sub_orig w b hwb
    · exact Or.inr (hπ_sub_path (w, b) (List.mem_of_mem_filter hwb))
  -- The remaining side-conditions are pure list/restriction algebra,
  -- bridging outer-level invariants to step-level ones.
  have hρ_extends_fn_step : ∀ w,
      restrictionAsFunction asgn w ≠ none →
      restrictionAsFunction (combineRestrictions ρ πI) w =
      restrictionAsFunction asgn w := by
    intro w hw_ne
    have hρw : restrictionAsFunction ρ w =
        restrictionAsFunction asgn w :=
      hρ_extends_fn_orig w hw_ne
    -- If `restrictionAsFunction asgn w ≠ none`, extension gives
    -- `restrictionAsFunction ρ w ≠ none`, so the lookup in ρ succeeds.
    have hρ_some : ∃ v, ρ.find? (fun p => p.1 == w) = some v := by
      have hne : restrictionAsFunction ρ w ≠ none := hρw ▸ hw_ne
      simp only [restrictionAsFunction] at hne
      cases h : ρ.find? fun p => p.1 == w with
      | none => simp [h] at hne
      | some v => exact ⟨v, rfl⟩
    obtain ⟨v, hf⟩ := hρ_some
    -- Now compute both sides explicitly.
    have h_lhs : restrictionAsFunction (combineRestrictions ρ πI) w
        = some v.2 := by
      simp only [restrictionAsFunction, combineRestrictions,
        List.find?_append, hf, Option.some_or]
    have hρ_val : restrictionAsFunction ρ w = some v.2 := by
      simp only [restrictionAsFunction, hf]
    rw [h_lhs, ← hρ_val, hρw]
  have hρ_disj_step : ∀ (w : Nat) (b : Bool),
      (w, b) ∈ remaining_π.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w)) →
      ((combineRestrictions ρ πI).any fun (z, _) => z == w) = false := by
    intro w b hwb
    have hwb_rem : (w, b) ∈ remaining_π := List.mem_of_mem_filter hwb
    have hρ_no : (ρ.any fun (z, _) => z == w) = false := hρ_disj_orig w b hwb_rem
    have hwb_pred : (!πI.any fun (w', _) => w' == w) = true :=
      (List.mem_filter.mp hwb).2
    have hπi_no : (πI.any fun (w', _) => w' == w) = false := by
      cases hh : πI.any fun (w', _) => w' == w with
      | true => rw [hh] at hwb_pred; simp at hwb_pred
      | false => rfl
    -- (ρ ++ πI.filter ¬ρ.any).any (·.1 == w) = false: ρ.any false ∧ filt.any false.
    -- filt ⊆ πI so any element of filt with first == w would lie in πI, contradicting hπi_no.
    have hfilt_no : ((πI.filter (fun p => !ρ.any fun (z, _) => z == p.1)).any
        fun p => p.1 == w) = false := by
      cases hh : (πI.filter (fun p => !ρ.any fun (z, _) => z == p.1)).any
          fun p => p.1 == w with
      | false => rfl
      | true =>
        rw [List.any_eq_true] at hh
        obtain ⟨⟨w', b'⟩, hmem, hbeq⟩ := hh
        have hin_πi : (w', b') ∈ πI := List.mem_of_mem_filter hmem
        have : (πI.any fun p => p.1 == w) = true :=
          List.any_eq_true.mpr ⟨(w', b'), hin_πi, hbeq⟩
        rw [hπi_no] at this; exact absurd this (by decide)
    simp only [combineRestrictions, List.any_append, hρ_no, hfilt_no, Bool.or_self]
  have hnodup_rem_step :
      ((remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w))).map Prod.fst).Nodup := by
    have hsub : (remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w))).Sublist remaining_π := List.filter_sublist
    exact (List.Sublist.map Prod.fst hsub).nodup hnodup_rem_outer
  have hrem_sub_step : ∀ x ∈ remaining_π.filter (fun (w, _) =>
      !πI.any (fun (w', _) => w' == w)), x ∈ path.take d := fun x hx =>
    hrem_sub_outer x (List.mem_of_mem_filter hx)
  have hrem_complete_step : ∀ x ∈ path.take d,
      ((combineRestrictions ρ πI).any fun (z, _) => z == x.1) = false →
      x ∈ remaining_π.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w)) := by
    intro x hx hno
    -- Decompose: ρ.any false ∧ filter.any false.
    simp only [combineRestrictions, List.any_append, Bool.or_eq_false_iff] at hno
    obtain ⟨hρ_no, hfilt_no⟩ := hno
    have hx_rem : x ∈ remaining_π := hrem_complete_orig x hx hρ_no
    -- Suppose (w'', b'') ∈ πI with w'' == x.1.  Since (w'', b'') ∈ πI ⊆ remaining_π,
    -- by hρ_disj_orig ρ.any (·==w'') = false, so (w'', b'') survives the filter
    -- in combineRestrictions; but hfilt_no contradicts.
    have hπ_no : (πI.any fun (w', _) => w' == x.1) = false := by
      cases hp : πI.any fun (w', _) => w' == x.1 with
      | false => rfl
      | true =>
        exfalso
        rw [List.any_eq_true] at hp
        obtain ⟨⟨w'', b''⟩, hw_πi, hw_eq⟩ := hp
        simp only at hw_eq
        have hw_rem : (w'', b'') ∈ remaining_π := List.mem_of_mem_filter hw_πi
        have hρ_no_w : (ρ.any fun (z, _) => z == w'') = false :=
          hρ_disj_orig w'' b'' hw_rem
        have hsurv : (w'', b'') ∈ πI.filter
            (fun p => !ρ.any fun (z, _) => z == p.1) := by
          refine List.mem_filter.mpr ⟨hw_πi, ?_⟩
          show (!ρ.any fun (z, _) => z == w'') = true
          rw [hρ_no_w]; rfl
        have hbad : ((πI.filter (fun p => !ρ.any fun (z, _) => z == p.1)).any
            fun p => p.1 == x.1) = true :=
          List.any_eq_true.mpr ⟨(w'', b''), hsurv, hw_eq⟩
        rw [hbad] at hfilt_no; exact absurd hfilt_no (by decide)
    refine List.mem_filter.mpr ⟨hx_rem, ?_⟩
    show (!πI.any fun (w', _) => w' == x.1) = true
    rw [hπ_no]; rfl
  -- If `remaining' = []`, the right disjunct holds trivially (nil is a
  -- prefix of anything); otherwise feed everything to the step lemma.
  by_cases hrem_ne : remaining' = []
  · right
    have : remaining'.map Prod.fst = [] := by rw [hrem_ne]; rfl
    rw [this]; exact List.nil_prefix
  · exact ftnkb_prefix_after_consume_encoder_step
      f ρ remaining_π πI hrem_ne
      h_r_combined_ne
      h_r_combined_pref

#print axioms encoder_path_prefix_after_one_step

/- **Dead vars assigned in ρ stay in dead_acc.**

    If `v` is already assigned in `ρ` (i.e., `ρ.any (·.1 == v) = true`),
    then any `(v, b)` in the encoder's dead-variable output must come from
    `dead_acc` (the seed),
    not from γ-bits added at any recursion level.

    Reason: γ-bits at every level come from the surviving clause after
    variables already assigned by the current restriction have been removed.
    Since `combineRestrictions ρ πI` only extends `ρ`, an
    initially-assigned `v` stays assigned at every deeper level, hence
    `v` never appears in a deeper surviving clause and hence never in its
    γ-bits. -/
private lemma encoder_aux_dead_when_assigned
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (v : Nat) (b : Bool)
    (hmem : (v, b) ∈ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1)
    (hρ_v : (ρ.any fun (w, _) => w == v) = true) :
    (v, b) ∈ dead_acc := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero =>
    simp only [beameEncoderAux] at hmem; exact hmem
  | succ fuel' ih =>
    simp only [beameEncoderAux] at hmem
    by_cases hrem_e : remaining_π = []
    · rw [if_pos hrem_e] at hmem; exact hmem
    · rw [if_neg hrem_e] at hmem
      set clauses := dnfClauses dnf
      set U_i := restrictionOfFirstTermNotKilledByList clauses ρ
      set U_vars := U_i.map Prod.fst
      set p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
      set πI := remaining_π.filter p
      set γ_i := (gammaBitsForClause U_i).take πI.length
      -- v not in U_vars (since v is assigned in ρ).
      have hv_not_u : v ∉ U_vars := by
        intro hcontra
        rcases List.mem_map.mp hcontra with ⟨⟨w, neg⟩, hw_u, hw_eq⟩
        simp only at hw_eq
        subst hw_eq
        have hbad :=
          restrictionOfFirstTermNotKilledByList_vars_notMem_asgn
            clauses ρ (w, neg) hw_u
        rw [hρ_v] at hbad; cases hbad
      have hv_not_γ : (v, b) ∉ γ_i := by
        intro hγ
        have hγ_full : (v, b) ∈ gammaBitsForClause U_i :=
          List.mem_of_mem_take hγ
        simp only [gammaBitsForClause, List.mem_map] at hγ_full
        obtain ⟨⟨w, neg⟩, hw_u, hw_eq⟩ := hγ_full
        have hw_v : w = v := by
          have := congrArg Prod.fst hw_eq; simp at this; exact this
        rw [hw_v] at hw_u
        exact hv_not_u (List.mem_map_of_mem (f := Prod.fst) hw_u)
      split at hmem
      · -- πI.length = 0: encoder.1 = dead_acc ++ γ_i.
        rw [List.mem_append] at hmem
        rcases hmem with h | h
        · exact h
        · exact absurd h hv_not_γ
      · -- recursive case: encoder.1 = (rec.2). v stays assigned in combineRestrictions ρ πI.
        set ρ' := combineRestrictions ρ πI
        have hρ'_v : (ρ'.any fun (w, _) => w == v) = true := by
          show ((ρ ++ πI.filter (fun (x, _) =>
              !ρ.any fun (w, _) => w == x)).any fun (w, _) => w == v) = true
          rw [List.any_append, hρ_v]; rfl
        have hmem_dead' : (v, b) ∈ dead_acc ++ γ_i :=
          ih _ _ _ hmem hρ'_v
        rw [List.mem_append] at hmem_dead'
        rcases hmem_dead' with h | h
        · exact h
        · exact absurd h hv_not_γ

private lemma encoder_aux_dead_val_of_mem_ftnkb
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ : List (Nat × Bool))
    (dead_acc : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (hfuel : remaining_π.length ≤ fuel)
    (v : Nat) (b : Bool) (neg : Bool)
    (hmem : (v, b) ∈ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1)
    (hnot_acc : (v, b) ∉ dead_acc)
    (hmem_t : (v, neg) ∈ firstTermNotKilledByList (dnfClauses dnf) ρ)
    (hv_none : (ρ.any fun (w, _) => w == v) = false)
    -- ── Killed-heads CDT context ────────────────────────────────────
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (_hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf asgn) d
        = some path)
    (hrem_sub_path : ∀ x ∈ remaining_π, x ∈ path.take d)
    -- ── Selected-clause prefix invariant (from `EncoderLoopInv.hpfx_ρ`). ────
    (hpfx_ρ : (restrictionOfFirstTermNotKilledByList
      (dnfClauses dnf) ρ).map Prod.fst <+: remaining_π.map Prod.fst) :
    b = literalSatisfyingBit neg := by
  -- Inline the nodup first-component argument to avoid a forward reference.
  have nodup_eq : ∀ {l : List (Nat × Bool)} {a : Nat} {b₁ b₂ : Bool},
      (l.map Prod.fst).Nodup → (a, b₁) ∈ l → (a, b₂) ∈ l → b₁ = b₂ := by
    intro l a b₁ b₂ hnd h₁ h₂
    induction l with
    | nil => simp at h₁
    | cons hd tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hd_not_tl, htl_nd⟩ := hnd
      cases List.mem_cons.mp h₁ with
      | inl h₁_eq =>
        cases List.mem_cons.mp h₂ with
        | inl h₂_eq => exact congrArg Prod.snd (h₁_eq.trans h₂_eq.symm)
        | inr h₂_tl =>
          exfalso; apply hd_not_tl
          have := List.mem_map_of_mem (f := Prod.fst) h₂_tl
          rwa [congrArg Prod.fst h₁_eq] at this
      | inr h₁_tl =>
        cases List.mem_cons.mp h₂ with
        | inl h₂_eq =>
          exfalso; apply hd_not_tl
          have := List.mem_map_of_mem (f := Prod.fst) h₁_tl
          rwa [congrArg Prod.fst h₂_eq] at this
        | inr h₂_tl => exact ih htl_nd h₁_tl h₂_tl
  -- ── Main induction on fuel. ────────────────────────────────────────
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero =>
    simp [beameEncoderAux] at hmem
    exact absurd hmem hnot_acc
  | succ fuel' ih =>
    simp only [beameEncoderAux] at hmem
    by_cases hrem_e : remaining_π = []
    · rw [if_pos hrem_e] at hmem
      exact absurd hmem hnot_acc
    · rw [if_neg hrem_e] at hmem
      -- ── Names matching the encoder's `let` bindings. ────────────────
      set clauses := dnfClauses dnf with hclauses_def
      set T_i := firstTermNotKilledByList clauses ρ with h_t_i_def
      set U_i := restrictionOfFirstTermNotKilledByList clauses ρ
        with h_u_i_def
      set U_vars := U_i.map Prod.fst with h_u_vars_def
      set p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
        with hp_def
      set πI := remaining_π.filter p with hπ_i_def
      set γ_i := (gammaBitsForClause U_i).take πI.length
        with hγ_i_def
      -- ── T_0 nodup (used for γ-polarity bridge). ────────────────────
      have h_t_nodup : (T_i.map Prod.fst).Nodup := by
        rcases firstTermNotKilledByList_mem_or_nil clauses ρ with h | h
        · rw [h_t_i_def]
          exact hnodup _ h
        · exfalso
          rw [h_t_i_def, h] at hmem_t
          simp at hmem_t
      -- ── (v, neg) ∈ U_i since v ∉ ρ. ────────────────────────────────
      have hv_u : (v, neg) ∈ U_i := by
        rw [h_u_i_def]
        apply restrictClauseByListAssignment_mem_of_unassigned
        · rwa [← h_t_i_def]
        · exact hv_none
        · exact firstTermNotKilledByList_self clauses ρ
      have hv_u_vars : v ∈ U_vars := List.mem_map_of_mem (f := Prod.fst) hv_u
      -- ── γ-case bridge. ─────────────────────────────────────────────
      have hval_of_γ : (v, b) ∈ γ_i → b = literalSatisfyingBit neg := by
        intro hγ
        have hγ_full : (v, b) ∈ gammaBitsForClause U_i :=
          List.mem_of_mem_take hγ
        simp only [gammaBitsForClause, List.mem_map] at hγ_full
        obtain ⟨⟨w, n⟩, hw_u, heq⟩ := hγ_full
        have hb_eq : b = literalSatisfyingBit n := by
          have := congrArg Prod.snd heq; simp at this; exact this.symm
        have hw_v : w = v := by
          have := congrArg Prod.fst heq; simp at this; exact this
        rw [hw_v] at hw_u
        have hn_t : (v, n) ∈ T_i := by
          rw [h_u_i_def] at hw_u
          exact restrictClauseByListAssignment_subset _ _ _ hw_u
        have hneg_t : (v, neg) ∈ T_i := hmem_t
        rw [hb_eq]
        exact congrArg literalSatisfyingBit (nodup_eq h_t_nodup hn_t hneg_t)
      -- ── Main inner if-split on `πI.length = 0`. ───────────────────
      split at hmem
      · -- πI.length = 0: encoder.1 = dead_acc ++ γ_i.
        rw [List.mem_append] at hmem
        rcases hmem with h | h
        · exact absurd h hnot_acc
        · exact hval_of_γ h
      · -- ── Recursive case (πI.length ≠ 0). ─────────────────────────
        rename_i hπ_len_ne
        -- Names matching the encoder's recursive bindings.
        set ρ' := combineRestrictions ρ πI with hρ'_def
        set remaining' := remaining_π.filter
          fun (w, _) => !πI.any fun (w', _) => w' == w with hrem'_def
        set dead_acc' := dead_acc ++ γ_i with hdead'_def
        -- `hmem` after the `else` branch points into the recursive call's `.1`.
        have hmem_rec : (v, b) ∈ (beameEncoderAux fuel'
            remaining' (dnfClauses dnf) ρ' dead_acc').1 := hmem
        -- ── Case a: v already in remaining_π.fst (so v ends up in ρ'). ──
        by_cases hv_rem : (remaining_π.any fun (w, _) => w == v) = true
        · -- (v, b') ∈ remaining_π for some b'; since v ∈ U_vars, (v, b') ∈ πI.
          have ⟨⟨w, b'⟩, hwb_mem, hwb_eq⟩ := List.any_eq_true.mp hv_rem
          simp only [beq_iff_eq] at hwb_eq
          subst hwb_eq
          have hwb_πi : (w, b') ∈ πI := by
            rw [hπ_i_def]
            refine List.mem_filter.mpr ⟨hwb_mem, ?_⟩
            show U_vars.contains w = true
            exact List.contains_iff_mem.mpr hv_u_vars
          -- v assigned in ρ' (via πI contribution).
          have hρ'_v : (ρ'.any fun (z, _) => z == w) = true := by
            rw [hρ'_def]
            show ((ρ ++ πI.filter (fun (x, _) =>
                !ρ.any fun (z, _) => z == x)).any
                fun (z, _) => z == w) = true
            rw [List.any_append]
            -- πI has (w, b'); since w ∉ ρ.fst (= hv_none), it survives the filter.
            have hfilt_mem : (w, b') ∈ πI.filter
                (fun (x, _) => !ρ.any fun (z, _) => z == x) := by
              refine List.mem_filter.mpr ⟨hwb_πi, ?_⟩
              show (!ρ.any fun (z, _) => z == w) = true
              rw [hv_none]; rfl
            have hany : ((πI.filter
                (fun (x, _) => !ρ.any fun (z, _) => z == x)).any
                fun (z, _) => z == w) = true :=
              List.any_eq_true.mpr ⟨(w, b'), hfilt_mem, by simp⟩
            rw [hany]; simp
          -- By `encoder_aux_dead_when_assigned`, (w, b) ∈ dead_acc'.
          have hmem_dead' : (w, b) ∈ dead_acc' :=
            encoder_aux_dead_when_assigned fuel' remaining' dnf ρ'
              dead_acc' w b hmem_rec hρ'_v
          -- Decompose dead_acc' = dead_acc ++ γ_i.
          rw [hdead'_def, List.mem_append] at hmem_dead'
          rcases hmem_dead' with hda | hγ
          · exact absurd hda hnot_acc
          · exact hval_of_γ hγ
        · -- ── Case b: v ∉ remaining_π.fst.  **Vacuous via `hpfx_ρ`.** ──
          -- `(v, neg) ∈ U_i` (= `hv_u`), so `v ∈ U_vars`.  Combined with
          -- `hpfx_ρ : U_vars <+: remaining_π.map Prod.fst`, this forces
          -- `v ∈ remaining_π.map Prod.fst`, contradicting `hv_rem`.
          exfalso
          have hv_u_vars_r : v ∈ (restrictionOfFirstTermNotKilledByList
              (dnfClauses dnf) ρ).map Prod.fst := by
            show v ∈ U_vars; exact hv_u_vars
          have hv_rem_fst : v ∈ remaining_π.map Prod.fst :=
            hpfx_ρ.subset hv_u_vars_r
          obtain ⟨⟨w', b''⟩, hwb_mem, hw_eq⟩ := List.mem_map.mp hv_rem_fst
          have hw'_eq : w' = v := hw_eq
          have hwb_mem' : (v, b'') ∈ remaining_π := hw'_eq ▸ hwb_mem
          have hany_true : (remaining_π.any fun (z, _) => z == v) = true :=
            List.any_eq_true.mpr ⟨(v, b''), hwb_mem', by simp⟩
          exact hv_rem hany_true

#print axioms encoder_aux_dead_val_of_mem_ftnkb

/- **Generalized initial restrictionOfFirstTermNotKilledByList alignment for the encoder (killed-heads form).**

    Dead entries from the encoder do not change the selected clause,
    provided every `dead_acc` variable is already assigned in `ρ` (so
    the dead entries get filtered out by `combineRestrictions ρ ·`).

    The proof uses the per-segment killed-heads coverage of the canonical
    full-query DT, formalised in
    `cdt_full_query_killed_heads_covered_by_prefix`
    (`SwitchingLemmaCanonicalDT.lean:3948`).  That lemma decomposes the
    leftmost full-query path into segments `(prefix_i, head_i)` where:

      * `prefix_i.map Prod.fst = head_i.map Prod.fst`, and
      * every `v ∈ head_i.map Prod.fst` has a witness `(v, b) ∈ prefix_i`.

    The encoder's `γ_i = (gammaBitsForClause U_i).take πI.length`
    is exactly the "killed-heads" payload for the `i`-th segment, so
    every entry pushed onto `dead_acc` is either already in `ρ` (Or.inl)
    or sits at a known position in `path.take d` via the killed-heads
    witness (Or.inr).  Either way, `combineRestrictions ρ dead` agrees
    with ρ on every variable inspected while selecting the first non-killed clause.

    The path, remaining-path containment, and dead-variable coverage
    hypotheses supply the required segment witnesses. -/
private lemma encoder_aux_initial_alignment_gen
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ : List (Nat × Bool))
    (dead_acc : List (Nat × Bool))
    (_hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (hfuel : remaining_π.length ≤ fuel)
    (hdead_sub_ρ : ∀ v, v ∈ dead_acc.map Prod.fst →
                    (ρ.any fun (w, _) => w == v) = true)
    -- Canonical-DT killed-heads context.
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf asgn) d
        = some path)
    (hrem_sub_path : ∀ x ∈ remaining_π, x ∈ path.take d)
    (_hdead_killed_covered : ∀ v ∈ dead_acc.map Prod.fst,
      (ρ.any fun (w, _) => w == v) = true ∨
      ∃ b, (v, b) ∈ path.take d)
    -- Selected-clause prefix invariant.
    (hpfx_ρ : (restrictionOfFirstTermNotKilledByList
      (dnfClauses dnf) ρ).map Prod.fst <+: remaining_π.map Prod.fst) :
    firstTermNotKilledByList (dnfClauses dnf)
      (combineRestrictions ρ
        (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1) =
    firstTermNotKilledByList (dnfClauses dnf) ρ := by
  -- Factor the bit-polarity step through
  -- `encoder_aux_dead_val_of_mem_ftnkb`.
  set clauses := dnfClauses dnf with hclauses_def
  set encoder := beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc
  set dead := encoder.1 with hdead_def
  set A₁ := restrictionAsFunction ρ
  set A₂ := restrictionAsFunction (combineRestrictions ρ dead)
  apply firstTermNotKilledByList_eq clauses ρ
    (combineRestrictions ρ dead)
  · intro w hw
    exact cr_none_combineRestrictions_extends_base ρ dead w hw
  · rw [isClauseKilledBy_eq_isClauseKilled]
    apply not_killed_by_satisfying
    intro ⟨v, neg⟩ hmem_t₀
    by_cases hv : A₁ v = none
    · have hv_ρ_any : (ρ.any fun (w, _) => w == v) = false := by
        rw [list_any_eq_cr_none_isSome]
        change (A₁ v).isSome = false
        rw [hv]; rfl
      have hv_ρ_find : ρ.find? (fun p => p.1 == v) = none := by
        rw [List.find?_eq_none]; intro ⟨x, bx⟩ hmem
        simp only [BEq.beq]; intro hxv
        have : (ρ.any fun (w, _) => w == v) = true :=
          List.any_eq_true.mpr ⟨(x, bx), hmem, by simp [BEq.beq, hxv]⟩
        simp [this] at hv_ρ_any
      have h_a₂_simp : A₂ v =
          match (dead.filter (fun x => !(ρ.any fun (w, _) => w == x.1))).find?
            (fun p => p.1 == v) with
          | some (_, b) => some b
          | none => none := by
        simp only [A₂, combineRestrictions, restrictionAsFunction, List.find?_append,
          hv_ρ_find, Option.none_or]
        rfl
      cases hfind : (dead.filter (fun x => !(ρ.any fun (w, _) => w == x.1))).find?
          (fun p => p.1 == v) with
      | none =>
          left
          change A₂ v = none
          rw [h_a₂_simp, hfind]
      | some pair =>
          right
          obtain ⟨w, bw⟩ := pair
          change A₂ v = some (literalSatisfyingBit neg)
          rw [h_a₂_simp, hfind]
          simp only
          congr 1
          have hmem_filt := List.mem_of_find?_eq_some hfind
          have hmem_dead : (w, bw) ∈ dead := List.mem_of_mem_filter hmem_filt
          have hw_eq : w = v := by
            have := List.find?_some hfind; simpa [BEq.beq] using this
          have hmem_t₀' : (w, neg) ∈ firstTermNotKilledByList clauses ρ := by
            rwa [hw_eq]
          have hv_ρ_any' : (ρ.any fun (w', _) => w' == w) = false := by
            rw [hw_eq]; exact hv_ρ_any
          have hnot_acc : (w, bw) ∉ dead_acc := by
            intro hmem_da
            have := hdead_sub_ρ w
              (List.mem_map_of_mem (f := Prod.fst) hmem_da)
            rw [hw_eq] at this
            simp [hv_ρ_any] at this
          exact encoder_aux_dead_val_of_mem_ftnkb fuel remaining_π
            dnf ρ dead_acc hnodup hfuel w bw neg hmem_dead hnot_acc
            hmem_t₀' hv_ρ_any' asgn d path hpath hrem_sub_path hpfx_ρ
    · right
      show A₂ v = some (literalSatisfyingBit neg)
      have h_a₂_eq : A₂ v = A₁ v := cr_none_combineRestrictions_extends_base ρ dead v hv
      rw [h_a₂_eq]
      have hself := firstTermNotKilledByList_self clauses ρ
      rw [isClauseKilledBy_eq_isClauseKilled] at hself
      simp only [isClauseKilled] at hself
      rw [List.any_eq_false] at hself
      have := hself (v, neg) hmem_t₀
      simp only at this
      cases hav : A₁ v with
      | none => exact absurd hav hv
      | some bv =>
        have hav' : restrictionAsFunction ρ v = some bv := hav
        rw [hav'] at this
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at this
        push Not at this
        rw [this]

#print axioms encoder_aux_initial_alignment_gen

/- **Canonical-DT loop invariant bundle for the encoder.**

    Packages the canonical-DT leftmost-path coverage data and side
    invariants required by `encoder_path_prefix_after_one_step`.
    Threading this single bundle through the loop is cheaper than
    listing 12 separate hypotheses on each invocation. -/
private structure EncoderLoopInv
    (dnf : UnboundedFanInFormula) (asgn : List (Nat × Bool))
    (d : Nat) (path : List (Nat × Bool))
    (ρ remaining_π : List (Nat × Bool)) : Prop where
  hpath : leftmostPathExceedingDepth
    (canonicalDecisionTree dnf asgn) d = some path
  hpfx_ρ :
    (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) ρ).map Prod.fst
      <+: remaining_π.map Prod.fst
  hρ_sub_orig : ∀ w b, (w, b) ∈ ρ → (w, b) ∈ asgn ∨ (w, b) ∈ path.take d
  hρ_extends_fn_orig : ∀ w,
    restrictionAsFunction asgn w ≠ none →
    restrictionAsFunction ρ w =
    restrictionAsFunction asgn w
  hρ_disj_orig : ∀ w b, (w, b) ∈ remaining_π →
    (ρ.any fun (z, _) => z == w) = false
  hrem_sub_outer : ∀ x ∈ remaining_π, x ∈ path.take d
  hrem_complete_orig : ∀ x ∈ path.take d,
    (ρ.any fun (z, _) => z == x.1) = false → x ∈ remaining_π
  hrem_sublist : remaining_π.Sublist (path.take d)
  hpre_ρ_inv : ∀ v ∈
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) asgn).map Prod.fst,
    (ρ.any fun (z, _) => z == v) = true ∨
    v ∈ (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) ρ).map Prod.fst
  -- Iter-split-pinned, encoder-faithful invariants.
  h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ []
  /- **Encoder-faithfulness (α′)**: ρ has consumed exactly the bits of the
      first `k` segments of the canonical-DT iter-split of `path` beyond
      `asgn`, and `remaining_π` is exactly the un-consumed segments
      filtered to the depth-`d` window.

      This bundle-level witness legitimizes per-segment reasoning. -/
  hρ_segments_consumed :
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))) (k : Nat)
      (partial_seg : List (Nat × Bool)),
      path = (segments.map Prod.fst).flatten ∧
      k ≤ segments.length ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) dnf))
            (((segments.take j).map Prod.fst).flatten)
          = (segments[j]'hj).2 :: tail_j) ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      -- Within-depth nondegeneracy.
      -- Each iter-split segment whose cumulative path-length-through-end
      -- is `≤ d` consumes at least one path bit.  This excludes any trailing
      -- degenerate `([],[])` segments (which can occur past depth `d` when
      -- the canonical DT 1-leaf-terminates).  Discharged at seed/step via
      -- `cdt_segment_pre_ne_nil_within_depth`.
      (∀ (j : Nat) (hj : j < segments.length),
        ((segments.take (j+1)).map Prod.fst).flatten.length ≤ d →
        (segments[j]'hj).1 ≠ []) ∧
      ρ = asgn ++ ((segments.take k).map Prod.fst).flatten ++ partial_seg ∧
      -- Two-case discriminant.  The partial-last-segment state is terminal
      -- (remaining_π = []) since the encoder consumes all bits within depth
      -- in one shot and the rest is past the window.
      ((partial_seg = [] ∧
        remaining_π =
          (((segments.drop k).map Prod.fst).flatten).filter
            (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) ∧
        -- Encoder depth-monotonicity. In the alive case, when `k < segments.length` and
        -- the cumulative length through segment `k` fits in the depth window,
        -- the segment lies entirely in `path.take d`.  This is the
        -- encoder-faithfulness witness used by the bridge.
        (∀ (hk : k < segments.length),
          ((segments.take (k+1)).map Prod.fst).flatten.length ≤ d →
          ∀ p ∈ (segments[k]'hk).1, p ∈ path.take d)) ∨
       (∃ (hk : k < segments.length),
         partial_seg.Sublist (segments[k]'hk).1 ∧ remaining_π = []))


/- In the alive-straddler case, the encoder consumes the entire truncated
   segment, leaving no variables for the next iteration. -/
private lemma encoder_alive_straddler_yields_remaining_post_step_nil
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val asgn) d = some path)
    (ρ remaining_π : List (Nat × Bool))
    (segs_canon : List (List (Nat × Bool) × List (Nat × Bool)))
    (k_bundle : Nat) (hk_lt : k_bundle < segs_canon.length)
    (hpath_canon : path = (segs_canon.map Prod.fst).flatten)
    (hcanon_prov :
      ∀ (j : Nat) (hj : j < segs_canon.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segs_canon.take j).map Prod.fst).flatten)
          = (segs_canon[j]'hj).2 :: tail_j)
    (hvm_canon : ∀ p ∈ segs_canon, p.1.map Prod.fst = p.2.map Prod.fst)
    /- Alive-case discriminant: ρ = asgn ++ prefix_k_canon. -/
    (hρ_eq : ρ = asgn ++ ((segs_canon.take k_bundle).map Prod.fst).flatten)
    /- Remaining π form (alive disjunct, `partial_seg = []`). -/
    (hrem_alive :
      remaining_π = (((segs_canon.drop k_bundle).map Prod.fst).flatten).filter
        (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)))
    /- Straddler discriminant. -/
    (h_prefix_k_le :
      ((segs_canon.take k_bundle).map Prod.fst).flatten.length ≤ d)
    (h_straddler :
      d < ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten.length) :
    let πI := remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        |>.contains x.1)
    remaining_π.filter (fun (w, _) => !πI.any fun (w', _) => w' == w) = [] := by
  -- Step 1: identify `remaining_π` with the canonical truncation.
  have hrem_eq_trunc :
      remaining_π = (segs_canon[k_bundle]'hk_lt).1.take
        (d - ((segs_canon.take k_bundle).map Prod.fst).flatten.length) := by
    rw [hrem_alive]
    exact remaining_π_eq_truncated_at_alive_straddler f asgn hnodup d path hpath
      segs_canon hpath_canon k_bundle hk_lt h_prefix_k_le h_straddler
  -- Set up abbreviation for the truncated segment.
  set prefix_k_canon : List (Nat × Bool) :=
    ((segs_canon.take k_bundle).map Prod.fst).flatten with hprefix_k_canon_def
  set m : Nat := d - prefix_k_canon.length with hm_def
  set seg_k : List (Nat × Bool) := (segs_canon[k_bundle]'hk_lt).1 with hseg_k_def
  set truncated : List (Nat × Bool) := seg_k.take m with htruncated_def
  -- Step 2: the selected clause under ρ has the variables of the current segment.
  -- Subchain (2a): combineRestrictions asgn prefix_k_canon = ρ (path bits asgn-disjoint).
  have h_combined_asgn_eq : combineRestrictions asgn prefix_k_canon = ρ := by
    rw [hρ_eq]
    unfold combineRestrictions
    congr 1
    apply List.filter_eq_self.mpr
    intro p hp
    rw [Bool.not_eq_true']
    have hp_path : p ∈ path := by
      rw [hpath_canon]
      exact (List.IsPrefix.flatten
        (List.IsPrefix.map _ (List.take_prefix _ _))).subset hp
    have hnone := canonical_dt_path_var_none f.val asgn
      f.property.2 d path hpath p.1 p.2 hp_path
    cases hany : asgn.any fun (z, _) => z == p.1
    · rfl
    · exfalso
      rw [List.any_eq_true] at hany
      obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
      simp at hw'_eq; subst hw'_eq
      simp only [restrictionAsFunction] at hnone
      have hfind : asgn.find? (fun q => q.1 == p.1) ≠ none := by
        rw [Ne, List.find?_eq_none]; push Not
        exact ⟨(p.1, b'), hw'_mem, by simp⟩
      rcases hfind_eq : asgn.find? (fun q => q.1 == p.1)
        with _ | ⟨_, _⟩
      · exact hfind hfind_eq
      · rw [hfind_eq] at hnone; cases hnone
  -- Subchain (2b): identify the selected clause under the extended assignment
  -- with the current segment head.
  have h_r_at_canon :
      (segs_canon[k_bundle]'hk_lt).2.map Prod.fst =
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions asgn prefix_k_canon)).map Prod.fst :=
    iter_split_seg_eq_rtnkb_at_canonical_prefix f asgn hnodup d path
      hpath segs_canon hpath_canon hcanon_prov k_bundle hk_lt
  -- Combine 2a and 2b to obtain the corresponding equality under ρ.
  have h_r_ρ_eq :
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst =
      (segs_canon[k_bundle]'hk_lt).2.map Prod.fst := by
    rw [← h_combined_asgn_eq, ← h_r_at_canon]
  -- Subchain (2c): segs[k].1.fst = segs[k].2.fst (vars-match).
  have hvm_k := hvm_canon (segs_canon[k_bundle]'hk_lt) (List.getElem_mem hk_lt)
  -- Transfer the equality from the segment head to the segment path.
  have h_r_ρ_eq_segk1 :
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst =
      seg_k.map Prod.fst := by
    rw [h_r_ρ_eq]; exact hvm_k.symm
  -- Step 3: πI = truncated.
  -- Rewriting `remaining_π` and the selected clause's variable list reduces
  -- πI to `truncated.filter (seg_k.map Prod.fst |>.contains ·.1)`, which is
  -- `truncated` because `truncated` is a prefix of `seg_k`.
  intro πI
  have hπ_i_eq_trunc : πI = truncated := by
    show remaining_π.filter _ = truncated
    rw [hrem_eq_trunc, h_r_ρ_eq_segk1]
    -- Goal: truncated.filter (fun x => seg_k.fst.contains x.1) = truncated.
    apply List.filter_eq_self.mpr
    intro p hp
    -- p ∈ truncated ⊆ seg_k.
    have hp_segk : p ∈ seg_k := List.mem_of_mem_take hp
    apply List.elem_eq_true_of_mem
    exact List.mem_map.mpr ⟨p, hp_segk, rfl⟩
  -- Step 4: remaining' = remaining_π.filter (¬πI.any ...) = []
  --       since πI = remaining_π and each elem matches itself.
  rw [List.filter_eq_nil_iff]
  intro p hp_rem hcond
  -- hcond says ¬(πI.any (·.1 == p.1)) — but p ∈ remaining_π = πI, contradiction.
  obtain ⟨pv, pb⟩ := p
  simp only at hcond
  have hp_πi : (pv, pb) ∈ πI := by
    rw [hπ_i_eq_trunc, ← hrem_eq_trunc]; exact hp_rem
  have hany_true : (πI.any fun (w', _) => w' == pv) = true := by
    rw [List.any_eq_true]
    exact ⟨(pv, pb), hp_πi, by simp⟩
  rw [hany_true] at hcond
  exact absurd hcond (by decide)

/- Supplies the encoder-faithful canonical segment index together with
   membership of earlier segment bits in `combineRestrictions ρ πI` and alignment of the
   selected segment head with `restrictionOfFirstTermNotKilledByList` under
   `combineRestrictions ρ πI`. -/
private lemma encoder_k_canonical_provider_from_loop_inv
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (ρ remaining_π : List (Nat × Bool))
    (hloop : EncoderLoopInv f.val asgn d path ρ remaining_π) :
    let πI := remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        |>.contains x.1)
    -- Post-step `remaining' ≠ []` (used to discharge straddler subcase
    -- via `encoder_alive_straddler_yields_remaining_post_step_nil`).
    remaining_π.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w)) ≠ [] →
    ∀ (segments : List (List (Nat × Bool) × List (Nat × Bool))),
      path = (segments.map Prod.fst).flatten →
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) f.val))
            (((segments.take j).map Prod.fst).flatten)
          = (segments[j]'hj).2 :: tail_j) →
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) →
      ∃ (k_canonical : Nat) (hk_lt : k_canonical < segments.length),
        1 ≤ k_canonical ∧
        -- Bits below k are already present in the combined restriction.
        (∀ (i : Nat) (hi : i < segments.length), 1 ≤ i → i < k_canonical →
          ∀ p ∈ (segments[i]'hi).1,
            ((combineRestrictions ρ πI).any fun (z, _) => z == p.1) = true) ∧
        -- R-form alignment at k_canonical.
        (segments[k_canonical]'hk_lt).2.map Prod.fst =
          (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
            (combineRestrictions ρ πI)).map Prod.fst ∧
        -- The encoder's truncated iter-split equation:
        -- `combineRestrictions ρ πI` is exactly `asgn` extended by the
        -- first `k_canonical` segments of `segments`.  This is the
        -- precise form that the consumer needs to bridge `consumed' ↔
        -- ((segments.take k_canonical).map fst).flatten`.
        combineRestrictions ρ πI =
          asgn ++ ((segments.take k_canonical).map Prod.fst).flatten := by
  intro πI hrem_ne segments hseg_cat hseg_prov hvm_seg
  -- Step 0: standing facts.
  have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hloop.hpath
  -- Step 1: unpack the bundle's canonical iter-split witness.
  obtain ⟨segs_canon, k_bundle, partial_seg, hpath_canon, hk_le,
          hcanon_prov, hvm_canon, hne_canon_within_d, hρ_eq, h_two_case⟩ :=
    hloop.hρ_segments_consumed
  -- Step 2: identify user `segments` with bundle `segs_canon` pointwise via
  -- `iter_split_first_k_eq`.
  have hsegs_take_eq :
      ∀ (K : Nat) (_h_k1 : K ≤ segments.length) (_h_k2 : K ≤ segs_canon.length),
        segments.take K = segs_canon.take K := by
    intro K h_k1 h_k2
    exact iter_split_first_k_eq
      (dnfClauses (simpleRestrictDNF
        (restrictionAsFunction asgn) f.val))
      path segments segs_canon hseg_cat hpath_canon
      hseg_prov hcanon_prov hvm_seg hvm_canon K h_k1 h_k2
  -- Step 3: case on the bundle discriminant.
  rcases h_two_case with
    ⟨hpartial_nil, hrem_alive, hwindow_canon⟩ |
    ⟨hk_lt_canon, hpartial_sub, hrem_terminal⟩
  · -- ───────── ALIVE CASE: partial_seg = [], remaining_π = drop_k_filter.
    rw [hpartial_nil, List.append_nil] at hρ_eq
    by_cases hk_eq_len : k_bundle = segs_canon.length
    · -- ALIVE-FULL: k_bundle = segs_canon.length.  Then
      -- `(segs_canon.drop k_bundle) = []`, so `remaining_π = [].filter = []`,
      -- so `remaining' = []`, contradicting `hrem_ne`.
      exfalso
      apply hrem_ne
      have hdrop_nil :
          ((segs_canon.drop k_bundle).map Prod.fst).flatten = [] := by
        rw [hk_eq_len, List.drop_length]; rfl
      have hrem_nil : remaining_π = [] := by
        rw [hrem_alive, hdrop_nil]; rfl
      rw [hrem_nil]; rfl
    · -- ALIVE-PROPER: k_bundle < segs_canon.length.
      have hk_canon_lt : k_bundle < segs_canon.length :=
        lt_of_le_of_ne hk_le hk_eq_len
      -- The straddler case contradicts the canonical prefix bounds.
      by_cases h_straddler :
          ¬ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten.length ≤ d
      · push Not at h_straddler
        -- Establish the cumulative prefix length bound.
        have h_prefix_k_le_d :
            (((segs_canon.take k_bundle).map Prod.fst).flatten).length ≤ d := by
          have hprefix_pre :
              ((segs_canon.take k_bundle).map Prod.fst).flatten <+: path := by
            rw [hpath_canon]
            exact List.IsPrefix.flatten (List.IsPrefix.map _ (List.take_prefix _ _))
          have hprefix_nodup :
              (((segs_canon.take k_bundle).map Prod.fst).flatten).Nodup :=
            (List.Nodup.of_map _ hpath_nodup_fst).sublist hprefix_pre.sublist
          have h_sub :
              ∀ p ∈ ((segs_canon.take k_bundle).map Prod.fst).flatten,
                p ∈ path.take d := by
            intro p hp
            have hp_ρ : p ∈ ρ := by
              rw [hρ_eq]; exact List.mem_append_right asgn hp
            have hp_path : p ∈ path := hprefix_pre.subset hp
            rcases hloop.hρ_sub_orig p.1 p.2 hp_ρ with hp_asgn | hp_take
            · exfalso
              have hnone := canonical_dt_path_var_none f.val asgn
                f.property.2 d path hloop.hpath p.1 p.2 hp_path
              simp only [restrictionAsFunction] at hnone
              have hfind_some : asgn.find? (fun q => q.1 == p.1) ≠ none := by
                rw [Ne, List.find?_eq_none]; push Not
                exact ⟨p, hp_asgn, by simp⟩
              rcases hf : asgn.find? (fun q => q.1 == p.1) with _ | ⟨_,_⟩
              · exact hfind_some hf
              · rw [hf] at hnone; cases hnone
            · exact hp_take
          have hsubperm :
              List.Subperm (((segs_canon.take k_bundle).map Prod.fst).flatten)
                (path.take d) :=
            hprefix_nodup.subperm h_sub
          have htake_le_d : (path.take d).length ≤ d := by
            rw [List.length_take]; exact Nat.min_le_left d _
          exact Nat.le_trans hsubperm.length_le htake_le_d
        exfalso
        exact hrem_ne (encoder_alive_straddler_yields_remaining_post_step_nil
          f hnodup asgn d path hloop.hpath ρ remaining_π
          segs_canon k_bundle hk_canon_lt hpath_canon hcanon_prov hvm_canon
          hρ_eq hrem_alive h_prefix_k_le_d h_straddler)
      push Not at h_straddler
      -- h_straddler : prefix_{k+1}.length ≤ d  (the non-straddler bound).
      by_cases hsucc_lt : k_bundle + 1 < segs_canon.length
      · -- ───────── ALIVE-NON-EDGE (the "good" case).
        -- Returns ⟨k_bundle + 1, hsucc_lt_seg, ..., h_below_k, alignment⟩.
        -- (a) hwindow: every bit of segs_canon[k_bundle].1 lies in path.take d.
        have hwindow :
            ∀ p ∈ (segs_canon[k_bundle]'hk_canon_lt).1, p ∈ path.take d :=
          hwindow_canon hk_canon_lt h_straddler
        -- (b) πI = segs_canon[k_bundle].1.
        have hπ_i_eq : πI = (segs_canon[k_bundle]'hk_canon_lt).1 := by
          show remaining_π.filter _ = _
          rw [hrem_alive]
          exact pi_eq_segments_k_alive f asgn hnodup d path hloop.hpath segs_canon
            hpath_canon hcanon_prov hvm_canon k_bundle hk_canon_lt hwindow ρ hρ_eq
        -- (c) combineRestrictions ρ πI = asgn ++ prefix_{k+1}_canon.
        have h_combined_eq : combineRestrictions ρ πI =
            asgn ++ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
          rw [hπ_i_eq]
          exact combined_alive_eq_canonical_prefix_succ f asgn hnodup d path hloop.hpath
            segs_canon hpath_canon k_bundle hk_canon_lt ρ hρ_eq
        -- (d) Align the selected clause after the step with the next segment head.
        have h_rhs_seg :
            (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
              (combineRestrictions ρ πI)).map Prod.fst =
            (segs_canon[k_bundle + 1]'hsucc_lt).2.map Prod.fst := by
          have h := iter_split_seg_eq_rtnkb_at_canonical_prefix f asgn hnodup d path
            hloop.hpath segs_canon hpath_canon hcanon_prov (k_bundle + 1) hsucc_lt
          have h_combined_asgn_eq :
              combineRestrictions asgn
                (((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten) =
              asgn ++ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
            unfold combineRestrictions
            congr 1
            apply List.filter_eq_self.mpr
            intro p hp
            rw [Bool.not_eq_true']
            have hp_path : p ∈ path := by
              rw [hpath_canon]
              exact (List.IsPrefix.flatten
                (List.IsPrefix.map _ (List.take_prefix _ _))).subset hp
            have hnone := canonical_dt_path_var_none f.val asgn
              f.property.2 d path hloop.hpath p.1 p.2 hp_path
            cases hany : asgn.any fun (z, _) => z == p.1
            · rfl
            · exfalso
              rw [List.any_eq_true] at hany
              obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
              simp at hw'_eq; subst hw'_eq
              simp only [restrictionAsFunction] at hnone
              have hfind : asgn.find? (fun q => q.1 == p.1) ≠ none := by
                rw [Ne, List.find?_eq_none]; push Not
                exact ⟨(p.1, b'), hw'_mem, by simp⟩
              rcases hfind_eq : asgn.find? (fun q => q.1 == p.1)
                with _ | ⟨_, _⟩
              · exact hfind hfind_eq
              · rw [hfind_eq] at hnone; cases hnone
          have h_r_combined_eq :
              restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
                (combineRestrictions ρ πI) =
              restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
                (combineRestrictions asgn
                  (((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten)) := by
            rw [h_combined_eq, h_combined_asgn_eq]
          rw [h_r_combined_eq]; exact h.symm
        -- (e) hsucc_lt_seg: k_bundle + 1 < segments.length.
        have hsucc_lt_seg : k_bundle + 1 < segments.length := by
          by_contra hge
          push Not at hge
          set L : Nat := segments.length with h_l_def
          have h_l_le_canon : L ≤ segs_canon.length :=
            Nat.le_trans hge (Nat.le_of_lt hsucc_lt)
          have h_l_le_seg : L ≤ segments.length := le_refl _
          have htake_eq :
              segments.take L = segs_canon.take L :=
            hsegs_take_eq L h_l_le_seg h_l_le_canon
          have hseg_eq : segments = segs_canon.take L := by
            calc segments
                _ = segments.take L := by rw [h_l_def]; exact List.take_length.symm
                _ = segs_canon.take L := htake_eq
          have hpath_le :
              path.length ≤
                ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten.length := by
            have hpath_eq2 :
                path = ((segs_canon.take L).map Prod.fst).flatten := by
              rw [hseg_cat, hseg_eq]
            rw [hpath_eq2]
            have hsub_take :
                segs_canon.take L
                  = (segs_canon.take (k_bundle + 1)).take L := by
              rw [List.take_take, Nat.min_eq_left hge]
            rw [hsub_take]
            exact (List.IsPrefix.flatten
              (List.IsPrefix.map _ (List.take_prefix _ _))).length_le
          have hpath_gt : path.length > d :=
            leftmostPathExceedingDepth_some_path_length_gt _ _ _ hloop.hpath
          omega
        -- (f) hsegs_at_succ: segments[k+1].2 = segs_canon[k+1].2.
        have hsegs_at_succ :
            (segments[k_bundle + 1]'hsucc_lt_seg).2
              = (segs_canon[k_bundle + 1]'hsucc_lt).2 := by
          have h_k1 : k_bundle + 2 ≤ segments.length := hsucc_lt_seg
          have h_k2 : k_bundle + 2 ≤ segs_canon.length := hsucc_lt
          have htake_eq : segments.take (k_bundle + 2) = segs_canon.take (k_bundle + 2) :=
            hsegs_take_eq (k_bundle + 2) h_k1 h_k2
          have hpair_eq :
              segments[k_bundle + 1]'hsucc_lt_seg
                = segs_canon[k_bundle + 1]'hsucc_lt := by
            have hlt_take : k_bundle + 1 < (segments.take (k_bundle + 2)).length := by
              rw [List.length_take]; omega
            have hlt_take' : k_bundle + 1 < (segs_canon.take (k_bundle + 2)).length := by
              rw [List.length_take]; omega
            have h1 :
                (segments.take (k_bundle + 2))[k_bundle + 1]'hlt_take
                  = segments[k_bundle + 1]'hsucc_lt_seg :=
              List.getElem_take ..
            have h2 :
                (segs_canon.take (k_bundle + 2))[k_bundle + 1]'hlt_take'
                  = segs_canon[k_bundle + 1]'hsucc_lt :=
              List.getElem_take ..
            calc segments[k_bundle + 1]'hsucc_lt_seg
                _ = (segments.take (k_bundle + 2))[k_bundle + 1]'hlt_take := h1.symm
                _ = (segs_canon.take (k_bundle + 2))[k_bundle + 1]'hlt_take' := by
                      congr 1
                _ = segs_canon[k_bundle + 1]'hsucc_lt := h2
          exact congrArg Prod.snd hpair_eq
        -- (g) below-k-in-combineRestrictions: every bit of segments[i].1 (for 1 ≤ i ≤ k_bundle)
        --     is in combineRestrictions = asgn ++ prefix_{k+1}_canon.
        have h_below_k :
            ∀ (i : Nat) (hi : i < segments.length), 1 ≤ i → i < k_bundle + 1 →
              ∀ p ∈ (segments[i]'hi).1,
                ((combineRestrictions ρ πI).any fun (z, _) => z == p.1) = true := by
          intro i hi _hi_pos hi_lt p hp
          -- Identify segments[i] with segs_canon[i] via hsegs_take_eq at K=k_bundle+1.
          have hi_canon : i < segs_canon.length := Nat.lt_of_lt_of_le hi_lt hsucc_lt.le
          have h_k1 : k_bundle + 1 ≤ segments.length := Nat.le_of_lt hsucc_lt_seg
          have h_k2 : k_bundle + 1 ≤ segs_canon.length := Nat.le_of_lt hsucc_lt
          have htake_eq : segments.take (k_bundle + 1) = segs_canon.take (k_bundle + 1) :=
            hsegs_take_eq (k_bundle + 1) h_k1 h_k2
          have hlt_take : i < (segments.take (k_bundle + 1)).length := by
            rw [List.length_take]; omega
          have hlt_take' : i < (segs_canon.take (k_bundle + 1)).length := by
            rw [List.length_take]; omega
          have hpair_eq :
              segments[i]'hi = segs_canon[i]'hi_canon := by
            calc segments[i]'hi
                _ = (segments.take (k_bundle + 1))[i]'hlt_take :=
                  (List.getElem_take ..).symm
                _ = (segs_canon.take (k_bundle + 1))[i]'hlt_take' := by congr 1
                _ = segs_canon[i]'hi_canon := List.getElem_take ..
          rw [hpair_eq] at hp
          -- p ∈ segs_canon[i].1 ⊆ prefix_{k+1}_canon ⊆ combineRestrictions ρ πI.
          have hp_in_prefix :
              p ∈ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
            rw [List.mem_flatten]
            refine ⟨(segs_canon[i]'hi_canon).1, ?_, hp⟩
            rw [List.mem_map]
            refine ⟨segs_canon[i]'hi_canon, ?_, rfl⟩
            rw [List.mem_iff_getElem]
            exact ⟨i, hlt_take', List.getElem_take ..⟩
          have hp_combined : p ∈ combineRestrictions ρ πI := by
            rw [h_combined_eq]; exact List.mem_append_right asgn hp_in_prefix
          exact List.any_eq_true.mpr ⟨p, hp_combined, by simp⟩
        -- (h) Assemble the existential.
        refine ⟨k_bundle + 1, hsucc_lt_seg, Nat.succ_le_succ (Nat.zero_le _),
                h_below_k, ?_, ?_⟩
        -- Align the next supplied segment with the selected clause after the step.
        · rw [hsegs_at_succ, h_rhs_seg]
        -- Transfer `h_combined_eq` from `segs_canon` to the supplied segments.
        · -- segments.take (k_bundle+1) = segs_canon.take (k_bundle+1) by hsegs_take_eq.
          have h_k1 : k_bundle + 1 ≤ segments.length := Nat.le_of_lt hsucc_lt_seg
          have h_k2 : k_bundle + 1 ≤ segs_canon.length := Nat.le_of_lt hsucc_lt
          have htake_eq :
              segments.take (k_bundle + 1) = segs_canon.take (k_bundle + 1) :=
            hsegs_take_eq (k_bundle + 1) h_k1 h_k2
          rw [htake_eq]
          exact h_combined_eq
      · -- ALIVE-PROPER-EDGE: k_bundle + 1 = segs_canon.length.
        -- The non-straddler bound `h_straddler : prefix_{k+1}.length ≤ d`
        -- becomes `path.length ≤ d` (since `take (k+1) = take len = full`),
        -- contradicting canonical-DT's `path.length > d`.
        exfalso
        push Not at hsucc_lt
        -- hsucc_lt : segs_canon.length ≤ k_bundle + 1; combined with
        -- hk_canon_lt : k_bundle < segs_canon.length, get k+1 = segs_canon.length.
        have hk_succ_eq : k_bundle + 1 = segs_canon.length := by omega
        have htake_full : segs_canon.take (k_bundle + 1) = segs_canon := by
          rw [hk_succ_eq]; exact List.take_length
        have hpath_le : path.length ≤ d := by
          have : path = ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
            rw [htake_full]; exact hpath_canon
          rw [this]; exact h_straddler
        have hpath_gt : path.length > d :=
          leftmostPathExceedingDepth_some_path_length_gt _ _ _ hloop.hpath
        omega
  · -- ───────── TERMINAL CASE: bundle gives `remaining_π = []` directly,
    -- so `remaining' = []`, contradicting `hrem_ne`.
    exfalso
    apply hrem_ne
    rw [hrem_terminal]
    rfl

#print axioms encoder_k_canonical_provider_from_loop_inv


/- Proves that the selected clause under `combineRestrictions ρ πI` is nonempty from
    the bundle `EncoderLoopInv` under the precondition `remaining' ≠ []`.

    Used to discharge the `h_r_combined_ne` parameter of
    `encoder_path_prefix_after_one_step` at the encoder-loop level.

    **Strategy.**
    1. Apply `encoder_k_canonical_provider_from_loop_inv` with `segments := segs_canon`
       (from the bundle) to obtain `k_canonical` and the equation
       `combineRestrictions ρ πI = asgn ++ ((segs_canon.take k_canonical).fst).flatten`.
    2. Apply `r_ne_nil_via_canonical_iter_split` with
       `consumed := ((segs_canon.take k_canonical).fst).flatten` to obtain
       nonemptiness under `combineRestrictions asgn consumed`.
    3. Since `consumed` consists of canonical-DT path bits, every
       `v ∈ consumed.fst` satisfies `asgn_fn v = none`;
       hence `consumed.filter (asgn-disjoint) = consumed`, and so
       `combineRestrictions asgn consumed = asgn ++ consumed = combineRestrictions ρ πI`.
    -/
private lemma encoder_h_r_combined_ne_from_loop_inv
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (ρ remaining_π : List (Nat × Bool))
    (hloop : EncoderLoopInv f.val asgn d path ρ remaining_π) :
    let πI := remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        |>.contains x.1)
    remaining_π.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w)) ≠ [] →
    restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions ρ πI) ≠ [] := by
  intro πI hrem_post_ne
  -- Unpack the bundle's canonical iter-split.
  obtain ⟨segs_canon, k_bundle, partial_seg, hpath_canon, hk_le,
          hcanon_prov, hvm_canon, _hne_within, _hρ_eq, _h_two_case⟩ :=
    hloop.hρ_segments_consumed
  -- Reformat vars-match from per-element to per-index for `r_ne_nil_via_canonical_iter_split`.
  have hvm_canon_idx : ∀ (j : Nat) (hj : j < segs_canon.length),
      (segs_canon[j]'hj).1.map Prod.fst = (segs_canon[j]'hj).2.map Prod.fst := by
    intro j hj
    exact hvm_canon (segs_canon[j]'hj) (List.getElem_mem hj)
  -- Apply the canonical-k provider with `segments := segs_canon`.
  obtain ⟨k_can, hk_lt, _hk_pos, _h_below_k, _h_align, h_combined_eq⟩ :=
    encoder_k_canonical_provider_from_loop_inv f hnodup asgn d path
      ρ remaining_π hloop hrem_post_ne segs_canon hpath_canon hcanon_prov hvm_canon
  -- Set `consumed = ((segs_canon.take k_can).fst).flatten`.
  set consumed : List (Nat × Bool) :=
    ((segs_canon.take k_can).map Prod.fst).flatten with hconsumed_def
  -- Show `consumed ⊆ path.take d` via `combineRestrictions ρ πI = asgn ++ consumed`,
  -- and the fact that bits of combineRestrictions are either ρ-bits (⊆ asgn ∪ path.take d)
  -- or πI-bits (⊆ remaining_π ⊆ path.take d), and consumed bits are
  -- asgn-disjoint (path bits unassigned by `canonical_dt_path_var_none`).
  -- ── First: every `p ∈ consumed` is a path bit.
  have hconsumed_in_path : ∀ p ∈ consumed, p ∈ path := by
    intro p hp
    -- consumed ⊆ ((segs_canon).fst).flatten = path
    have : ((segs_canon.take k_can).map Prod.fst).flatten ⊆
        (segs_canon.map Prod.fst).flatten := by
      intro x hx
      rw [List.mem_flatten] at hx ⊢
      obtain ⟨L, h_l_mem, hx_l⟩ := hx
      obtain ⟨seg, hseg_in_take, hseg_eq⟩ := List.mem_map.mp h_l_mem
      refine ⟨L, ?_, hx_l⟩
      exact List.mem_map.mpr ⟨seg, List.mem_of_mem_take hseg_in_take, hseg_eq⟩
    rw [hpath_canon]
    exact this hp
  -- ── Second: every `p ∈ consumed` has `asgn_fn p.1 = none` (path bit unassigned).
  have hconsumed_asgn_none :
      ∀ p ∈ consumed, restrictionAsFunction asgn p.1 = none := by
    intro p hp
    obtain ⟨q, b⟩ := p
    exact canonical_dt_path_var_none f.val asgn f.property.2
      d path hloop.hpath q b (hconsumed_in_path (q, b) hp)
  -- ── Third: every `p ∈ consumed` is asgn-disjoint as a list-membership predicate.
  have hconsumed_asgn_disj :
      ∀ p ∈ consumed, (asgn.any fun q => q.1 == p.1) = false := by
    intro p hp
    cases h : asgn.any (fun q => q.1 == p.1) with
    | false => rfl
    | true =>
      exfalso
      rw [List.any_eq_true] at h
      obtain ⟨q, hq, hqeq⟩ := h
      have hsome : (restrictionAsFunction asgn p.1).isSome = true := by
        rw [← list_any_eq_cr_none_isSome asgn p.1, List.any_eq_true]
        exact ⟨q, hq, hqeq⟩
      rw [hconsumed_asgn_none p hp] at hsome
      simp at hsome
  -- ── Fourth: every `p ∈ consumed` is in `path.take d`, derived from `h_combined_eq`.
  -- Strategy: p ∈ consumed = combineRestrictions ρ πI minus asgn-prefix. combineRestrictions ρ πI = ρ ++ πI_filt.
  -- p ∈ ρ: by hloop.hρ_sub_orig, p ∈ asgn ∨ p ∈ path.take d.  But p asgn-disjoint
  --        (above) excludes p ∈ asgn, so p ∈ path.take d.
  -- p ∈ πI_filt ⊆ πI ⊆ remaining_π ⊆ path.take d (via hloop.hrem_sub_outer).
  have hconsumed_in_window : ∀ p ∈ consumed, p ∈ path.take d := by
    intro p hp
    have hp_combined : p ∈ combineRestrictions ρ πI := by
      rw [h_combined_eq]; exact List.mem_append_right asgn hp
    -- Unfold combineRestrictions: p ∈ ρ ∨ p ∈ πI.filter(¬ρ.any)
    have hp_cases : p ∈ ρ ∨ p ∈ πI.filter
        (fun (v, _) => !ρ.any fun (w, _) => w == v) := by
      change p ∈ ρ ++ πI.filter (fun (v, _) => !ρ.any fun (w, _) => w == v) at hp_combined
      exact List.mem_append.mp hp_combined
    rcases hp_cases with hp_ρ | hp_πf
    · obtain ⟨q, b⟩ := p
      rcases hloop.hρ_sub_orig q b hp_ρ with hp_asgn | hp_take
      · exfalso
        have hany : (asgn.any fun r => r.1 == q) = true := by
          rw [List.any_eq_true]; exact ⟨(q, b), hp_asgn, by simp⟩
        have hany_false := hconsumed_asgn_disj (q, b) hp
        rw [hany] at hany_false
        exact absurd hany_false (by decide)
      · exact hp_take
    · have hp_πi : p ∈ πI := List.mem_of_mem_filter hp_πf
      exact hloop.hrem_sub_outer p (List.mem_of_mem_filter hp_πi)
  -- Apply `r_ne_nil_via_canonical_iter_split`.
  have h_r_outer :=
    r_ne_nil_via_canonical_iter_split f hnodup asgn d path hloop.hpath
      segs_canon k_can hpath_canon (Nat.le_of_lt hk_lt) hcanon_prov hvm_canon_idx
      consumed rfl hconsumed_in_window
  -- Bridge the two combined restrictions through their induced functions.
  have hfilter_id : consumed.filter
      (fun p => !asgn.any fun q => q.1 == p.1) = consumed :=
    List.filter_eq_self.mpr (fun p hp => by
      rw [hconsumed_asgn_disj p hp]; rfl)
  -- combineRestrictions asgn consumed = asgn ++ consumed (via filter id)
  have h_combined_asgn_eq : combineRestrictions asgn consumed = asgn ++ consumed := by
    show asgn ++ consumed.filter (fun p => !asgn.any fun q => q.1 == p.1)
        = asgn ++ consumed
    rw [hfilter_id]
  -- And combineRestrictions ρ πI = asgn ++ consumed (from h_combined_eq).
  -- Thus combineRestrictions asgn consumed = combineRestrictions ρ πI (literal).
  have h_combined_lists_eq :
      combineRestrictions asgn consumed = combineRestrictions ρ πI := by
    rw [h_combined_asgn_eq, ← h_combined_eq]
  rw [h_combined_lists_eq] at h_r_outer
  exact h_r_outer

/- Compares the selected clause's variables under `combineRestrictions ρ πI`
   with the variables remaining after the current encoder step; one list is a
   prefix of the other. -/
private lemma encoder_h_r_combined_pref_from_loop_inv
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (ρ remaining_π : List (Nat × Bool))
    (hloop : EncoderLoopInv f.val asgn d path ρ remaining_π) :
    let πI := remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses f.val) ρ).map Prod.fst
        |>.contains x.1)
    remaining_π.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w)) ≠ [] →
    (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
      (combineRestrictions ρ πI)).map Prod.fst
      <+: (remaining_π.filter (fun (w, _) =>
        !πI.any (fun (w', _) => w' == w))).map Prod.fst ∨
    (remaining_π.filter (fun (w, _) =>
      !πI.any (fun (w', _) => w' == w))).map Prod.fst
      <+: (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
        (combineRestrictions ρ πI)).map Prod.fst := by
  intro πI hrem_post_ne
  -- ─── Step 1: standing facts. ────────────────────────────────────
  have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst f.val asgn hnodup d path hloop.hpath
  -- ─── Step 2: unpack the bundle's canonical iter-split. ──────────
  obtain ⟨segs_canon, k_bundle, partial_seg, hpath_canon, hk_le,
          hcanon_prov, hvm_canon, _hne_within, hρ_eq, h_two_case⟩ :=
    hloop.hρ_segments_consumed
  -- ─── Step 3: case on the bundle discriminant. ───────────────────
  rcases h_two_case with
    ⟨hpartial_nil, hrem_alive, hwindow_canon⟩ |
    ⟨hk_lt_canon, _hpartial_sub, hrem_terminal⟩
  · -- ALIVE CASE.
    rw [hpartial_nil, List.append_nil] at hρ_eq
    by_cases hk_eq_len : k_bundle = segs_canon.length
    · -- ALIVE-FULL: drop = []; remaining_π = []; remaining' = [] — contradicts hrem_post_ne.
      exfalso; apply hrem_post_ne
      have hdrop_nil :
          ((segs_canon.drop k_bundle).map Prod.fst).flatten = [] := by
        rw [hk_eq_len, List.drop_length]; rfl
      have hrem_nil : remaining_π = [] := by
        rw [hrem_alive, hdrop_nil]; rfl
      rw [hrem_nil]; rfl
    · have hk_canon_lt : k_bundle < segs_canon.length :=
        lt_of_le_of_ne hk_le hk_eq_len
      by_cases h_straddler :
          ¬ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten.length ≤ d
      · -- ALIVE-STRADDLER: existing helper says remaining' = [].
        push Not at h_straddler
        have h_prefix_k_le_d :
            (((segs_canon.take k_bundle).map Prod.fst).flatten).length ≤ d := by
          have hprefix_pre :
              ((segs_canon.take k_bundle).map Prod.fst).flatten <+: path := by
            rw [hpath_canon]
            exact List.IsPrefix.flatten (List.IsPrefix.map _ (List.take_prefix _ _))
          have hprefix_nodup :
              (((segs_canon.take k_bundle).map Prod.fst).flatten).Nodup :=
            (List.Nodup.of_map _ hpath_nodup_fst).sublist hprefix_pre.sublist
          have h_sub :
              ∀ p ∈ ((segs_canon.take k_bundle).map Prod.fst).flatten,
                p ∈ path.take d := by
            intro p hp
            have hp_ρ : p ∈ ρ := by
              rw [hρ_eq]; exact List.mem_append_right asgn hp
            have hp_path : p ∈ path := hprefix_pre.subset hp
            rcases hloop.hρ_sub_orig p.1 p.2 hp_ρ with hp_asgn | hp_take
            · exfalso
              have hnone := canonical_dt_path_var_none f.val asgn
                f.property.2 d path hloop.hpath p.1 p.2 hp_path
              simp only [restrictionAsFunction] at hnone
              have hfind_some : asgn.find? (fun q => q.1 == p.1) ≠ none := by
                rw [Ne, List.find?_eq_none]; push Not
                exact ⟨p, hp_asgn, by simp⟩
              rcases hf : asgn.find? (fun q => q.1 == p.1) with _ | ⟨_,_⟩
              · exact hfind_some hf
              · rw [hf] at hnone; cases hnone
            · exact hp_take
          have hsubperm := hprefix_nodup.subperm h_sub
          have htake_le_d : (path.take d).length ≤ d := by
            rw [List.length_take]; exact Nat.min_le_left d _
          exact Nat.le_trans hsubperm.length_le htake_le_d
        exfalso
        exact hrem_post_ne (encoder_alive_straddler_yields_remaining_post_step_nil
          f hnodup asgn d path hloop.hpath ρ remaining_π
          segs_canon k_bundle hk_canon_lt hpath_canon hcanon_prov hvm_canon
          hρ_eq hrem_alive h_prefix_k_le_d h_straddler)
      push Not at h_straddler
      by_cases hsucc_lt : k_bundle + 1 < segs_canon.length
      · -- ALIVE-NON-EDGE: the productive case.
        have hwindow :
            ∀ p ∈ (segs_canon[k_bundle]'hk_canon_lt).1, p ∈ path.take d :=
          hwindow_canon hk_canon_lt h_straddler
        have hπ_i_eq : πI = (segs_canon[k_bundle]'hk_canon_lt).1 := by
          show remaining_π.filter _ = _
          rw [hrem_alive]
          exact pi_eq_segments_k_alive f asgn hnodup d path hloop.hpath segs_canon
            hpath_canon hcanon_prov hvm_canon k_bundle hk_canon_lt hwindow ρ hρ_eq
        have h_combined_eq : combineRestrictions ρ πI =
            asgn ++ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
          rw [hπ_i_eq]
          exact combined_alive_eq_canonical_prefix_succ f asgn hnodup d path hloop.hpath
            segs_canon hpath_canon k_bundle hk_canon_lt ρ hρ_eq
        -- Align the selected clause after the step with the next segment path.
        have h_rhs_seg :
            (restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
              (combineRestrictions ρ πI)).map Prod.fst =
            (segs_canon[k_bundle + 1]'hsucc_lt).1.map Prod.fst := by
          have h := iter_split_seg_eq_rtnkb_at_canonical_prefix f asgn hnodup d path
            hloop.hpath segs_canon hpath_canon hcanon_prov (k_bundle + 1) hsucc_lt
          have h_combined_asgn_eq :
              combineRestrictions asgn
                (((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten) =
              asgn ++ ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
            unfold combineRestrictions
            congr 1
            apply List.filter_eq_self.mpr
            intro p hp
            rw [Bool.not_eq_true']
            have hp_path : p ∈ path := by
              rw [hpath_canon]
              exact (List.IsPrefix.flatten
                (List.IsPrefix.map _ (List.take_prefix _ _))).subset hp
            have hnone := canonical_dt_path_var_none f.val asgn
              f.property.2 d path hloop.hpath p.1 p.2 hp_path
            cases hany : asgn.any fun (z, _) => z == p.1
            · rfl
            · exfalso
              rw [List.any_eq_true] at hany
              obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
              simp at hw'_eq; subst hw'_eq
              simp only [restrictionAsFunction] at hnone
              have hfind : asgn.find? (fun q => q.1 == p.1) ≠ none := by
                rw [Ne, List.find?_eq_none]; push Not
                exact ⟨(p.1, b'), hw'_mem, by simp⟩
              rcases hfind_eq : asgn.find? (fun q => q.1 == p.1)
                with _ | ⟨_, _⟩
              · exact hfind hfind_eq
              · rw [hfind_eq] at hnone; cases hnone
          have h_r_combined_eq :
              restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
                (combineRestrictions ρ πI) =
              restrictionOfFirstTermNotKilledByList (dnfClauses f.val)
                (combineRestrictions asgn
                  (((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten)) := by
            rw [h_combined_eq, h_combined_asgn_eq]
          rw [h_r_combined_eq, h.symm]
          exact (hvm_canon _ (List.getElem_mem hsucc_lt)).symm
        rw [h_rhs_seg]
        -- ─── Step 4 (PRODUCTIVE BRANCH PROOF) ─────────────────────
        -- Step A: derive `remaining' = drop_{k+1}.flatten.filter window`.
        --
        -- From hrem_alive (= drop_k.flatten.filter window), hπ_i_eq (= σk),
        -- σk ⊆ window (= hwindow), and path-nodup-fst disjointness of
        -- σk-vars from drop_{k+1} bits.
        have hdrop_k_eq : segs_canon.drop k_bundle =
            (segs_canon[k_bundle]'hk_canon_lt) :: segs_canon.drop (k_bundle + 1) :=
          List.drop_eq_getElem_cons hk_canon_lt
        have hdrop_k_flat_eq :
            ((segs_canon.drop k_bundle).map Prod.fst).flatten
              = (segs_canon[k_bundle]'hk_canon_lt).1
                  ++ ((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten := by
          rw [hdrop_k_eq, List.map_cons, List.flatten_cons]
        -- path-fst nodup decomposition into prefix_k.fst ++ σk.fst ++ rest_flat.fst.
        have hpath_fst_split :
            path.map Prod.fst =
              ((((segs_canon.take k_bundle).map Prod.fst).flatten).map Prod.fst
                ++ ((segs_canon[k_bundle]'hk_canon_lt).1).map Prod.fst)
                ++ (((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten).map Prod.fst := by
          rw [hpath_canon]
          have hsplit :
              segs_canon = segs_canon.take k_bundle ++ segs_canon.drop k_bundle :=
            (List.take_append_drop k_bundle segs_canon).symm
          conv_lhs => rw [hsplit]
          rw [hdrop_k_eq, List.map_append, List.map_cons,
              List.flatten_append, List.flatten_cons,
              List.map_append, List.map_append]
          ac_rfl
        have hndp :
            ((((segs_canon.take k_bundle).map Prod.fst).flatten).map Prod.fst
              ++ ((segs_canon[k_bundle]'hk_canon_lt).1).map Prod.fst
              ++ (((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten).map Prod.fst).Nodup := by
          rw [← hpath_fst_split]; exact hpath_nodup_fst
        have hdisj := List.disjoint_of_nodup_append hndp
        -- The window predicate (literal expansion).
        -- σk passes window everywhere.
        have hfilt_σk_window :
            (segs_canon[k_bundle]'hk_canon_lt).1.filter
              (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2))
              = (segs_canon[k_bundle]'hk_canon_lt).1 := by
          apply List.filter_eq_self.mpr
          intro p hp
          exact List.any_eq_true.mpr ⟨p, hwindow p hp, by simp⟩
        -- σk filtered by ¬σk.any = [].
        have hfilt_σk_πi :
            (segs_canon[k_bundle]'hk_canon_lt).1.filter
              (fun (w, _) => !πI.any (fun (w', _) => w' == w)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro p hp
          simp only [Bool.not_eq_true', Bool.not_eq_false]
          rw [hπ_i_eq]
          exact List.any_eq_true.mpr ⟨p, hp, by simp⟩
        -- Tail elements pass ¬σk.any (disjointness).
        have h_tail_passes_πi :
            ∀ p ∈ ((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten.filter
              (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)),
              (!πI.any (fun (w', _) => w' == p.1)) = true := by
          intro p hp_filt
          have hp_rest : p ∈ ((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten :=
            List.mem_of_mem_filter hp_filt
          have hp1_in_rest :
              p.1 ∈ (((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten).map Prod.fst :=
            List.mem_map.mpr ⟨p, hp_rest, rfl⟩
          rw [hπ_i_eq, Bool.not_eq_true']
          cases hany : (segs_canon[k_bundle]'hk_canon_lt).1.any (fun (w', _) => w' == p.1)
          · rfl
          · exfalso
            rw [List.any_eq_true] at hany
            obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
            simp at hw'_eq; subst hw'_eq
            have hp1_in_σk : p.1 ∈ (segs_canon[k_bundle]'hk_canon_lt).1.map Prod.fst :=
              List.mem_map.mpr ⟨(p.1, b'), hw'_mem, rfl⟩
            have hp1_in_left :
                p.1 ∈ (((segs_canon.take k_bundle).map Prod.fst).flatten).map Prod.fst
                        ++ (segs_canon[k_bundle]'hk_canon_lt).1.map Prod.fst :=
              List.mem_append_right _ hp1_in_σk
            exact hdisj hp1_in_left hp1_in_rest
        -- Now the main computation.
        have hrem' :
            remaining_π.filter (fun (w, _) => !πI.any (fun (w', _) => w' == w))
              = ((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten.filter
                  (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) := by
          rw [hrem_alive, hdrop_k_flat_eq, List.filter_append, hfilt_σk_window,
              List.filter_append, hfilt_σk_πi, List.nil_append]
          exact List.filter_eq_self.mpr h_tail_passes_πi
        rw [hrem']
        -- Step B: case split on whether segment k_bundle+1 is itself a straddler.
        by_cases h_kp2_strad :
            d < ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten.length
        · -- STRADDLER subcase: remaining' = β.take m, prefix of β.
          right
          have h := remaining_π_eq_truncated_at_alive_straddler
            f asgn hnodup d path hloop.hpath segs_canon hpath_canon
            (k_bundle + 1) hsucc_lt h_straddler h_kp2_strad
          rw [h, List.map_take]
          exact List.take_prefix _ _
        · -- NON-STRADDLER subcase: β ⊆ window, β prefix of remaining'.
          push Not at h_kp2_strad
          left
          -- Show β ⊆ path.take d via prefix_{k+2}.flatten <+: path.take d.
          have hpref_kp2_eq :
              ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten
                = ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten
                    ++ (segs_canon[k_bundle + 1]'hsucc_lt).1 := by
            have htake_eq : segs_canon.take (k_bundle + 2) =
                segs_canon.take (k_bundle + 1) ++ [segs_canon[k_bundle + 1]'hsucc_lt] := by
              rw [List.take_add_one, List.getElem?_eq_getElem hsucc_lt]; rfl
            rw [htake_eq, List.map_append, List.flatten_append]; simp
          have hpref_kp2_pre :
              ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten <+: path := by
            rw [hpath_canon]
            exact List.IsPrefix.flatten (List.IsPrefix.map _ (List.take_prefix _ _))
          have hwindow_kp1 :
              ∀ p ∈ (segs_canon[k_bundle + 1]'hsucc_lt).1, p ∈ path.take d := by
            intro p hp
            have hp_pref :
                p ∈ ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten := by
              rw [hpref_kp2_eq]; exact List.mem_append_right _ hp
            -- Show prefix_{k+2}.flatten <+: path.take d, then use subset.
            have hpref_take :
                ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten <+: path.take d := by
              obtain ⟨rest, hrest⟩ := hpref_kp2_pre
              have h1 :
                  ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten
                    = (path.take d).take
                        ((segs_canon.take (k_bundle + 2)).map Prod.fst).flatten.length := by
                rw [List.take_take, min_eq_left h_kp2_strad, ← hrest,
                    List.take_left]
              rw [h1]
              exact List.take_prefix _ _
            exact hpref_take.subset hp_pref
          have hdrop_kp1_eq : segs_canon.drop (k_bundle + 1) =
              (segs_canon[k_bundle + 1]'hsucc_lt) :: segs_canon.drop (k_bundle + 2) :=
            List.drop_eq_getElem_cons hsucc_lt
          have hdrop_kp1_flat_eq :
              ((segs_canon.drop (k_bundle + 1)).map Prod.fst).flatten
                = (segs_canon[k_bundle + 1]'hsucc_lt).1
                    ++ ((segs_canon.drop (k_bundle + 2)).map Prod.fst).flatten := by
            rw [hdrop_kp1_eq, List.map_cons, List.flatten_cons]
          have hfilt_β :
              (segs_canon[k_bundle + 1]'hsucc_lt).1.filter
                (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2))
                = (segs_canon[k_bundle + 1]'hsucc_lt).1 := by
            apply List.filter_eq_self.mpr
            intro p hp
            exact List.any_eq_true.mpr ⟨p, hwindow_kp1 p hp, by simp⟩
          rw [hdrop_kp1_flat_eq, List.filter_append, hfilt_β, List.map_append]
          exact List.prefix_append _ _
      · -- ALIVE-PROPER-EDGE: k_bundle+1 = segs_canon.length;
        -- non-straddler ⇒ path.length ≤ d, contradicting CDT.
        exfalso
        push Not at hsucc_lt
        have hk_succ_eq : k_bundle + 1 = segs_canon.length := by omega
        have htake_full : segs_canon.take (k_bundle + 1) = segs_canon := by
          rw [hk_succ_eq]; exact List.take_length
        have hpath_le : path.length ≤ d := by
          have : path = ((segs_canon.take (k_bundle + 1)).map Prod.fst).flatten := by
            rw [htake_full]; exact hpath_canon
          rw [this]; exact h_straddler
        have hpath_gt : path.length > d :=
          leftmostPathExceedingDepth_some_path_length_gt _ _ _ hloop.hpath
        omega
  · -- TERMINAL CASE: remaining_π = []; remaining' = []; contradicts hrem_post_ne.
    exfalso; apply hrem_post_ne
    rw [hrem_terminal]; rfl

#print axioms encoder_h_r_combined_pref_from_loop_inv

/- **Seed discharge of `hρ_segments_consumed`.**

    At the seed (loop start) `ρ = β = asgn` and `remaining_π = path.take d`,
    so we instantiate the existential with the canonical-DT iter-split
    of `path` and `k = 0`.  Then `(segments.take 0).map fst).flatten = []`,
    making `ρ = asgn ++ []` and the `remaining_π` equation reduces to a
    `path.filter window = path.take d` claim.

    The witness `segments` and the `hseg_prov` provenance come from
    `cdt_full_query_killed_heads_covered_by_prefix` (CanonicalDT).
    The iter-split construction also ensures that each segment's path bits
    and head clause share the same fst-list. -/
private lemma encoder_seed_hρ_segments_consumed
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (_h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path) :
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))) (k : Nat)
      (partial_seg : List (Nat × Bool)),
      path = (segments.map Prod.fst).flatten ∧
      k ≤ segments.length ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction β) dnf))
            (((segments.take j).map Prod.fst).flatten)
          = (segments[j]'hj).2 :: tail_j) ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ((segments.take (j+1)).map Prod.fst).flatten.length ≤ d →
        (segments[j]'hj).1 ≠ []) ∧
      β = β ++ ((segments.take k).map Prod.fst).flatten ++ partial_seg ∧
      ((partial_seg = [] ∧
        path.take d =
          (((segments.drop k).map Prod.fst).flatten).filter
            (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) ∧
        (∀ (hk : k < segments.length),
          ((segments.take (k+1)).map Prod.fst).flatten.length ≤ d →
          ∀ p ∈ (segments[k]'hk).1, p ∈ path.take d)) ∨
       (∃ (hk : k < segments.length),
         partial_seg.Sublist (segments[k]'hk).1 ∧ path.take d = [])) := by
  -- Bundle dnf into UnboundedFanInDNF for the helper lemmas (mirrors seed bundle).
  set N := ufiLargestInput dnf + 1 with h_n_def
  have h_n_lt : ufiLargestInput dnf < N := Nat.lt_succ_self _
  let f : UnboundedFanInDNF N := ⟨dnf, h_n_lt, hdnf⟩
  -- IsPathIn from leftmostPathExceedingDepth.
  have hp : IsPathIn (canonicalDecisionTree dnf β) path :=
    leftmostPathExceedingDepth_isPathIn _ _ _ hpath
  -- Restricted-clause nodup-fst, derived from `hnodup` via the bridge lemma.
  have hnodup_restricted :
      ∀ c ∈ dnfClauses (simpleRestrictDNF
        (restrictionAsFunction β) dnf),
        (c.map Prod.fst).Nodup := by
    intro c hc
    exact restrictDNF_preserves_clause_nodup dnf
      (restrictionAsFunction β) hnodup c hc
  -- Invoke the canonical-DT iter-split producer.
  obtain ⟨segments, hcat, _hlen, hcov, _hheads, _hnd, hkill, hcum_a⟩ :=
    cdt_full_query_per_segment_killed f β hnodup_restricted path hp
  -- Path nodup-fst (for the filter equation).
  have hpath_nodup_fst : (path.map Prod.fst).Nodup :=
    canonical_dt_path_nodup_fst dnf β hnodup d path hpath
  -- Witness with `(segments, 0, [])`.
  refine ⟨segments, 0, [], hcat, Nat.zero_le _, hcum_a, hcov, ?_, ?_, ?_⟩
  · -- Within-depth nondegeneracy via `cdt_segment_pre_ne_nil_within_depth`.
    intro j hj h_within_d
    exact cdt_segment_pre_ne_nil_within_depth f β hnodup_restricted d path hpath
      segments hcat hcov hkill j hj h_within_d
  · -- β = β ++ ((segments.take 0).map fst).flatten ++ [] = β.
    simp
  · -- Pick the regular case: partial_seg = [] ∧ path.take d = filter window
    -- ∧ encoder depth-monotonicity at k=0.
    refine Or.inl ⟨rfl, ?_, ?_⟩
    · show path.take d =
        (((segments.drop 0).map Prod.fst).flatten).filter
          (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2))
      rw [List.drop_zero, ← hcat]
      -- Goal: path.take d = path.filter (fun p => (path.take d).any (...))
      -- Bind `pref := path.take d` to keep the filter predicate stable when
      -- splitting `path = pref ++ path.drop d`.
      set pref := path.take d with hpref_def
      -- Filter predicate (closed over `pref` only).
      set g : (Nat × Bool) → Bool := fun p => pref.any (fun q => q.1 == p.1 && q.2 == p.2)
        with hg_def
      have hpath_split : path = pref ++ path.drop d := by
        rw [hpref_def]; exact (List.take_append_drop d path).symm
      conv_rhs => rw [hpath_split, List.filter_append]
      -- Take-side: every p ∈ pref satisfies g (p itself is the witness).
      have htake_filter : pref.filter g = pref := by
        apply List.filter_eq_self.mpr
        intro p hp_take
        rw [hg_def]
        rw [List.any_eq_true]
        refine ⟨p, hp_take, ?_⟩
        simp
      -- Drop-side: nodup-fst forces no p ∈ path.drop d to match any q ∈ pref.
      have hdrop_filter : (path.drop d).filter g = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp_drop hany
        rw [hg_def, List.any_eq_true] at hany
        obtain ⟨q, hq_take, hq_eq⟩ := hany
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hq_eq
        obtain ⟨hq1, _hq2⟩ := hq_eq
        have hq1_take : q.1 ∈ pref.map Prod.fst := List.mem_map_of_mem hq_take
        have hp1_drop : p.1 ∈ (path.drop d).map Prod.fst := List.mem_map_of_mem hp_drop
        have hsplit : (path.map Prod.fst) =
            pref.map Prod.fst ++ (path.drop d).map Prod.fst := by
          rw [hpref_def, ← List.map_append, List.take_append_drop]
        rw [hsplit] at hpath_nodup_fst
        have hdisj := List.disjoint_of_nodup_append hpath_nodup_fst
        rw [hq1] at hq1_take
        exact hdisj hq1_take hp1_drop
      rw [htake_filter, hdrop_filter, List.append_nil]
    · -- Encoder depth-monotonicity at k=0:
      -- Given `0 < segments.length` and `((segments.take 1).map fst).flatten.length ≤ d`,
      -- show `∀ p ∈ segments[0].1, p ∈ path.take d`.
      intro hk h_len_d p hp
      -- Bridge: segments[0] = segments.head ⋯
      have hne_seg : segments ≠ [] := List.ne_nil_of_length_pos hk
      -- Step 0: split segments = segments[0] :: segments.tail.
      have hsplit_seg :
          segments = (segments[0]'hk) :: segments.tail := by
        have h1 : segments = segments.head hne_seg :: segments.tail :=
          (List.cons_head_tail hne_seg).symm
        have h2 : segments.head hne_seg = (segments[0]'hk) :=
          (List.head_eq_getElem_zero hne_seg)
        rw [h2] at h1
        exact h1
      -- Step 1: `(segments.take 1).map fst).flatten = segments[0].1`.
      have hseg0_eq : ((segments.take 1).map Prod.fst).flatten = (segments[0]'hk).1 := by
        conv_lhs => rw [hsplit_seg]
        simp
      -- Step 2: hence segments[0].1.length ≤ d.
      have hlen_seg0 : (segments[0]'hk).1.length ≤ d := by
        rw [← hseg0_eq]; exact h_len_d
      -- Step 3: segments[0].1 is a prefix of path.
      have hprefix : (segments[0]'hk).1 = path.take ((segments[0]'hk).1.length) := by
        set L := (segments[0]'hk).1.length with h_l
        rw [hcat]
        conv_rhs => rw [hsplit_seg]
        simp
        rw [h_l]
        exact List.take_left.symm
      -- Step 4: p ∈ path.take seg0.length ⊆ path.take d.
      rw [hprefix] at hp
      exact (List.take_prefix_take_left hlen_seg0).subset hp

#print axioms encoder_seed_hρ_segments_consumed

/- Structural lemma: if `path = L₁ ++ L₂ ++ L₃` is nodup-on-fst and some bit
   `b ∈ L₂` is past depth `d` in `path` (i.e., `b ∉ path.take d`), then
   every bit `q ∈ L₃` is also past depth `d` (`q ∉ path.take d`).
   No canonical-DT machinery needed — pure list arithmetic. -/
private lemma path_drop_disjoint_take_d
    (path L₁ L₂ L₃ : List (Nat × Bool)) (d : Nat)
    (hpath_nodup_fst : (path.map Prod.fst).Nodup)
    (hpath_eq : path = L₁ ++ L₂ ++ L₃)
    (b : Nat × Bool) (hb_l₂ : b ∈ L₂) (hb_notake : b ∉ path.take d) :
    ∀ q ∈ L₃, q ∉ path.take d := by
  -- Step 1: d ≤ |L₁ ++ L₂|.  Otherwise path.take d ⊇ L₁ ++ L₂ ⊇ {b}, contradicting hb_notake.
  have hd_le : d ≤ (L₁ ++ L₂).length := by
    by_contra hd_gt
    push Not at hd_gt
    apply hb_notake
    rw [hpath_eq]
    have heq : ((L₁ ++ L₂) ++ L₃).take d =
        (L₁ ++ L₂) ++ L₃.take (d - (L₁ ++ L₂).length) := by
      rw [List.take_append,
        List.take_of_length_le (le_of_lt hd_gt)]
    rw [heq]
    exact List.mem_append_left _ (List.mem_append_right _ hb_l₂)
  -- Step 2: q ∈ L₃, q ∈ path.take d ⊆ L₁ ++ L₂ contradicts nodup-fst (q.1 in both halves).
  intro q hq_l₃ hq_take
  rw [hpath_eq] at hq_take
  -- (L₁ ++ L₂ ++ L₃).take d = (L₁ ++ L₂).take d (since d ≤ |L₁ ++ L₂|).
  have heq2 : ((L₁ ++ L₂) ++ L₃).take d = (L₁ ++ L₂).take d := by
    rw [List.take_append_of_le_length hd_le]
  rw [heq2] at hq_take
  have hq_l1_l2 : q ∈ L₁ ++ L₂ := List.mem_of_mem_take hq_take
  -- Now contradiction via nodup-fst on path = (L₁ ++ L₂) ++ L₃.
  have hq_fst_l1_l2 : q.1 ∈ ((L₁ ++ L₂).map Prod.fst) :=
    List.mem_map.mpr ⟨q, hq_l1_l2, rfl⟩
  have hq_fst_l3 : q.1 ∈ (L₃.map Prod.fst) :=
    List.mem_map.mpr ⟨q, hq_l₃, rfl⟩
  have hpath_split_fst : (path.map Prod.fst) =
      (L₁ ++ L₂).map Prod.fst ++ L₃.map Prod.fst := by
    rw [hpath_eq, List.map_append]
  rw [hpath_split_fst] at hpath_nodup_fst
  exact List.disjoint_of_nodup_append hpath_nodup_fst hq_fst_l1_l2 hq_fst_l3

private lemma encoder_step_hρ_segments_consumed
    (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true)
    (asgn : List (Nat × Bool))
    (d : Nat) (path : List (Nat × Bool))
    (hpath_nodup_fst : (path.map Prod.fst).Nodup)
    (hasgn_disj_path : ∀ p ∈ path, (asgn.any fun (z, _) => z == p.1) = false)
    (ρ remaining_π : List (Nat × Bool))
    (segs_canon : List (List (Nat × Bool) × List (Nat × Bool))) (k : Nat)
    (_hpath_eq : path = (segs_canon.map Prod.fst).flatten)
    (_hk_le : k ≤ segs_canon.length)
    (_hk_lt : k < segs_canon.length)
    (_hprov : ∀ (j : Nat) (hj : j < segs_canon.length),
      ∃ tail_j,
        simplifyClausesByPath
          (dnfClauses (simpleRestrictDNF
            (restrictionAsFunction asgn) dnf))
          (((segs_canon.take j).map Prod.fst).flatten)
        = (segs_canon[j]'hj).2 :: tail_j)
    (_hvm : ∀ p ∈ segs_canon, p.1.map Prod.fst = p.2.map Prod.fst)
    (_hρ_eq : ρ = asgn ++ ((segs_canon.take k).map Prod.fst).flatten)
    (_hrem_eq : remaining_π =
      (((segs_canon.drop k).map Prod.fst).flatten).filter
        (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)))
    (πI : List (Nat × Bool))
    (_hπ_i_eq : πI = remaining_π.filter (fun x =>
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) ρ).map Prod.fst
        |>.contains x.1))
    (ρ' remaining' : List (Nat × Bool))
    (_hρ'_def : ρ' = combineRestrictions ρ πI)
    (_hrem'_def : remaining' = remaining_π.filter
      (fun x => !πI.any (fun (w', _) => w' == x.1)))
    -- The encoder only steps when the current segment is fully within
    -- the depth-`d` window.  Discharged at call sites from local context
    -- (loop only iterates while the alive non-T segment fits within fuel).
    (_hseg_k_in_window :
      ∀ p ∈ (segs_canon[k]'_hk_lt).1, p ∈ path.take d)
    -- Within-depth nondegeneracy of the input bundle (carried through).
    (_hne_within_d :
      ∀ (j : Nat) (hj : j < segs_canon.length),
        ((segs_canon.take (j + 1)).map Prod.fst).flatten.length ≤ d →
        (segs_canon[j]'hj).1 ≠ []) :
    ∃ (segments : List (List (Nat × Bool) × List (Nat × Bool))) (k' : Nat)
      (partial_seg' : List (Nat × Bool)),
      path = (segments.map Prod.fst).flatten ∧
      k' ≤ segments.length ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ∃ tail_j,
          simplifyClausesByPath
            (dnfClauses (simpleRestrictDNF
              (restrictionAsFunction asgn) dnf))
            (((segments.take j).map Prod.fst).flatten)
          = (segments[j]'hj).2 :: tail_j) ∧
      (∀ p ∈ segments, p.1.map Prod.fst = p.2.map Prod.fst) ∧
      (∀ (j : Nat) (hj : j < segments.length),
        ((segments.take (j+1)).map Prod.fst).flatten.length ≤ d →
        (segments[j]'hj).1 ≠ []) ∧
      ρ' = asgn ++ ((segments.take k').map Prod.fst).flatten ++ partial_seg' ∧
      ((partial_seg' = [] ∧
        remaining' =
          (((segments.drop k').map Prod.fst).flatten).filter
            (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) ∧
        (∀ (hk : k' < segments.length),
          ((segments.take (k'+1)).map Prod.fst).flatten.length ≤ d →
          ∀ p ∈ (segments[k']'hk).1, p ∈ path.take d)) ∨
       (∃ (hk : k' < segments.length),
         partial_seg'.Sublist (segments[k']'hk).1 ∧ remaining' = [])) := by
  -- Reuse the SAME canonical witness (`segs_canon`); advance only `k → k+1`.
  -- Trivial conjuncts (path eq, length, provenance, vars-match) are
  -- inherited unchanged.  The two non-trivial obligations are:
  --   (A) ρ' = asgn ++ (segs_canon.take (k+1)).map fst).flatten
  --   (B) remaining' = (((segs_canon.drop (k+1)).map fst).flatten).filter window
  --
  -- Both reduce to identifying `πI` with `segs_canon[k].1` as a list.
  -- ── Keystone bridge via `r_of_combined_eq_restricted_simplify_head` ──
  -- Set `cum := ((segs_canon.take k).map fst).flatten`.  From `_hprov k _hk_lt`,
  -- we have `simplifyClausesByPath (dnfClauses (simpleRestrictDNF
  --   (restrictionAsFunction asgn) dnf)) cum = segs_canon[k].2 :: tail_k`.
  -- The parent identifies the selected clause under `asgn ++ cum` (and hence
  -- under ρ) with `segs_canon[k].2`. This is the keystone for sub-claim (A.1).
  -- ── Prerequisite hypotheses for the parent ──
  -- (i)  `(cum.map fst).Nodup`: prefix of path under nodup-fst.
  -- (ii) `cum disj asgn`: each path bit's var is asgn-disjoint.
  set cum : List (Nat × Bool) := ((segs_canon.take k).map Prod.fst).flatten with hcum_def
  -- cum.fst is a sublist of path.fst (sublist of flatten of map fst on take prefix).
  have hcum_sub_path : List.Sublist (cum.map Prod.fst) (path.map Prod.fst) := by
    rw [hcum_def, _hpath_eq]
    -- `((segs_canon.take k).map fst).flatten.map fst` <+
    -- `(segs_canon.map fst).flatten.map fst`
    have h1 : List.Sublist ((segs_canon.take k).map Prod.fst) (segs_canon.map Prod.fst) :=
      (List.take_sublist k segs_canon).map _
    exact (h1.flatten).map _
  have hcum_nodup : (cum.map Prod.fst).Nodup :=
    hcum_sub_path.nodup hpath_nodup_fst
  have hasgn_disj_cum : ∀ v ∈ cum.map Prod.fst,
      (asgn.any fun p => p.1 == v) = false := by
    intro v hv
    -- v ∈ cum.fst ⊆ path.fst, so ∃ b, (v, b) ∈ path, then apply hasgn_disj_path.
    have hv_path : v ∈ path.map Prod.fst := hcum_sub_path.subset hv
    rcases List.mem_map.mp hv_path with ⟨⟨w, b⟩, hwb_path, hwfst⟩
    simp at hwfst; subst hwfst
    have := hasgn_disj_path (w, b) hwb_path
    -- Convert `fun (z, _) => z == w` to `fun p => p.1 == w` form.
    simpa using this
  -- Apply the parent lemma to extract the head and bridge it to the selected
  -- clause under ρ.
  obtain ⟨tail_k, hsimp⟩ := _hprov k _hk_lt
  have h_r_eq_segs :
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) (asgn ++ cum)).map
        Prod.fst = (segs_canon[k]'_hk_lt).2.map Prod.fst :=
    r_of_combined_eq_restricted_simplify_head dnf hdnf asgn cum
      hcum_nodup hasgn_disj_cum (segs_canon[k]'_hk_lt).2 tail_k hsimp
  have h_r_ρ_eq_segs :
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) ρ).map Prod.fst
      = (segs_canon[k]'_hk_lt).2.map Prod.fst := by
    rw [_hρ_eq]; exact h_r_eq_segs
  -- The keystone `h_r_ρ_eq_segs` reduces sub-claims (A) and (B) to:
  --   (A.2) πI = segs_canon[k].1 as a list (via `_hπ_i_eq` + `_hvm k` +
  --         nodup-fst + `h_r_ρ_eq_segs`),
  --   (A.3) combineRestrictions ρ πI = ρ ++ πI (disjointness of πI.fst from ρ.fst),
  --   (A.4) `_hρ_eq` + (2,3) + take_succ list arithmetic.
  --   (B)   list arithmetic on `drop k = segs_canon[k] :: drop (k+1)` +
  --         filtering out the segment's bits via `πI.any (·.1 == ·)`.
  -- ── Decompose `(segs_canon.drop k).map fst).flatten = segs_canon[k].1 ++ rest`. ──
  set rest : List (Nat × Bool) :=
    ((segs_canon.drop (k+1)).map Prod.fst).flatten with hrest_def
  have hdrop_k_map :
      (segs_canon.drop k).map Prod.fst =
        (segs_canon[k]'_hk_lt).1 :: ((segs_canon.drop (k+1)).map Prod.fst) := by
    rw [List.drop_eq_getElem_cons _hk_lt, List.map_cons]
  have hflatten_drop_k :
      (((segs_canon.drop k).map Prod.fst).flatten) =
        (segs_canon[k]'_hk_lt).1 ++ rest := by
    rw [hdrop_k_map, List.flatten_cons]
  -- ── Window holds for every p ∈ segs_canon[k].1. ──
  have hwindow_seg_k : ∀ p ∈ (segs_canon[k]'_hk_lt).1,
      ((path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) = true := by
    intro p hp
    have hp_take : p ∈ path.take d := _hseg_k_in_window p hp
    exact List.any_eq_true.mpr ⟨p, hp_take, by simp⟩
  -- ── path decomposes as cum ++ segs_canon[k].1 ++ rest. ──
  have hpath_eq3 : path = cum ++ (segs_canon[k]'_hk_lt).1 ++ rest := by
    rw [_hpath_eq, hcum_def, hrest_def]
    have hsplit : segs_canon =
        segs_canon.take k ++ ((segs_canon[k]'_hk_lt) ::
          segs_canon.drop (k+1)) := by
      rw [← List.drop_eq_getElem_cons _hk_lt, List.take_append_drop]
    conv_lhs => rw [hsplit]
    rw [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons,
      List.append_assoc]
  have hpath_nodup_fst' :
      ((cum ++ (segs_canon[k]'_hk_lt).1 ++ rest).map Prod.fst).Nodup :=
    hpath_eq3 ▸ hpath_nodup_fst
  -- Disjointness between segs_canon[k].1.fst and rest.fst.
  have hseg_k_disj_rest : ∀ p ∈ rest, p.1 ∉ (segs_canon[k]'_hk_lt).1.map Prod.fst := by
    intro p hp_rest hp_in_seg
    -- Express path.fst as ((cum ++ seg).fst) ++ rest.fst.
    have hsplit_path_fst :
        path.map Prod.fst =
          (cum ++ (segs_canon[k]'_hk_lt).1).map Prod.fst ++ rest.map Prod.fst := by
      rw [hpath_eq3, ← List.map_append]
    rw [hsplit_path_fst] at hpath_nodup_fst
    have hdisj := List.disjoint_of_nodup_append hpath_nodup_fst
    have hp_cs : p.1 ∈ (cum ++ (segs_canon[k]'_hk_lt).1).map Prod.fst := by
      rw [List.map_append]; exact List.mem_append_right _ hp_in_seg
    have hp_rest_fst : p.1 ∈ rest.map Prod.fst :=
      List.mem_map.mpr ⟨p, hp_rest, rfl⟩
    exact hdisj hp_cs hp_rest_fst
  -- Disjointness between cum.fst and segs_canon[k].1.fst.
  have hcum_disj_seg_k : ∀ p ∈ (segs_canon[k]'_hk_lt).1, p.1 ∉ cum.map Prod.fst := by
    intro p hp_seg hp_cum
    -- Express path.fst as cum.fst ++ seg.fst ++ rest.fst, then split (cum ++ seg).fst.
    have hsplit_cum_seg :
        (cum ++ (segs_canon[k]'_hk_lt).1).map Prod.fst =
          cum.map Prod.fst ++ (segs_canon[k]'_hk_lt).1.map Prod.fst := by
      rw [List.map_append]
    -- Get nodup on (cum ++ seg).fst by sublist of path.fst.
    have hnodup_cs : ((cum ++ (segs_canon[k]'_hk_lt).1).map Prod.fst).Nodup := by
      have hsub : ((cum ++ (segs_canon[k]'_hk_lt).1)).Sublist path := by
        rw [hpath_eq3]; exact List.sublist_append_left _ _
      exact (hsub.map _).nodup hpath_nodup_fst
    rw [hsplit_cum_seg] at hnodup_cs
    have hdisj := List.disjoint_of_nodup_append hnodup_cs
    have hp_seg_fst : p.1 ∈ (segs_canon[k]'_hk_lt).1.map Prod.fst :=
      List.mem_map.mpr ⟨p, hp_seg, rfl⟩
    exact hdisj hp_cum hp_seg_fst
  -- segs_canon[k].1.fst disjoint from asgn.fst.
  have hasgn_disj_seg_k : ∀ p ∈ (segs_canon[k]'_hk_lt).1,
      (asgn.any fun (z, _) => z == p.1) = false := by
    intro p hp_seg
    have hp_path : p ∈ path := by
      rw [_hpath_eq, List.mem_flatten]
      exact ⟨(segs_canon[k]'_hk_lt).1, List.mem_map.mpr
        ⟨segs_canon[k]'_hk_lt, List.getElem_mem _hk_lt, rfl⟩, hp_seg⟩
    exact hasgn_disj_path p hp_path
  -- ── remaining_π = segs_canon[k].1 ++ rest.filter window. ──
  have hrem_split : remaining_π =
      (segs_canon[k]'_hk_lt).1 ++ rest.filter
        (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) := by
    rw [_hrem_eq, hflatten_drop_k, List.filter_append]
    congr 1
    apply List.filter_eq_self.mpr
    intro p hp
    exact hwindow_seg_k p hp
  -- ── Transfer the selected-clause equality to `segs_canon[k].1`. ──
  have h_r_eq_seg_k_fst :
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) ρ).map Prod.fst
      = (segs_canon[k]'_hk_lt).1.map Prod.fst := by
    rw [h_r_ρ_eq_segs, (_hvm _ (List.getElem_mem _hk_lt)).symm]
  -- ── πI = segs_canon[k].1. ──
  have hπ_i_eq_seg_k : πI = (segs_canon[k]'_hk_lt).1 := by
    rw [_hπ_i_eq, hrem_split, List.filter_append]
    -- The first filter keeps every element of `segs_canon[k].1`.
    have hfirst : ((segs_canon[k]'_hk_lt).1).filter
        (fun x => ((restrictionOfFirstTermNotKilledByList
          (dnfClauses dnf) ρ).map Prod.fst).contains x.1) =
        (segs_canon[k]'_hk_lt).1 := by
      apply List.filter_eq_self.mpr
      intro p hp
      rw [h_r_eq_seg_k_fst]
      exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
    -- Second piece: (rest.filter window).filter (·.1 ∈ segs_canon[k].1.fst) = [].
    have hsecond : (rest.filter
          (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2))).filter
        (fun x => ((restrictionOfFirstTermNotKilledByList
          (dnfClauses dnf) ρ).map Prod.fst).contains x.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro p hp_filt
      have hp_rest : p ∈ rest := List.mem_of_mem_filter hp_filt
      rw [h_r_eq_seg_k_fst]
      simp only [List.contains_iff_mem]
      intro hp_in
      exact hseg_k_disj_rest p hp_rest hp_in
    rw [hfirst, hsecond, List.append_nil]
  -- ── combineRestrictions ρ πI = ρ ++ πI (filter is identity since πI.fst disjoint from ρ.fst). ──
  have h_combined_eq : combineRestrictions ρ πI = ρ ++ πI := by
    rw [combineRestrictions]
    congr 1
    apply List.filter_eq_self.mpr
    intro p hp_πi
    rw [hπ_i_eq_seg_k] at hp_πi
    -- ρ.any (·.1 == p.1) = false because ρ = asgn ++ cum and both disjoint.
    rw [_hρ_eq]
    -- Goal: !(asgn ++ cum).any (·.1 == p.1) = true
    have hasgn_false : (asgn.any fun (z, _) => z == p.1) = false :=
      hasgn_disj_seg_k p hp_πi
    have hcum_false : (cum.any fun (z, _) => z == p.1) = false := by
      by_contra hcum_true
      rw [Bool.not_eq_false] at hcum_true
      apply hcum_disj_seg_k p hp_πi
      rw [List.any_eq_true] at hcum_true
      obtain ⟨⟨w, b⟩, hw_mem, hw_eq⟩ := hcum_true
      simp at hw_eq
      exact List.mem_map.mpr ⟨(w, b), hw_mem, hw_eq⟩
    simp [List.any_append, hasgn_false, hcum_false]
  refine ⟨segs_canon, k + 1, [], _hpath_eq, _hk_lt, _hprov, _hvm, _hne_within_d, ?_, ?_⟩
  · -- Sub-claim (A): ρ' = asgn ++ ((segs_canon.take (k+1)).map fst).flatten ++ [].
    rw [_hρ'_def, h_combined_eq, _hρ_eq, hπ_i_eq_seg_k]
    -- Goal: asgn ++ cum ++ segs_canon[k].1 = asgn ++ ((take (k+1)).map fst).flatten ++ [].
    rw [List.append_nil, List.take_succ_eq_append_getElem _hk_lt, List.map_append,
        List.flatten_append, List.map_singleton, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc]
  · -- Pick regular case (Or.inl).
    refine Or.inl ⟨rfl, ?_, ?_⟩
    · -- Sub-claim (B): remaining' = (((segs_canon.drop (k+1)).map fst).flatten).filter window.
      rw [_hrem'_def, hrem_split, hπ_i_eq_seg_k, List.filter_append]
      -- (segs_canon[k].1).filter (!segs_canon[k].1.any (·.1 == ·)) = []
      -- (rest_filtered).filter (!segs_canon[k].1.any (·.1 == ·)) = rest_filtered
      have hfirst : ((segs_canon[k]'_hk_lt).1).filter
          (fun x => !((segs_canon[k]'_hk_lt).1).any
            (fun p => p.1 == x.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
        have : ((segs_canon[k]'_hk_lt).1).any (fun q => q.1 == p.1) = true :=
          List.any_eq_true.mpr ⟨p, hp, by simp⟩
        simp only [Bool.not_eq_false]
        exact this
      have hsecond : (rest.filter
            (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2))).filter
          (fun x => !((segs_canon[k]'_hk_lt).1).any
            (fun p => p.1 == x.1)) =
          rest.filter
            (fun p => (path.take d).any (fun q => q.1 == p.1 && q.2 == p.2)) := by
        apply List.filter_eq_self.mpr
        intro p hp_filt
        have hp_rest : p ∈ rest := List.mem_of_mem_filter hp_filt
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          ]
        rw [Bool.eq_false_iff]
        intro hany
        apply hseg_k_disj_rest p hp_rest
        rw [List.any_eq_true] at hany
        obtain ⟨⟨w, b⟩, hw_mem, hw_eq⟩ := hany
        simp at hw_eq
        exact List.mem_map.mpr ⟨(w, b), hw_mem, hw_eq⟩
      rw [hfirst, hsecond, List.nil_append]
    · -- Sub-claim (C): encoder depth-monotonicity at index k+1.
      -- Direct from `path = (segs_canon.map fst).flatten` plus depth bound.
      intro hk_succ_lt h_len_succ p hp
      -- segs_canon[k+1].1 ⊆ ((segs_canon.take (k+1+1)).map fst).flatten = path.take L
      -- where L = ((segs_canon.take (k+2)).map fst).flatten.length ≤ d.
      set L := ((segs_canon.take (k+1+1)).map Prod.fst).flatten.length with h_l
      -- Step 1: ((segs_canon.take (k+2)).map fst).flatten is a prefix of path.
      have hprefix_eq : ((segs_canon.take (k+1+1)).map Prod.fst).flatten = path.take L := by
        rw [_hpath_eq, h_l]
        -- Goal: ((take m segs_canon).map fst).flatten = (segs_canon.map fst).flatten.take ((take m).map fst).flatten.length
        -- Use: segs_canon.map fst = (take m).map fst ++ (drop m).map fst
        conv_rhs =>
          rw [show (segs_canon.map Prod.fst) =
            (segs_canon.take (k+1+1)).map Prod.fst ++ (segs_canon.drop (k+1+1)).map Prod.fst from
            by rw [← List.map_append, List.take_append_drop]]
          rw [List.flatten_append]
        rw [List.take_left]
      -- Step 2: segs_canon[k+1].1 ⊆ ((segs_canon.take (k+2)).map fst).flatten.
      have hp_in_prefix : p ∈ ((segs_canon.take (k+1+1)).map Prod.fst).flatten := by
        rw [List.mem_flatten]
        refine ⟨(segs_canon[k+1]'hk_succ_lt).1, ?_, hp⟩
        rw [List.mem_map]
        refine ⟨segs_canon[k+1]'hk_succ_lt, ?_, rfl⟩
        -- segs_canon[k+1] ∈ segs_canon.take (k+1+1)
        have : (segs_canon.take (k+1+1))[k+1]'(by
          rw [List.length_take]; omega) = segs_canon[k+1]'hk_succ_lt :=
          List.getElem_take ..
        rw [← this]
        exact List.getElem_mem _
      -- Step 3: rewrite + prefix-take inclusion.
      rw [hprefix_eq] at hp_in_prefix
      exact (List.take_prefix_take_left h_len_succ).subset hp_in_prefix

#print axioms encoder_step_hρ_segments_consumed

/-- Equal first components in a nodup-fst pair list force equal second components. -/
private lemma nodup_map_fst_eq_snd
    {l : List (Nat × Bool)} (hnodup : (l.map Prod.fst).Nodup)
    {a : Nat} {b₁ b₂ : Bool} (h₁ : (a, b₁) ∈ l) (h₂ : (a, b₂) ∈ l) : b₁ = b₂ := by
  induction l with
  | nil => simp at h₁
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hd_not_tl, htl_nodup⟩ := hnodup
    cases List.mem_cons.mp h₁ with
    | inl h₁_eq =>
      cases List.mem_cons.mp h₂ with
      | inl h₂_eq => exact congrArg Prod.snd (h₁_eq.trans h₂_eq.symm)
      | inr h₂_tl =>
        exfalso; apply hd_not_tl
        have := List.mem_map_of_mem (f := Prod.fst) h₂_tl
        rwa [congrArg Prod.fst h₁_eq] at this
    | inr h₁_tl =>
      cases List.mem_cons.mp h₂ with
      | inl h₂_eq =>
        exfalso; apply hd_not_tl
        have := List.mem_map_of_mem (f := Prod.fst) h₁_tl
        rwa [congrArg Prod.fst h₂_eq] at this
      | inr h₂_tl => exact ih htl_nodup h₁_tl h₂_tl

/- **Branch-2 termination auxiliary**: hoisted above the loop lemma to
    avoid forward-reference. When the step lemma's branch 2 fires
    (`remaining'.fst <+: U_vars(ρ').fst`), the next encoder iteration
    consumes all of `remaining'` in one chunk and the iteration after
    hits the empty base case. Pure list algebra. -/
private lemma encoder_branch2_consumes_all
    {clauses : List (List (Nat × Bool))}
    (ρ' remaining' : List (Nat × Bool))
    (hsub : ∀ v ∈ remaining'.map Prod.fst,
      v ∈ (restrictionOfFirstTermNotKilledByList clauses ρ').map Prod.fst) :
    let U_vars' := (restrictionOfFirstTermNotKilledByList clauses ρ').map Prod.fst
    let πI' := remaining'.filter (fun x => U_vars'.contains x.1)
    let remaining'' := remaining'.filter
      (fun (w, _) => !πI'.any fun (w', _) => w' == w)
    πI' = remaining' ∧ remaining'' = [] := by
  intro U_vars' πI' remaining''
  have hpred : ∀ x ∈ remaining', U_vars'.contains x.1 = true := by
    intro x hx
    have hx_fst : x.1 ∈ remaining'.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hx
    have hx_u : x.1 ∈ U_vars' := hsub x.1 hx_fst
    exact List.contains_iff_mem.mpr hx_u
  have hπ_eq : πI' = remaining' := by
    show remaining'.filter (fun x => U_vars'.contains x.1) = remaining'
    exact List.filter_eq_self.mpr hpred
  refine ⟨hπ_eq, ?_⟩
  show remaining'.filter (fun (w, _) => !πI'.any fun (w', _) => w' == w) = []
  rw [hπ_eq]
  rw [List.filter_eq_nil_iff]
  intro ⟨w, b⟩ hwb
  show ¬(!remaining'.any fun (w', _) => w' == w) = true
  have hany : (remaining'.any fun (w', _) => w' == w) = true :=
    List.any_eq_true.mpr ⟨(w, b), hwb, by simp⟩
  rw [hany]; decide

/-- `dead_acc` is monotone under recursion: anything in the input accumulator
    persists in the output. -/
private lemma encoder_aux_dead_acc_mono
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (v : Nat) (b : Bool)
    (hmem : (v, b) ∈ dead_acc) :
    (v, b) ∈ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1 := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero => simp only [beameEncoderAux]; exact hmem
  | succ fuel' ih =>
    simp only [beameEncoderAux]
    split
    · exact hmem
    · split
      · exact List.mem_append_left _ hmem
      · exact ih _ _ _ (List.mem_append_left _ hmem)

-- Increase maxHeartbeats: this lemma's loop induction expands large
-- DNF/canonical-DT term graphs and exceeds the default heartbeat budget.
set_option maxHeartbeats 1200000 in
-- Loop induction over fuel + remaining_π unfolds large `combineRestrictions`
-- and canonical-DT term graphs, exceeding the default heartbeat budget.
private lemma encoder_aux_decode_gen_loop
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ B_cur : List (Nat × Bool))
    (dead_acc vars_acc : List (Nat × Bool))
    -- Canonical-DT path-coverage bundle.
    (asgn : List (Nat × Bool)) (d : Nat) (path : List (Nat × Bool))
    (hloop : EncoderLoopInv dnf asgn d path ρ remaining_π)
    (hfuel : remaining_π.length ≤ fuel)
    (hπ_nodup : (remaining_π.map Prod.fst).Nodup)
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (halign : firstTermNotKilledByList (dnfClauses dnf) B_cur =
              firstTermNotKilledByList (dnfClauses dnf) ρ)
    (hdead_sub : ∀ w, w ∈ dead_acc.map Prod.fst → w ∈ vars_acc.map Prod.fst)
    (hdead_sub_ρ : ∀ v, v ∈ dead_acc.map Prod.fst →
                  (ρ.any fun (w, _) => w == v) = true)
    (h_b_val : ∀ v, restrictionAsFunction B_cur v =
        restrictionAsFunction
          (combineRestrictions ρ
            (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1) v) :
    let clauses := dnfClauses dnf
    let encoder := beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc
    let decoderResult := encoder.2.foldl (decoderOuterStep clauses) (B_cur, vars_acc)
    ∀ w, (w ∈ decoderResult.2.map Prod.fst ↔
          w ∈ vars_acc.map Prod.fst ∨ w ∈ encoder.1.map Prod.fst) := by
  -- Induct over the encoder fuel while maintaining the path-prefix invariant.
  induction fuel generalizing remaining_π ρ B_cur dead_acc vars_acc with
  | zero =>
    -- fuel = 0: encoder returns `([], dead_acc)`; decoder foldl is identity.
    simp only [beameEncoderAux, List.foldl_nil]
    intro w
    exact ⟨Or.inl, fun h => h.elim id (hdead_sub w)⟩
  | succ fuel' ih =>
    simp only [beameEncoderAux]
    by_cases hrem : remaining_π = []
    · -- remaining_π = []: encoder returns `([], dead_acc)`; decoder foldl is identity.
      simp only [if_pos hrem, List.foldl_nil]
      intro w
      refine ⟨Or.inl, ?_⟩
      rintro (h | h)
      · exact h
      · exact hdead_sub w h
    · rw [if_neg hrem]
      set clauses := dnfClauses dnf with hclauses_def
      set T_i := firstTermNotKilledByList clauses ρ with h_t_i_def
      set U_i := restrictClauseByListAssignment T_i ρ with h_u_i_def
      have h_u_sub : ∀ v ∈ U_i.map Prod.fst,
          v ∈ remaining_π.map Prod.fst := by
        intro v hv
        apply hloop.hpfx_ρ.subset
        simpa [U_i, T_i, restrictionOfFirstTermNotKilledByList] using hv
      set U_vars := U_i.map Prod.fst with h_u_vars_def
      set p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1 with hp_def
      set πI := remaining_π.filter p with hπ_i_def
      set γ_i := (gammaBitsForClause U_i).take πI.length with hγ_i_def
      set dead_acc' := dead_acc ++ γ_i with hdead_acc'_def
      by_cases hπ0 : πI.length = 0
      · -- πI empty: encoder returns `([], dead_acc')`; decoder foldl is identity.
        rw [if_pos hπ0]
        simp only [List.foldl_nil]
        intro w
        refine ⟨Or.inl, ?_⟩
        rintro (h | h)
        · exact h
        · -- Here `w ∈ (dead_acc ++ γ_i).map fst`; it remains to place `w` in
          -- `vars_acc.map fst`.
          -- γ_i has length 0 (since πI.length = 0), so γ_i = [], and reduces
          -- to dead_acc, which routes through hdead_sub.
          rw [List.map_append, List.mem_append] at h
          rcases h with hda | hγ
          · exact hdead_sub w hda
          · -- γ_i = [] from hπ0: take 0 = [].
            have hγ_nil : γ_i = [] := by
              simp only [hγ_i_def, hπ0, List.take_zero]
            rw [hγ_nil] at hγ; simp at hγ
      · -- Recursive branch.
        rw [if_neg hπ0]
        set chunk := encoderChunk T_i πI with hchunk_def
        set ρ' := combineRestrictions ρ πI with hρ'_def
        set remaining' := remaining_π.filter
          (fun (w, _) => !πI.any fun (w', _) => w' == w) with hremaining'_def
        -- Recursive encoder call.
        set restEncoder := beameEncoderAux fuel' remaining' (dnfClauses dnf) ρ' dead_acc'
          with h_rest_encoder_def
        -- Encoder output decomposition.  Pull the recursive pair apart
        -- pattern through Prod-projections so we can reason about it.
        have h_encoder_match :
            (let (final_dead, restEncoder') :=
               beameEncoderAux fuel' remaining' (dnfClauses dnf) ρ' dead_acc';
             ((final_dead, chunk :: restEncoder') :
              List (Nat × Bool) × List (List (Nat × Bool)))) =
            (restEncoder.1, chunk :: restEncoder.2) := by
          rcases h : beameEncoderAux fuel' remaining' (dnfClauses dnf) ρ' dead_acc'
            with ⟨a, b⟩
          simp [h, h_rest_encoder_def]
        -- Set up the decoder one-step state.
        set B_cur' := (decoderOuterStep clauses (B_cur, vars_acc) chunk).1
          with h_b_cur'_def
        set vars_acc' := (decoderOuterStep clauses (B_cur, vars_acc) chunk).2
          with hvars_acc'_def
        intro w
        -- Use h_encoder_match to rewrite the goal into the structured form.
        show w ∈ List.map Prod.fst
          (List.foldl (decoderOuterStep clauses) (B_cur, vars_acc)
            (restEncoder.1, chunk :: restEncoder.2).2).2 ↔
          w ∈ List.map Prod.fst vars_acc ∨
          w ∈ List.map Prod.fst (restEncoder.1, chunk :: restEncoder.2).1
        simp only [List.foldl_cons]
        change w ∈ (restEncoder.2.foldl (decoderOuterStep clauses)
            (B_cur', vars_acc')).2.map Prod.fst ↔
          w ∈ vars_acc.map Prod.fst ∨ w ∈ restEncoder.1.map Prod.fst
        -- ────────────────────────────────────────────────────────────────────
        -- SUB-OBLIGATION 1: encoder fuel reduction.
        -- ────────────────────────────────────────────────────────────────────
        have hfuel' : remaining'.length ≤ fuel' := by
          -- πI.length ≥ 1 from `¬ πI.length = 0`.
          have hπ_pos : 0 < πI.length := Nat.pos_of_ne_zero hπ0
          -- πI is a sublist of remaining_π (it is `remaining_π.filter p`).
          have hπ_sub : πI.Sublist remaining_π := List.filter_sublist
          -- Any entry of πI has its `.1` matching some element via `==`.
          -- So `remaining'` (which removes elements whose `.1` matches some πI entry)
          -- removes at least the elements of πI themselves.
          -- Concretely: every `x ∈ πI` satisfies `πI.any (·.1 == x.1) = true`,
          -- hence the filter predicate `!πI.any …` evaluates to `false` on `x`,
          -- so `x ∉ remaining'`.
          -- Therefore `remaining' ⊆ remaining_π \ πI`, so
          -- `remaining'.length + πI.length ≤ remaining_π.length`.
          have h_rem_lt : remaining'.length < remaining_π.length := by
            -- Pick any `x₀ ∈ πI` (exists since πI is non-empty).
            have hne_nil : πI ≠ [] := List.ne_nil_of_length_pos hπ_pos
            obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil πI hne_nil
            have hx₀_mem : x₀ ∈ remaining_π := hπ_sub.subset hx₀
            -- The filter predicate is `false` at `x₀` (since `πI.any (·.1 == x₀.1) = true`).
            have hx₀_not_in : x₀ ∉ remaining' := by
              intro h
              have hpred := (List.mem_filter.mp h).2
              obtain ⟨w₀, b₀⟩ := x₀
              simp only [Bool.not_eq_true'] at hpred
              -- hpred : (πI.any fun x => x.1 == w₀) = false
              have hany : (πI.any fun x => x.1 == w₀) = true :=
                List.any_eq_true.mpr ⟨(w₀, b₀), hx₀, by simp⟩
              exact Bool.noConfusion (hany.symm.trans hpred)
            -- remaining' is a sublist of remaining_π; missing x₀ ⇒ shorter.
            have hsub : remaining'.Sublist remaining_π := List.filter_sublist
            have hne : remaining' ≠ remaining_π := by
              intro heq
              exact hx₀_not_in (heq ▸ hx₀_mem)
            have hsub_len : remaining'.length ≤ remaining_π.length := hsub.length_le
            -- A sublist that misses a member of the supersublist is strictly shorter.
            by_contra h_not_lt
            push Not at h_not_lt
            have hlen_eq : remaining'.length = remaining_π.length := le_antisymm hsub_len h_not_lt
            have heq : remaining' = remaining_π := hsub.eq_of_length hlen_eq
            exact hx₀_not_in (heq ▸ hx₀_mem)
          omega
        -- ────────────────────────────────────────────────────────────────────
        -- SUB-OBLIGATION 2: `Nodup` propagation through the filter.
        -- ────────────────────────────────────────────────────────────────────
        have hπ_nodup' : (remaining'.map Prod.fst).Nodup :=
          List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hπ_nodup
        -- (SUB-OBLIGATION 3 deferred until hρ_eq is in scope below.)
        -- ────────────────────────────────────────────────────────────────────
        -- SUB-OBLIGATION 4 (vars_acc' contains dead_acc' on fsts).
        -- ────────────────────────────────────────────────────────────────────
        have hdead_sub' : ∀ w', w' ∈ dead_acc'.map Prod.fst →
            w' ∈ vars_acc'.map Prod.fst := by
          intro w₁ hw₁
          rw [hdead_acc'_def, List.map_append, List.mem_append] at hw₁
          -- vars_acc' = (chunk.foldl (decoderInnerStep T_dec) (B_cur, vars_acc)).2
          -- where T_dec = firstTermNotKilledByList clauses B_cur.  By halign, T_dec = T_i.
          show w₁ ∈ (chunk.foldl
            (decoderInnerStep
              (firstTermNotKilledByList clauses B_cur))
            (B_cur, vars_acc)).2.map Prod.fst
          rw [halign]
          -- Switch from the named inner-step to the inline lambda used by the
          -- `decoder_list_inner_foldl_*` helpers.  Definitionally equal.
          change w₁ ∈ (chunk.foldl
            (fun (acc : List (Nat × Bool) × List (Nat × Bool)) (entry : Nat × Bool) =>
              let v := (T_i.getD entry.1 (0, false)).1
              ((v, entry.2) :: acc.1, (v, entry.2) :: acc.2))
            (B_cur, vars_acc)).2.map Prod.fst
          rcases hw₁ with hda | hγ
          · -- Previously accumulated dead variables remain in the accumulator.
            have hva : w₁ ∈ vars_acc.map Prod.fst := hdead_sub w₁ hda
            -- Bridge the inline lambda used in helper signature.
            have := decoder_list_inner_foldl_acc_mono T_i chunk B_cur vars_acc w₁ hva
            convert this using 2
          · -- γ_i contribution: γ_i.map fst ⊆ U_vars (from gamma_bits) ⊆ remaining_π
            -- (from h_u_sub) ⇒ ∃ b, (w₁,b) ∈ remaining_π ⇒ (w₁,b) ∈ πI ⇒
            -- (find_pos T_i w₁, b) ∈ chunk ⇒ roundtrip recovers w₁ in vars_acc'.
            have hw₁_full : w₁ ∈ (gammaBitsForClause U_i).map Prod.fst := by
              rw [hγ_i_def, List.map_take] at hγ
              exact List.mem_of_mem_take hγ
            have hw₁_u : w₁ ∈ U_vars := by
              rw [h_u_vars_def]
              rwa [gamma_bits_map_fst_eq] at hw₁_full
            have hw₁_rem : w₁ ∈ remaining_π.map Prod.fst := h_u_sub w₁ hw₁_u
            obtain ⟨⟨w_x, b'⟩, hmem_rem, hwfst⟩ := List.mem_map.mp hw₁_rem
            simp only at hwfst
            -- Now hwfst : w_x = w₁.  Substitute w_x ← w₁ via rewriting.
            rw [hwfst] at hmem_rem
            -- hmem_rem : (w₁, b') ∈ remaining_π.
            -- (w₁, b') ∈ πI
            have hw₁_πi : (w₁, b') ∈ πI := by
              rw [hπ_i_def]
              refine List.mem_filter.mpr ⟨hmem_rem, ?_⟩
              show p (w₁, b') = true
              rw [hp_def]
              exact List.contains_iff_mem.mpr hw₁_u
            -- chunk contains (find_pos T_i w₁, b')
            have hchunk_mem : (findPositionInClause' T_i w₁, b') ∈ chunk := by
              rw [hchunk_def]
              simp only [encoderChunk, List.mem_map]
              exact ⟨(w₁, b'), hw₁_πi, by simp⟩
            -- T_i.any (·.1 == w₁) = true (via U_i ⊆ T_i and w₁ ∈ U_vars).
            have h_t_any : T_i.any (fun lit => lit.1 == w₁) = true := by
              obtain ⟨⟨v', neg⟩, hv'_mem, hv'_fst⟩ := List.mem_map.mp hw₁_u
              simp only at hv'_fst
              change (v', neg) ∈ restrictionOfFirstTermNotKilledByList clauses ρ at hv'_mem
              unfold restrictionOfFirstTermNotKilledByList at hv'_mem
              have hv'_t : (v', neg) ∈ T_i :=
                restrictClauseByListAssignment_subset _ _ _ hv'_mem
              exact List.any_eq_true.mpr ⟨(v', neg), hv'_t,
                by simp [BEq.beq, hv'_fst]⟩
            have hrt : (T_i.getD (findPositionInClause' T_i w₁) (0, false)).1 = w₁ :=
              findPositionInClause'_roundtrip T_i w₁ h_t_any
            have hprod := decoder_list_inner_foldl_produces T_i chunk B_cur vars_acc
              (findPositionInClause' T_i w₁) b' hchunk_mem
            rw [hrt] at hprod
            convert hprod using 2
        -- ────────────────────────────────────────────────────────────────────
        -- Propagate `h_b_val'` through one decoder step.
        -- ────────────────────────────────────────────────────────────────────
        have h_b_val' : ∀ v, restrictionAsFunction B_cur' v =
            restrictionAsFunction
              (combineRestrictions ρ' restEncoder.1) v := by
          -- T_dec = T_i (from halign).
          have h_t_cur : firstTermNotKilledByList clauses B_cur = T_i := halign
          -- Every (w, d) ∈ πI has w ∈ U_vars (from filter).
          have hpi_mem_u : ∀ w d, (w, d) ∈ πI → w ∈ U_vars := by
            intro w d hwd
            rw [hπ_i_def] at hwd
            have hp_true : p (w, d) = true := (List.mem_filter.mp hwd).2
            rw [hp_def] at hp_true
            exact List.contains_iff_mem.mp hp_true
          -- Bridge h_b_val into one using restEncoder.1:
          --   encoder.1 in this branch = restEncoder.1.
          have h_b_at_v_gen : ∀ v, restrictionAsFunction B_cur v =
              restrictionAsFunction
                (combineRestrictions ρ restEncoder.1) v := by
            intro v₀
            have h := h_b_val v₀
            have h_encoder_snd : (beameEncoderAux (fuel' + 1) remaining_π
                (dnfClauses dnf) ρ dead_acc).1 = restEncoder.1 := by
              unfold beameEncoderAux
              simp only [if_neg hrem]
              split
              · next habs => exact absurd habs hπ0
              · -- The encoder branch returns
                -- (let (restEncoder', final_dead) := … ; (chunk :: restEncoder', final_dead)).snd
                rcases hh : beameEncoderAux fuel' remaining' (dnfClauses dnf) ρ' dead_acc'
                  with ⟨a, b⟩
                simp [hh, h_rest_encoder_def]
            rw [h_encoder_snd] at h
            exact h
          intro v
          -- Reduce LHS: B_cur' = (chunk.foldl (decoderInnerStep T_i) (B_cur, vars_acc)).1
          have h_decoder_fst : B_cur' =
              (chunk.foldl (decoderInnerStep T_i) (B_cur, vars_acc)).1 := by
            rw [h_b_cur'_def]
            show (chunk.foldl (decoderInnerStep
              (firstTermNotKilledByList clauses B_cur)) (B_cur, vars_acc)).1 = _
            rw [h_t_cur]
          have hpi_in_t : ∀ w d, (w, d) ∈ πI →
              T_i.any (fun lit => lit.1 == w) = true := by
            intro w d hwd
            have hw_u := hpi_mem_u w d hwd
            obtain ⟨⟨v', neg⟩, hv'_mem, hv'_fst⟩ := List.mem_map.mp hw_u
            change (v', neg) ∈ restrictionOfFirstTermNotKilledByList clauses ρ at hv'_mem
            unfold restrictionOfFirstTermNotKilledByList at hv'_mem
            have hv'_t : (v', neg) ∈ T_i :=
              restrictClauseByListAssignment_subset _ _ _ hv'_mem
            exact List.any_eq_true.mpr ⟨(v', neg), hv'_t,
              by simpa [BEq.beq] using hv'_fst⟩
          have h_decoder_entries : (chunk.map fun (pos, bit) =>
              ((T_i.getD pos (0, false)).1, bit)) = πI := by
            rw [hchunk_def]; exact decoder_encoderChunk_decode_eq T_i πI hpi_in_t
          rw [h_decoder_fst, decoder_list_inner_foldl_fst_eq, h_decoder_entries]
          -- Goal: the restrictions induced by `πI.reverse ++ B_cur` and
          -- `combineRestrictions ρ' restEncoder.1` agree at v.
          by_cases hv_pi : v ∈ πI.map Prod.fst
          · -- v ∈ πI.
            obtain ⟨⟨v₀, d₁⟩, hv₀_mem, hv₀_fst⟩ := List.mem_map.mp hv_pi
            simp only at hv₀_fst
            rw [show v₀ = v from hv₀_fst] at hv₀_mem
            have hpi_nodup : (πI.map Prod.fst).Nodup := by
              rw [hπ_i_def]
              exact List.Nodup.sublist
                (List.Sublist.map Prod.fst List.filter_sublist) hπ_nodup
            have hpi_rev_nodup : (πI.reverse.map Prod.fst).Nodup := by
              rw [List.map_reverse]; exact List.nodup_reverse.mpr hpi_nodup
            have hfind_rev : πI.reverse.find? (fun p => p.1 == v) = some (v, d₁) :=
              find?_eq_of_nodup_mem πI.reverse v d₁ hpi_rev_nodup
                (List.mem_reverse.mpr hv₀_mem)
            have hfind_lhs : (πI.reverse ++ B_cur).find? (fun p => p.1 == v) =
                some (v, d₁) := by
              simp only [List.find?_append, hfind_rev, Option.some_or]
            have hcr_lhs : restrictionAsFunction (πI.reverse ++ B_cur) v =
                some d₁ := by
              simp only [restrictionAsFunction, hfind_lhs]
            -- v ∈ U_vars.
            have hv_u : v ∈ U_vars := hpi_mem_u v d₁ hv₀_mem
            obtain ⟨⟨v_u, neg_u⟩, hvu_mem, hvu_fst⟩ := List.mem_map.mp hv_u
            simp only at hvu_fst
            rw [show v_u = v from hvu_fst] at hvu_mem
            change (v, neg_u) ∈ restrictionOfFirstTermNotKilledByList clauses ρ at hvu_mem
            have hρ_any :=
              restrictionOfFirstTermNotKilledByList_vars_notMem_asgn
                clauses ρ (v, neg_u) hvu_mem
            have hρ_none : (restrictionAsFunction ρ) v = none := by
              rw [← Option.not_isSome_iff_eq_none,
                ← list_any_eq_cr_none_isSome]
              simp [hρ_any]
            have hρ_find : (ρ.find? fun p => p.1 == v) = none := by
              by_contra h
              push Not at h
              obtain ⟨⟨w_r, b_r⟩, hfr⟩ := Option.ne_none_iff_exists'.mp h
              have : restrictionAsFunction ρ v = some b_r := by
                simp only [restrictionAsFunction, hfr]
              rw [this] at hρ_none; exact absurd hρ_none (by simp)
            have hfilt_mem : (v, d₁) ∈ πI.filter
                (fun x => !(ρ.any fun (w, _) => w == x.1)) := by
              refine List.mem_filter.mpr ⟨hv₀_mem, ?_⟩
              simp only [Bool.not_eq_true']; rw [list_any_eq_cr_none_isSome, hρ_none]; rfl
            have hnodup_filt : ((πI.filter
                (fun x => !(ρ.any fun (w, _) => w == x.1))).map Prod.fst).Nodup :=
              List.Nodup.sublist (List.Sublist.map Prod.fst List.filter_sublist) hpi_nodup
            have hfind_fp : (πI.filter
                (fun x => !(ρ.any fun (w, _) => w == x.1))).find?
                (fun p => p.1 == v) = some (v, d₁) :=
              find?_eq_of_nodup_mem _ v d₁ hnodup_filt hfilt_mem
            have hfind_rho' : (ρ'.find? fun p => p.1 == v) = some (v, d₁) := by
              rw [hρ'_def]
              simp only [combineRestrictions, List.find?_append, hρ_find,
                Option.none_or, hfind_fp]
            have hfind_rhs : ((combineRestrictions ρ' restEncoder.1).find?
                fun p => p.1 == v) = some (v, d₁) := by
              simp only [combineRestrictions, List.find?_append, hfind_rho',
                Option.some_or]
            have hcr_rhs : restrictionAsFunction
                (combineRestrictions ρ' restEncoder.1) v = some d₁ := by
              simp only [restrictionAsFunction, hfind_rhs]
            rw [hcr_lhs, hcr_rhs]
          · -- v ∉ πI.
            have hfind_rev : (πI.reverse.find? fun p => p.1 == v) = none := by
              rw [List.find?_eq_none]
              intro ⟨w, d⟩ hmem
              simp only [beq_iff_eq]
              rw [List.mem_reverse] at hmem
              intro habs
              exact hv_pi (habs ▸ List.mem_map_of_mem (f := Prod.fst) hmem)
            have hcr_lhs : restrictionAsFunction (πI.reverse ++ B_cur) v =
                restrictionAsFunction B_cur v := by
              simp only [restrictionAsFunction, List.find?_append, hfind_rev, Option.none_or]
            rw [hcr_lhs, h_b_at_v_gen]
            -- Goal: extending ρ and ρ' by `restEncoder.1` induces the same value at v.
            simp only [combineRestrictions]
            simp only [restrictionAsFunction, List.find?_append]
            rw [hρ'_def]
            simp only [combineRestrictions]
            rw [List.find?_append]
            cases hfρ : ρ.find? (fun p => p.1 == v) with
            | some val =>
              simp only [Option.some_or]
            | none =>
              simp only [Option.none_or]
              have hfilt_fp_none : (πI.filter
                  (fun x => !(ρ.any fun (w, _) => w == x.1))).find?
                  (fun p => p.1 == v) = none := by
                rw [List.find?_eq_none]
                intro ⟨w, d⟩ hmem
                simp only [beq_iff_eq]
                intro habs
                exact hv_pi (habs ▸ List.mem_map_of_mem (f := Prod.fst)
                  (List.mem_of_mem_filter hmem))
              rw [hfilt_fp_none]
              simp only [Option.none_or]
              have hρ_any_v : (ρ.any fun (w, _) => w == v) = false := by
                rw [list_any_eq_cr_none_isSome]
                simp only [restrictionAsFunction, hfρ, Option.isSome]
              have hfp_filt_any_v :
                  ((πI.filter fun x => !(ρ.any fun (w, _) => w == x.1)).any
                    fun (w, _) => w == v) = false := by
                rw [List.any_eq_false]
                intro ⟨w, d⟩ hmem
                simp only [beq_iff_eq]
                intro habs
                exact hv_pi (habs ▸ List.mem_map_of_mem (f := Prod.fst)
                  (List.mem_of_mem_filter hmem))
              induction restEncoder.1 with
              | nil => simp
              | cons hd tl ih_rest =>
                simp only [List.filter_cons]
                by_cases hd_eq : hd.1 = v
                · have hf1 : (!(ρ.any fun (w, _) => w == hd.1)) = true := by
                    rw [hd_eq, hρ_any_v]; decide
                  have hf2 : (!((ρ ++ πI.filter fun x =>
                      !(ρ.any fun (w, _) => w == x.1)).any
                      fun (w, _) => w == hd.1)) = true := by
                    rw [hd_eq, List.any_append, hρ_any_v, hfp_filt_any_v]; decide
                  rw [if_pos hf1, if_pos hf2]
                  have hbeq_true : (hd.1 == v) = true := by rw [beq_iff_eq]; exact hd_eq
                  simp only [List.find?_cons, hbeq_true]
                · have hhd_skip : (hd.1 == v) = false := by simp [hd_eq]
                  by_cases hf1 : (!(ρ.any fun (w, _) => w == hd.1)) = true <;>
                  by_cases hf2 : (!((ρ ++ πI.filter fun x =>
                      !(ρ.any fun (w, _) => w == x.1)).any
                      fun (w, _) => w == hd.1)) = true
                  · rw [if_pos hf1, if_pos hf2]
                    simp only [List.find?_cons, hhd_skip]
                    exact ih_rest
                  · rw [if_pos hf1, if_neg hf2]
                    simp only [List.find?_cons, hhd_skip]
                    exact ih_rest
                  · exfalso
                    simp only [Bool.not_eq_true'] at hf1
                    have hρ_true : (ρ.any fun (w, _) => w == hd.1) = true := by
                      cases ρ.any fun (w, _) => w == hd.1 <;> simp_all
                    have : ((ρ ++ πI.filter fun x =>
                        !(ρ.any fun (w, _) => w == x.1)).any
                        fun (w, _) => w == hd.1) = true := by
                      rw [List.any_append, hρ_true]; rfl
                    simp only [this, Bool.not_true] at hf2
                    exact absurd hf2 Bool.false_ne_true
                  · rw [if_neg hf1, if_neg hf2]; exact ih_rest
        -- ────────────────────────────────────────────────────────────────────
        -- Derive the next-level loop invariant by splitting on the prefix
        -- relation. Branch 1 (prefix
        -- propagates) constructs the new bundle field-by-field; branch 2
        -- (where `remaining'` prefixes the selected clause's variables) uses
        -- `encoder_branch2_consumes_all`.
        -- ────────────────────────────────────────────────────────────────────
        -- Bundle dnf into UnboundedFanInDNF for the step lemma's signature.
        set N := ufiLargestInput dnf + 1
        have h_n_lt : ufiLargestInput dnf < N := Nat.lt_succ_self _
        let f : UnboundedFanInDNF N := ⟨dnf, h_n_lt, hdnf⟩
        -- Apply the path-prefix lemma by destructuring `hloop`.
        have hstep := encoder_path_prefix_after_one_step
          (n := N) f asgn d path ρ remaining_π
          hloop.hρ_sub_orig
          hloop.hρ_extends_fn_orig hπ_nodup hloop.hρ_disj_orig
          hloop.hrem_sub_outer hloop.hrem_complete_orig
          -- Nonemptiness of the selected clause when `remaining' ≠ []`, obtained by applying
          -- `r_ne_nil_via_canonical_iter_split` to `hloop.hρ_segments_consumed`).
          (encoder_h_r_combined_ne_from_loop_inv (n := N) f hnodup asgn d path ρ remaining_π hloop)
          -- Prefix comparability of the selected clause's variables and `remaining'`.
          (encoder_h_r_combined_pref_from_loop_inv (n := N) f hnodup asgn d path ρ remaining_π hloop)
        -- ────────────────────────────────────────────────────────────────────

        -- SUB-OBLIGATION 4.5 (hdead_sub_ρ' propagation).
        -- dead_acc'.fst ⊆ ρ'-assigned vars (each new γ-bit lands in πI ⊆ ρ').
        -- ────────────────────────────────────────────────────────────────────
        have hdead_sub_ρ' : ∀ v, v ∈ dead_acc'.map Prod.fst →
            (ρ'.any fun (w, _) => w == v) = true := by
          intro v hv
          rw [hdead_acc'_def, List.map_append, List.mem_append] at hv
          rw [hρ'_def]
          show ((ρ ++ πI.filter fun (x, _) => !ρ.any fun (w, _) => w == x).any
              fun (w, _) => w == v) = true
          rw [List.any_append]
          rcases hv with hda | hγ
          · -- v ∈ dead_acc.fst → ρ.any = true → or-true
            rw [hdead_sub_ρ v hda]; rfl
          · -- v ∈ γ_i.fst.  Get (v, b) ∈ πI via U_vars ⊆ remaining_π.
            have hv_full : v ∈ (gammaBitsForClause U_i).map Prod.fst := by
              rw [hγ_i_def, List.map_take] at hγ
              exact List.mem_of_mem_take hγ
            have hv_u : v ∈ U_vars := by
              rw [h_u_vars_def]
              rwa [gamma_bits_map_fst_eq] at hv_full
            have hv_rem : v ∈ remaining_π.map Prod.fst := h_u_sub v hv_u
            obtain ⟨⟨w_x, b'⟩, hmem_rem, hwfst⟩ := List.mem_map.mp hv_rem
            simp only at hwfst
            rw [hwfst] at hmem_rem
            have hv_πi : (v, b') ∈ πI := by
              rw [hπ_i_def]
              refine List.mem_filter.mpr ⟨hmem_rem, ?_⟩
              show p (v, b') = true
              rw [hp_def]
              exact List.contains_iff_mem.mpr hv_u
            -- Case split on ρ.any.
            by_cases hρ_any : (ρ.any fun (w, _) => w == v) = true
            · rw [hρ_any]; rfl
            · -- ρ.any = false; (v, b') survives filter.
              have hρ_false : (ρ.any fun (w, _) => w == v) = false := by
                cases h : ρ.any fun (w, _) => w == v
                · rfl
                · exact absurd h hρ_any
              have hfilt_mem : (v, b') ∈ πI.filter
                  (fun (x, _) => !ρ.any fun (w, _) => w == x) := by
                refine List.mem_filter.mpr ⟨hv_πi, ?_⟩
                show (!ρ.any fun (w, _) => w == v) = true
                rw [hρ_false]; rfl
              have hfilt_any : ((πI.filter
                  (fun (x, _) => !ρ.any fun (w, _) => w == x)).any
                  fun (w, _) => w == v) = true :=
                List.any_eq_true.mpr ⟨(v, b'), hfilt_mem, by simp⟩
              rw [hfilt_any]; simp
        -- ────────────────────────────────────────────────────────────────────
        -- SUB-OBLIGATION 3 (restrictionOfFirstTermNotKilledByList alignment after one decoder step).
        -- Routes through h_b_val' (functionalized) + general alignment helper.
        -- ────────────────────────────────────────────────────────────────────
        have halign' : firstTermNotKilledByList clauses B_cur' =
            firstTermNotKilledByList clauses ρ' := by
          have hcr_eq : restrictionAsFunction B_cur' =
              restrictionAsFunction
                (combineRestrictions ρ' restEncoder.1) := by
            funext v; exact h_b_val' v
          rw [firstTermNotKilledByList_eq_of_cr_none_eq clauses B_cur'
            (combineRestrictions ρ' restEncoder.1)
            (fun v => congrFun hcr_eq v)]
          -- In branch 1, the prefix invariant for `ρ'` propagates directly;
          -- branch 2 consumes all remaining variables in one chunk.
          have hstep_copy := hstep
          rcases hstep_copy with ⟨hpfx_ρ'_b1, _hne_ρ'_b1⟩ | hbranch2_step
          · exact encoder_aux_initial_alignment_gen fuel' remaining' dnf ρ' dead_acc'
              hdnf hnodup hfuel' hdead_sub_ρ'
              asgn d path hloop.hpath
              (fun x hx => hloop.hrem_sub_outer x (List.mem_of_mem_filter hx))
              (fun v hv => Or.inl (hdead_sub_ρ' v hv))
              hpfx_ρ'_b1
          · -- Branch 2 of `hstep`: `remaining'.fst <+: U_vars(ρ').fst`.
            -- The encoder consumes all of `remaining'` in one chunk, then base-cases.
            -- Compute `restEncoder.1` explicitly and compare the surviving clauses.
            show firstTermNotKilledByList clauses (combineRestrictions ρ' restEncoder.1)
                  = firstTermNotKilledByList clauses ρ'
            set A₁_b2 := restrictionAsFunction ρ' with h_a₁_b2_def
            set A₂_b2 := restrictionAsFunction
              (combineRestrictions ρ' restEncoder.1) with h_a₂_b2_def
            apply firstTermNotKilledByList_eq clauses ρ'
              (combineRestrictions ρ' restEncoder.1)
            · intro w hw
              exact cr_none_combineRestrictions_extends_base ρ' restEncoder.1 w hw
            · rw [isClauseKilledBy_eq_isClauseKilled]
              apply not_killed_by_satisfying
              intro ⟨v, neg⟩ hmem_t₀_b2
              by_cases hv : A₁_b2 v = none
              · -- v unassigned in ρ'.
                have hv_ρ_any : (ρ'.any fun (w, _) => w == v) = false := by
                  rw [list_any_eq_cr_none_isSome]
                  show (A₁_b2 v).isSome = false
                  rw [hv]; rfl
                have hv_ρ_find : ρ'.find? (fun p => p.1 == v) = none := by
                  rw [List.find?_eq_none]; intro ⟨x, bx⟩ hmem
                  simp only [BEq.beq]; intro hxv
                  have habs : (ρ'.any fun (w, _) => w == v) = true :=
                    List.any_eq_true.mpr ⟨(x, bx), hmem, by simp [BEq.beq, hxv]⟩
                  simp [habs] at hv_ρ_any
                have h_a₂_simp : A₂_b2 v =
                    match (restEncoder.1.filter
                        (fun x => !(ρ'.any fun (w, _) => w == x.1))).find?
                      (fun p => p.1 == v) with
                    | some (_, b) => some b
                    | none => none := by
                  show A₂_b2 v = _
                  simp only [A₂_b2, combineRestrictions, restrictionAsFunction,
                    List.find?_append, hv_ρ_find, Option.none_or]
                  rfl
                cases hfind : (restEncoder.1.filter
                    (fun x => !(ρ'.any fun (w, _) => w == x.1))).find?
                    (fun p => p.1 == v) with
                | none =>
                  left
                  change A₂_b2 v = none
                  rw [h_a₂_simp, hfind]
                | some pair =>
                  right
                  obtain ⟨w, bw⟩ := pair
                  change A₂_b2 v = some (literalSatisfyingBit neg)
                  rw [h_a₂_simp, hfind]
                  simp only
                  congr 1
                  have hmem_filt := List.mem_of_find?_eq_some hfind
                  have hmem_dead : (w, bw) ∈ restEncoder.1 :=
                    List.mem_of_mem_filter hmem_filt
                  have hw_eq : w = v := by
                    have := List.find?_some hfind
                    simpa [BEq.beq] using this
                  rw [hw_eq] at hmem_dead
                  -- hmem_dead : (v, bw) ∈ restEncoder.1.
                  -- (v, bw) ∉ dead_acc' (else hdead_sub_ρ' contradicts hv_ρ_any).
                  have hnot_dead : (v, bw) ∉ dead_acc' := by
                    intro hd
                    have habs := hdead_sub_ρ' v
                      (List.mem_map_of_mem (f := Prod.fst) hd)
                    rw [habs] at hv_ρ_any; cases hv_ρ_any
                  -- Compute restEncoder.1 explicitly via case-split on remaining' = [].
                  by_cases hrem'_empty : remaining' = []
                  · -- restEncoder.1 = dead_acc' (no γ added). Contradiction.
                    exfalso
                    have hrest2 : restEncoder.1 = dead_acc' := by
                      rw [h_rest_encoder_def]
                      cases fuel' with
                      | zero => simp [beameEncoderAux]
                      | succ n =>
                        simp only [beameEncoderAux, if_pos hrem'_empty]
                    rw [hrest2] at hmem_dead
                    exact hnot_dead hmem_dead
                  · -- restEncoder.1 = dead_acc' ++ γ_i'.
                    set U_i'_b2 := restrictionOfFirstTermNotKilledByList clauses ρ'
                      with h_u_i'_b2_def
                    set U_vars'_b2 := U_i'_b2.map Prod.fst with h_u_vars'_b2_def
                    set p'_b2 : (Nat × Bool) → Bool :=
                      fun x => U_vars'_b2.contains x.1 with hp'_b2_def
                    set πI'_b2 := remaining'.filter p'_b2 with hπ_i'_b2_def
                    set γ_i'_b2 := (gammaBitsForClause U_i'_b2).take πI'_b2.length
                      with hγ_i'_b2_def
                    set dead_acc''_b2 := dead_acc' ++ γ_i'_b2 with hdead_acc''_b2_def
                    have hsub_b2_v : ∀ v ∈ remaining'.map Prod.fst, v ∈ U_vars'_b2 :=
                      fun _ hv => hbranch2_step.subset hv
                    obtain ⟨hπ'_eq_b2, hrem''_eq_b2⟩ :=
                      encoder_branch2_consumes_all (clauses := clauses) ρ' remaining'
                        hsub_b2_v
                    have hπ'_len_ne : πI'_b2.length ≠ 0 := by
                      rw [show πI'_b2 = remaining' from hπ'_eq_b2]
                      intro h
                      exact hrem'_empty (List.length_eq_zero_iff.mp h)
                    have hfuel'_pos : 0 < fuel' :=
                      lt_of_lt_of_le (List.length_pos_iff.mpr hrem'_empty) hfuel'
                    obtain ⟨n', hfuel'_eq⟩ : ∃ n', fuel' = n' + 1 :=
                      ⟨fuel' - 1, by omega⟩
                    have hrec_nil : beameEncoderAux n'
                        (remaining'.filter
                          (fun (w, _) => !πI'_b2.any fun (w', _) => w' == w))
                        (dnfClauses dnf) (combineRestrictions ρ' πI'_b2) dead_acc''_b2
                        = (dead_acc''_b2, []) := by
                      rw [hrem''_eq_b2]
                      cases n' with
                      | zero => rfl
                      | succ k => simp [beameEncoderAux]
                    have hrest2 : restEncoder.1 = dead_acc''_b2 := by
                      rw [h_rest_encoder_def, hfuel'_eq]
                      conv_lhs => rw [beameEncoderAux]
                      rw [if_neg hrem'_empty]
                      show (if πI'_b2.length = 0 then (dead_acc''_b2, []) else
                            (((beameEncoderAux n'
                                (remaining'.filter
                                  (fun (w, _) =>
                                    !πI'_b2.any fun (w', _) => w' == w))
                                (dnfClauses dnf) (combineRestrictions ρ' πI'_b2)
                                dead_acc''_b2).1,
                              encoderChunk
                                (firstTermNotKilledByList clauses ρ') πI'_b2 ::
                                (beameEncoderAux n'
                                (remaining'.filter
                                  (fun (w, _) =>
                                    !πI'_b2.any fun (w', _) => w' == w))
                                (dnfClauses dnf) (combineRestrictions ρ' πI'_b2)
                                dead_acc''_b2).2) :
                              List (Nat × Bool) × List (List (Nat × Bool)))).1
                          = dead_acc''_b2
                      rw [if_neg hπ'_len_ne, hrec_nil]
                    rw [hrest2, hdead_acc''_b2_def, List.mem_append] at hmem_dead
                    rcases hmem_dead with hda | hγ_b2
                    · exact absurd hda hnot_dead
                    · -- (v, bw) ∈ γ_i'_b2: bridge polarity via U_i' ⊆ T_i' nodup.
                      have hγ_full : (v, bw) ∈ gammaBitsForClause U_i'_b2 :=
                        List.mem_of_mem_take hγ_b2
                      simp only [gammaBitsForClause, List.mem_map] at hγ_full
                      obtain ⟨⟨w_u, n_u⟩, hwu_mem, hwu_eq⟩ := hγ_full
                      have hbw_eq : bw = literalSatisfyingBit n_u := by
                        have := congrArg Prod.snd hwu_eq; simp at this
                        exact this.symm
                      have hw_v : w_u = v := by
                        have := congrArg Prod.fst hwu_eq; simp at this
                        exact this
                      rw [hw_v] at hwu_mem
                      have hn_u_t : (v, n_u) ∈
                          firstTermNotKilledByList clauses ρ' := by
                        rw [h_u_i'_b2_def] at hwu_mem
                        unfold restrictionOfFirstTermNotKilledByList at hwu_mem
                        exact restrictClauseByListAssignment_subset _ _ _ hwu_mem
                      have h_t_nodup : (firstTermNotKilledByList clauses ρ').map
                          Prod.fst |>.Nodup := by
                        rcases firstTermNotKilledByList_mem_or_nil clauses ρ'
                          with h | h
                        · exact hnodup _ h
                        · exfalso; rw [h] at hmem_t₀_b2; simp at hmem_t₀_b2
                      rw [hbw_eq]
                      exact congrArg literalSatisfyingBit
                        (nodup_map_fst_eq_snd h_t_nodup hn_u_t hmem_t₀_b2)
              · -- v assigned in ρ'.
                right
                show A₂_b2 v = some (literalSatisfyingBit neg)
                have h_a₂_eq : A₂_b2 v = A₁_b2 v :=
                  cr_none_combineRestrictions_extends_base ρ' restEncoder.1 v hv
                rw [h_a₂_eq]
                have hself := firstTermNotKilledByList_self clauses ρ'
                rw [isClauseKilledBy_eq_isClauseKilled] at hself
                simp only [isClauseKilled] at hself
                rw [List.any_eq_false] at hself
                have hns := hself (v, neg) hmem_t₀_b2
                simp only at hns
                cases hav : A₁_b2 v with
                | none => exact absurd hav hv
                | some bv =>
                  have hav' : restrictionAsFunction ρ' v = some bv := hav
                  rw [hav'] at hns
                  simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hns
                  push Not at hns
                  rw [hns]
        -- Hoisted: γ_i = gammaBitsForClause U_i (full take, no truncation).
        -- Used by both branches in the final iff.
        obtain ⟨tail_h, htail_h⟩ := hloop.hpfx_ρ
        have hmap_take_h : (remaining_π.map Prod.fst).take U_vars.length = U_vars := by
          rw [htail_h.symm]; exact List.take_left
        have h_l_fst_h : (remaining_π.take U_vars.length).map Prod.fst = U_vars := by
          rw [List.map_take, hmap_take_h]
        have h_l_filt_self_h : (remaining_π.take U_vars.length).filter p =
            remaining_π.take U_vars.length := by
          apply List.filter_eq_self.mpr
          intro x hx
          rw [hp_def]
          show U_vars.contains x.1 = true
          apply List.contains_iff_mem.mpr
          have : x.1 ∈ (remaining_π.take U_vars.length).map Prod.fst :=
            List.mem_map_of_mem (f := Prod.fst) hx
          rw [h_l_fst_h] at this; exact this
        have hπi_split_h : πI = remaining_π.take U_vars.length ++
            (remaining_π.drop U_vars.length).filter p := by
          show remaining_π.filter p = _
          conv_lhs => rw [show remaining_π =
            remaining_π.take U_vars.length ++ remaining_π.drop U_vars.length
            from (List.take_append_drop _ _).symm]
          rw [List.filter_append, h_l_filt_self_h]
        have hπi_len_ge_h : U_i.length ≤ πI.length := by
          rw [hπi_split_h, List.length_append]
          have h_l_len : (remaining_π.take U_vars.length).length = U_vars.length := by
            rw [← List.length_map (f := Prod.fst), h_l_fst_h]
          have h_uv_eq_ui : U_vars.length = U_i.length := by
            rw [h_u_vars_def, List.length_map]
          rw [h_l_len, h_uv_eq_ui]
          omega
        have hg_len_h : (gammaBitsForClause U_i).length = U_i.length := by
          simp [gammaBitsForClause]
        have hγ_full : γ_i = gammaBitsForClause U_i := by
          rw [hγ_i_def]
          apply List.take_of_length_le
          rw [hg_len_h]; exact hπi_len_ge_h
        -- Case-split on step lemma to either propagate the bundle (branch 1)
        -- or short-circuit (branch 2).
        rcases hstep with ⟨hpfx_ρ', hne_ρ'⟩ | hbranch2
        · -- Branch 1: prefix invariant propagates; build hloop' for IH.
          -- ── Side conditions for the new loop-invariant bundle. ──
          have hρ_sub_orig' : ∀ w b, (w, b) ∈ ρ' →
              (w, b) ∈ asgn ∨ (w, b) ∈ path.take d := by
            intro w b hwb
            rw [hρ'_def] at hwb
            simp only [combineRestrictions, List.mem_append] at hwb
            rcases hwb with hwb | hwb
            · exact hloop.hρ_sub_orig w b hwb
            · exact Or.inr (hloop.hrem_sub_outer (w, b)
                (List.mem_of_mem_filter (List.mem_of_mem_filter hwb)))
          have hρ_extends_fn_orig' : ∀ w,
              restrictionAsFunction asgn w ≠ none →
              restrictionAsFunction ρ' w =
              restrictionAsFunction asgn w := by
            intro w hw_ne
            have hρw : restrictionAsFunction ρ w =
                restrictionAsFunction asgn w :=
              hloop.hρ_extends_fn_orig w hw_ne
            have hρ_some : ∃ v, ρ.find? (fun p => p.1 == w) = some v := by
              have hne : restrictionAsFunction ρ w ≠ none := hρw ▸ hw_ne
              simp only [restrictionAsFunction] at hne
              cases h : ρ.find? fun p => p.1 == w with
              | none => simp [h] at hne
              | some v => exact ⟨v, rfl⟩
            obtain ⟨v, hf⟩ := hρ_some
            have h_lhs : restrictionAsFunction ρ' w = some v.2 := by
              rw [hρ'_def]
              simp only [restrictionAsFunction, combineRestrictions,
                List.find?_append, hf, Option.some_or]
            have hρ_val : restrictionAsFunction ρ w = some v.2 := by
              simp only [restrictionAsFunction, hf]
            rw [h_lhs, ← hρ_val, hρw]
          have hρ_disj_orig' : ∀ w b, (w, b) ∈ remaining' →
              (ρ'.any fun (z, _) => z == w) = false := by
            intro w b hwb
            rw [hremaining'_def] at hwb
            have hwb_rem : (w, b) ∈ remaining_π := List.mem_of_mem_filter hwb
            have hρ_no : (ρ.any fun (z, _) => z == w) = false :=
              hloop.hρ_disj_orig w b hwb_rem
            have hwb_pred : (!πI.any fun (w', _) => w' == w) = true :=
              (List.mem_filter.mp hwb).2
            have hπi_no : (πI.any fun (w', _) => w' == w) = false := by
              cases hh : πI.any fun (w', _) => w' == w with
              | true => rw [hh] at hwb_pred; simp at hwb_pred
              | false => rfl
            have hfilt_no : ((πI.filter
                (fun p => !ρ.any fun (z, _) => z == p.1)).any
                fun p => p.1 == w) = false := by
              cases hh : (πI.filter (fun p => !ρ.any fun (z, _) => z == p.1)).any
                  fun p => p.1 == w with
              | false => rfl
              | true =>
                rw [List.any_eq_true] at hh
                obtain ⟨⟨w', b'⟩, hmem, hbeq⟩ := hh
                have hin_πi : (w', b') ∈ πI := List.mem_of_mem_filter hmem
                have habs : (πI.any fun p => p.1 == w) = true :=
                  List.any_eq_true.mpr ⟨(w', b'), hin_πi, hbeq⟩
                rw [hπi_no] at habs; exact absurd habs (by decide)
            rw [hρ'_def]
            simp only [combineRestrictions, List.any_append, hρ_no, hfilt_no,
              Bool.or_self]
          have hrem_sub_outer' : ∀ x ∈ remaining', x ∈ path.take d := by
            intro x hx
            rw [hremaining'_def] at hx
            exact hloop.hrem_sub_outer x (List.mem_of_mem_filter hx)
          have hrem_complete_orig' : ∀ x ∈ path.take d,
              (ρ'.any fun (z, _) => z == x.1) = false → x ∈ remaining' := by
            intro x hx hno
            rw [hρ'_def] at hno
            simp only [combineRestrictions, List.any_append,
              Bool.or_eq_false_iff] at hno
            obtain ⟨hρ_no, hfilt_no⟩ := hno
            have hx_rem : x ∈ remaining_π := hloop.hrem_complete_orig x hx hρ_no
            have hπ_no : (πI.any fun (w', _) => w' == x.1) = false := by
              cases hp : πI.any fun (w', _) => w' == x.1 with
              | false => rfl
              | true =>
                exfalso
                rw [List.any_eq_true] at hp
                obtain ⟨⟨w'', b''⟩, hw_πi, hw_eq⟩ := hp
                simp only at hw_eq
                have hw_rem : (w'', b'') ∈ remaining_π :=
                  List.mem_of_mem_filter hw_πi
                have hρ_no_w : (ρ.any fun (z, _) => z == w'') = false :=
                  hloop.hρ_disj_orig w'' b'' hw_rem
                have hsurv : (w'', b'') ∈ πI.filter
                    (fun p => !ρ.any fun (z, _) => z == p.1) := by
                  refine List.mem_filter.mpr ⟨hw_πi, ?_⟩
                  show (!ρ.any fun (z, _) => z == w'') = true
                  rw [hρ_no_w]; rfl
                have hbad : ((πI.filter (fun p => !ρ.any fun (z, _) => z == p.1)).any
                    fun p => p.1 == x.1) = true :=
                  List.any_eq_true.mpr ⟨(w'', b''), hsurv, hw_eq⟩
                rw [hbad] at hfilt_no; exact absurd hfilt_no (by decide)
            rw [hremaining'_def]
            refine List.mem_filter.mpr ⟨hx_rem, ?_⟩
            show (!πI.any fun (w', _) => w' == x.1) = true
            rw [hπ_no]; rfl
          have hrem_sublist' : remaining'.Sublist (path.take d) := by
            rw [hremaining'_def]
            exact List.Sublist.trans List.filter_sublist hloop.hrem_sublist
          have hpre_ρ_inv' : ∀ v ∈ (restrictionOfFirstTermNotKilledByList
              (dnfClauses dnf) asgn).map Prod.fst,
              (ρ'.any fun (z, _) => z == v) = true ∨
              v ∈ (restrictionOfFirstTermNotKilledByList
                (dnfClauses dnf) ρ').map Prod.fst := by
            intro v hv
            -- Use bundle `hpfx_ρ'` to show that if `v` is absent from the
            -- selected clause under ρ', then it was consumed by ρ',
            -- or there's no path forward.  Simpler: case-split via the
            -- outer `hpre_ρ_inv` and lift `ρ.any → ρ'.any`.
            rcases hloop.hpre_ρ_inv v hv with h_ρ_any | h_v_r
            · left
              -- ρ.any = true → ρ'.any = true since ρ ⊆ ρ'.
              rw [hρ'_def]
              simp only [combineRestrictions, List.any_append, h_ρ_any,
                Bool.true_or]
            · -- Since `v` is in the selected clause under ρ, `hpfx_ρ.subset`
              -- places it in `remaining_π.map Prod.fst`.
              -- So ∃ b, (v,b) ∈ remaining_π, hence (v,b) ∈ πI (v ∈ U_vars),
              -- hence ρ' contains (v,b), so ρ'.any v = true.
              left
              have hv_rem : v ∈ remaining_π.map Prod.fst :=
                hloop.hpfx_ρ.subset h_v_r
              obtain ⟨⟨w_x, b'⟩, hmem_rem, hwfst⟩ := List.mem_map.mp hv_rem
              simp only at hwfst
              rw [hwfst] at hmem_rem
              have hv_πi : (v, b') ∈ πI := by
                rw [hπ_i_def]
                refine List.mem_filter.mpr ⟨hmem_rem, ?_⟩
                show p (v, b') = true
                rw [hp_def]
                exact List.contains_iff_mem.mpr h_v_r
              -- Now (v, b') ∈ πI ⊆ ρ' (in the combineRestrictions sense).  Show ρ'.any v = true.
              by_cases hρ_any : (ρ.any fun (z, _) => z == v) = true
              · rw [hρ'_def]
                simp only [combineRestrictions, List.any_append, hρ_any,
                  Bool.true_or]
              · have hρ_false : (ρ.any fun (z, _) => z == v) = false := by
                  cases h : ρ.any fun (z, _) => z == v
                  · rfl
                  · exact absurd h hρ_any
                have hfilt_mem : (v, b') ∈ πI.filter
                    (fun (x, _) => !ρ.any fun (w, _) => w == x) := by
                  refine List.mem_filter.mpr ⟨hv_πi, ?_⟩
                  show (!ρ.any fun (w, _) => w == v) = true
                  rw [hρ_false]; rfl
                have hfilt_any : ((πI.filter
                    (fun (x, _) => !ρ.any fun (w, _) => w == x)).any
                    fun (z, _) => z == v) = true :=
                  List.any_eq_true.mpr ⟨(v, b'), hfilt_mem, by simp⟩
                rw [hρ'_def]
                simp only [combineRestrictions, List.any_append, hfilt_any,
                  Bool.or_true]
          have hloop' : EncoderLoopInv dnf asgn d path ρ' remaining' := {
            hpath := hloop.hpath
            hpfx_ρ := hpfx_ρ'
            hρ_sub_orig := hρ_sub_orig'
            hρ_extends_fn_orig := hρ_extends_fn_orig'
            hρ_disj_orig := hρ_disj_orig'
            hrem_sub_outer := hrem_sub_outer'
            hrem_complete_orig := hrem_complete_orig'
            hrem_sublist := hrem_sublist'
            hpre_ρ_inv := hpre_ρ_inv'
            h_clauses_ne_nil := hloop.h_clauses_ne_nil
            hρ_segments_consumed := by
              -- Extend `k` to `k+1` using
              -- `encoder_step_hρ_segments_consumed` for non-last,
              -- in-window segments, with a separate inline proof for the
              -- last-segment partial-consumption case.
              obtain ⟨segs_canon, k, partial_seg_in, hpath_eq_canon, hk_le,
                hprov_canon, hvm_canon, hne_within_d_in, hρ_eq_canon, hdisj_in⟩ :=
                hloop.hρ_segments_consumed
              -- Path-fst Nodup from canonical-DT.
              have hpath_nodup_fst :=
                canonical_dt_path_nodup_fst f.val asgn hnodup d path
                  hloop.hpath
              -- asgn-disjointness of every path bit, via canonical-DT.
              have hasgn_disj_path : ∀ p ∈ path,
                  (asgn.any fun (z, _) => z == p.1) = false := by
                intro p hp
                have hp1_none : restrictionAsFunction asgn p.1 = none :=
                  canonical_dt_path_var_none f.val asgn f.property.2 d path
                    hloop.hpath p.1 p.2 hp
                by_contra hany
                rw [Bool.not_eq_false] at hany
                rw [List.any_eq_true] at hany
                obtain ⟨⟨w', b'⟩, hw'_mem, hw'_eq⟩ := hany
                simp at hw'_eq
                subst hw'_eq
                simp only [restrictionAsFunction] at hp1_none
                have hfind : asgn.find? (fun q => q.1 == p.1) ≠ none := by
                  rw [Ne, List.find?_eq_none]; push Not
                  exact ⟨(p.1, b'), hw'_mem, by simp⟩
                rcases hfind_eq : asgn.find? (fun q => q.1 == p.1) with _ | ⟨_, _⟩
                · exact hfind hfind_eq
                · rw [hfind_eq] at hp1_none; cases hp1_none
              -- Case-split on the input bundle's discriminant.
              rcases hdisj_in with ⟨hpartial_in_nil, hrem_eq_canon, hwindow_in⟩ | ⟨_, _, hrem_in_nil⟩
              · -- INPUT REGULAR STATE: partial_seg_in = [], regular remaining_π eqn.
                subst hpartial_in_nil
                rw [List.append_nil] at hρ_eq_canon
                -- Loop progressing: k < segs_canon.length, since πI ≠ ∅
                -- ⇒ remaining_π ≠ ∅ ⇒ (segs_canon.drop k).flatten ≠ ∅.
                have hk_lt : k < segs_canon.length := by
                  by_contra hk_ge
                  push Not at hk_ge
                  have hdrop_nil : segs_canon.drop k = [] :=
                    List.drop_eq_nil_iff.mpr hk_ge
                  have hrem_nil : remaining_π = [] := by
                    rw [hrem_eq_canon, hdrop_nil]; simp
                  have hπi_sub : πI.length ≤ remaining_π.length :=
                    List.Sublist.length_le List.filter_sublist
                  rw [hrem_nil] at hπi_sub
                  simp at hπi_sub
                  exact hπ0 (List.length_eq_zero_iff.mpr hπi_sub)
                have hπ_i_eq_for_helper :
                    πI = remaining_π.filter (fun x =>
                      (restrictionOfFirstTermNotKilledByList
                        (dnfClauses dnf) ρ).map Prod.fst |>.contains x.1) := rfl
                -- Now case-split: is segs[k].1 within the depth-d window?
                by_cases hwin : ∀ p ∈ (segs_canon[k]'hk_lt).1, p ∈ path.take d
                · -- Within window: use the existing step helper.
                  exact encoder_step_hρ_segments_consumed dnf hdnf asgn d path
                    hpath_nodup_fst hasgn_disj_path ρ remaining_π
                    segs_canon k hpath_eq_canon hk_le hk_lt hprov_canon hvm_canon
                    hρ_eq_canon hrem_eq_canon πI hπ_i_eq_for_helper
                    ρ' remaining' hρ'_def hremaining'_def hwin hne_within_d_in
                · -- Not within window: derive structural facts via path-Nodup.
                  --
                  -- Key observation: from `hwin` negation we get a bit `b ∈ segs[k].1`
                  -- past depth `d`.  By path nodup-fst + structural-lemma
                  -- `path_drop_disjoint_take_d`, every bit in `(segs.drop (k+1)).flatten`
                  -- is also past depth `d`, so its `filter window` is empty.
                  -- Hence `remaining_π = segs[k].1.filter window` (without needing
                  -- `k+1 = segs.length`).  This makes πI ⊆ segs[k].1 (Sublist) and
                  -- yields `remaining' = []` via the canonical-DT bridge
                  -- the selected clause under ρ has the variables of `segs[k].1`.
                  push Not at hwin
                  obtain ⟨b, hb_seg, hb_notake⟩ := hwin
                  -- Path decomposition: path = (take k).flatten ++ segs[k].1 ++ (drop (k+1)).flatten.
                  have hsplit_segs : segs_canon =
                      segs_canon.take k ++
                        (segs_canon[k]'hk_lt :: segs_canon.drop (k+1)) := by
                    rw [← List.drop_eq_getElem_cons hk_lt, List.take_append_drop]
                  have hpath_split : path =
                      ((segs_canon.take k).map Prod.fst).flatten ++
                      (segs_canon[k]'hk_lt).1 ++
                      ((segs_canon.drop (k+1)).map Prod.fst).flatten := by
                    rw [hpath_eq_canon]
                    conv_lhs => rw [hsplit_segs]
                    rw [List.map_append, List.flatten_append, List.map_cons,
                      List.flatten_cons, List.append_assoc]
                  -- Structural lemma: every bit in (drop (k+1)).flatten is past depth d.
                  have h_drop_notake : ∀ q ∈
                      ((segs_canon.drop (k+1)).map Prod.fst).flatten, q ∉ path.take d :=
                    path_drop_disjoint_take_d path
                      (((segs_canon.take k).map Prod.fst).flatten)
                      ((segs_canon[k]'hk_lt).1)
                      (((segs_canon.drop (k+1)).map Prod.fst).flatten)
                      d hpath_nodup_fst hpath_split b hb_seg hb_notake
                  -- Translate to the window predicate (decidable equality on Nat × Bool).
                  have h_drop_filter_nil :
                      (((segs_canon.drop (k+1)).map Prod.fst).flatten).filter
                        (fun p => (path.take d).any
                          (fun q => q.1 == p.1 && q.2 == p.2)) = [] := by
                    rw [List.filter_eq_nil_iff]
                    intro q hq hany
                    apply h_drop_notake q hq
                    rw [List.any_eq_true] at hany
                    obtain ⟨r, hr_take, hreq⟩ := hany
                    have hr_eq_q : r = q := by
                      have h1 : r.1 = q.1 := by
                        have := (Bool.and_eq_true _ _).mp hreq
                        exact (beq_iff_eq).mp this.1
                      have h2 : r.2 = q.2 := by
                        have := (Bool.and_eq_true _ _).mp hreq
                        exact (beq_iff_eq).mp this.2
                      exact Prod.ext h1 h2
                    rw [← hr_eq_q]; exact hr_take
                  -- (segs.drop k).flatten.fst = segs[k].1 ++ (segs.drop (k+1)).flatten.fst.
                  have h_drop_k : ((segs_canon.drop k).map Prod.fst).flatten =
                      (segs_canon[k]'hk_lt).1 ++
                        ((segs_canon.drop (k+1)).map Prod.fst).flatten := by
                    rw [List.drop_eq_getElem_cons hk_lt, List.map_cons, List.flatten_cons]
                  -- remaining_π = segs[k].1.filter window.
                  have hrem_eq_seg : remaining_π =
                      (segs_canon[k]'hk_lt).1.filter
                        (fun p => (path.take d).any
                          (fun q => q.1 == p.1 && q.2 == p.2)) := by
                    rw [hrem_eq_canon, h_drop_k, List.filter_append, h_drop_filter_nil,
                      List.append_nil]
                  -- πI.Sublist segs[k].1.
                  have hπi_sub_seg : πI.Sublist (segs_canon[k]'hk_lt).1 := by
                    rw [hπ_i_def, hrem_eq_seg]
                    exact List.filter_sublist.trans List.filter_sublist
                  -- Canonical bridge from the selected clause under ρ to
                  -- `segs[k].1`, used to prove `remaining' = []`.
                  obtain ⟨tail_k, hsimp⟩ := hprov_canon k hk_lt
                  have hcum_sub_path :
                      List.Sublist
                        ((((segs_canon.take k).map Prod.fst).flatten).map Prod.fst)
                        (path.map Prod.fst) := by
                    rw [hpath_eq_canon]
                    have h1 : List.Sublist ((segs_canon.take k).map Prod.fst)
                        (segs_canon.map Prod.fst) :=
                      (List.take_sublist k segs_canon).map _
                    exact (h1.flatten).map _
                  have hcum_nodup :
                      ((((segs_canon.take k).map Prod.fst).flatten).map Prod.fst).Nodup :=
                    hcum_sub_path.nodup hpath_nodup_fst
                  have hasgn_disj_cum : ∀ v ∈
                      (((segs_canon.take k).map Prod.fst).flatten).map Prod.fst,
                      (asgn.any fun q => q.1 == v) = false := by
                    intro v hv
                    have hv_path : v ∈ path.map Prod.fst :=
                      hcum_sub_path.subset hv
                    rcases List.mem_map.mp hv_path with ⟨⟨w, b'⟩, hwb_path, hwfst⟩
                    simp at hwfst; subst hwfst
                    have := hasgn_disj_path (w, b') hwb_path
                    simpa using this
                  have h_r_eq_segs :
                      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf)
                        (asgn ++ ((segs_canon.take k).map Prod.fst).flatten)).map
                        Prod.fst = (segs_canon[k]'hk_lt).2.map Prod.fst :=
                    r_of_combined_eq_restricted_simplify_head dnf hdnf asgn
                      (((segs_canon.take k).map Prod.fst).flatten)
                      hcum_nodup hasgn_disj_cum (segs_canon[k]'hk_lt).2 tail_k hsimp
                  have h_r_ρ_eq_seg_fst :
                      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) ρ).map
                        Prod.fst = (segs_canon[k]'hk_lt).1.map Prod.fst := by
                    rw [hρ_eq_canon, h_r_eq_segs,
                      (hvm_canon _ (List.getElem_mem hk_lt)).symm]
                  -- Construct the witness.
                  refine ⟨segs_canon, k, πI, hpath_eq_canon, hk_le, hprov_canon,
                    hvm_canon, hne_within_d_in, ?_, Or.inr ⟨hk_lt, hπi_sub_seg, ?_⟩⟩
                  · -- ρ' = ρ ++ πI = asgn ++ (segs.take k).flatten ++ πI.
                    rw [hρ'_def]
                    have hπi_disj_ρ : ∀ q ∈ πI, (ρ.any fun (z, _) => z == q.1) = false := by
                      intro q hq_πi
                      have hq_rem : q ∈ remaining_π :=
                        List.mem_of_mem_filter (hπ_i_def ▸ hq_πi)
                      exact hloop.hρ_disj_orig q.1 q.2 hq_rem
                    have h_combined_eq : combineRestrictions ρ πI = ρ ++ πI := by
                      rw [combineRestrictions]
                      congr 1
                      apply List.filter_eq_self.mpr
                      intro q hq_πi
                      have := hπi_disj_ρ q hq_πi
                      simp [this]
                    rw [h_combined_eq, hρ_eq_canon]
                  · -- remaining' = [].
                    rw [hremaining'_def]
                    apply List.filter_eq_nil_iff.mpr
                    intro p hp_rem
                    simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
                      Bool.not_eq_false]
                    have hp_seg : p ∈ (segs_canon[k]'hk_lt).1 := by
                      have : p ∈ (segs_canon[k]'hk_lt).1.filter
                          (fun p => (path.take d).any
                            (fun q => q.1 == p.1 && q.2 == p.2)) := by
                        rw [← hrem_eq_seg]; exact hp_rem
                      exact List.mem_of_mem_filter this
                    have hp_πi : p ∈ πI := by
                      rw [hπ_i_def]
                      refine List.mem_filter.mpr ⟨hp_rem, ?_⟩
                      show ((restrictionOfFirstTermNotKilledByList
                        (dnfClauses dnf) ρ).map Prod.fst).contains p.1 = true
                      rw [h_r_ρ_eq_seg_fst]
                      exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨p, hp_seg, rfl⟩)
                    apply List.any_eq_true.mpr
                    exact ⟨p, hp_πi, by simp⟩
              · -- INPUT TERMINAL STATE: remaining_π = [], contradicts hrem.
                exact absurd hrem_in_nil hrem
          }
          -- Apply IH.  Note: `asgn`, `d`, `path` are fixed from outer
          -- ctx (not generalized in induction); only the loop-state vars
          -- and dependent hypotheses are quantified in the IH.
          have hih := ih remaining' ρ' B_cur' dead_acc' vars_acc'
            hloop' hfuel' hπ_nodup' halign'
            hdead_sub' hdead_sub_ρ' h_b_val' w
          rw [hih]
          -- ────────────────────────────────────────────────────────────────────
          -- SUB-OBLIGATION 6 (final iff in branch 1).
          -- Forward: decompose vars_acc' via decoder_list_inner_foldl_subset
          --   into vars_acc (Or.inl) or chunk-derived → γ_i ⊆ dead_acc' ⊆
          --   restEncoder.1 via encoder_aux_dead_acc_mono (Or.inr).
          -- Backward: vars_acc → vars_acc' via decoder_list_inner_foldl_acc_mono.
          -- Key encoder fact: γ_i = gammaBitsForClause U_i (full, no take)
          --   because πI.length ≥ U_i.length (prefix invariant + nodup).
          -- ────────────────────────────────────────────────────────────────────
          have hvars_acc'_inline : vars_acc' =
              (chunk.foldl
                (fun (acc : List (Nat × Bool) × List (Nat × Bool)) (entry : Nat × Bool) =>
                  let v := (T_i.getD entry.1 (0, false)).1
                  ((v, entry.2) :: acc.1, (v, entry.2) :: acc.2))
                (B_cur, vars_acc)).2 := by
            rw [hvars_acc'_def]
            show (chunk.foldl
              (decoderInnerStep
                (firstTermNotKilledByList clauses B_cur))
              (B_cur, vars_acc)).2 = _
            rw [halign]
            rfl
          -- πI.length ≥ U_i.length, so γ_i = gammaBitsForClause U_i (full).
          -- (Hoisted before rcases hstep.)
          constructor
          · rintro (hva | hre)
            · rw [hvars_acc'_inline] at hva
              rcases decoder_list_inner_foldl_subset T_i chunk B_cur vars_acc w hva
                with horig | ⟨pos, bit, hpos_mem, hw_eq⟩
              · exact Or.inl horig
              · -- chunk-derived: extract v_orig from chunk = encoderChunk T_i πI.
                right
                have hpos_chunk : (pos, bit) ∈ encoderChunk T_i πI := by
                  rw [← hchunk_def]; exact hpos_mem
                simp only [encoderChunk, List.mem_map] at hpos_chunk
                obtain ⟨⟨v_orig, dir⟩, hv_orig_πi, hpb_eq⟩ := hpos_chunk
                simp only [Prod.mk.injEq] at hpb_eq
                obtain ⟨hpos_eq, _hbit_eq⟩ := hpb_eq
                have hv_orig_u : v_orig ∈ U_vars := by
                  have hpred : p (v_orig, dir) = true :=
                    (List.mem_filter.mp (hπ_i_def ▸ hv_orig_πi)).2
                  rw [hp_def] at hpred
                  exact List.mem_of_elem_eq_true hpred
                obtain ⟨⟨v_u, neg_u⟩, hvu_mem, hvu_fst⟩ := List.mem_map.mp hv_orig_u
                simp only at hvu_fst
                rw [hvu_fst] at hvu_mem
                have h_t_any : T_i.any (fun lit => lit.1 == v_orig) = true := by
                  -- v_orig ∈ U_i.map fst → v_orig ∈ T_i.map fst (U_i is a filter of T_i).
                  have hv_t : v_orig ∈ T_i.map Prod.fst := by
                    rw [h_t_i_def]
                    have hv_u : v_orig ∈ U_i.map Prod.fst := by
                      rw [h_u_vars_def] at hv_orig_u; exact hv_orig_u
                    rw [List.mem_map] at hv_u ⊢
                    obtain ⟨pair, hpair_mem, hpair_fst⟩ := hv_u
                    rw [h_u_i_def] at hpair_mem
                    exact ⟨pair, restrictClauseByListAssignment_subset _ _ _ hpair_mem, hpair_fst⟩
                  obtain ⟨lit, hlit_mem, hlit_fst⟩ := List.mem_map.mp hv_t
                  exact List.any_eq_true.mpr ⟨lit, hlit_mem, by simp [hlit_fst]⟩
                have hrt : (T_i.getD pos (0, false)).1 = v_orig := by
                  rw [← hpos_eq]
                  exact findPositionInClause'_roundtrip T_i v_orig h_t_any
                have hw_v : w = v_orig := hw_eq.trans hrt
                have hg_in_γ : (v_orig, literalSatisfyingBit neg_u) ∈ γ_i := by
                  rw [hγ_full]
                  simp only [gammaBitsForClause, List.mem_map]
                  exact ⟨(v_orig, neg_u), hvu_mem, rfl⟩
                have hg_in_dead' : (v_orig, literalSatisfyingBit neg_u) ∈ dead_acc' := by
                  rw [hdead_acc'_def]; exact List.mem_append_right _ hg_in_γ
                have hg_in_rest : (v_orig, literalSatisfyingBit neg_u) ∈ restEncoder.1 := by
                  rw [h_rest_encoder_def]
                  exact encoder_aux_dead_acc_mono fuel' remaining' dnf ρ' dead_acc'
                    v_orig _ hg_in_dead'
                rw [hw_v]
                exact List.mem_map_of_mem (f := Prod.fst) hg_in_rest
            · exact Or.inr hre
          · rintro (hva | hre)
            · left
              rw [hvars_acc'_inline]
              exact decoder_list_inner_foldl_acc_mono T_i chunk B_cur vars_acc w hva
            · exact Or.inr hre
        · -- Branch 2: encoder's next iteration consumes `remaining'` entirely
          -- in one chunk and base-cases.  We compute `restEncoder` directly and
          -- discharge the iff by chunk-tracing through one or two outer
          -- decoder steps (depending on `remaining'`'s emptiness).
          --
          -- hbranch2 : remaining'.map fst <+: U_vars'(ρ').map fst.
          change remaining'.map Prod.fst <+:
            (restrictionOfFirstTermNotKilledByList clauses ρ').map Prod.fst
            at hbranch2
          have hvars_acc'_inline : vars_acc' =
              (chunk.foldl
                (fun (acc : List (Nat × Bool) × List (Nat × Bool)) (entry : Nat × Bool) =>
                  let v := (T_i.getD entry.1 (0, false)).1
                  ((v, entry.2) :: acc.1, (v, entry.2) :: acc.2))
                (B_cur, vars_acc)).2 := by
            rw [hvars_acc'_def]
            show (chunk.foldl
              (decoderInnerStep
                (firstTermNotKilledByList clauses B_cur))
              (B_cur, vars_acc)).2 = _
            rw [halign]
            rfl
          by_cases hrem'_empty : remaining' = []
          · -- Sub-case 2a: remaining' = []. restEncoder = (dead_acc', []).
            have hrest : restEncoder = (dead_acc', []) := by
              rw [h_rest_encoder_def]
              cases fuel' with
              | zero => simp [beameEncoderAux]
              | succ n =>
                simp only [beameEncoderAux, if_pos hrem'_empty]
            rw [hrest]
            simp only [List.foldl_nil]
            -- Goal: w ∈ vars_acc'.fst ↔ w ∈ vars_acc.fst ∨ w ∈ dead_acc'.fst.
            constructor
            · intro hva
              rw [hvars_acc'_inline] at hva
              rcases decoder_list_inner_foldl_subset T_i chunk B_cur vars_acc w hva
                with horig | ⟨pos, bit, hpos_mem, hw_eq⟩
              · exact Or.inl horig
              · right
                have hpos_chunk : (pos, bit) ∈ encoderChunk T_i πI := by
                  rw [← hchunk_def]; exact hpos_mem
                simp only [encoderChunk, List.mem_map] at hpos_chunk
                obtain ⟨⟨v_orig, dir⟩, hv_orig_πi, hpb_eq⟩ := hpos_chunk
                simp only [Prod.mk.injEq] at hpb_eq
                obtain ⟨hpos_eq, _hbit_eq⟩ := hpb_eq
                have hv_orig_u : v_orig ∈ U_vars := by
                  have hpred : p (v_orig, dir) = true :=
                    (List.mem_filter.mp (hπ_i_def ▸ hv_orig_πi)).2
                  rw [hp_def] at hpred
                  exact List.mem_of_elem_eq_true hpred
                obtain ⟨⟨v_u, neg_u⟩, hvu_mem, hvu_fst⟩ := List.mem_map.mp hv_orig_u
                simp only at hvu_fst
                rw [hvu_fst] at hvu_mem
                have h_t_any : T_i.any (fun lit => lit.1 == v_orig) = true := by
                  have hv_t : v_orig ∈ T_i.map Prod.fst := by
                    rw [h_t_i_def]
                    have hv_u : v_orig ∈ U_i.map Prod.fst := by
                      rw [h_u_vars_def] at hv_orig_u; exact hv_orig_u
                    rw [List.mem_map] at hv_u ⊢
                    obtain ⟨pair, hpair_mem, hpair_fst⟩ := hv_u
                    rw [h_u_i_def] at hpair_mem
                    exact ⟨pair, restrictClauseByListAssignment_subset _ _ _ hpair_mem, hpair_fst⟩
                  obtain ⟨lit, hlit_mem, hlit_fst⟩ := List.mem_map.mp hv_t
                  exact List.any_eq_true.mpr ⟨lit, hlit_mem, by simp [hlit_fst]⟩
                have hrt : (T_i.getD pos (0, false)).1 = v_orig := by
                  rw [← hpos_eq]
                  exact findPositionInClause'_roundtrip T_i v_orig h_t_any
                have hw_v : w = v_orig := hw_eq.trans hrt
                have hg_in_γ : (v_orig, literalSatisfyingBit neg_u) ∈ γ_i := by
                  rw [hγ_full]
                  simp only [gammaBitsForClause, List.mem_map]
                  exact ⟨(v_orig, neg_u), hvu_mem, rfl⟩
                have hg_in_dead' : (v_orig, literalSatisfyingBit neg_u) ∈ dead_acc' := by
                  rw [hdead_acc'_def]; exact List.mem_append_right _ hg_in_γ
                rw [hw_v]
                exact List.mem_map_of_mem (f := Prod.fst) hg_in_dead'
            · rintro (hva | hre)
              · rw [hvars_acc'_inline]
                exact decoder_list_inner_foldl_acc_mono T_i chunk B_cur vars_acc w hva
              · exact hdead_sub' w hre
          · -- Sub-case 2b: remaining' ≠ ∅.  Compute one more encoder step.
            have hrem'_pos : 0 < remaining'.length := by
              rw [List.length_pos_iff]; exact hrem'_empty
            have hfuel'_pos : 0 < fuel' := lt_of_lt_of_le hrem'_pos hfuel'
            obtain ⟨n', hfuel'_eq⟩ : ∃ n', fuel' = n' + 1 :=
              ⟨fuel' - 1, by omega⟩
            have hsub_b2 : ∀ v ∈ remaining'.map Prod.fst,
                v ∈ (restrictionOfFirstTermNotKilledByList clauses ρ').map Prod.fst :=
              fun v hv => hbranch2.subset hv
            have hb2 := encoder_branch2_consumes_all (clauses := clauses) ρ' remaining'
              hsub_b2
            obtain ⟨hπ'_eq, hrem''_eq⟩ := hb2
            set U_i' := restrictionOfFirstTermNotKilledByList clauses ρ'
              with h_u_i'_def
            set U_vars' := U_i'.map Prod.fst with h_u_vars'_def
            set p' : (Nat × Bool) → Bool := fun x => U_vars'.contains x.1 with hp'_def
            set πI' := remaining'.filter p' with hπ_i'_def
            set γ_i' := (gammaBitsForClause U_i').take πI'.length with hγ_i'_def
            set dead_acc'' := dead_acc' ++ γ_i' with hdead_acc''_def
            set ρ'' := combineRestrictions ρ' πI' with hρ''_def
            set T_i' := firstTermNotKilledByList clauses ρ' with h_t_i'_def
            set chunk' := encoderChunk T_i' πI' with hchunk'_def
            -- πI' = remaining' (from branch2 lemma).
            have hπ'_eq' : πI' = remaining' := hπ'_eq
            have hπ'_ne : πI' ≠ [] := hπ'_eq'.symm ▸ hrem'_empty
            have hπ'_len_ne : πI'.length ≠ 0 := by
              intro h; exact hπ'_ne (List.length_eq_zero_iff.mp h)
            have hrem''_nil : remaining'.filter
                (fun (w, _) => !πI'.any fun (w', _) => w' == w) = [] :=
              hrem''_eq
            -- Compute restEncoder.
            have hrec : beameEncoderAux n'
                (remaining'.filter
                  (fun (w, _) => !πI'.any fun (w', _) => w' == w))
                (dnfClauses dnf) ρ'' dead_acc'' = (dead_acc'', []) := by
              rw [hrem''_nil]
              cases n' with
              | zero => rfl
              | succ k => simp [beameEncoderAux]
            have hrest_eq : restEncoder = (dead_acc'', [chunk']) := by
              rw [h_rest_encoder_def, hfuel'_eq]
              show beameEncoderAux (n' + 1) remaining' (dnfClauses dnf) ρ' dead_acc'
                = (dead_acc'', [chunk'])
              -- Single-step unfold then dispatch the two `if`s and the recursive call.
              conv_lhs => rw [beameEncoderAux]
              rw [if_neg hrem'_empty]
              -- Now the let-bindings inside match our `set` names definitionally.
              show (if πI'.length = 0 then (dead_acc'', []) else
                    (((beameEncoderAux n'
                      (remaining'.filter
                        (fun (w, _) => !πI'.any fun (w', _) => w' == w))
                      (dnfClauses dnf) ρ'' dead_acc'').1,
                      chunk' :: (beameEncoderAux n'
                        (remaining'.filter
                          (fun (w, _) => !πI'.any fun (w', _) => w' == w))
                        (dnfClauses dnf) ρ'' dead_acc'').2) :
                      List (Nat × Bool) × List (List (Nat × Bool))))
                = (dead_acc'', [chunk'])
              rw [if_neg hπ'_len_ne, hrec]
            rw [hrest_eq]
            simp only [List.foldl_cons, List.foldl_nil]
            -- Goal: w ∈ (decode_outer_step (B_cur', vars_acc') chunk').2.fst ↔
            --       w ∈ vars_acc.fst ∨ w ∈ dead_acc''.fst.
            -- Inline vars_acc'' through halign'.
            have hvars_acc''_inline :
                (decoderOuterStep clauses (B_cur', vars_acc') chunk').2 =
                (chunk'.foldl
                  (fun (acc : List (Nat × Bool) × List (Nat × Bool)) (entry : Nat × Bool) =>
                    let v := (T_i'.getD entry.1 (0, false)).1
                    ((v, entry.2) :: acc.1, (v, entry.2) :: acc.2))
                  (B_cur', vars_acc')).2 := by
              show (chunk'.foldl
                (decoderInnerStep
                  (firstTermNotKilledByList clauses B_cur'))
                (B_cur', vars_acc')).2 = _
              rw [halign']
              rfl
            rw [hvars_acc''_inline]
            -- Forward: split chunk' contribution to γ_i' or back into vars_acc'
            -- (which then splits into contributions from `vars_acc`, `γ_i`, or `dead_acc'`).
            constructor
            · intro hva''
              rcases decoder_list_inner_foldl_subset T_i' chunk' B_cur' vars_acc' w hva''
                with horig | ⟨pos, bit, hpos_mem, hw_eq⟩
              · -- `w ∈ vars_acc'.fst`; decompose `vars_acc'` as the chunk fold
                -- over `vars_acc`.
                rw [hvars_acc'_inline] at horig
                rcases decoder_list_inner_foldl_subset T_i chunk B_cur vars_acc w horig
                  with horig' | ⟨pos₀, bit₀, hpos₀_mem, hw_eq₀⟩
                · exact Or.inl horig'
                · -- chunk-derived from outer step: w ∈ γ_i ⊆ dead_acc' ⊆ dead_acc''.
                  right
                  have hpos_chunk : (pos₀, bit₀) ∈ encoderChunk T_i πI := by
                    rw [← hchunk_def]; exact hpos₀_mem
                  simp only [encoderChunk, List.mem_map] at hpos_chunk
                  obtain ⟨⟨v_orig, dir⟩, hv_orig_πi, hpb_eq⟩ := hpos_chunk
                  simp only [Prod.mk.injEq] at hpb_eq
                  obtain ⟨hpos_eq, _hbit_eq⟩ := hpb_eq
                  have hv_orig_u : v_orig ∈ U_vars := by
                    have hpred : p (v_orig, dir) = true :=
                      (List.mem_filter.mp (hπ_i_def ▸ hv_orig_πi)).2
                    rw [hp_def] at hpred
                    exact List.mem_of_elem_eq_true hpred
                  obtain ⟨⟨v_u, neg_u⟩, hvu_mem, hvu_fst⟩ := List.mem_map.mp hv_orig_u
                  simp only at hvu_fst
                  rw [hvu_fst] at hvu_mem
                  have h_t_any : T_i.any (fun lit => lit.1 == v_orig) = true := by
                    have hv_t : v_orig ∈ T_i.map Prod.fst := by
                      rw [h_t_i_def]
                      have hv_u : v_orig ∈ U_i.map Prod.fst := by
                        rw [h_u_vars_def] at hv_orig_u; exact hv_orig_u
                      rw [List.mem_map] at hv_u ⊢
                      obtain ⟨pair, hpair_mem, hpair_fst⟩ := hv_u
                      rw [h_u_i_def] at hpair_mem
                      exact ⟨pair, restrictClauseByListAssignment_subset _ _ _ hpair_mem, hpair_fst⟩
                    obtain ⟨lit, hlit_mem, hlit_fst⟩ := List.mem_map.mp hv_t
                    exact List.any_eq_true.mpr ⟨lit, hlit_mem, by simp [hlit_fst]⟩
                  have hrt : (T_i.getD pos₀ (0, false)).1 = v_orig := by
                    rw [← hpos_eq]
                    exact findPositionInClause'_roundtrip T_i v_orig h_t_any
                  have hw_v : w = v_orig := hw_eq₀.trans hrt
                  have hg_in_γ : (v_orig, literalSatisfyingBit neg_u) ∈ γ_i := by
                    rw [hγ_full]
                    simp only [gammaBitsForClause, List.mem_map]
                    exact ⟨(v_orig, neg_u), hvu_mem, rfl⟩
                  have hg_in_dead' : (v_orig, literalSatisfyingBit neg_u) ∈ dead_acc' := by
                    rw [hdead_acc'_def]; exact List.mem_append_right _ hg_in_γ
                  have hg_in_dead'' : (v_orig, literalSatisfyingBit neg_u) ∈ dead_acc'' := by
                    rw [hdead_acc''_def]; exact List.mem_append_left _ hg_in_dead'
                  rw [hw_v]
                  exact List.mem_map_of_mem (f := Prod.fst) hg_in_dead''
              · -- chunk' derived: extract v_orig from chunk' = encoderChunk T_i' πI'.
                right
                have hpos_chunk : (pos, bit) ∈ encoderChunk T_i' πI' := by
                  rw [← hchunk'_def]; exact hpos_mem
                simp only [encoderChunk, List.mem_map] at hpos_chunk
                obtain ⟨⟨v_orig, dir⟩, hv_orig_πi, hpb_eq⟩ := hpos_chunk
                simp only [Prod.mk.injEq] at hpb_eq
                obtain ⟨hpos_eq, _hbit_eq⟩ := hpb_eq
                have hv_orig_u' : v_orig ∈ U_vars' := by
                  have hpred : p' (v_orig, dir) = true :=
                    (List.mem_filter.mp (hπ_i'_def ▸ hv_orig_πi)).2
                  rw [hp'_def] at hpred
                  exact List.mem_of_elem_eq_true hpred
                obtain ⟨⟨v_u, neg_u⟩, hvu_mem, hvu_fst⟩ := List.mem_map.mp hv_orig_u'
                simp only at hvu_fst
                rw [hvu_fst] at hvu_mem
                have h_t_any : T_i'.any (fun lit => lit.1 == v_orig) = true := by
                  have hv_t : v_orig ∈ T_i'.map Prod.fst := by
                    rw [h_t_i'_def]
                    have hv_u : v_orig ∈ U_i'.map Prod.fst := by
                      rw [h_u_vars'_def] at hv_orig_u'; exact hv_orig_u'
                    rw [List.mem_map] at hv_u ⊢
                    obtain ⟨pair, hpair_mem, hpair_fst⟩ := hv_u
                    rw [h_u_i'_def] at hpair_mem
                    exact ⟨pair, restrictClauseByListAssignment_subset _ _ _ hpair_mem, hpair_fst⟩
                  obtain ⟨lit, hlit_mem, hlit_fst⟩ := List.mem_map.mp hv_t
                  exact List.any_eq_true.mpr ⟨lit, hlit_mem, by simp [hlit_fst]⟩
                have hrt : (T_i'.getD pos (0, false)).1 = v_orig := by
                  rw [← hpos_eq]
                  exact findPositionInClause'_roundtrip T_i' v_orig h_t_any
                have hw_v : w = v_orig := hw_eq.trans hrt
                -- Need (v_orig, lsb neg_u) ∈ γ_i' = (gamma_bits U_i').take πI'.length.
                -- πI' = remaining', remaining'.fst <+: U_vars' (hbranch2).
                -- So v_orig is in the first remaining'.length entries of U_vars'.
                -- Equivalently, in the first πI'.length entries of gamma_bits U_i'.
                obtain ⟨tail', htail'⟩ := hbranch2
                -- htail' : remaining'.fst ++ tail' = U_vars'.
                -- v_orig ∈ remaining'.fst (since (v_orig, dir) ∈ πI' = remaining').
                have hv_orig_rem'_fst : v_orig ∈ remaining'.map Prod.fst := by
                  rw [← hπ'_eq']
                  exact List.mem_map_of_mem (f := Prod.fst) hv_orig_πi
                -- Index of v_orig in U_vars' = its index in remaining'.fst (< remaining'.length).
                obtain ⟨k, hk_lt, hk_get⟩ := List.mem_iff_getElem.mp hv_orig_rem'_fst
                have hk_lt_πi' : k < πI'.length := by
                  rw [hπ'_eq']
                  rw [List.length_map] at hk_lt; exact hk_lt
                -- (v_orig, neg_u) ∈ U_i' at the same index k (since U_i'.fst = U_vars'
                -- and the first remaining'.length entries match remaining'.fst).
                -- Build directly via gamma_bits structure.
                -- Get U_i'[k] = (v_orig, n_k) for some n_k.
                have hk_lt_uvars' : k < U_vars'.length := by
                  have h_uv_len : U_vars'.length =
                      (remaining'.map Prod.fst).length + tail'.length := by
                    rw [← htail', List.length_append]
                  have hk_lt' : k < remaining'.length := by
                    rw [List.length_map] at hk_lt; exact hk_lt
                  rw [h_uv_len, List.length_map]; omega
                have hk_lt_ui' : k < U_i'.length := by
                  have : U_vars'.length = U_i'.length := by
                    rw [h_u_vars'_def, List.length_map]
                  omega
                -- U_vars'[k] = remaining'.fst[k] = v_orig (from htail' ++).
                have h_uvars'_k : U_vars'[k]'hk_lt_uvars' = v_orig := by
                  have heq : U_vars'[k]'hk_lt_uvars' =
                      (remaining'.map Prod.fst ++ tail')[k]'(by rw [htail']; exact hk_lt_uvars') := by
                    congr 1
                    · exact htail'.symm
                  rw [heq, List.getElem_append_left (h := hk_lt)]
                  exact hk_get
                -- U_i'[k].fst = U_vars'[k] = v_orig.
                have h_ui'_k_fst : (U_i'[k]'hk_lt_ui').1 = v_orig := by
                  have hmap : U_vars' = U_i'.map Prod.fst := h_u_vars'_def
                  have hidx : (U_i'.map Prod.fst)[k]'(by rw [List.length_map]; exact hk_lt_ui')
                      = (U_i'[k]'hk_lt_ui').1 := List.getElem_map _
                  rw [← hidx]
                  have hcvt : U_vars'[k]'hk_lt_uvars' =
                      (U_i'.map Prod.fst)[k]'(by rw [List.length_map]; exact hk_lt_ui') := by
                    congr 1
                  rw [← hcvt]; exact h_uvars'_k
                -- Polarity uniqueness: U_i'[k] = (v_orig, neg_u) (since U_i' has nodup fst
                -- via clauses nodup).
                -- Get the pair at index k.
                set pair_k := U_i'[k]'hk_lt_ui'
                have hpair_k_mem : pair_k ∈ U_i' := List.getElem_mem hk_lt_ui'
                have hpair_k_fst : pair_k.1 = v_orig := h_ui'_k_fst
                -- (v_orig, lsb pair_k.2) ∈ gamma_bits U_i' at index k.
                have hg_at_k : (v_orig, literalSatisfyingBit pair_k.2) ∈
                    (gammaBitsForClause U_i').take πI'.length := by
                  have hg_len : (gammaBitsForClause U_i').length = U_i'.length := by
                    simp [gammaBitsForClause]
                  have hk_lt_g : k < (gammaBitsForClause U_i').length := by
                    rw [hg_len]; exact hk_lt_ui'
                  have hg_take_len : ((gammaBitsForClause U_i').take πI'.length).length =
                      min πI'.length (gammaBitsForClause U_i').length := by
                    simp [List.length_take]
                  have hk_lt_take : k < ((gammaBitsForClause U_i').take πI'.length).length := by
                    rw [hg_take_len]
                    apply Nat.lt_min.mpr ⟨hk_lt_πi', hk_lt_g⟩
                  refine List.mem_iff_getElem.mpr ⟨k, hk_lt_take, ?_⟩
                  rw [List.getElem_take]
                  simp only [gammaBitsForClause, List.getElem_map]
                  rw [show pair_k = U_i'[k]'hk_lt_ui' from rfl]
                  ext
                  · exact hpair_k_fst
                  · rfl
                -- Show pair_k.2 = neg_u (polarity uniqueness via clauses-nodup on T_i').
                -- T_i' = firstTermNotKilledByList clauses ρ', and U_i' = simplify(T_i', ρ').
                -- T_i' has nodup fst (via hnodup on clauses).
                have h_t_i'_nodup : (T_i'.map Prod.fst).Nodup := by
                  rw [h_t_i'_def]
                  rcases firstTermNotKilledByList_mem_or_nil clauses ρ'
                    with hmem | hnil
                  · exact hnodup _ hmem
                  · rw [hnil]; simp
                -- pair_k ∈ U_i' ⊆ T_i'.
                have hpair_k_t : pair_k ∈ T_i' := by
                  rw [h_t_i'_def]
                  have : pair_k ∈ restrictionOfFirstTermNotKilledByList
                      clauses ρ' := by rw [← h_u_i'_def]; exact hpair_k_mem
                  unfold restrictionOfFirstTermNotKilledByList at this
                  exact restrictClauseByListAssignment_subset _ _ _ this
                have hvu_t : (v_orig, neg_u) ∈ T_i' := by
                  rw [h_t_i'_def]
                  have : (v_orig, neg_u) ∈ restrictionOfFirstTermNotKilledByList
                      clauses ρ' := by rw [← h_u_i'_def]; exact hvu_mem
                  unfold restrictionOfFirstTermNotKilledByList at this
                  exact restrictClauseByListAssignment_subset _ _ _ this
                have hpair_k_v : pair_k = (v_orig, neg_u) := by
                  have h1 : pair_k = (v_orig, pair_k.2) := by
                    ext; exact hpair_k_fst; rfl
                  rw [h1]
                  congr 1
                  have hp1 : (v_orig, pair_k.2) ∈ T_i' := h1 ▸ hpair_k_t
                  exact nodup_map_fst_eq_snd h_t_i'_nodup hp1 hvu_t
                rw [hpair_k_v] at hg_at_k
                -- Now (v_orig, lsb neg_u) ∈ γ_i' ⊆ dead_acc''.
                have hg_in_dead'' : (v_orig, literalSatisfyingBit neg_u) ∈ dead_acc'' := by
                  rw [hdead_acc''_def]; exact List.mem_append_right _ hg_at_k
                rw [hw_v]
                exact List.mem_map_of_mem (f := Prod.fst) hg_in_dead''
            · rintro (hva | hre)
              · -- vars_acc → vars_acc' → vars_acc'' via two applications of acc_mono.
                have h1 : w ∈ vars_acc'.map Prod.fst := by
                  rw [hvars_acc'_inline]
                  exact decoder_list_inner_foldl_acc_mono T_i chunk B_cur vars_acc w hva
                exact decoder_list_inner_foldl_acc_mono T_i' chunk' B_cur' vars_acc' w h1
              · -- dead_acc'' = dead_acc' ++ γ_i'.  Split.
                rw [hdead_acc''_def, List.map_append, List.mem_append] at hre
                rcases hre with hda' | hg'
                · -- w ∈ dead_acc'.fst → w ∈ vars_acc'.fst (hdead_sub') → vars_acc''.
                  have h1 : w ∈ vars_acc'.map Prod.fst := hdead_sub' w hda'
                  exact decoder_list_inner_foldl_acc_mono T_i' chunk' B_cur' vars_acc' w h1
                · -- w ∈ γ_i'.fst.  Use hπ'_eq' to get (w, b) ∈ remaining' = πI';
                  -- chunk' contains (find_pos T_i' w, b); produces chunk'-derived
                  -- entry in vars_acc''.fst.
                  have hg'_full : w ∈ (gammaBitsForClause U_i').map Prod.fst := by
                    rw [hγ_i'_def, List.map_take] at hg'
                    exact List.mem_of_mem_take hg'
                  have hw_u' : w ∈ U_vars' := by
                    rw [h_u_vars'_def]
                    rwa [gamma_bits_map_fst_eq] at hg'_full
                  -- v ∈ U_vars' ⊆ T_i'.fst.
                  have hw_t' : w ∈ T_i'.map Prod.fst := by
                    rw [h_t_i'_def]
                    have hv_u : w ∈ U_i'.map Prod.fst := by
                      rw [h_u_vars'_def] at hw_u'; exact hw_u'
                    rw [List.mem_map] at hv_u ⊢
                    obtain ⟨pair, hpair_mem, hpair_fst⟩ := hv_u
                    rw [h_u_i'_def] at hpair_mem
                    exact ⟨pair, restrictClauseByListAssignment_subset _ _ _ hpair_mem, hpair_fst⟩
                  -- Find a `(w, b)` in `πI' = remaining'` via the prefix invariant.
                  obtain ⟨tail2, htail2⟩ := hbranch2
                  -- Since `γ_i'` is the prefix of `U_vars'` with length
                  -- `remaining'.length`, membership in `γ_i'` places `w` in
                  -- `remaining'.map Prod.fst`.
                  have hg_take_fst : ((gammaBitsForClause U_i').take πI'.length).map Prod.fst =
                      U_vars'.take πI'.length := by
                    rw [List.map_take, gamma_bits_map_fst_eq, h_u_vars'_def]
                  have hw_take : w ∈ U_vars'.take πI'.length := by
                    rw [← hg_take_fst]
                    rw [hγ_i'_def] at hg'; exact hg'
                  -- U_vars'.take πI'.length = remaining'.fst (since πI'.length =
                  -- remaining'.length and remaining'.fst <+: U_vars').
                  have hπ'_len_eq : πI'.length = remaining'.length := by
                    rw [hπ'_eq']
                  have h_uvars_take : U_vars'.take πI'.length = remaining'.map Prod.fst := by
                    rw [hπ'_len_eq, ← htail2,
                        show remaining'.length = (remaining'.map Prod.fst).length from
                          (List.length_map _).symm,
                        List.take_left]
                  rw [h_uvars_take] at hw_take
                  -- w ∈ remaining'.fst, so ∃ b, (w, b) ∈ remaining' = πI'.
                  obtain ⟨⟨wx, b⟩, hwb_mem, hwb_fst⟩ := List.mem_map.mp hw_take
                  simp only at hwb_fst
                  rw [hwb_fst] at hwb_mem
                  -- (w, b) ∈ πI' = remaining'.
                  have hwb_πi' : (w, b) ∈ πI' := hπ'_eq'.symm ▸ hwb_mem
                  -- chunk' contains (find_pos T_i' w, b).
                  have hchunk_mem : (findPositionInClause' T_i' w, b) ∈ chunk' := by
                    rw [hchunk'_def]
                    simp only [encoderChunk, List.mem_map]
                    exact ⟨(w, b), hwb_πi', by simp⟩
                  have h_t_any : T_i'.any (fun lit => lit.1 == w) = true := by
                    obtain ⟨lit, hlit_mem, hlit_fst⟩ := List.mem_map.mp hw_t'
                    exact List.any_eq_true.mpr ⟨lit, hlit_mem, by simp [hlit_fst]⟩
                  have hrt : (T_i'.getD (findPositionInClause' T_i' w) (0, false)).1 = w :=
                    findPositionInClause'_roundtrip T_i' w h_t_any
                  have hprod := decoder_list_inner_foldl_produces T_i' chunk' B_cur' vars_acc'
                    (findPositionInClause' T_i' w) b hchunk_mem
                  rw [hrt] at hprod
                  exact hprod

#print axioms encoder_aux_decode_gen_loop

/-- **dead_acc factoring for `beameEncoderAux`.**

    Threading any `dead_acc` through the encoder is equivalent to
    threading `[]` and then prepending `dead_acc` to the dead-vars
    output.  The chunks (`.1`) are independent of `dead_acc` entirely.

    This is the key structural fact that lets us bridge the
    `dead_acc = β` user-facing seed to the `dead_acc = []` loop-invariant
    seed (used by `encoder_aux_decode_gen_loop`). -/
private lemma encoder_aux_dead_acc_factor
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool)) :
    beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc =
    (dead_acc ++ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ []).1,
     (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ []).2) := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero => simp [beameEncoderAux]
  | succ fuel' ih =>
    simp only [beameEncoderAux]
    by_cases hrem : remaining_π = []
    · simp [hrem]
    · simp only [if_neg hrem]
      set clauses := dnfClauses dnf
      set U_i := restrictClauseByListAssignment (firstTermNotKilledByList clauses ρ) ρ
      set U_vars := U_i.map Prod.fst
      set p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
      set πI := remaining_π.filter p
      set γ_i := (gammaBitsForClause U_i).take πI.length
      by_cases hπ0 : πI.length = 0
      · rw [if_pos hπ0, if_pos hπ0]; simp []
      · simp only [if_neg hπ0]
        set ρ' := combineRestrictions ρ πI
        set rem' := remaining_π.filter fun (w, _) => !πI.any fun (w', _) => w' == w
        have ih1 := ih rem' ρ' (dead_acc ++ γ_i)
        have ih2 := ih rem' ρ' ([] ++ γ_i)
        rw [ih1, ih2]
        simp [List.append_assoc]

/-- Seed-level NoDup-on-fst for `path.take d` from canonical-DT path
    nodup. -/
private lemma encoder_aux_seed_path_nodup
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path) :
    ((path.take d).map Prod.fst).Nodup :=
  canonical_dt_path_take_nodup_fst dnf β hnodup d path hpath

/-- Seed-level `h_b_val` invariant: at the seed `B_cur = combineRestrictions β encoder.1`
    the `h_b_val` hypothesis of the loop reduces to reflexivity modulo
    a `dead_acc = []` simplification. -/
private lemma encoder_aux_seed_b_val
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (path : List (Nat × Bool)) :
    let encoder := beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β []
    ∀ v, restrictionAsFunction (combineRestrictions β encoder.1) v =
        restrictionAsFunction
          (combineRestrictions β
            (beameEncoderAux
              (path.take d).length (path.take d) (dnfClauses dnf) β []).1) v := by
  intro encoder v; rfl

/-- Encoder wrapper bridging the user-facing encoder seed `dead_acc = β` to the
    loop-invariant seed `dead_acc = []`. This follows directly
    of `encoder_aux_dead_acc_factor`: under the seed bridge,
    `encoder(β,β).1 = β ++ encoder(β,[]).1`, and `hw_β` rules out the `β`-disjunct. -/
private lemma encoder_aux_dead_seed_β_eq_nil
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (path : List (Nat × Bool))
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false) :
    w ∈ (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β β).1.map Prod.fst ↔
    w ∈ (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β []).1.map Prod.fst := by
  rw [encoder_aux_dead_acc_factor (path.take d).length (path.take d) dnf β β]
  simp only [List.map_append, List.mem_append]
  refine ⟨?_, fun h => Or.inr h⟩
  rintro (hβ | h)
  · -- w ∈ β.map fst contradicts hw_β.
    exfalso
    rw [List.mem_map] at hβ
    obtain ⟨⟨v, b⟩, hvβ, hveq⟩ := hβ
    simp only at hveq
    have hany : (β.any fun (z, _) => z == w) = true :=
      List.any_eq_true.mpr ⟨(v, b), hvβ, by simp [hveq]⟩
    rw [hany] at hw_β
    exact Bool.false_ne_true hw_β.symm
  · exact h


/- **Decoder bridge for `beameDecoder`**: starting the foldl from
    `β ++ extra` produces the same result as starting from
    `combineRestrictions β extra`.

    Proof outline:
      (a) `restrictionAsFunction (β ++ extra) v =
          restrictionAsFunction (combineRestrictions β extra) v` for all v
          (β-keys agree, non-β-keys agree because the filter only drops
          β-keys).
      (b) The decoder outer-step `decoderOuterStep` only consults
          `B` through its induced restriction. Hence, by induction on the
          chunks list, two `B`'s with equal `restrictionAsFunction` images produce the
          same `vars_acc` accumulator (and `restrictionAsFunction`-equivalent `B_cur`'s
          throughout, preserved by prepending the same entries). -/
private lemma decoder_β_append_eq_combined
    (dnf : UnboundedFanInFormula) (β extra : List (Nat × Bool))
    (chunks : List (List (Nat × Bool))) :
    beameDecoder dnf (β ++ extra) chunks =
    beameDecoder dnf (combineRestrictions β extra) chunks := by
  -- (a) restrictionAsFunction agreement.
  have h_crnone :
      ∀ v,
        restrictionAsFunction (β ++ extra) v =
        restrictionAsFunction (combineRestrictions β extra) v := by
    intro v
    -- combineRestrictions β extra = β ++ extra.filter (fun (w,_) => !β.any ((·.1) == w))
    -- find? on β ++ X looks at β first; if a β entry matches, both sides
    -- return it.  Otherwise scan into the tail.  In the tail, the filter
    -- only removes entries whose key IS in β.fst; but our key v is NOT in
    -- β.fst (else find? would have returned in β), so the filter does not
    -- remove any candidate matching `(·.1 == v)`.
    simp only [restrictionAsFunction, combineRestrictions, List.find?_append]
    cases hβ : β.find? (fun p => p.1 == v) with
    | some p => rfl
    | none =>
      -- v ∉ β.fst.  Show extra.find? = (extra.filter notInβ).find?.
      have h_filt : (extra.filter
            (fun (w, _) => !β.any fun (z, _) => z == w)).find?
              (fun p => p.1 == v) =
          extra.find? (fun p => p.1 == v) := by
        induction extra with
        | nil => rfl
        | cons hd tl ih =>
          obtain ⟨hw, hb⟩ := hd
          simp only [List.filter_cons, List.find?_cons]
          by_cases hp : (hw == v) = true
          · -- hd matches find?'s pred ⇒ hw = v ⇒ hd survives the filter
            -- (since v ∉ β.fst, deduced from hβ).
            have hv_eq : hw = v := by simpa [BEq.beq] using hp
            have hkeep : (!β.any fun x => x.1 == hw) = true := by
              simp only [Bool.not_eq_true', hv_eq]
              cases hany : β.any (fun x => x.1 == v) with
              | true =>
                exfalso
                rw [List.any_eq_true] at hany
                obtain ⟨⟨w, b⟩, hwm, hwe⟩ := hany
                simp only [beq_iff_eq] at hwe
                have h_some : (β.find? (fun p => p.1 == v)).isSome = true := by
                  rw [List.find?_isSome]
                  exact ⟨(w, b), hwm, by simpa [BEq.beq] using hwe⟩
                rw [hβ] at h_some; simp at h_some
              | false => rfl
            simp only [hkeep, ↓reduceIte, List.find?_cons, hp]
          · have hp' : (hw == v) = false := by
              cases h : (hw == v) with
              | true => exact absurd h hp
              | false => rfl
            simp only [hp']
            by_cases hkeep : (!β.any fun x => x.1 == hw) = true
            · simp only [hkeep, ↓reduceIte, List.find?_cons, hp', ih]
            · have hkeep' : (!β.any fun x => x.1 == hw) = false := by
                cases h : (!β.any fun x => x.1 == hw) with
                | true => exact absurd h hkeep
                | false => rfl
              simp only [hkeep', Bool.false_eq_true, ↓reduceIte, ih]
      rw [h_filt]
  -- (b) Generalize: for any `vars_acc` and inputs inducing the same
  -- restriction function, the fold produces the same reversed second component.
  rw [decoder_eq_foldl_reverse, decoder_eq_foldl_reverse]
  -- The stronger invariant gives the same second component and equal
  -- restriction functions for the first components.
  suffices hgen : ∀ (chunks : List (List (Nat × Bool)))
      (B1 B2 vacc : List (Nat × Bool)),
      (∀ v, restrictionAsFunction B1 v =
            restrictionAsFunction B2 v) →
      let r1 := chunks.foldl (decoderOuterStep (dnfClauses dnf)) (B1, vacc)
      let r2 := chunks.foldl (decoderOuterStep (dnfClauses dnf)) (B2, vacc)
      r1.2 = r2.2 ∧
      (∀ v, restrictionAsFunction r1.1 v =
            restrictionAsFunction r2.1 v) by
    have h := hgen chunks (β ++ extra) (combineRestrictions β extra) [] h_crnone
    rw [h.1]
  -- Inner-fold helper: a single chunk fold with a fixed T prepends the
  -- SAME delta to BOTH the B accumulator and the vars_acc.  Concretely,
  -- after `chunk.foldl (decoderInnerStep T) (B, vacc)` the result
  -- is `(delta ++ B, delta ++ vacc)` where `delta` depends only on T and
  -- chunk (NOT on B).
  have hinner_delta :
      ∀ (T : List (Nat × Bool)) (chunk : List (Nat × Bool))
        (B vacc : List (Nat × Bool)),
        ∃ delta : List (Nat × Bool),
          chunk.foldl (decoderInnerStep T) (B, vacc) =
            (delta ++ B, delta ++ vacc) := by
    intro T chunk
    induction chunk with
    | nil => intro B vacc; exact ⟨[], by simp [List.foldl_nil]⟩
    | cons hd tl ih =>
      intro B vacc
      obtain ⟨pos, π_bit⟩ := hd
      simp only [List.foldl_cons, decoderInnerStep]
      obtain ⟨d_tail, hd_tail⟩ :=
        ih ((((T.getD pos (0, false)).1, π_bit)) :: B)
           ((((T.getD pos (0, false)).1, π_bit)) :: vacc)
      refine ⟨d_tail ++ [((T.getD pos (0, false)).1, π_bit)], ?_⟩
      rw [hd_tail]
      simp [List.append_assoc]
  -- restrictionAsFunction agreement is preserved when prepending the same delta to both.
  have hcr_prepend :
      ∀ (delta B1 B2 : List (Nat × Bool)),
        (∀ v, restrictionAsFunction B1 v =
              restrictionAsFunction B2 v) →
        ∀ v, restrictionAsFunction (delta ++ B1) v =
             restrictionAsFunction (delta ++ B2) v := by
    intro delta B1 B2 heq v
    simp only [restrictionAsFunction, List.find?_append]
    cases delta.find? (fun p => p.1 == v) with
    | some _ => rfl
    | none => exact heq v
  -- The `.2` projection of `chunk.foldl (inner_step T)` does not depend on
  -- the input `B`: at each inner step, both `B` and `vacc` are prepended
  -- with the SAME pair `((T.getD pos (0,false)).1, π_bit)`.
  have hindep_vacc :
      ∀ (T : List (Nat × Bool)) (chunk : List (Nat × Bool))
        (B B' vacc : List (Nat × Bool)),
        (chunk.foldl (decoderInnerStep T) (B, vacc)).2 =
        (chunk.foldl (decoderInnerStep T) (B', vacc)).2 := by
    intro T chunk
    induction chunk with
    | nil => intros; rfl
    | cons hd tl ihc =>
      intro B B' vacc
      obtain ⟨pos, π_bit⟩ := hd
      simp only [List.foldl_cons, decoderInnerStep]
      exact ihc _ _ _
  -- Now prove the generalization by induction on chunks.
  intro chunks
  clear h_crnone
  induction chunks with
  | nil => intro B1 B2 vacc heq; exact ⟨rfl, heq⟩
  | cons chunk rest ih =>
    intro B1 B2 vacc heq
    simp only [List.foldl_cons]
    -- One outer step: T_i depends only on restrictionAsFunction B; given heq, T_i agrees.
    have h_t : firstTermNotKilledByList (dnfClauses dnf) B1 =
              firstTermNotKilledByList (dnfClauses dnf) B2 := by
      exact firstTermNotKilledByList_eq_of_cr_none_eq
        (dnfClauses dnf) B1 B2 heq
    -- Unfold `decoderOuterStep` and apply `hinner_delta`.
    set T := firstTermNotKilledByList (dnfClauses dnf) B1 with h_t_def
    obtain ⟨δ, hδ1⟩ := hinner_delta T chunk B1 vacc
    -- For B2 we get the same δ (delta depends only on T and chunk).
    have hδ2 :
        chunk.foldl (decoderInnerStep T) (B2, vacc) = (δ ++ B2, δ ++ vacc) := by
      obtain ⟨δ', hδ'⟩ := hinner_delta T chunk B2 vacc
      have hv : δ ++ vacc = δ' ++ vacc := by
        have h1 : (chunk.foldl (decoderInnerStep T) (B1, vacc)).2 = δ ++ vacc :=
          by rw [hδ1]
        have h2 : (chunk.foldl (decoderInnerStep T) (B2, vacc)).2 = δ' ++ vacc :=
          by rw [hδ']
        have hindep := hindep_vacc T chunk B1 B2 vacc
        rw [h1, h2] at hindep
        exact hindep
      have hδeq : δ = δ' := List.append_cancel_right hv
      rw [← hδeq] at hδ'; exact hδ'
    -- Reduce both sides of the goal via outer_step unfolding.
    show (rest.foldl (decoderOuterStep (dnfClauses dnf))
            (decoderOuterStep (dnfClauses dnf) (B1, vacc) chunk)).2 =
         (rest.foldl (decoderOuterStep (dnfClauses dnf))
            (decoderOuterStep (dnfClauses dnf) (B2, vacc) chunk)).2 ∧ _
    have hstep1 : decoderOuterStep (dnfClauses dnf) (B1, vacc) chunk =
        (δ ++ B1, δ ++ vacc) := by
      simp only [decoderOuterStep, h_t_def] at hδ1 ⊢
      exact hδ1
    have hstep2 : decoderOuterStep (dnfClauses dnf) (B2, vacc) chunk =
        (δ ++ B2, δ ++ vacc) := by
      show chunk.foldl (decoderInnerStep
          (firstTermNotKilledByList (dnfClauses dnf) B2)) (B2, vacc) =
        (δ ++ B2, δ ++ vacc)
      rw [← h_t]; exact hδ2
    rw [hstep1, hstep2]
    -- Apply IH with restrictionAsFunction agreement preserved by hcr_prepend.
    have hcr_after := hcr_prepend δ B1 B2 heq
    exact ih (δ ++ B1) (δ ++ B2) (δ ++ vacc) hcr_after


/- **β-disjointness of canonical-DT path bits.**

    Every prefix-bit of a `leftmostPathExceedingDepth` traversal of
    the full-query canonical DT (built from the β-restricted DNF) lies
    outside `β.fst`.  This is the standard structural fact:
    `canonical_dt_path_var_none` says path variables are
    `none` under `restrictionAsFunction β`, which is
    equivalent to `β.any (·.1 == w) = false` via
    `list_any_eq_cr_none_isSome`. -/
private lemma encoder_β_disj_path
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (w : Nat) (b : Bool) (hw_take : (w, b) ∈ path.take d) :
    (β.any fun (z, _) => z == w) = false := by
  rw [list_any_eq_cr_none_isSome,
      canonical_dt_path_var_none dnf β hdnf d path hpath
        w b (List.mem_of_mem_take hw_take)]
  rfl

/- At the encoder seed, either the loop invariant holds or the surviving
    clause extends the complete depth-bounded path prefix:
    - LEFT: the standard `EncoderLoopInv` bundle holds when the selected
      clause's variable list prefixes `(path.take d).map Prod.fst`;
    - RIGHT: the terminal case in which `(path.take d).map Prod.fst` prefixes
      the selected clause's variable list,
      which forces the encoder to consume all of `path.take d` in one go
      (the loop never advances past the seed) so the roundtrip can be
      handled directly without entering the loop.

    The disjunction is structural: both variable lists are prefixes of
    `path.map Prod.fst` (the selected clause via
    `ftnkb_remaining_vars_prefix_in_dt_path`, the latter via
    `List.take_prefix`/`List.map_take`), so by `prefix_or_prefix_of_prefix`
    one is a prefix of the other. -/
private lemma encoder_seed_bundle_nolen
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (_hpath_nodup : ((path.take d).map Prod.fst).Nodup)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false) :
    EncoderLoopInv dnf β d path β (path.take d) ∨
    (path.take d).map Prod.fst <+:
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β).map Prod.fst := by
  -- Bundle dnf into UnboundedFanInDNF for the helper lemmas.
  set N := ufiLargestInput dnf + 1
  have h_n_lt : ufiLargestInput dnf < N := Nat.lt_succ_self _
  let f : UnboundedFanInDNF N := ⟨dnf, h_n_lt, hdnf⟩
  have hp := leftmostPathExceedingDepth_isPathIn _ _ _ hpath
  have ⟨_, hr_clauses_ne⟩ := roftnkb_ne_of_long_path f β d path hpath
  -- The selected clause's variable list prefixes the canonical path.
  have hpre := ftnkb_remaining_vars_prefix_in_dt_path f β path hp hr_clauses_ne
  -- (path.take d).fst <+: path.fst (pure list fact).
  have hpre_take : (path.take d).map Prod.fst <+: path.map Prod.fst := by
    rw [List.map_take]
    exact List.take_prefix d _
  -- Dispatch via prefix_or_prefix_of_prefix.
  rcases prefix_or_prefix_of_prefix hpre hpre_take with hpfx | hrev
  · -- LEFT: build the loop-invariant bundle.
    refine Or.inl ?_
    refine {
      hpath := hpath
      hpfx_ρ := hpfx
      hρ_sub_orig := fun w b hwb => Or.inl hwb
      hρ_extends_fn_orig := fun _ _ => rfl
      hρ_disj_orig := hβ_disj_path
      hrem_sub_outer := fun _ hx => hx
      hrem_complete_orig := fun x hx _ => hx
      hrem_sublist := List.Sublist.refl _
      hpre_ρ_inv := fun v hv => Or.inr hv
      h_clauses_ne_nil := h_clauses_ne_nil
      hρ_segments_consumed := by
        exact encoder_seed_hρ_segments_consumed d dnf β hdnf hnodup
          h_clauses_ne_nil path hpath
    }
  · -- RIGHT: the depth-bounded path is the shorter prefix.
    exact Or.inr hrev

#print axioms encoder_seed_bundle_nolen

/- **Strengthened anchor**: full structural equation for the encoder's
   `dead_acc` output in the terminal right branch. The encoder
   bottoms out in one iteration with `encoder.1 = γ_i` where γ_i is the first
   `(path.take d).length` literal-satisfying bits of the selected clause. -/
private lemma encoder_aux_seed_terminal_dead_eq
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (path : List (Nat × Bool))
    (h_rev : (path.take d).map Prod.fst <+:
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β).map Prod.fst) :
    (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β []).1 =
      (gammaBitsForClause
        (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β)).take
        (path.take d).length := by
  -- Recursive encoder calls on empty `remaining_π` always return `(acc, [])`.
  have h_aux_nil : ∀ (fuel : Nat) (ρ acc : List (Nat × Bool)),
      beameEncoderAux fuel [] (dnfClauses dnf) ρ acc = (acc, []) := by
    intro fuel ρ acc
    cases fuel with
    | zero => rfl
    | succ _ => simp [beameEncoderAux]
  -- The filter keeps every element of `path.take d`.
  have h_filter_eq : (path.take d).filter
      (fun x => ((restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β).map
        Prod.fst).contains x.1) = path.take d := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hxfst : x.1 ∈ (path.take d).map Prod.fst := List.mem_map_of_mem hx
    have h_in :
        x.1 ∈ (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β).map Prod.fst :=
      h_rev.subset hxfst
    simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq]
    exact ⟨x.1, h_in, rfl⟩
  -- Case split on whether `path.take d` is empty.
  by_cases hπnil : path.take d = []
  · rw [hπnil]
    simp [beameEncoderAux]
  · have hlen_pos : 0 < (path.take d).length :=
      List.length_pos_iff.mpr hπnil
    obtain ⟨n, hn⟩ : ∃ n, (path.take d).length = n + 1 :=
      ⟨(path.take d).length - 1, by omega⟩
    -- Unfold one step of the encoder via `hn`.
    conv_lhs => rw [hn]
    rw [show beameEncoderAux (n + 1) (path.take d) (dnfClauses dnf) β [] =
        (if (path.take d) = [] then ([], [])
         else
           let clauses := dnfClauses dnf
           let T_i := firstTermNotKilledByList clauses β
           let U_i := restrictionOfFirstTermNotKilledByList clauses β
           let U_vars := U_i.map Prod.fst
           let p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
           let πI := (path.take d).filter p
           let γ_i := (gammaBitsForClause U_i).take πI.length
           let dead_acc' := [] ++ γ_i
           if πI.length = 0 then (dead_acc', [])
           else
             let chunk := encoderChunk T_i πI
             let ρ' := combineRestrictions β πI
             let remaining' := (path.take d).filter
               fun (w, _) => !πI.any fun (w', _) => w' == w
             let (final_dead, restEncoder) :=
               beameEncoderAux n remaining' (dnfClauses dnf) ρ' dead_acc'
             (final_dead, chunk :: restEncoder)) from rfl]
    simp only [hπnil, ↓reduceIte, h_filter_eq]
    have h_πi_len_pos : (path.take d).length ≠ 0 := Nat.pos_iff_ne_zero.mp hlen_pos
    simp only [h_πi_len_pos, ↓reduceIte]
    have h_rem'_nil : (path.take d).filter
        (fun (x : Nat × Bool) => !(path.take d).any fun (x' : Nat × Bool) => x'.1 == x.1)
        = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      simp only [Bool.not_eq_true', Bool.not_eq_false]
      exact List.any_eq_true.mpr ⟨x, hx, by simp⟩
    rw [h_rem'_nil]
    rw [h_aux_nil]
    simp only [List.nil_append]

/- **Anchor lemma (`.fst`-projection corollary)**: in the RIGHT branch,
   the encoder's dead-vars output has first-components equal to
   `(path.take d).fst`.  Direct corollary of
   `encoder_aux_seed_terminal_dead_eq`. -/
private lemma encoder_aux_seed_terminal_dead_eq_path_take_d
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (path : List (Nat × Bool))
    (h_rev : (path.take d).map Prod.fst <+:
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β).map Prod.fst) :
    (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β []).1.map Prod.fst =
      (path.take d).map Prod.fst := by
  rw [encoder_aux_seed_terminal_dead_eq d dnf β path h_rev]
  rw [List.map_take, gamma_bits_map_fst_eq]
  have hlen : ((path.take d).map Prod.fst).length = (path.take d).length :=
    List.length_map _
  rw [← hlen]
  exact (List.prefix_iff_eq_take.mp h_rev).symm

#print axioms encoder_aux_seed_terminal_dead_eq_path_take_d

/- **Seed alignment without a surviving-clause length hypothesis.**

   Routes via `encoder_seed_bundle_nolen`'s disjunction:
   - LEFT (short-R): uses the loop bundle.
   - RIGHT (long-R terminal): the encoder bottoms out in one iteration with
     `encoder.1 = γ_i = (gammaBitsForClause U_i).take (path.take d).length`.
     The combined assignment `combineRestrictions β γ_i` extends β by setting
     a prefix of U_i's variables to their literal-satisfying bits.  Since every
     literal (v, neg) ∈ T₀ unassigned in β belongs to U_i with the same `neg`
     (by clause-Nodup), and γ_i sets such v to `literalSatisfyingBit neg`
     (or leaves it unassigned), T₀ stays alive — alignment preserved. -/
private lemma encoder_aux_seed_align_nolen
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false) :
    let encoder := beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β []
    firstTermNotKilledByList (dnfClauses dnf) (combineRestrictions β encoder.1) =
    firstTermNotKilledByList (dnfClauses dnf) β := by
  -- Discriminate on `encoder_seed_bundle_nolen`'s disjunction.
  have hpath_nodup := encoder_aux_seed_path_nodup d dnf β hnodup path hpath
  rcases encoder_seed_bundle_nolen d dnf β hdnf hnodup
    h_clauses_ne_nil path hpath hpath_nodup hβ_disj_path with hbundle | h_rev
  · -- LEFT (short-R): use the loop-invariant `hpfx_ρ` and the existing helper.
    exact encoder_aux_initial_alignment_gen
      (path.take d).length (path.take d) dnf β [] hdnf hnodup le_rfl
      (by intro v hv; simp at hv)
      β d path hpath
      (fun x hx => hx)
      (by intro v hv; simp at hv)
      hbundle.hpfx_ρ
  · -- RIGHT (long-R terminal): substitute the explicit form of `encoder.1`.
    set U_i := restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β with h_u_i_def
    have h_encoder_aux_dead_eq : (beameEncoderAux
        (path.take d).length (path.take d) (dnfClauses dnf) β []).1 =
        (gammaBitsForClause U_i).take (path.take d).length :=
      encoder_aux_seed_terminal_dead_eq d dnf β path h_rev
    show firstTermNotKilledByList (dnfClauses dnf)
        (combineRestrictions β (beameEncoderAux
          (path.take d).length (path.take d) (dnfClauses dnf) β []).1) =
      firstTermNotKilledByList (dnfClauses dnf) β
    rw [h_encoder_aux_dead_eq]
    set γ_i := (gammaBitsForClause U_i).take (path.take d).length with hγ_i_def
    set A₁ := restrictionAsFunction β with h_a₁_def
    set A₂ := restrictionAsFunction (combineRestrictions β γ_i)
      with h_a₂_def
    apply firstTermNotKilledByList_eq (dnfClauses dnf) β
      (combineRestrictions β γ_i)
    · -- A₁ extends to A₂: when β assigns v, combined assigns same value.
      intro w hw
      exact cr_none_combineRestrictions_extends_base β γ_i w hw
    · -- T₀ is not killed by A₂.
      rw [isClauseKilledBy_eq_isClauseKilled]
      apply not_killed_by_satisfying
      intro ⟨v, neg⟩ hmem_t₀
      -- Case-split on whether v is assigned in β.
      by_cases hv : A₁ v = none
      · -- v unassigned in β.
        -- Compute A₂ v explicitly.  Since v ∉ β.fst, β.find? on v is none, so combineRestrictions
        -- falls through to looking up v in γ_i (filtered to keep entries with fst
        -- not in β.fst).
        have hv_β_any : (β.any fun (w, _) => w == v) = false := by
          rw [list_any_eq_cr_none_isSome]
          show (A₁ v).isSome = false
          rw [hv]; rfl
        have hv_β_find : β.find? (fun p => p.1 == v) = none := by
          rw [List.find?_eq_none]
          intro ⟨x, bx⟩ hmem hxv
          simp only [beq_iff_eq] at hxv; subst hxv
          have habs : (β.any fun (z, _) => z == x) = true :=
            List.any_eq_true.mpr ⟨(x, bx), hmem, by simp⟩
          simp [habs] at hv_β_any
        -- Inner case-split on whether γ_i (after filter) contains v.
        cases hfind :
            (γ_i.filter (fun x => !(β.any fun (w, _) => w == x.1))).find?
              (fun p => p.1 == v) with
        | none =>
          -- A₂ v = none.
          left
          show A₂ v = none
          simp only [h_a₂_def, combineRestrictions, restrictionAsFunction,
            List.find?_append, hv_β_find, Option.none_or, hfind]
        | some pair =>
          -- A₂ v = some bw.  Show bw = literalSatisfyingBit neg.
          obtain ⟨w, bw⟩ := pair
          right
          have h_a₂_val : A₂ v = some bw := by
            show A₂ v = some bw
            simp only [h_a₂_def, combineRestrictions, restrictionAsFunction,
              List.find?_append, hv_β_find, Option.none_or, hfind]
          change A₂ v = some (literalSatisfyingBit neg)
          rw [h_a₂_val]
          congr 1
          have hmem_filt := List.mem_of_find?_eq_some hfind
          have hmem_γ : (w, bw) ∈ γ_i := List.mem_of_mem_filter hmem_filt
          have hw_eq : w = v := by
            have hsat := List.find?_some hfind
            simp only [beq_iff_eq] at hsat; exact hsat
          rw [hw_eq] at hmem_γ
          -- γ_i ⊆ gammaBitsForClause U_i.
          have hmem_gamma : (v, bw) ∈ gammaBitsForClause U_i :=
            List.mem_of_mem_take hmem_γ
          simp only [gammaBitsForClause, List.mem_map] at hmem_gamma
          obtain ⟨⟨v', neg'⟩, hmem_u', heq⟩ := hmem_gamma
          simp only [Prod.mk.injEq] at heq
          obtain ⟨hv'_eq, hbw_eq⟩ := heq
          -- hv'_eq : v' = v, hbw_eq : literalSatisfyingBit neg' = bw
          rw [hv'_eq] at hmem_u'
          -- hmem_u' : (v, neg') ∈ U_i
          -- (v, neg) ∈ T₀ and (v, neg') ∈ U_i ⊆ T₀; Nodup_fst of T₀ ⇒ neg = neg'.
          have h_u_sub_t : ∀ x ∈ U_i,
              x ∈ firstTermNotKilledByList (dnfClauses dnf) β := by
            intro x hx
            rw [h_u_i_def] at hx
            exact restrictClauseByListAssignment_subset _ _ _ hx
          have h_t_nodup : ((firstTermNotKilledByList (dnfClauses dnf) β).map
              Prod.fst).Nodup := by
            rcases firstTermNotKilledByList_mem_or_nil (dnfClauses dnf) β with
              hmem_t | hnil_t
            · exact hnodup _ hmem_t
            · rw [hnil_t]
              simp
          have hmem_t_neg' : (v, neg') ∈ firstTermNotKilledByList
              (dnfClauses dnf) β := h_u_sub_t _ hmem_u'
          have hmem_t₀_2 : (v, neg) ∈ firstTermNotKilledByList (dnfClauses dnf) β := by
            exact hmem_t₀
          have hneg_eq : neg = neg' :=
            Lists.ListLemmas.nodup_map_fst_snd_eq h_t_nodup hmem_t₀_2 hmem_t_neg'
          rw [hneg_eq, ← hbw_eq]
      · -- v assigned in β.  combineRestrictions extends β, so A₂ v = A₁ v ≠ none.
        -- (v, neg) ∈ T₀ = ftnkb A₁, and A₁ doesn't kill T₀, so A₁ v matches neg.
        have hagree := cr_none_combineRestrictions_extends_base β γ_i v hv
        -- hagree : A₂ v = A₁ v as combined terms.
        have h_a₂_eq : A₂ v = A₁ v := by
          show A₂ v = A₁ v
          rw [h_a₂_def, h_a₁_def]; exact hagree
        change A₂ v = none ∨ A₂ v = some (literalSatisfyingBit neg)
        rw [h_a₂_eq]
        -- Now reduce to: A₁ v = none ∨ A₁ v = literalSatisfyingBit neg.
        have h_not_kill := firstTermNotKilledByList_self (dnfClauses dnf) β
        rw [isClauseKilledBy_eq_isClauseKilled] at h_not_kill
        -- T₀ = firstTermNotKilledBy clauses A₁; not killed by A₁.
        -- Extract per-literal satisfying property.
        simp only [isClauseKilled, List.any_eq_false] at h_not_kill
        have := h_not_kill ⟨v, neg⟩ hmem_t₀
        simp only at this
        cases h_a₁v : A₁ v with
        | none => left; rfl
        | some b =>
          right
          have h_a₁v' : restrictionAsFunction β v = some b := h_a₁v
          rw [h_a₁v'] at this
          -- this : (!b == literalSatisfyingBit neg) = false
          have hb : b = literalSatisfyingBit neg := by
            have h1 : (b == literalSatisfyingBit neg) = true := by
              cases hbe : (b == literalSatisfyingBit neg) <;> simp [hbe] at this ; rfl
            exact (beq_iff_eq).mp h1
          rw [hb]

#print axioms encoder_aux_seed_align_nolen

/- **Terminal right-branch decoder helper.**
   When the depth-bounded path's variable list prefixes the selected clause's
   variable list, the encoder
   bottoms out in one iteration with `encoder.2 = [encoderChunk T_0 π]` and
   `encoder.1 = γ_0.take π.length`, where `π = path.take d` and `γ_0` contains
   the selected clause's literal-satisfying bits.

   Computes the foldl decoder result's `.2` (vars_acc) component
   explicitly: it equals `π.reverse`. -/
private lemma encoder_aux_decode_right_foldl_snd
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false)
    (h_rev : (path.take d).map Prod.fst <+:
      (restrictionOfFirstTermNotKilledByList (dnfClauses dnf) β).map Prod.fst) :
    let π := path.take d
    let encoder := beameEncoderAux π.length π (dnfClauses dnf) β []
    (encoder.2.foldl (decoderOuterStep (dnfClauses dnf))
      (combineRestrictions β encoder.1, [])).2 = π.reverse := by
  simp only
  set π := path.take d with hπ_def
  by_cases hπ_nil : π = []
  · -- π = []: encoder returns ([], []), foldl is identity, result is [].
    have h_encoder_eq : beameEncoderAux π.length π (dnfClauses dnf) β [] = ([], []) := by
      simp [hπ_nil, beameEncoderAux]
    rw [h_encoder_eq]
    simp [hπ_nil]
  · -- π ≠ []: one encoder iteration; analyze.
    set clauses := dnfClauses dnf with hclauses_def
    set T_0 := firstTermNotKilledByList clauses β with h_t0_def
    set U_0 := restrictClauseByListAssignment T_0 β with h_u0_def
    set U_vars := U_0.map Prod.fst with h_uvars_def
    set p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1 with hp_def
    -- Show π_0 = π (filter keeps everything since π.fst <+: U_0.fst).
    have hπ0_eq : π.filter p = π := by
      apply List.filter_eq_self.mpr
      intro ⟨v, b⟩ hmem
      simp only [hp_def, List.elem_eq_mem, decide_eq_true_eq]
      have hv_in_πfst : v ∈ π.map Prod.fst := List.mem_map.mpr ⟨(v, b), hmem, rfl⟩
      have hv_in_u0fst : v ∈ U_0.map Prod.fst := by
        have := h_rev.subset hv_in_πfst
        simpa [U_0, T_0, restrictionOfFirstTermNotKilledByList] using this
      exact hv_in_u0fst
    have hπ_len_pos : π.length ≠ 0 := by
      intro h; exact hπ_nil (List.length_eq_zero_iff.mp h)
    obtain ⟨n, hn⟩ : ∃ n, π.length = n + 1 := by
      cases hl : π.length with
      | zero => exact absurd hl hπ_len_pos
      | succ k => exact ⟨k, rfl⟩
    have h_remaining'_nil :
        π.filter (fun (w, _) => !π.any (fun (w', _) => w' == w)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro ⟨v, b⟩ hmem
      have hany : (π.any fun (w', _) => w' == v) = true := by
        apply List.any_eq_true.mpr
        exact ⟨(v, b), hmem, by simp⟩
      simp [hany]
    -- Compute encoder explicitly.
    have h_encoder_eq : beameEncoderAux π.length π (dnfClauses dnf) β [] =
        ((gammaBitsForClause U_0).take π.length,
         [encoderChunk T_0 π]) := by
      conv_lhs => rw [hn]
      unfold beameEncoderAux
      simp only [if_neg hπ_nil]
      simp only [← hclauses_def, ← h_t0_def, ← h_u0_def, ← h_uvars_def, ← hp_def]
      rw [hπ0_eq]
      have hπlen_ne0 : ¬ (π.length = 0) := hπ_len_pos
      simp only [if_neg hπlen_ne0]
      rw [h_remaining'_nil]
      simp only [List.nil_append]
      have hrec : beameEncoderAux n []
          (dnfClauses dnf) (combineRestrictions β π)
          ((gammaBitsForClause U_0).take π.length) =
          ((gammaBitsForClause U_0).take π.length, []) := by
        cases n <;> simp [beameEncoderAux]
      rw [hrec]
    rw [h_encoder_eq]
    simp only [List.foldl_cons, List.foldl_nil, decoderOuterStep]
    -- The outer decoder step computes `firstTermNotKilledByList` from
    -- `combineRestrictions β encoder.1`; apply the seed-alignment result.
    have h_t_align : firstTermNotKilledByList clauses
        (combineRestrictions β ((gammaBitsForClause U_0).take π.length)) = T_0 := by
      have h := encoder_aux_seed_align_nolen d dnf β hdnf hnodup
        h_clauses_ne_nil path hpath hβ_disj_path
      simp only at h
      -- The surviving clauses agree before and after adding `encoder.1` to β.
      -- encoder.1 = (gamma_bits U_0).take π.length by h_encoder_eq.
      have h_encoder_aux_dead_eq : (beameEncoderAux π.length π (dnfClauses dnf) β []).1 =
          (gammaBitsForClause U_0).take π.length := by
        rw [h_encoder_eq]
      rw [h_encoder_aux_dead_eq] at h
      exact h
    rw [h_t_align]
    rw [decoder_list_inner_foldl_snd_eq]
    rw [List.append_nil]
    -- Apply roundtrip: chunk.map (...) = π.
    have h_u : ∀ v b, (v, b) ∈ π →
        T_0.any (fun lit => lit.1 == v) = true := by
      intro v b hmem
      have hv_in_πfst : v ∈ π.map Prod.fst := List.mem_map.mpr ⟨(v, b), hmem, rfl⟩
      have hv_in_u0fst : v ∈ U_0.map Prod.fst := h_rev.subset hv_in_πfst
      have h_u0_sub_t0 : ∀ x ∈ U_0, x ∈ T_0 := by
        intro x hx
        rw [h_u0_def] at hx
        exact restrictClauseByListAssignment_subset _ _ _ hx
      simp only [List.mem_map] at hv_in_u0fst
      obtain ⟨⟨v', neg'⟩, hmem_u0, hv'_eq⟩ := hv_in_u0fst
      simp only at hv'_eq
      rw [hv'_eq] at hmem_u0
      have : (v, neg') ∈ T_0 := h_u0_sub_t0 _ hmem_u0
      apply List.any_eq_true.mpr
      exact ⟨(v, neg'), this, by simp⟩
    rw [decoder_encoderChunk_decode_eq T_0 π h_u]

#print axioms encoder_aux_decode_right_foldl_snd

/- **Decoder-to-encoder membership.** Routes via
   `encoder_seed_bundle_nolen`'s disjunction:
   - LEFT: passes the bundle to the loop lemma with
     `encoder_aux_seed_align_nolen`.
   - RIGHT: terminal one-iteration encoder/decoder analysis (see helper). -/
private lemma encoder_aux_decode_gen_iff_mp
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false)
    (hw_decoder : w ∈ (beameDecoder dnf
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).1
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).2).map Prod.fst) :
    w ∈ (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β β).1.map Prod.fst := by
  rw [encoder_aux_dead_seed_β_eq_nil d dnf β path w hw_β]
  set encoder := beameEncoderAux
    (path.take d).length (path.take d) (dnfClauses dnf) β [] with h_encoder_def
  have hw_decoder' : w ∈ (beameDecoder dnf
      (combineRestrictions β encoder.1) encoder.2).map Prod.fst := by
    have hfact := encoder_aux_dead_acc_factor (path.take d).length
      (path.take d) dnf β β
    rw [hfact] at hw_decoder
    simp only at hw_decoder
    rw [decoder_β_append_eq_combined] at hw_decoder
    exact hw_decoder
  rw [decoder_eq_foldl_reverse, List.map_reverse, List.mem_reverse] at hw_decoder'
  have hpath_nodup := encoder_aux_seed_path_nodup d dnf β hnodup path hpath
  rcases encoder_seed_bundle_nolen d dnf β hdnf hnodup
    h_clauses_ne_nil path hpath hpath_nodup hβ_disj_path with hbundle | h_rev
  · -- LEFT: existing loop-based logic.
    have hgen := encoder_aux_decode_gen_loop
      (path.take d).length (path.take d) dnf β
      (combineRestrictions β encoder.1) [] []
      β d path
      hbundle
      le_rfl
      hpath_nodup hdnf hnodup
      (encoder_aux_seed_align_nolen d dnf β hdnf hnodup
        h_clauses_ne_nil path hpath hβ_disj_path)
      (by simp) (by simp) (encoder_aux_seed_b_val d dnf β path)
    rcases (hgen w).mp hw_decoder' with hempty | hdead
    · simp at hempty
    · exact hdead
  · -- RIGHT: use terminal one-iteration helper.
    have hfoldl := encoder_aux_decode_right_foldl_snd d dnf β
      hdnf hnodup h_clauses_ne_nil path hpath hβ_disj_path h_rev
    simp only at hfoldl
    rw [hfoldl] at hw_decoder'
    rw [List.map_reverse, List.mem_reverse] at hw_decoder'
    rw [encoder_aux_seed_terminal_dead_eq_path_take_d d dnf β path h_rev]
    exact hw_decoder'

/- **Encoder-to-decoder membership.** -/
private lemma encoder_aux_decode_gen_iff_mpr
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false)
    (hw_encoder : w ∈ (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β β).1.map Prod.fst) :
    w ∈ (beameDecoder dnf
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).1
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).2
    ).map Prod.fst := by
  rw [encoder_aux_dead_seed_β_eq_nil d dnf β path w hw_β] at hw_encoder
  set encoder := beameEncoderAux
    (path.take d).length (path.take d) (dnfClauses dnf) β [] with h_encoder_def
  suffices hgoal : w ∈ (beameDecoder dnf
      (combineRestrictions β encoder.1) encoder.2).map Prod.fst by
    have hfact := encoder_aux_dead_acc_factor (path.take d).length
      (path.take d) dnf β β
    rw [hfact]
    simp only
    rw [decoder_β_append_eq_combined]
    exact hgoal
  rw [decoder_eq_foldl_reverse, List.map_reverse, List.mem_reverse]
  have hpath_nodup := encoder_aux_seed_path_nodup d dnf β hnodup path hpath
  rcases encoder_seed_bundle_nolen d dnf β hdnf hnodup
    h_clauses_ne_nil path hpath hpath_nodup hβ_disj_path with hbundle | h_rev
  · -- LEFT: existing loop-based logic.
    have hgen := encoder_aux_decode_gen_loop
      (path.take d).length (path.take d) dnf β
      (combineRestrictions β encoder.1) [] []
      β d path
      hbundle
      le_rfl
      hpath_nodup hdnf hnodup
      (encoder_aux_seed_align_nolen d dnf β hdnf hnodup
        h_clauses_ne_nil path hpath hβ_disj_path)
      (by simp) (by simp) (encoder_aux_seed_b_val d dnf β path)
    exact (hgen w).mpr (Or.inr hw_encoder)
  · -- RIGHT: use terminal one-iteration helper.
    have hfoldl := encoder_aux_decode_right_foldl_snd d dnf β
      hdnf hnodup h_clauses_ne_nil path hpath hβ_disj_path h_rev
    simp only at hfoldl
    rw [hfoldl]
    rw [List.map_reverse, List.mem_reverse]
    rw [encoder_aux_seed_terminal_dead_eq_path_take_d d dnf β path h_rev] at hw_encoder
    exact hw_encoder

#print axioms encoder_aux_decode_gen_iff_mp
#print axioms encoder_aux_decode_gen_iff_mpr

/-- **Generalised restrictionOfFirstTermNotKilledByList-alignment helper for the decoder.**

    Composition of `encoder_aux_decode_gen_iff_mp` (decoder ⊆ encoder
    dead vars, via the loop lemma) and `encoder_dead_vars_subset_path`
    (encoder dead vars ⊆ `path.take d`, via the segment-alignment trace). -/
private lemma encoder_aux_decode_gen
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (hnodup_β : (β.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false)
    (hw : w ∈ (beameDecoder dnf
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).1
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).2).map
        Prod.fst) :
    w ∈ (path.take d).map Prod.fst := by
  -- (1) Path vars are unassigned by β (canonical-DT structural invariant).
  have hβ_disj_path := encoder_β_disj_path d dnf β hdnf path hpath
  -- (2) Decoder → encoder dead vars.
  have hw_encoder : w ∈ (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β β).1.map Prod.fst :=
    encoder_aux_decode_gen_iff_mp d dnf β hdnf hnodup h_clauses_ne_nil path hpath
      hβ_disj_path w hw_β hw
  -- (3) Encoder dead vars → `path.take d`.  Reify `dnf` as a
  --     `UnboundedFanInDNF` value via the trivial `n` bound.
  let f : UnboundedFanInDNF (ufiLargestInput dnf + 1) :=
    ⟨dnf, Nat.lt_succ_self _, hdnf⟩
  have hw_encoder' : w ∈ (encodeRestrictionFromFormula d f.val β).1.map Prod.fst := by
    show w ∈ (encodeRestrictionFromFormula d dnf β).1.map Prod.fst
    simp only [encodeRestrictionFromFormula, hpath]
    exact hw_encoder
  exact encoder_dead_vars_subset_path f hnodup β hnodup_β d path hpath w hw_β hw_encoder'

#print axioms encoder_aux_decode_gen

/-- **restrictionOfFirstTermNotKilledByList alignment for `beameEncoderAux` (encoder-specific).**

    Decoded variables from the encoder's chunks lie in `path.take d`.
    Wrapper around `encoder_aux_decode_gen` that converts
    `.contains = true` to membership. -/
private lemma encoder_decoded_subset_path
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (hnodup_β : (β.map Prod.fst).Nodup)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false)
    (hw : ((beameDecoder dnf
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).1
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).2).map
        Prod.fst).contains w = true) :
    w ∈ (path.take d).map Prod.fst := by
  have hw_mem : w ∈ (beameDecoder dnf
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).1
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).2).map
        Prod.fst := List.mem_of_elem_eq_true hw
  exact encoder_aux_decode_gen d dnf β hdnf hnodup h_clauses_ne_nil hnodup_β path hpath
    w hw_β hw_mem

#print axioms encoder_decoded_subset_path

private lemma encoder_aux_decode_gen_iff
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false) :
    let encoder := beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β β
    w ∈ (beameDecoder dnf encoder.1 encoder.2).map Prod.fst ↔
    w ∈ encoder.1.map Prod.fst := by
  refine ⟨?_, ?_⟩
  · intro h_decoder
    exact encoder_aux_decode_gen_iff_mp d dnf β hdnf hnodup h_clauses_ne_nil path hpath
      hβ_disj_path w hw_β h_decoder
  · intro h_encoder
    exact encoder_aux_decode_gen_iff_mpr d dnf β hdnf hnodup h_clauses_ne_nil path hpath
      hβ_disj_path w hw_β h_encoder

private lemma encoder_aux_decoded_contains_dead
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d = some path)
    (hβ_disj_path : ∀ w b, (w, b) ∈ path.take d →
      (β.any fun (z, _) => z == w) = false)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false)
    (hw : w ∈ (beameEncoderAux
        (path.take d).length (path.take d) (dnfClauses dnf) β β).1.map Prod.fst) :
    ((beameDecoder dnf
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).1
      (beameEncoderAux (path.take d).length (path.take d) (dnfClauses dnf) β β).2
    ).map Prod.fst).contains w = true := by
  rw [List.contains_iff_mem]
  exact (encoder_aux_decode_gen_iff d dnf β hdnf hnodup h_clauses_ne_nil path hpath
    hβ_disj_path w hw_β).mpr hw

#print axioms encoder_aux_decode_gen_iff
#print axioms encoder_aux_decoded_contains_dead


-- ────────────────────────────────────────────────────────────────────────
-- (a.3) restrictionOfFirstTermNotKilledByList initial alignment helpers for `beameEncoderAux`
-- ────────────────────────────────────────────────────────────────────────

/-- (3a) **Gamma values are satisfying bits.**

    Every entry `(v, b)` of `γ_i = (gammaBitsForClause U_i).take πI.length`
    is a gamma bit, so `b = literalSatisfyingBit n` for the literal `(v, n)`
    that produced it.  Pure list fact about
    `gammaBitsForClause = clause.map fun (v, n) => (v, lsb n)`. -/
private lemma encoder_gamma_take_val
    (U_i : List (Nat × Bool)) (k : Nat) (v : Nat) (b : Bool)
    (hmem : (v, b) ∈ (gammaBitsForClause U_i).take k) :
    ∃ neg, (v, neg) ∈ U_i ∧ b = literalSatisfyingBit neg := by
  have hmem_full : (v, b) ∈ gammaBitsForClause U_i :=
    List.mem_of_mem_take hmem
  simp only [gammaBitsForClause, List.mem_map] at hmem_full
  obtain ⟨⟨w, n⟩, hw_u, heq⟩ := hmem_full
  have hw_v : w = v := by
    have := congrArg Prod.fst heq; simp at this; exact this
  have hb_eq : b = literalSatisfyingBit n := by
    have := congrArg Prod.snd heq; simp at this; exact this.symm
  exact ⟨n, hw_v ▸ hw_u, hb_eq⟩

/-- (3b) **Gamma vars are subset of U_i.fst.**

    Every var in `γ_i = (gammaBitsForClause U_i).take πI.length` lies
    in `U_i.fst`. Pure list fact. -/
private lemma encoder_gamma_take_fst_subset
    (U_i : List (Nat × Bool)) (k : Nat) (v : Nat)
    (hv : v ∈ ((gammaBitsForClause U_i).take k).map Prod.fst) :
    v ∈ U_i.map Prod.fst := by
  rw [List.mem_map] at hv
  obtain ⟨⟨v', b'⟩, hpair_mem, hpair_fst⟩ := hv
  obtain ⟨n, hn_u, _⟩ := encoder_gamma_take_val U_i k v' b' hpair_mem
  rw [List.mem_map]
  refine ⟨(v', n), hn_u, ?_⟩
  simpa using hpair_fst

/-- `restrictClauseByListAssignment` removes assigned variables.

    If `v ∈ ρ.fst`, then
    `v ∉ (restrictClauseByListAssignment c ρ).fst` for any clause `c`. -/
private lemma restrictClauseByListAssignment_fst_disjoint_assigned
    (c : List (Nat × Bool)) (ρ : List (Nat × Bool)) (v : Nat)
    (hv : (ρ.any fun (w, _) => w == v) = true) :
    v ∉ (restrictClauseByListAssignment c ρ).map Prod.fst := by
  simp only [restrictClauseByListAssignment, List.mem_map]
  split
  · intro ⟨_, hmem, _⟩; simp at hmem
  · rintro ⟨⟨w, n⟩, hmem_filt, hw_eq⟩
    have hfilt := (List.mem_filter.mp hmem_filt).2
    -- hfilt : !(ρ.any (· == w)) = true; hv : ρ.any (· == v) = true; w = v
    simp only at hw_eq; subst hw_eq
    rw [hv] at hfilt
    exact Bool.noConfusion hfilt

/-- `restrictionOfFirstTermNotKilledByList` removes assigned variables. -/
private lemma rtnkb_fst_disjoint_assigned
    (clauses : List (List (Nat × Bool))) (ρ : List (Nat × Bool)) (v : Nat)
    (hv : (ρ.any fun (w, _) => w == v) = true) :
    v ∉ (restrictionOfFirstTermNotKilledByList clauses ρ).map Prod.fst :=
  restrictClauseByListAssignment_fst_disjoint_assigned _ ρ v hv

/-- The encoder creates no new dead entries for assigned variables.

    If `v` is already in `ρ.fst`, then any `(v, b) ∈ encoder.1` was already in
    `dead_acc`. The encoder cannot add a new dead entry whose variable is
    in the running restriction.

    *Why*: each `γ_i = (gammaBitsForClause U_i).take πI.length` only
    contains vars in `U_i.fst`. By
    `rtnkb_fst_disjoint_assigned`, `U_i.fst` is disjoint from `ρ.fst`.
    Hence `v ∉ γ_i.fst`. By induction, recursive calls preserve this. -/
private lemma encoder_aux_no_new_dead_for_assigned
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (v : Nat) (b : Bool)
    (hv_ρ : (ρ.any fun (w, _) => w == v) = true)
    (hmem : (v, b) ∈ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1) :
    (v, b) ∈ dead_acc := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero =>
    simp only [beameEncoderAux] at hmem
    exact hmem
  | succ fuel' ih =>
    simp only [beameEncoderAux] at hmem
    by_cases hrem : remaining_π = []
    · rw [if_pos hrem] at hmem; exact hmem
    · rw [if_neg hrem] at hmem
      set clauses := dnfClauses dnf
      set U_i := restrictionOfFirstTermNotKilledByList clauses ρ
      set U_vars := U_i.map Prod.fst
      set p : (Nat × Bool) → Bool := fun x => U_vars.contains x.1
      set πI := remaining_π.filter p
      set γ_i := (gammaBitsForClause U_i).take πI.length
      have hv_not_u : v ∉ U_vars :=
        rtnkb_fst_disjoint_assigned clauses ρ v hv_ρ
      have hv_not_γ : (v, b) ∉ γ_i := by
        intro hmem_γ
        apply hv_not_u
        exact encoder_gamma_take_fst_subset U_i πI.length v
          (List.mem_map_of_mem (f := Prod.fst) hmem_γ)
      split at hmem
      · rw [List.mem_append] at hmem
        rcases hmem with h | h
        · exact h
        · exact absurd h hv_not_γ
      · -- Recursive case: ρ' = combineRestrictions ρ πI ⊇ ρ
        set ρ' := combineRestrictions ρ πI
        have hv_ρ' : (ρ'.any fun (w, _) => w == v) = true := by
          show (ρ'.any _) = true
          simp only [ρ', combineRestrictions, List.any_append, hv_ρ, Bool.true_or]
        have h_ih := ih _ _ _ hv_ρ' hmem
        rw [List.mem_append] at h_ih
        rcases h_ih with h | h
        · exact h
        · exact absurd h hv_not_γ


/-- **β-preservation**: every pair initially in `β` (the seed
    assignment) is preserved in the encoder's dead-vars output, *provided*
    the canonical DT actually has a path exceeding depth `d` (otherwise
    the encoder short-circuits to `([], [])`).

    Direct wrapper around `encoder_aux_dead_acc_mono`, because
    `encodeRestrictionFromFormula d dnf β` reduces in the `some path` branch to
    `beameEncoderAux π.length π (dnfClauses dnf) β β`, where `dead_acc = β`.

    This is the formal statement of "the seeded β-variables are intentionally
    placed in `dead_acc` by the encoder" referenced in
    `encoder_dead_vars_subset_recovered` below. -/
private lemma encoder_β_subset_dead_acc
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (v : Nat) (b : Bool)
    (hmem : (v, b) ∈ β)
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree dnf β) d ≠ none) :
    (v, b) ∈ (encodeRestrictionFromFormula d dnf β).1 := by
  simp only [encodeRestrictionFromFormula]
  -- Case-split on the `leftmostPathExceedingDepth` result; the `none`
  -- branch is excluded by `hpath`.
  cases hlpe :
      leftmostPathExceedingDepth
        (canonicalDecisionTree dnf β) d with
  | none => exact absurd hlpe hpath
  | some path =>
    exact encoder_aux_dead_acc_mono
      (path.take d).length (path.take d) dnf β β v b hmem

/-- **Completeness**: every NEWLY-killed variable in dead_vars produced
    by the encoder is recovered by the iterative decoder.

    The hypothesis `hw_β : w ∉ β.fst` excludes the seeded β-variables, which
    are intentionally placed in `dead_acc` by the encoder but are NOT meant
    to be recovered by the decoder because they are already known from β. -/
private lemma encoder_dead_vars_subset_recovered
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (hβ_disj_path : ∀ p,
      leftmostPathExceedingDepth
        (canonicalDecisionTree dnf β) d = some p →
      ∀ w b, (w, b) ∈ p.take d → (β.any fun (z, _) => z == w) = false)
    (w : Nat)
    (hw_β : (β.any fun (z, _) => z == w) = false)
    (hw : w ∈ (encodeRestrictionFromFormula d dnf β).1.map Prod.fst) :
    ((beameDecoder dnf
      (encodeRestrictionFromFormula d dnf β).1
      (encodeRestrictionFromFormula d dnf β).2).map Prod.fst).contains w = true := by
  -- Unfold the encoder to expose the decision-tree path match.
  cases hlpe :
      leftmostPathExceedingDepth
        (canonicalDecisionTree dnf β) d with
  | none =>
    -- No deep path → encoder emits ([], β), so `hw` puts `w ∈ β.fst`,
    -- contradicting `hw_β`.
    simp only [encodeRestrictionFromFormula, hlpe] at hw
    rw [List.any_eq_false] at hw_β
    obtain ⟨⟨w', b'⟩, hmem', hwfst⟩ := List.mem_map.mp hw
    cases hw_β (w', b') hmem' (by simpa [BEq.beq] using hwfst)
  | some path =>
    simp only [encodeRestrictionFromFormula, hlpe] at hw ⊢
    exact encoder_aux_decoded_contains_dead
      d dnf β hdnf hnodup h_clauses_ne_nil path hlpe
      (hβ_disj_path path hlpe) w hw_β hw

#print axioms encoder_dead_vars_subset_recovered

/-- **Newly-killed dead vars equal `path.take d` vars (as Finsets).**

    Combines:
    * subset: every dead var not in `β.fst` lies in `(path.take d).fst`
      (`encoder_dead_vars_subset_path`),
    * matching cardinality: `dead.length - β.length = d = (path.take d).length`
      (from `encoder_dead_length` + `encoder_dead_nodup_fst`,
      `canonical_dt_path_take_nodup_fst`),
    via `Finset.eq_of_subset_of_card_le`. -/
private lemma encoder_new_dead_vars_equal_path
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (β : List (Nat × Bool))
    (hnodup_β : (β.map Prod.fst).Nodup)
    (d : Nat)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val β) d = some path) :
    ((encodeRestrictionFromFormula d f.val β).1.map Prod.fst).toFinset \
        (β.map Prod.fst).toFinset =
      ((path.take d).map Prod.fst).toFinset := by
  -- Names.
  set dead_fst := (encodeRestrictionFromFormula d f.val β).1.map Prod.fst with hdf_def
  set Sβ := (β.map Prod.fst).toFinset with h_sβ_def
  set Sdead := dead_fst.toFinset with h_sdead_def
  set Spath := ((path.take d).map Prod.fst).toFinset with h_spath_def
  -- (1) Cardinalities.
  have hdead_nodup : dead_fst.Nodup :=
    encoder_dead_nodup_fst f hnodup β hnodup_β d path hpath
  have hdead_len : dead_fst.length = β.length + d := by
    show ((encodeRestrictionFromFormula d f.val β).1.map Prod.fst).length = β.length + d
    rw [List.length_map]
    exact encoder_dead_length f hnodup β d path hpath
  have h_sβ_card : Sβ.card = β.length := by
    rw [h_sβ_def, List.toFinset_card_of_nodup hnodup_β, List.length_map]
  have h_sdead_card : Sdead.card = β.length + d := by
    rw [h_sdead_def, List.toFinset_card_of_nodup hdead_nodup, hdead_len]
  have hpath_take_len : (path.take d).length = d := by
    have hpath_len := leftmostPathExceedingDepth_some_path_length_gt
      (canonicalDecisionTree f.val β) d path hpath
    exact List.length_take_of_le (by omega)
  have hpath_take_nodup_fst : ((path.take d).map Prod.fst).Nodup :=
    canonical_dt_path_take_nodup_fst f.val β hnodup d path hpath
  have h_spath_card : Spath.card = d := by
    rw [h_spath_def, List.toFinset_card_of_nodup hpath_take_nodup_fst,
        List.length_map, hpath_take_len]
  -- (2) `Sβ ⊆ Sdead` via `encoder_β_subset_dead_acc`.
  have hpath_ne_none : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val β) d ≠ none := by
    intro hcontra; rw [hcontra] at hpath; cases hpath
  have hβ_sub_dead : Sβ ⊆ Sdead := by
    intro w hw
    rw [h_sβ_def, List.mem_toFinset, List.mem_map] at hw
    obtain ⟨⟨v, b⟩, hvb_β, rfl⟩ := hw
    have hvb_dead : (v, b) ∈ (encodeRestrictionFromFormula d f.val β).1 :=
      encoder_β_subset_dead_acc d f.val β v b hvb_β hpath_ne_none
    rw [h_sdead_def, hdf_def, List.mem_toFinset, List.mem_map]
    exact ⟨(v, b), hvb_dead, rfl⟩
  -- (3) `(Sdead \ Sβ).card = d`.
  have hdiff_card : (Sdead \ Sβ).card = d := by
    rw [Finset.card_sdiff_of_subset hβ_sub_dead, h_sdead_card, h_sβ_card]
    omega
  -- (4) `Sdead \ Sβ ⊆ Spath` via `encoder_dead_vars_subset_path`.
  have hdiff_sub_path : Sdead \ Sβ ⊆ Spath := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    obtain ⟨hw_dead, hw_not_β⟩ := hw
    have hw_dead' : w ∈ dead_fst := by
      rw [h_sdead_def] at hw_dead; exact List.mem_toFinset.mp hw_dead
    have hw_β_false : (β.any fun (z, _) => z == w) = false := by
      by_contra hcontra
      apply hw_not_β
      have h_any : (β.any fun (z, _) => z == w) = true := by
        cases hb : β.any fun (z, _) => z == w with
        | true => rfl
        | false => exact absurd hb hcontra
      rw [h_sβ_def, List.mem_toFinset, List.mem_map]
      obtain ⟨⟨z, bz⟩, hz_β, hz_eq⟩ := List.any_eq_true.mp h_any
      simp only [beq_iff_eq] at hz_eq
      exact ⟨(z, bz), hz_β, hz_eq⟩
    have hw_path : w ∈ (path.take d).map Prod.fst :=
      encoder_dead_vars_subset_path f hnodup β hnodup_β d path hpath w hw_β_false hw_dead'
    rw [h_spath_def]; exact List.mem_toFinset.mpr hw_path
  -- (5) Equality from subset + matching cardinality.
  exact Finset.eq_of_subset_of_card_le hdiff_sub_path
    (by rw [h_spath_card, hdiff_card])

#print axioms encoder_new_dead_vars_equal_path

/- **"Decoder filters β"**: every variable recovered by the
    iterative decoder lies *outside* `β.fst`.

    This is the structural disjointness property linking the decoder's
    output names to the encoder's β-disjoint γ slots: each decoded `v`
    arises as `T_i.getD pos (0, false)`'s name, which under the
    encoder/decoder alignment (`encoder_aux_decode_gen_iff_mp`)
    coincides with a `U_i = restrictionOfFirstTermNotKilledByList …`
    entry, and `U_i.fst` is disjoint from `β.fst` by
    `rtnkb_fst_disjoint_assigned`.

    The proof follows the decoder alignment induction independently of the
    existing `encoder_aux_decode_gen_iff_mp` direction. -/
private lemma encoder_decoded_disjoint_β
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool))
    (hdnf : isDNF dnf = true)
    (hnodup : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (h_clauses_ne_nil : ∀ c ∈ dnfClauses dnf, c ≠ [])
    (_hnodup_β : (β.map Prod.fst).Nodup)
    (w : Nat)
    (hw : w ∈ (beameDecoder dnf
      (encodeRestrictionFromFormula d dnf β).1
      (encodeRestrictionFromFormula d dnf β).2).map Prod.fst) :
    (β.any fun (z, _) => z == w) = false := by
  -- Argue by contradiction. Suppose w ∈ β.fst.
  by_contra h_ne
  have hw_β : (β.any fun (z, _) => z == w) = true := by
    cases hb : β.any fun (z, _) => z == w with
    | true => rfl
    | false => exact absurd hb h_ne
  -- Unfold encoder; case split on whether a deep DT path exists.
  simp only [encodeRestrictionFromFormula] at hw
  split at hw
  · rw [decoder_eq_foldl_reverse] at hw
    simp [List.foldl_nil] at hw
  · rename_i path hpath
    have hβ_disj_path := encoder_β_disj_path d dnf β hdnf path hpath
    have hfact := encoder_aux_dead_acc_factor (path.take d).length
      (path.take d) dnf β β
    set encoderResult := beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses dnf) β [] with h_encoder_result_def
    rw [hfact] at hw
    simp only at hw
    rw [decoder_β_append_eq_combined] at hw
    rw [decoder_eq_foldl_reverse, List.map_reverse, List.mem_reverse] at hw
    have hpath_nodup := encoder_aux_seed_path_nodup d dnf β hnodup path hpath
    rcases encoder_seed_bundle_nolen d dnf β hdnf hnodup
      h_clauses_ne_nil path hpath hpath_nodup hβ_disj_path with hbundle | h_rev
    · -- LEFT: original loop-based logic.
      have hgen := encoder_aux_decode_gen_loop
        (path.take d).length (path.take d) dnf β
        (combineRestrictions β encoderResult.1) [] []
        β d path
        hbundle
        le_rfl
        hpath_nodup hdnf hnodup
        (encoder_aux_seed_align_nolen d dnf β hdnf hnodup
          h_clauses_ne_nil path hpath hβ_disj_path)
        (by simp) (by simp) (encoder_aux_seed_b_val d dnf β path)
      rcases (hgen w).mp hw with hempty | hdead
      · simp at hempty
      · rw [List.mem_map] at hdead
        obtain ⟨⟨v', b⟩, hpair, hv_eq⟩ := hdead
        simp only at hv_eq
        subst hv_eq
        have h_in_empty : (v', b) ∈ ([] : List (Nat × Bool)) :=
          encoder_aux_no_new_dead_for_assigned _ _ _ _ _ v' b hw_β hpair
        exact List.not_mem_nil h_in_empty
    · -- RIGHT: terminal one-iteration; decoder result.2 = π.reverse.
      have hfoldl := encoder_aux_decode_right_foldl_snd d dnf β
        hdnf hnodup h_clauses_ne_nil path hpath hβ_disj_path h_rev
      simp only at hfoldl
      rw [hfoldl] at hw
      rw [List.map_reverse, List.mem_reverse] at hw
      -- hw : w ∈ (path.take d).map fst.  Take a witness pair.
      obtain ⟨⟨v', b'⟩, hmem, hv_eq⟩ := List.mem_map.mp hw
      simp only at hv_eq
      subst hv_eq
      have hβ_false := hβ_disj_path v' b' hmem
      exact absurd hw_β (by simp [hβ_false])

#print axioms encoder_decoded_disjoint_β

-- ════════════════════════════════════════════════════════════════════════════
-- §  Injection map
-- ════════════════════════════════════════════════════════════════════════════

private lemma chunk_end_bits_length {α : Type*}
    (chunks : List (List α))
    (hne : ∀ c ∈ chunks, c ≠ []) :
    (chunkEndBitsOfChunks chunks).length =
      (chunks.flatMap id).length := by
  simp only [chunkEndBitsOfChunks]
  induction chunks with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, id_eq, List.length_append]
    rw [ih (fun c hc => hne c (List.mem_cons_of_mem _ hc))]
    have hc_ne : c ≠ [] := hne c (List.mem_cons.mpr (Or.inl rfl))
    have hc_not_empty : c.isEmpty = false := by
      cases c with
      | nil => exact absurd rfl hc_ne
      | cons _ _ => rfl
    simp only [hc_not_empty, List.length_replicate]
    cases c with
    | nil => exact absurd rfl hc_ne
    | cons x xs => simp [List.length]

/- Structural properties of the encoder's chunk list are stated relative to
   the `some path` branch of
   `leftmostPathExceedingDepth dt d` so that the relevant length
   equality `(path.take d).length = d` is available. -/

/-- Every chunk in `encoder.2` is non-empty. -/
lemma encoder_chunks_nonempty
    (d : Nat) (dnf : UnboundedFanInFormula) (β : List (Nat × Bool)) :
    ∀ c ∈ (encodeRestrictionFromFormula d dnf β).2, c ≠ [] := by
  -- Reduce to a helper lemma about `beameEncoderAux`.
  simp only [encodeRestrictionFromFormula]
  -- Helper: every chunk in `beameEncoderAux` is non-empty (induction on fuel).
  suffices h : ∀ (fuel : Nat) (remaining_π : List (Nat × Bool))
      (ρ dead_acc : List (Nat × Bool)),
      ∀ c ∈ (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).2,
        c ≠ [] by
    cases hpath : leftmostPathExceedingDepth
        (canonicalDecisionTree dnf β) d with
    | none =>
      intro c hc
      simp at hc
    | some path =>
      intro c hc
      exact h _ _ _ _ c hc
  intro fuel
  induction fuel with
  | zero =>
    intro remaining_π ρ dead_acc c hc
    simp [beameEncoderAux] at hc
  | succ n ih =>
    intro remaining_π ρ dead_acc c hc
    simp only [beameEncoderAux] at hc
    by_cases hne : remaining_π = []
    · rw [if_pos hne] at hc; simp at hc
    · rw [if_neg hne] at hc
      set clauses := dnfClauses dnf
      set U_i := restrictClauseByListAssignment (firstTermNotKilledByList clauses ρ) ρ
      set p : (Nat × Bool) → Bool := fun x => (U_i.map Prod.fst).contains x.1
      set πI := remaining_π.filter p
      by_cases hπ_len : πI.length = 0
      · -- πI = [] branch returns ([], dead_acc')
        rw [if_pos hπ_len] at hc; simp at hc
      · -- πI.length ≠ 0 branch: chunks list = (encoderChunk T_i πI) :: rest
        rw [if_neg hπ_len] at hc
        simp only at hc
        -- `hc : c ∈ (encoderChunk ... :: restEncoder)`.
        rcases List.mem_cons.mp hc with rfl | hrest
        · -- c = encoderChunk T_i πI; nonempty since πI ≠ [].
          intro habs
          unfold encoderChunk at habs
          have hπne : πI ≠ [] := fun h => hπ_len (by rw [h]; rfl)
          exact hπne (List.map_eq_nil_iff.mp habs)
        · exact ih _ _ _ _ hrest

/-- Helper: parallel counting between chunk-flat length and dead-vars length.

    Whenever the encoder steps in the recursive branch
    (`πI.length ≠ 0`), it adds `πI.length` entries to the chunks list
    and `min |U_i| πI.length` entries to `dead_acc`.  Under the Nodup
    hypotheses, `πI.length ≤ U_i.length`, so `γ_i.length = πI.length`,
    and the two counts stay synchronised. -/
private lemma encoder_aux_flat_length_plus_dead_eq
    (fuel : Nat) (remaining_π : List (Nat × Bool))
    (dnf : UnboundedFanInFormula) (ρ dead_acc : List (Nat × Bool))
    (hnodup_clauses : ∀ c ∈ dnfClauses dnf, (c.map Prod.fst).Nodup)
    (hnodup_rem : (remaining_π.map Prod.fst).Nodup) :
    ((beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).2.flatMap
        id).length + dead_acc.length =
      (beameEncoderAux fuel remaining_π (dnfClauses dnf) ρ dead_acc).1.length := by
  induction fuel generalizing remaining_π ρ dead_acc with
  | zero =>
    simp [beameEncoderAux]
  | succ k ih =>
    simp only [beameEncoderAux]
    by_cases hne : remaining_π = []
    · rw [if_pos hne]; simp
    rw [if_neg hne]
    set clauses := dnfClauses dnf
    set T_i := firstTermNotKilledByList clauses ρ
    set U_i := restrictClauseByListAssignment T_i ρ
    set p : (Nat × Bool) → Bool := fun x => (U_i.map Prod.fst).contains x.1
    set πI := remaining_π.filter p with hπi_def
    set γ_i := (gammaBitsForClause U_i).take πI.length with hγi_def
    by_cases hπ_len : πI.length = 0
    · -- Bail branch: ([], dead_acc ++ γ_i).  γ_i = take 0 = [].
      rw [if_pos hπ_len]
      simp only [List.flatMap_nil, List.length_nil, List.length_append,
        Nat.zero_add]
      have : γ_i = [] := by simp [hγi_def, hπ_len]
      rw [this]; simp
    rw [if_neg hπ_len]
    -- Recursive branch.  remaining' is sublist of remaining_π.
    set remaining' := remaining_π.filter
      (fun x => !πI.any fun y => y.1 == x.1) with hrem'_def
    have hnodup_rem' : (remaining'.map Prod.fst).Nodup :=
      List.Pairwise.sublist (List.filter_sublist.map _) hnodup_rem
    -- IH on the recursive call.
    have hih := ih remaining' (combineRestrictions ρ πI)
      (dead_acc ++ γ_i) hnodup_rem'
    -- Compute the LHS.  chunk = encoderChunk T_i πI, length = πI.length.
    simp only [List.flatMap_cons, List.length_append, id_eq]
    rw [show (encoderChunk T_i πI).length = πI.length from by
      simp [encoderChunk]]
    -- Goal:  πI.length + (rest.flatMap id).length + dead_acc.length =
    --        final_dead.length
    -- Use IH:  (rest.flatMap id).length + (dead_acc ++ γ_i).length =
    --          final_dead.length
    -- ⇒ goal becomes πI.length + ... = ... + (dead_acc ++ γ_i).length
    -- ⇒ πI.length = γ_i.length, which holds since πI.length ≤ U_i.length.
    have h_u_nodup : (U_i.map Prod.fst).Nodup := by
      have h_t_nodup : (T_i.map Prod.fst).Nodup := by
        rcases firstTermNotKilledByList_mem_or_nil clauses ρ with hmem | hnil
        · exact hnodup_clauses _ hmem
        · have h_t_nil : T_i = [] := by simpa [T_i] using hnil
          rw [h_t_nil]
          simp
      show ((restrictClauseByListAssignment T_i ρ).map Prod.fst).Nodup
      unfold restrictClauseByListAssignment
      split
      · simp
      · exact List.Pairwise.sublist (List.filter_sublist.map _) h_t_nodup
    have hπi_nodup : (πI.map Prod.fst).Nodup :=
      List.Pairwise.sublist (List.filter_sublist.map _) hnodup_rem
    have hπ_sub_u : ∀ v ∈ πI.map Prod.fst, v ∈ U_i.map Prod.fst := by
      intro v hv
      rw [List.mem_map] at hv
      obtain ⟨⟨vv, dir⟩, hin, hfst⟩ := hv
      simp only at hfst; subst hfst
      have hin' := List.mem_filter.mp hin
      rw [List.contains_iff_mem] at hin'
      exact hin'.2
    have hπi_le_u : πI.length ≤ U_i.length := by
      have h1 : πI.length = (πI.map Prod.fst).length := by
        rw [List.length_map]
      have h2 : (πI.map Prod.fst).length = (πI.map Prod.fst).toFinset.card :=
        (List.toFinset_card_of_nodup hπi_nodup).symm
      have h3 : (πI.map Prod.fst).toFinset ⊆ (U_i.map Prod.fst).toFinset := by
        intro v hv; rw [List.mem_toFinset] at hv ⊢; exact hπ_sub_u v hv
      have h3' : (πI.map Prod.fst).toFinset.card ≤
          (U_i.map Prod.fst).toFinset.card := Finset.card_le_card h3
      have h4 : (U_i.map Prod.fst).toFinset.card ≤ (U_i.map Prod.fst).length :=
        List.toFinset_card_le _
      have h5 : (U_i.map Prod.fst).length = U_i.length := by rw [List.length_map]
      omega
    have hγi_len : γ_i.length = πI.length := by
      simp only [hγi_def, List.length_take, gammaBitsForClause,
        List.length_map]
      omega
    -- Reduce goal: split off the head chunk, use IH.
    simp only [List.length_append] at hih
    omega

/-- The flattened chunk list has total length `d` whenever the
    leftmost-path-exceeding-depth lookup succeeds.

    Proof: combine `encoder_dead_length` (which gives `encoder.1.length =
    β.length + d`) with the parallel-counting helper
    `encoder_aux_flat_length_plus_dead_eq` (which gives
    `(encoder.2.flatMap id).length + dead_acc.length = encoder.1.length`).
    Initial `dead_acc = β`, so flat length = `d`. -/
lemma encoder_flat_length_eq_d
    {n : Nat} (f : UnboundedFanInDNF n)
    (hnodup : ∀ c ∈ dnfClauses f.val, (c.map Prod.fst).Nodup)
    (β : List (Nat × Bool)) (d : Nat)
    (path : List (Nat × Bool))
    (hpath : leftmostPathExceedingDepth
      (canonicalDecisionTree f.val β) d
        = some path) :
    ((encodeRestrictionFromFormula d f.val β).2.flatMap id).length = d := by
  -- encoder_dead_length: encoder.1.length = β.length + d.
  have hdead := encoder_dead_length f hnodup β d path hpath
  -- encoder unfolds to encoder_aux with remaining_π = path.take d, ρ = β,
  -- dead_acc = β.
  have hπ_nodup : ((path.take d).map Prod.fst).Nodup :=
    canonical_dt_path_take_nodup_fst f.val β hnodup d path hpath
  have hcount := encoder_aux_flat_length_plus_dead_eq
    (path.take d).length (path.take d) f.val β β hnodup hπ_nodup
  -- Reduce encoder to encoder_aux.
  simp only [encodeRestrictionFromFormula] at hdead ⊢
  rw [hpath] at hdead ⊢
  simp only at hdead ⊢
  -- hcount : (encoder_aux ... (path.take d) f.val β β).1.flatMap id |>.length
  --          + β.length = (encoder_aux ...).2.length
  -- hdead  : (encoder_aux ...).2.length = β.length + d
  omega

/-- Every position recorded in the flattened chunk list is `< w` whenever
    the underlying clauses have width `≤ w`. -/
lemma encoder_position_lt_w
    (d : Nat) (n w : Nat) (f : UnboundedFanInDNF n) (β : List (Nat × Bool))
    (hwidth : dnfWidth f.val ≤ w) :
    ∀ pos ∈ ((encodeRestrictionFromFormula d f.val β).2.flatMap id).map Prod.fst,
      pos < w := by
  simp only [encodeRestrictionFromFormula]
  -- Helper: positions in `beameEncoderAux` chunks are `< w`.
  suffices h : ∀ (fuel : Nat) (remaining_π ρ dead_acc : List (Nat × Bool)),
      ∀ pos ∈
        ((beameEncoderAux fuel remaining_π (dnfClauses f.val) ρ dead_acc).2.flatMap
          id).map Prod.fst,
        pos < w by
    cases hpath : leftmostPathExceedingDepth
        (canonicalDecisionTree f.val β) d with
    | none =>
      intro pos hpos
      simp at hpos
    | some path =>
      intro pos hpos
      exact h _ _ _ _ pos hpos
  intro fuel
  induction fuel with
  | zero =>
    intro remaining_π ρ dead_acc pos hpos
    simp [beameEncoderAux] at hpos
  | succ k ih =>
    intro remaining_π ρ dead_acc pos hpos
    simp only [beameEncoderAux] at hpos
    by_cases hne : remaining_π = []
    · rw [if_pos hne] at hpos; simp at hpos
    rw [if_neg hne] at hpos
    set clauses := dnfClauses f.val
    set T_i := firstTermNotKilledByList clauses ρ
    set U_i := restrictClauseByListAssignment T_i ρ
    set p : (Nat × Bool) → Bool := fun x => (U_i.map Prod.fst).contains x.1
    set πI := remaining_π.filter p
    by_cases hπ_len : πI.length = 0
    · rw [if_pos hπ_len] at hpos; simp at hpos
    rw [if_neg hπ_len] at hpos
    -- chunks = (encoderChunk T_i πI) :: restEncoder
    simp only [List.flatMap_cons, List.map_append, List.mem_append,
      id_eq] at hpos
    rcases hpos with hin_chunk | hin_rest
    · -- pos ∈ (encoderChunk T_i πI).map Prod.fst
      unfold encoderChunk at hin_chunk
      rw [List.map_map, List.mem_map] at hin_chunk
      obtain ⟨⟨v, dir⟩, hv_in_πi, hpos_eq⟩ := hin_chunk
      -- pos = findPositionInClause' T_i v
      simp only [Function.comp] at hpos_eq
      subst hpos_eq
      -- v ∈ πI ⇒ v ∈ U_i.map fst (since πI = remaining_π.filter (U_vars.contains))
      have hv_in_u : (U_i.map Prod.fst).contains v = true :=
        (List.mem_filter.mp hv_in_πi).2
      -- U_i ⊆ T_i: restriction either returns [] or filters T_i.
      have hv_in_t : T_i.any (fun lit => lit.1 == v) = true := by
        rw [List.contains_iff_mem, List.mem_map] at hv_in_u
        obtain ⟨⟨v', neg'⟩, hmem_u, hfst⟩ := hv_in_u
        simp only at hfst; subst hfst
        -- U_i is T_i restricted by ρ.
        simp only [U_i, restrictClauseByListAssignment] at hmem_u
        -- Splits depending on whether T_i is killed; if killed, U_i = []
        split at hmem_u
        · simp at hmem_u
        · -- U_i = T_i.filter (...), so v' ∈ T_i
          have : (v', neg') ∈ T_i := List.mem_of_mem_filter hmem_u
          rw [List.any_eq_true]
          exact ⟨(v', neg'), this, by simp⟩
      have h_pos_lt : findPositionInClause' T_i v < T_i.length :=
        findPositionInClause'_lt T_i v hv_in_t
      -- T_i.length ≤ dnfWidth f.val ≤ w.
      have h_t_len_le_w : T_i.length ≤ w := by
        rcases firstTermNotKilledByList_mem_or_nil clauses ρ with hmem | hnil
        · exact le_trans
            (clause_length_le_dnfWidth f.val f.property.2 _ hmem)
            hwidth
        · simp [T_i, hnil]
      omega
    · exact ih _ _ _ pos hin_rest

/-- **Beame injection map (full-query DT).**

    Uses the *full-query* canonical
    DT (`canonicalDecisionTree`), which queries
    every variable of the selected clause on every branch (matching the
    Beame switching-lemma construction). Internally it runs the structured
    encoder `encoderRestriction`.

    The encoding:
    1. Convert `(S, bits)` to list-based assignment `β`.
    2. Build the full-query canonical DT
       `dt = canonicalDecisionTree f.val β`.
    3. Take the first `d` entries of the leftmost path of length > `d`,
       call it `path_d`; let `J = (path_d.map fst).toFinset`.
    4. Run `encoderRestriction d f assignedRestriction` to obtain
       `(dead_vars, chunks)`, where each chunk records encoded clause positions
       paired with path directions.
    5. Form `B_fn = restrictionAsFunction dead_vars`; `dead_vars` already
       contains `β` because the encoder seeds its accumulator with `β`.
    6. `S' = S \ J`, `bits' = extractDeadBits B_fn S' n`.
    7. Flatten `chunks` to obtain the `d` base-`w` positions and `d` path
       directions, and record another `d` bits marking chunk boundaries.
    8. Output triple `(S', encodeBits bits',
                       pos_idx · 2^(2d) + dir_boundary_idx)`, where
       `dir_boundary_idx` encodes the directions followed by the chunk-end
       markers.

    Advisory bound: `< w^d * 2^(2d) = (4w)^d`. -/
def beameEncoderMap
    (d n : Nat) (f : UnboundedFanInProperDNF n) (w : Nat)
    (hwidth : dnfWidth f.val ≤ w) (_hw : 0 < w)
    (σ : OpenUnitIntervalQ)
    (_hsd : d < Nat.ceil (σ.val * n))
    (S : Finset Nat) (h_s : S ⊆ Finset.range n)
    (hcard : S.card = Nat.ceil (σ.val * n))
    (bits : List Bool)
    (hbits_len : S.card + bits.length = n)
    (hbad : isBadRestriction d n σ f
      ⟨⟨⟨S, h_s⟩, hcard⟩, bits, hbits_len⟩ = true) :
    (injectionTargetSet n (Nat.ceil (σ.val * n)) d w) :=
  -- Build list-based assignment β from (S, bits)
  let β := mkAssignmentList S bits n
  -- Build full-query canonical DT
  let dt := canonicalDecisionTree f.val β
  let path_d :=
    match leftmostPathExceedingDepth dt d with
    | none => ([] : List (Nat × Bool))
    | some path => path.take d
  let J := (path_d.map Prod.fst).toFinset
  let S' := S \ J
  let assignedRestriction : AssignedRandomRestriction σ n :=
    ⟨⟨⟨S, h_s⟩, hcard⟩, bits, hbits_len⟩
  -- Run the structured encoder.
  let encoder := encoderRestriction d f assignedRestriction
  let dead_vars := encoder.1
  -- `dead_vars` already contains β as a prefix.
  let B_fn := restrictionAsFunction dead_vars
  -- Dead bits of B_fn relative to S'
  let bits' := extractDeadBits B_fn S' n
  -- Pack the encoder's seed-walk chunks directly for the decoder.
  let chunks := encoder.2
  let positions := (chunks.flatMap id).map Prod.fst
  let directions := (chunks.flatMap id).map Prod.snd
  let pos_idx := encodeBaseW positions w
  -- Encode directions (d bits) and chunk-end markers (d bits) together
  let ceb := chunkEndBitsOfChunks chunks
  let dir_boundary_idx := encodeBits (directions ++ ceb)
  ⟨(S', encodeBits bits',
    pos_idx * 2 ^ (2 * d) + dir_boundary_idx),
   by
    set s := Nat.ceil (σ.val * n) with hs_def
    have hsn : s ≤ n := ceil_sigma_n_le σ n
    change decide (decisionTreeDepth
      (canonicalDecisionTree f.val β) > d) = true at hbad
    simp only [Nat.lt_iff_add_one_le, decide_eq_true_eq] at hbad
    -- DT in hbad matches dt
    have hdt_eq : dt =
        canonicalDecisionTree f.val β := rfl
    have hbad' : decisionTreeDepth dt > d := by
      rw [hdt_eq]; exact hbad
    have his := leftmostPathExceedingDepth_depth_gt_imp_isSome dt d hbad'
    obtain ⟨path, hpath_eq⟩ := Option.isSome_iff_exists.mp his
    have hpath_len := leftmostPathExceedingDepth_some_path_length_gt
      dt d path hpath_eq
    have htake_len : (path.take d).length = d :=
      List.length_take_of_le (by omega)
    have hpath_d_eq : path_d = path.take d := by
      simp only [path_d, hpath_eq]
    have hnodup_fst : ((path.take d).map Prod.fst).Nodup :=
      canonical_dt_path_take_nodup_fst
        f.val β f.property.2.2.2 d path hpath_eq
    have hpath_vars_in_s : ∀ v, v ∈ (path_d.map Prod.fst) → v ∈ S := by
      intro v hv
      rw [hpath_d_eq] at hv
      rw [List.mem_map] at hv
      obtain ⟨⟨w', b'⟩, hmem, rfl⟩ := hv
      have hmem_path : (w', b') ∈ path := List.mem_of_mem_take hmem
      have hasgn_fn_none :=
        canonical_dt_path_var_none f.val β f.property.2.1
          d path hpath_eq w' b' hmem_path
      have hw_in_dt := leftmostPathExceedingDepth_vars_in_collect
        dt d path hpath_eq w' b' hmem_path
      simp only [dt, canonicalDecisionTree] at hw_in_dt
      obtain ⟨c, hc_mem, hw_in_c⟩ :=
        canonicalDecisionTreeAuxPreciseFull_vars_in
          (dnfClauses (simpleRestrictDNF
            (restrictionAsFunction β) f.val)).length
          _ w' hw_in_dt
      have hv_vars : w' ∈ canonicalDTVarOrder
          (simpleRestrictDNF (restrictionAsFunction β) f.val) := by
        rw [canonicalDTVarOrder, mem_dedupFirst]
        exact List.mem_flatMap.mpr ⟨c, hc_mem, hw_in_c⟩
      have hv_inp := canonicalDTVarOrder_subset_inputs
        (simpleRestrictDNF (restrictionAsFunction β) f.val)
        (restrictDNF_preserves_dnf (restrictionAsFunction β)
          f.val f.property.2.1) w' hv_vars
      have hv_orig := (restrictDNF_preserves_valid_inputs
        (restrictionAsFunction β) f.val f.property.2.1 w'
        (List.mem_dedup.mpr hv_inp)).1
      have hw_lt_n : w' < n :=
        Nat.lt_of_le_of_lt (adder_foldr_max_ge_of_mem (List.mem_dedup.mp hv_orig))
          f.property.1
      have hasgn_none : mkAssignment S bits w' = none := by
        rw [← cr_none_mkAssignmentList_eq S bits n w' hw_lt_n]
        exact hasgn_fn_none
      exact mkAssignment_none_imp_mem S bits n h_s hbits_len w' hw_lt_n hasgn_none
    have h_j_sub_s : J ⊆ S := by
      intro v hv; simp only [J] at hv
      rw [List.mem_toFinset] at hv; exact hpath_vars_in_s v hv
    have h_j_card : J.card = d := by
      change (List.map Prod.fst path_d).toFinset.card = d
      rw [hpath_d_eq, List.card_toFinset, hnodup_fst.dedup,
        List.length_map, htake_len]
    simp only [injectionTargetSet, Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · -- S' ∈ powersetCard (s - d)
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.sdiff_subset.trans h_s,
        by rw [Finset.card_sdiff_of_subset h_j_sub_s, hcard, h_j_card]⟩
    · -- bit_idx < 2^(n-(s-d))
      have h_s'_card : S'.card = s - d := by
        rw [Finset.card_sdiff_of_subset h_j_sub_s, hcard, h_j_card]
      have h_s'_sub : S' ⊆ Finset.range n := Finset.sdiff_subset.trans h_s
      have hbits'_len_le : bits'.length ≤ n - (s - d) := by
        rw [show bits' = extractDeadBits B_fn S' n from rfl, ← h_s'_card]
        exact extractDeadBits_length_le B_fn S' n h_s'_sub
      calc encodeBits bits'
          < 2 ^ bits'.length := encodeBits_lt
        _ ≤ 2 ^ (n - (s - d)) := Nat.pow_le_pow_right (by omega) hbits'_len_le
    · -- adv_idx < (4w)^d
      have hflat_len : ((encodeRestrictionFromFormula d f.val β).2.flatMap id).length = d :=
        encoder_flat_length_eq_d
          ⟨f.val, f.property.1, f.property.2.1⟩
          f.property.2.2.2 β d path hpath_eq
      have hpos_len : positions.length = d := by
        simp only [positions, chunks]
        rw [List.length_map]; exact hflat_len
      have hdir_len : directions.length = d := by
        simp only [directions, chunks]
        rw [List.length_map]; exact hflat_len
      have hchunks_ne : ∀ c ∈ chunks, c ≠ [] := by
        intro c hc; exact encoder_chunks_nonempty d f.val β c hc
      have hceb_len : ceb.length = d := by
        simp only [ceb]
        rw [chunk_end_bits_length _ hchunks_ne]
        exact hflat_len
      have hpi : pos_idx < w ^ d := by
        calc encodeBaseW positions w
            < w ^ positions.length :=
              encodeBaseW_lt (fun a ha =>
                encoder_position_lt_w d n w
                  ⟨f.val, f.property.1, f.property.2.1⟩
                  β hwidth a ha)
          _ = w ^ d := by rw [hpos_len]
      have hdbi : dir_boundary_idx < 2 ^ (2 * d) := by
        calc encodeBits (directions ++ ceb)
            < 2 ^ (directions ++ ceb).length := encodeBits_lt
          _ = 2 ^ (2 * d) := by
              rw [List.length_append, hdir_len, hceb_len]; ring
      calc pos_idx * 2 ^ (2 * d) + dir_boundary_idx
          < pos_idx * 2 ^ (2 * d) + 2 ^ (2 * d) := by omega
        _ = (pos_idx + 1) * 2 ^ (2 * d) := by ring
        _ ≤ w ^ d * 2 ^ (2 * d) := by
            apply Nat.mul_le_mul_right; omega
        _ = w ^ d * (4 ^ d) := by
            have : 2 ^ (2 * d) = 4 ^ d := by
              rw [show (4 : Nat) = 2 ^ 2 from by norm_num, ← pow_mul]
            rw [this]
        _ = (4 * w) ^ d := by
            rw [mul_comm (w ^ d), ← mul_pow]⟩

-- ════════════════════════════════════════════════════════════════════════════
-- §  Injection-level decoder map and roundtrip
-- ════════════════════════════════════════════════════════════════════════════

/- Split a flat list at marked chunk ends, then recover the variable names
   encoded by each chunk. -/

private def splitByEndBits {α : Type*}
    : List α → List Bool → List (List α)
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs =>
    match b with
    | .true => [a] :: splitByEndBits as bs
    | .false =>
      match splitByEndBits as bs with
      | [] => [[a]]
      | chunk :: rest => (a :: chunk) :: rest

private lemma splitByEndBits_chunk_end_bits {α : Type*}
    (chunks : List (List α))
    (hne : ∀ c ∈ chunks, c ≠ []) :
    splitByEndBits (chunks.flatMap id)
      (chunkEndBitsOfChunks chunks) = chunks := by
  induction chunks with
  | nil => simp [splitByEndBits, chunkEndBitsOfChunks]
  | cons c cs ih =>
    have hc_ne : c ≠ [] := hne c (by simp)
    have hih := ih (fun c' hc' => hne c' (by simp [hc']))
    suffices hsuff : ∀ (c : List α) (rest : List α) (rest_bits : List Bool),
        c ≠ [] →
        splitByEndBits rest rest_bits = cs →
        splitByEndBits (c ++ rest)
          (List.replicate (c.length - 1) false ++ [true] ++ rest_bits) =
          c :: cs by
      rw [show (c :: cs).flatMap id = c ++ cs.flatMap id from by simp]
      rw [show chunkEndBitsOfChunks (c :: cs) =
          List.replicate (c.length - 1) false ++ [true] ++
          chunkEndBitsOfChunks cs from by
        simp only [chunkEndBitsOfChunks, List.flatMap_cons,
          List.isEmpty_iff, hc_ne, ↓reduceIte, List.append_assoc]]
      exact hsuff c (cs.flatMap id) (chunkEndBitsOfChunks cs) hc_ne hih
    intro c
    induction c with
    | nil => intro _ _ h; exact absurd rfl h
    | cons x xs ihc =>
      intro rest rest_bits _hne hrest
      cases xs with
      | nil =>
        simp only [List.length_cons, List.length_nil, Nat.zero_add,
          Nat.add_one_sub_one, List.replicate_zero, List.nil_append,
          List.cons_append]
        rw [splitByEndBits]
        simp only [List.cons.injEq, true_and]
        exact hrest
      | cons y ys =>
        simp only [List.length_cons, Nat.add_sub_cancel, List.replicate_succ,
          List.cons_append, List.append_assoc]
        rw [splitByEndBits]
        have ihuse := ihc rest rest_bits (List.cons_ne_nil _ _) hrest
        simp only [List.length_cons, Nat.add_sub_cancel] at ihuse
        simp only [List.cons_append, List.append_assoc, List.nil_append]
          at ihuse ⊢
        rw [ihuse]

/-- **Beame injection-level decoder map (full-query DT).**

    Inverts `beameEncoderMap`.

    The advisory index encodes:
    * `pos_idx = adv_idx / 2^(2d)` — positions in base `w`
    * `dir_boundary_idx = adv_idx % 2^(2d)` — `d` direction bits ++ `d`
      chunk-end bits

    Chunk-end bits allow reconstructing the chunk structure used by the
    encoder so that each chunk is decoded under the correct selected clause. -/
def beameDecoderMap
    (d n : Nat) (f : UnboundedFanInProperDNF n) (w : Nat)
    (σ : OpenUnitIntervalQ)
    (S' : Finset Nat) (bit_idx adv_idx : Nat)
    : Finset Nat × List Bool :=
  let s := Nat.ceil (σ.val * n)
  let bits' := decodeBits bit_idx (n - (s - d))
  let B_fn := mkAssignment S' bits'
  let pos_idx := adv_idx / 2 ^ (2 * d)
  let dir_boundary_idx := adv_idx % 2 ^ (2 * d)
  let dir_boundary_bits := decodeBits dir_boundary_idx (2 * d)
  let directions := dir_boundary_bits.take d
  let chunk_end_markers := dir_boundary_bits.drop d
  let positions := decodeBaseW pos_idx w d
  let flat := positions.zip directions
  let chunks := splitByEndBits flat chunk_end_markers
  -- Recover variables with the decoder.
  -- We pass the reconstructed B_fn as a list (`mkAssignmentList S' bits' n`)
  -- in the `dead_vars` slot (with `asgn = []`), so that
  -- `combineRestrictions [] (mkAssignmentList S' bits' n)` agrees with
  -- B_fn as a function.
  let dead_vars_list := mkAssignmentList S' bits' n
  let J_list := (beameDecoder f.val dead_vars_list chunks).map Prod.fst
  let S := S' ∪ J_list.toFinset
  let bits := extractDeadBits B_fn S n
  (S, bits)


-- ════════════════════════════════════════════════════════════════════════════
-- §  Invariance of `beameDecoder` under equal induced restrictions
-- ════════════════════════════════════════════════════════════════════════════

/- The decoder `beameDecoder` only inspects its `B` argument
   through `firstTermNotKilledByList`, which itself reads `B` only via
   `B.find? (·.1 == v)`.  The bit produced by that find? is determined by
   `restrictionAsFunction B v`.  Hence the entire decoder
   is invariant when two values of `B` induce the same restriction function. -/

private lemma decoder_ftnkb_eq_of_cr_none_eq
    (clauses : List (List (Nat × Bool)))
    (B₁ B₂ : List (Nat × Bool))
    (h_eq : restrictionAsFunction B₁ =
            restrictionAsFunction B₂) :
    firstTermNotKilledByList clauses B₁ =
    firstTermNotKilledByList clauses B₂ := by
  exact firstTermNotKilledByList_eq_of_cr_none_eq clauses B₁ B₂
    (fun v => congrFun h_eq v)

private lemma decoder_cr_none_cons_eq_of_cr_none_eq
    (B₁ B₂ : List (Nat × Bool)) (vp : Nat × Bool)
    (h_eq : restrictionAsFunction B₁ =
            restrictionAsFunction B₂) :
    restrictionAsFunction (vp :: B₁) =
    restrictionAsFunction (vp :: B₂) := by
  funext w
  simp only [restrictionAsFunction, List.find?_cons]
  by_cases h : (vp.1 == w) = true
  · simp [h]
  · simp [h]
    exact congrFun h_eq w

private lemma decoder_inner_chunk_foldl_eq
    (T_i : List (Nat × Bool))
    (chunk : List (Nat × Bool))
    (B vars : List (Nat × Bool)) :
    chunk.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
      let v := (T_i.getD pb.1 (0, false)).1
      ((v, pb.2) :: st.1, (v, pb.2) :: st.2)) (B, vars) =
    (let prepends := (chunk.map (fun pb => ((T_i.getD pb.1 (0, false)).1, pb.2))).reverse
     (prepends ++ B, prepends ++ vars)) := by
  induction chunk generalizing B vars with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.reverse_cons]
    rw [ih]
    simp only [List.append_assoc, List.singleton_append]

private lemma decoder_outer_chunks_foldl_eq
    (clauses : List (List (Nat × Bool)))
    (chunks : List (List (Nat × Bool)))
    (B₁ B₂ vars : List (Nat × Bool))
    (h_eq : restrictionAsFunction B₁ =
            restrictionAsFunction B₂) :
    (chunks.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) chunk =>
      let T_i := firstTermNotKilledByList clauses st.1
      chunk.foldl (fun (st' : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
        let v := (T_i.getD pb.1 (0, false)).1
        ((v, pb.2) :: st'.1, (v, pb.2) :: st'.2)) st) (B₁, vars)).2 =
    (chunks.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) chunk =>
      let T_i := firstTermNotKilledByList clauses st.1
      chunk.foldl (fun (st' : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
        let v := (T_i.getD pb.1 (0, false)).1
        ((v, pb.2) :: st'.1, (v, pb.2) :: st'.2)) st) (B₂, vars)).2 := by
  suffices h : ∀ vars B₁ B₂,
      restrictionAsFunction B₁ =
        restrictionAsFunction B₂ →
      (chunks.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) chunk =>
        let T_i := firstTermNotKilledByList clauses st.1
        chunk.foldl (fun (st' : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
          let v := (T_i.getD pb.1 (0, false)).1
          ((v, pb.2) :: st'.1, (v, pb.2) :: st'.2)) st) (B₁, vars)).2 =
      (chunks.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) chunk =>
        let T_i := firstTermNotKilledByList clauses st.1
        chunk.foldl (fun (st' : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
          let v := (T_i.getD pb.1 (0, false)).1
          ((v, pb.2) :: st'.1, (v, pb.2) :: st'.2)) st) (B₂, vars)).2 ∧
      restrictionAsFunction
        (chunks.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) chunk =>
          let T_i := firstTermNotKilledByList clauses st.1
          chunk.foldl (fun (st' : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
            let v := (T_i.getD pb.1 (0, false)).1
            ((v, pb.2) :: st'.1, (v, pb.2) :: st'.2)) st) (B₁, vars)).1 =
      restrictionAsFunction
        (chunks.foldl (fun (st : List (Nat × Bool) × List (Nat × Bool)) chunk =>
          let T_i := firstTermNotKilledByList clauses st.1
          chunk.foldl (fun (st' : List (Nat × Bool) × List (Nat × Bool)) (pb : Nat × Bool) =>
            let v := (T_i.getD pb.1 (0, false)).1
            ((v, pb.2) :: st'.1, (v, pb.2) :: st'.2)) st) (B₂, vars)).1 from
    (h vars B₁ B₂ h_eq).1
  clear h_eq B₁ B₂ vars
  induction chunks with
  | nil =>
    intro vars B₁ B₂ h_eq
    exact ⟨rfl, h_eq⟩
  | cons hd tl ih =>
    intro vars B₁ B₂ h_eq
    simp only [List.foldl_cons]
    set T₁ := firstTermNotKilledByList clauses B₁ with h_t₁
    set T₂ := firstTermNotKilledByList clauses B₂ with h_t₂
    have h_t : T₁ = T₂ :=
      decoder_ftnkb_eq_of_cr_none_eq clauses B₁ B₂ h_eq
    rw [decoder_inner_chunk_foldl_eq T₁ hd B₁ vars]
    rw [decoder_inner_chunk_foldl_eq T₂ hd B₂ vars]
    rw [h_t]
    set P := (hd.map (fun pb => ((T₂.getD pb.1 (0, false)).1, pb.2))).reverse with h_p
    have h_p_pres : restrictionAsFunction (P ++ B₁) =
                   restrictionAsFunction (P ++ B₂) := by
      clear ih h_t h_t₁ h_t₂
      induction P with
      | nil => simpa using h_eq
      | cons p ps ih_p =>
        simp only [List.cons_append]
        exact decoder_cr_none_cons_eq_of_cr_none_eq _ _ p ih_p
    exact ih (P ++ vars) (P ++ B₁) (P ++ B₂) h_p_pres

/- **`beameDecoder` is invariant under equality of the restrictions induced by B.** -/
lemma beameDecoder_eq_of_cr_none_eq
    (dnf : UnboundedFanInFormula) (B₁ B₂ : List (Nat × Bool))
    (chunks : List (List (Nat × Bool)))
    (h_eq : restrictionAsFunction B₁ =
            restrictionAsFunction B₂) :
    beameDecoder dnf B₁ chunks =
    beameDecoder dnf B₂ chunks := by
  unfold beameDecoder
  have h := decoder_outer_chunks_foldl_eq (dnfClauses dnf) chunks B₁ B₂ [] h_eq
  exact congrArg List.reverse h

/-- **Encode-decode injection roundtrip for Beame.**

    States that `beameDecoderMap` recovers `(S, bits)` from
    the triple produced by `beameEncoderMap`, using the
    full-query canonical DT
    (`canonicalDecisionTree`). -/
lemma beame_encoder_decoder_injection_roundtrip
    (d n : Nat) (f : UnboundedFanInProperDNF n) (w : Nat)
    (hwidth : dnfWidth f.val ≤ w) (hw : 0 < w)
    (σ : OpenUnitIntervalQ)
    (hsd : d < Nat.ceil (σ.val * n))
    (S : Finset Nat) (h_s : S ⊆ Finset.range n)
    (hcard : S.card = Nat.ceil (σ.val * n))
    (bits : List Bool)
    (hbits_len : S.card + bits.length = n)
    (hbad : isBadRestriction d n σ f
      ⟨⟨⟨S, h_s⟩, hcard⟩, bits, hbits_len⟩ = true) :
    let result :=
      beameEncoderMap d n f w hwidth hw σ hsd
        S h_s hcard bits hbits_len hbad
    beameDecoderMap d n f w σ
      result.val.1 result.val.2.1 result.val.2.2 =
      (S, bits) := by
  let fDNF : UnboundedFanInDNF n :=
    ⟨f.val, f.property.1, f.property.2.1⟩
  -- Unfold encoder and decoder.
  simp only [beameEncoderMap,
    beameDecoderMap]
  set s := Nat.ceil (σ.val * n) with hs_def
  set β := mkAssignmentList S bits n with hβ_def
  set dt := canonicalDecisionTree
    f.val β with hdt_def
  -- Extract the path from `isBadRestriction`.
  have hbad' : decisionTreeDepth dt > d := by
    change decide (decisionTreeDepth dt > d) = true at hbad
    simp only [Nat.lt_iff_add_one_le, decide_eq_true_eq] at hbad
    exact hbad
  have his :=
    leftmostPathExceedingDepth_depth_gt_imp_isSome
      dt d hbad'
  obtain ⟨path, hpath_eq⟩ :=
    Option.isSome_iff_exists.mp his
  have hpath_len :=
    leftmostPathExceedingDepth_some_path_length_gt
      dt d path hpath_eq
  have htake_len : (path.take d).length = d :=
    List.length_take_of_le (by omega)
  set path_d := path.take d with hpath_d_def
  set J := (path_d.map Prod.fst).toFinset with h_j_def
  set S' := S \ J with h_s'_def
  -- Nodup of path-prefix variables (full-query DT version).
  have hnodup_fst : (path_d.map Prod.fst).Nodup :=
    canonical_dt_path_take_nodup_fst
      f.val β f.property.2.2.2 d path hpath_eq
  -- Every path-prefix variable is in `S` (since β = mkAssignmentList S bits n
  -- only assigns vars in S^c, and path vars are unassigned by β).
  have h_j_sub_s : J ⊆ S := by
    intro v hv; rw [h_j_def, List.mem_toFinset] at hv
    rw [List.mem_map] at hv
    obtain ⟨⟨w', b'⟩, hmem, rfl⟩ := hv
    have hmem_path : (w', b') ∈ path := List.mem_of_mem_take hmem
    have hasgn_fn_none :=
      canonical_dt_path_var_none
        f.val β f.property.2.1 d path hpath_eq w' b' hmem_path
    have hw_in_dt := leftmostPathExceedingDepth_vars_in_collect
      dt d path hpath_eq w' b' hmem_path
    simp only [dt, canonicalDecisionTree] at hw_in_dt
    obtain ⟨c, hc_mem, hw_in_c⟩ :=
      canonicalDecisionTreeAuxPreciseFull_vars_in
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction β) f.val)).length
        _ w' hw_in_dt
    have hv_vars : w' ∈ canonicalDTVarOrder
        (simpleRestrictDNF (restrictionAsFunction β) f.val) := by
      rw [canonicalDTVarOrder, mem_dedupFirst]
      exact List.mem_flatMap.mpr ⟨c, hc_mem, hw_in_c⟩
    have hv_inp := canonicalDTVarOrder_subset_inputs
      (simpleRestrictDNF (restrictionAsFunction β) f.val)
      (restrictDNF_preserves_dnf (restrictionAsFunction β)
        f.val f.property.2.1) w' hv_vars
    have hv_orig := (restrictDNF_preserves_valid_inputs
      (restrictionAsFunction β) f.val f.property.2.1 w'
      (List.mem_dedup.mpr hv_inp)).1
    have hw_lt_n : w' < n :=
      Nat.lt_of_le_of_lt (adder_foldr_max_ge_of_mem (List.mem_dedup.mp hv_orig))
        f.property.1
    have hasgn_none : mkAssignment S bits w' = none := by
      rw [← cr_none_mkAssignmentList_eq S bits n w' hw_lt_n]
      exact hasgn_fn_none
    exact mkAssignment_none_imp_mem S bits n h_s hbits_len w' hw_lt_n hasgn_none
  have h_j_card : J.card = d := by
    rw [h_j_def, List.card_toFinset,
      hnodup_fst.dedup, List.length_map, htake_len]
  have h_s'_card : S'.card = s - d := by
    rw [h_s'_def,
      Finset.card_sdiff_of_subset h_j_sub_s,
      hcard, h_j_card]
  -- S' ∪ J = S.
  have h_s'_j_eq_s : S' ∪ J = S := by
    rw [h_s'_def, Finset.sdiff_union_self_eq_union,
      Finset.union_eq_left.mpr h_j_sub_s]
  -- Match expression simplification (the encoder's `path_d` reduces to ours).
  have hmatch_eq :
      (match leftmostPathExceedingDepth dt d
        with
      | none => []
      | some path => path.take d) = path_d := by
    simp [hpath_eq, hpath_d_def]
  -- Encoder bookkeeping.
  let assignedRestriction : AssignedRandomRestriction σ n :=
    ⟨⟨⟨S, h_s⟩, hcard⟩, bits, hbits_len⟩
  set encoder :=
    encoderRestriction d f assignedRestriction with h_encoder_def
  have h_encoder_raw : encodeRestrictionFromFormula d f.val β = encoder := by
    rw [h_encoder_def]
    rfl
  set dead_vars := encoder.1 with hdead_def
  have h_encoder_dead_eq :
      encoder.1 = β ++ (beameEncoderAux
        (path.take d).length (path.take d) (dnfClauses f.val) β []).1 := by
    rw [← h_encoder_raw]
    simp only [encodeRestrictionFromFormula]
    cases hlpe : leftmostPathExceedingDepth
        (canonicalDecisionTree f.val β) d with
    | none =>
      exfalso
      rw [← hdt_def] at hlpe
      rw [hlpe] at hpath_eq
      cases hpath_eq
    | some path' =>
      have hp_eq : path' = path := by
        rw [← hdt_def] at hlpe
        rw [hlpe] at hpath_eq
        exact Option.some.inj hpath_eq
      rw [hp_eq]
      exact congrArg Prod.fst
        (encoder_aux_dead_acc_factor (path.take d).length (path.take d)
          f.val β β)
  set B_fn :=
    restrictionAsFunction dead_vars with h_b_fn_def
  set bits' :=
    extractDeadBits B_fn S' n with hbits'_def
  -- The encoder packs `encoder.2` directly.
  set chunks := encoder.2 with hchunks_def
  set positions := (chunks.flatMap id).map Prod.fst with hpos_def
  set directions := (chunks.flatMap id).map Prod.snd with hdir_def
  set ceb := chunkEndBitsOfChunks chunks with hceb_def
  set dir_boundary_idx := encodeBits (directions ++ ceb)
    with hdbi_def
  -- Length facts via the structural lemmas for `encoder.2`.
  have hflat_len : (chunks.flatMap id).length = d := by
    rw [hchunks_def, h_encoder_def]
    exact encoder_flat_length_eq_d fDNF f.property.2.2.2 β d path hpath_eq
  have hpos_len : positions.length = d := by
    rw [hpos_def, List.length_map]; exact hflat_len
  have hdir_len : directions.length = d := by
    rw [hdir_def, List.length_map]; exact hflat_len
  have hchunks_ne : ∀ c ∈ chunks, c ≠ [] := by
    intro c hc
    rw [hchunks_def, h_encoder_def] at hc
    exact encoder_chunks_nonempty d f.val β c hc
  have hceb_len : ceb.length = d := by
    rw [hceb_def, chunk_end_bits_length _ hchunks_ne]; exact hflat_len
  -- (2b) Direction-boundary decode roundtrip (alignment-free).
  have hdir_ceb_len : (directions ++ ceb).length = 2 * d := by
    rw [List.length_append, hdir_len, hceb_len]; ring
  have h_decoder_dir_ceb :
      decodeBits dir_boundary_idx (2 * d) = directions ++ ceb := by
    rw [hdbi_def, ← hdir_ceb_len, decodeBits_encodeBits]
  have h_decoder_dir :
      (decodeBits dir_boundary_idx (2 * d)).take d = directions := by
    rw [h_decoder_dir_ceb, List.take_left' hdir_len]
  have h_decoder_ceb :
      (decodeBits dir_boundary_idx (2 * d)).drop d = ceb := by
    rw [h_decoder_dir_ceb, List.drop_left' hdir_len]
  -- (3a) Encoder bookkeeping: B_fn ↔ S' characterization.
  have hβ_nodup_fst : (β.map Prod.fst).Nodup := by
    rw [hβ_def]; exact mkAssignmentList_map_fst_nodup S bits n
  have hsn : s ≤ n := ceil_sigma_n_le σ n
  have h_b_fn_ne_none :
      ∀ v, v < n → v ∉ S' → B_fn v ≠ none := by
    intro v hv_lt hv_not_s'
    rw [h_s'_def, Finset.mem_sdiff] at hv_not_s'
    push Not at hv_not_s'
    suffices h : ∃ b, (v, b) ∈ dead_vars by
      obtain ⟨b, hb⟩ := h
      rw [h_b_fn_def]
      intro heq
      have hany : (dead_vars.any fun (w, _) => w == v) = true :=
        List.any_eq_true.mpr ⟨(v, b), hb, by simp⟩
      rw [list_any_eq_cr_none_isSome] at hany
      simp [heq] at hany
    by_cases hv_s : v ∈ S
    · -- Case: v ∈ S → v ∈ J (path variable). Use
      --   `encoder_new_dead_vars_equal_path`: Spath = Sdead \ Sβ, so
      --   v ∈ J = Spath and v ∉ Sβ (since v ∈ S) ⇒ v ∈ Sdead.
      have hv_j : v ∈ J := hv_not_s' hv_s
      have hv_not_β_set : v ∉ (β.map Prod.fst).toFinset := by
        rw [List.mem_toFinset, List.mem_map]
        rintro ⟨⟨w', bw⟩, hmem, rfl⟩
        exact absurd hv_s
          (mkAssignmentList_fst_notMem_live S bits n w' bw (hβ_def ▸ hmem))
      have h_spath_eq :
          ((encodeRestrictionFromFormula d f.val β).1.map Prod.fst).toFinset \
              (β.map Prod.fst).toFinset =
            ((path.take d).map Prod.fst).toFinset :=
        encoder_new_dead_vars_equal_path
          fDNF f.property.2.2.2 β hβ_nodup_fst d path hpath_eq
      have hv_j' : v ∈ ((path.take d).map Prod.fst).toFinset := by
        rw [h_j_def, hpath_d_def] at hv_j; exact hv_j
      have hv_in_sdead :
          v ∈ ((encodeRestrictionFromFormula d f.val β).1.map Prod.fst).toFinset := by
        have := h_spath_eq ▸ hv_j'
        exact (Finset.mem_sdiff.mp this).1
      have hv_in_dead_fst :
          v ∈ (encodeRestrictionFromFormula d f.val β).1.map Prod.fst :=
        List.mem_toFinset.mp hv_in_sdead
      rw [List.mem_map] at hv_in_dead_fst
      obtain ⟨⟨v', b⟩, hvb_mem, hv'_eq⟩ := hv_in_dead_fst
      have hv'_eq' : v' = v := hv'_eq
      have hv_in_dead : ∃ b, (v, b) ∈ dead_vars :=
        ⟨b, by rw [hdead_def, h_encoder_def]; exact hv'_eq' ▸ hvb_mem⟩
      obtain ⟨b, hb_dead⟩ := hv_in_dead
      refine ⟨b, ?_⟩
      exact hb_dead
    · -- Case: v ∉ S → v is assigned by β, whose pairs are
      -- preserved in the encoder's dead-vars output.
      have hne : mkAssignment S bits v ≠ none := by
        intro h
        exact hv_s (mkAssignment_none_imp_mem S bits n
          h_s hbits_len v hv_lt h)
      simp only [mkAssignment, if_neg hv_s] at hne
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
      refine ⟨b, ?_⟩
      have hv_in_β : (v, b) ∈ β := by
        rw [hβ_def]
        exact List.mem_filterMap.mpr ⟨v,
          List.mem_range.mpr hv_lt, by
            simp only [if_neg hv_s, hb]⟩
      rw [hdead_def, ← h_encoder_raw]
      exact encoder_β_subset_dead_acc d f.val β v b hv_in_β (by
        rw [← hdt_def, hpath_eq]
        simp)
  have h_b_fn_none_of_s' : ∀ v, v ∈ S' → B_fn v = none := by
    intro v hv_s'
    have hv_s : v ∈ S := by
      rw [h_s'_def] at hv_s'; exact (Finset.mem_sdiff.mp hv_s').1
    have hv_not_j : v ∉ J := by
      rw [h_s'_def] at hv_s'; exact (Finset.mem_sdiff.mp hv_s').2
    suffices h : ∀ bw, (v, bw) ∉ dead_vars by
      rw [h_b_fn_def]
      by_contra hne
      rw [← Ne, ← Option.isSome_iff_ne_none,
        ← list_any_eq_cr_none_isSome] at hne
      rw [List.any_eq_true] at hne
      obtain ⟨⟨w', bw⟩, hmem, hweq⟩ := hne
      rw [beq_iff_eq] at hweq; subst hweq
      exact h bw hmem
    intro bw hmem_b
    have hv_notβ : (β.any fun (z, _) => z == v) = false := by
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨⟨w', b'⟩, hmem, hweq⟩ := hany
      rw [beq_iff_eq] at hweq
      exact absurd hv_s (hweq ▸
        mkAssignmentList_fst_notMem_live S bits n w' b' (hβ_def ▸ hmem))
    have hv_in_dead_fst : v ∈ dead_vars.map Prod.fst :=
      List.mem_map.mpr ⟨(v, bw), hmem_b, rfl⟩
    have hv_in_encoder_dead :
        v ∈ (encodeRestrictionFromFormula d f.val β).1.map Prod.fst := by
      rw [h_encoder_raw, ← hdead_def]
      exact hv_in_dead_fst
    have hv_path :=
      encoder_dead_vars_subset_path
        fDNF f.property.2.2.2 β hβ_nodup_fst d path hpath_eq
        v hv_notβ hv_in_encoder_dead
    exact hv_not_j (List.mem_toFinset.mpr (hpath_d_def ▸ hv_path))
  have h_b_fn_none_iff : ∀ v, v < n → (B_fn v = none ↔ v ∈ S') := by
    intro v hv_lt
    exact ⟨fun h => by_contra fun hne => h_b_fn_ne_none v hv_lt hne h,
           h_b_fn_none_of_s' v⟩
  -- (3b) `mkAssignment S' bits' = B_fn`.
  have hmk_eq_b : mkAssignment S' bits' = B_fn := by
    funext v
    by_cases hv_lt : v < n
    · exact mkAssignment_extractDeadBits_eq B_fn S' n
        (Finset.Subset.trans Finset.sdiff_subset h_s) h_b_fn_none_iff v hv_lt
    · push Not at hv_lt
      have hv_not_s' : v ∉ S' := by
        intro h; exact absurd (Finset.mem_range.mp
          (Finset.sdiff_subset.trans h_s h)) (by omega)
      have h_b_fn_none : B_fn v = none := by
        suffices h : ∀ bw, (v, bw) ∉ dead_vars by
          rw [h_b_fn_def]
          by_contra hne
          rw [← Ne, ← Option.isSome_iff_ne_none,
            ← list_any_eq_cr_none_isSome] at hne
          rw [List.any_eq_true] at hne
          obtain ⟨⟨w', bw⟩, hmem, hweq⟩ := hne
          rw [beq_iff_eq] at hweq; subst hweq
          exact h bw hmem
        intro bw hmem_b
        have hv_notβ : (β.any fun (z, _) => z == v) = false := by
          rw [Bool.eq_false_iff]
          intro hany
          rw [List.any_eq_true] at hany
          obtain ⟨⟨z, bz⟩, hmem, hzeq⟩ := hany
          rw [beq_iff_eq] at hzeq
          rw [hβ_def] at hmem
          unfold mkAssignmentList at hmem
          rw [List.mem_filterMap] at hmem
          obtain ⟨i, hi_range, hfm⟩ := hmem
          rw [List.mem_range] at hi_range
          split_ifs at hfm with hi_s
          cases hg : bits[((Finset.range i \ S).card)]? with
          | none => simp [hg] at hfm
          | some b =>
            have hfm' : some (i, b) = some (z, bz) := by
              simpa [hg] using hfm
            have hi_eq : i = z := (Prod.mk.inj (Option.some.inj hfm')).1
            omega
        have hv_in_dead_fst : v ∈ dead_vars.map Prod.fst :=
          List.mem_map.mpr ⟨(v, bw), hmem_b, rfl⟩
        have hv_in_encoder_dead :
            v ∈ (encodeRestrictionFromFormula d f.val β).1.map Prod.fst := by
          rw [h_encoder_raw, ← hdead_def]
          exact hv_in_dead_fst
        have hv_path :=
          encoder_dead_vars_subset_path
            fDNF f.property.2.2.2 β hβ_nodup_fst d path hpath_eq
            v hv_notβ hv_in_encoder_dead
        have hv_j := List.mem_toFinset.mpr (hpath_d_def ▸ hv_path)
        exact absurd (Finset.mem_range.mp (h_s (h_j_sub_s hv_j)))
          (by omega)
      rw [h_b_fn_none]
      simp only [mkAssignment, if_neg hv_not_s']
      have hrank_ge : bits'.length ≤ (Finset.range v \ S').card := by
        rw [hbits'_def,
          extractDeadBits_length B_fn S' n
            (Finset.sdiff_subset.trans h_s) h_b_fn_ne_none]
        have h_s'_sub : S' ⊆ Finset.range n := Finset.sdiff_subset.trans h_s
        have h_s'_sub_v : S' ⊆ Finset.range v :=
          h_s'_sub.trans (Finset.range_mono (by omega))
        have := Finset.card_sdiff_add_card_inter (Finset.range n) S'
        rw [Finset.inter_eq_right.mpr h_s'_sub, Finset.card_range] at this
        have := Finset.card_sdiff_add_card_inter (Finset.range v) S'
        rw [Finset.inter_eq_right.mpr h_s'_sub_v, Finset.card_range] at this
        omega
      exact List.getElem?_eq_none hrank_ge
  -- (3c) bits' length and decode roundtrip (alignment-free).
  have hbits'_len : bits'.length = n - (s - d) := by
    rw [hbits'_def,
      extractDeadBits_length B_fn S' n
        (Finset.sdiff_subset.trans h_s) h_b_fn_ne_none,
      h_s'_card]
  have h_decoder_bits' :
      decodeBits (encodeBits bits') (n - (s - d)) = bits' := by
    rw [← hbits'_len]; exact decodeBits_encodeBits bits'
  -- (3d) Advisory index decomposition (alignment-free arithmetic).
  have hdbi_lt : dir_boundary_idx < 2 ^ (2 * d) := by
    rw [hdbi_def]
    calc encodeBits (directions ++ ceb)
        < 2 ^ (directions ++ ceb).length := encodeBits_lt
      _ = 2 ^ (2 * d) := by rw [hdir_ceb_len]
  have hadv_div :
      (encodeBaseW positions w * 2 ^ (2 * d) +
        dir_boundary_idx) / 2 ^ (2 * d) =
      encodeBaseW positions w := by
    have h2d_pos : (0 : Nat) < 2 ^ (2 * d) :=
      Nat.pos_of_ne_zero (by positivity)
    rw [Nat.add_comm, Nat.mul_comm,
        Nat.add_mul_div_left _ _ h2d_pos,
        Nat.div_eq_of_lt hdbi_lt, Nat.zero_add]
  have hadv_mod :
      (encodeBaseW positions w * 2 ^ (2 * d) +
        dir_boundary_idx) % 2 ^ (2 * d) =
      dir_boundary_idx := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hdbi_lt]
  -- (3e) Position roundtrip.  Reduces to the bound `a < w` via
  --      `decodeBaseW_encodeBaseW` + `hpos_len`, dispatched to the
  --      structural lemma `encoder_position_lt_w`.
  have h_decoder_pos :
      decodeBaseW (encodeBaseW positions w) w d = positions := by
    rw [← hpos_len]
    apply decodeBaseW_encodeBaseW hw
    intro a ha
    rw [hpos_def, hchunks_def, h_encoder_def] at ha
    exact encoder_position_lt_w d n w fDNF β hwidth a ha
  -- (3f) Variable recovery via the proven base encoder-decoder roundtrip.
  --
  --      First reconstruct `encoder.2` from the flattened position, direction,
  --      and chunk-boundary advice. Since `encoder.1 = β ++ rest` and
  --      `mkAssignment S' bits' = restrictionAsFunction encoder.1`, the list
  --      assignment reconstructed by the decoder is functionally equal to
  --      `encoder.1`. Decoder invariance under equal induced restrictions then reduces recovery to the
  --      structural decoder facts, which identify the recovered variables
  --      exactly with `J`.
  have h_j_recovery :
      ((beameDecoder f.val
        (mkAssignmentList S' bits' n)
        (splitByEndBits (positions.zip directions) ceb)).map
          Prod.fst).toFinset =
        J := by
    -- Step A: collapse `splitByEndBits (positions.zip directions) ceb`
    -- to `chunks = encoder.2` using two algebraic facts:
    --   * `(L.map fst).zip (L.map snd) = L` (inductive on L)
    --   * `splitByEndBits (chunks.flatMap id) (ceb chunks) = chunks`
    have hzip : positions.zip directions = chunks.flatMap id := by
      rw [hpos_def, hdir_def]
      generalize chunks.flatMap id = L
      induction L with
      | nil => simp
      | cons hd tl ih => simp [ih]
    have hsplit_eq :
        splitByEndBits (positions.zip directions) ceb = chunks := by
      rw [hzip, hceb_def]
      exact splitByEndBits_chunk_end_bits chunks hchunks_ne
    rw [hsplit_eq]
    -- Step B: name the suffix in the already-proved factorization
    -- `encoder.1 = β ++ rest`.
    set rest := (beameEncoderAux
      (path.take d).length (path.take d) (dnfClauses f.val) β []).1 with hrest_def
    -- Step C: restrictionAsFunction (mkAssignmentList S' bits' n) = restrictionAsFunction encoder.1.
    have h_mk_encoder_dead_eq :
        restrictionAsFunction
          (mkAssignmentList S' bits' n) =
        restrictionAsFunction encoder.1 := by
      funext v
      by_cases hv_lt : v < n
      · rw [cr_none_mkAssignmentList_eq S' bits' n v hv_lt]
        rw [show mkAssignment S' bits' v = B_fn v from
          congrFun hmk_eq_b v]
      · push Not at hv_lt
        have h_lhs : restrictionAsFunction
            (mkAssignmentList S' bits' n) v = none := by
          simp only [restrictionAsFunction]
          have hfn : (mkAssignmentList S' bits' n).find?
              (fun p => p.1 == v) = none := by
            rw [List.find?_eq_none]
            intro ⟨z, bz⟩ hmem
            simp only [beq_iff_eq]
            intro hzv; subst hzv
            unfold mkAssignmentList at hmem
            rw [List.mem_filterMap] at hmem
            obtain ⟨i, hi_range, hfm⟩ := hmem
            rw [List.mem_range] at hi_range
            split_ifs at hfm with hi_s
            cases hg : bits'[((Finset.range i \ S').card)]? with
            | none =>
              simp [hg] at hfm
            | some b =>
              have hfm' : some (i, b) = some (z, bz) := by
                simpa [hg] using hfm
              have hi_eq : i = z := (Prod.mk.inj (Option.some.inj hfm')).1
              omega
          rw [hfn]
        have h_rhs : restrictionAsFunction encoder.1 v = none := by
          simp only [restrictionAsFunction]
          have hfn : encoder.1.find? (fun p => p.1 == v) = none := by
            rw [h_encoder_dead_eq, List.find?_append]
            have hβ_none : β.find? (fun p => p.1 == v) = none := by
              rw [List.find?_eq_none]
              intro ⟨z, bz⟩ hmem
              simp only [beq_iff_eq]
              intro hzv; subst hzv
              rw [hβ_def] at hmem
              unfold mkAssignmentList at hmem
              rw [List.mem_filterMap] at hmem
              obtain ⟨i, hi_range, hfm⟩ := hmem
              rw [List.mem_range] at hi_range
              split_ifs at hfm with hi_s
              cases hg : bits[((Finset.range i \ S).card)]? with
              | none =>
                simp [hg] at hfm
              | some b =>
                have hfm' : some (i, b) = some (z, bz) := by
                  simpa [hg] using hfm
                have hi_eq : i = z := (Prod.mk.inj (Option.some.inj hfm')).1
                omega
            have hrest_none : rest.find? (fun p => p.1 == v) = none := by
              rw [List.find?_eq_none]
              intro ⟨z, bz⟩ hmem
              simp only [beq_iff_eq]
              intro hzv
              have h_z_mem_encoder : z ∈ encoder.1.map Prod.fst := by
                rw [h_encoder_dead_eq, List.map_append, List.mem_append]
                right
                exact List.mem_map_of_mem (f := Prod.fst) hmem
              have hz_β_false : (β.any fun (w', _) => w' == z) = false := by
                rw [Bool.eq_false_iff]
                intro hany
                rw [List.any_eq_true] at hany
                obtain ⟨⟨w', bw'⟩, hwβ, hweq⟩ := hany
                simp only [beq_iff_eq] at hweq
                have h_w_in_β : (β.any fun (w'', _) => w'' == z) = true :=
                  List.any_eq_true.mpr ⟨(w', bw'), hwβ, by simp [hweq]⟩
                have h_in_empty : (z, bz) ∈ ([] : List (Nat × Bool)) :=
                  encoder_aux_no_new_dead_for_assigned
                    (path.take d).length (path.take d) f.val β [] z bz
                    h_w_in_β hmem
                exact List.not_mem_nil h_in_empty
              have hz_path :=
                encoder_dead_vars_subset_path fDNF f.property.2.2.2 β hβ_nodup_fst d
                  path hpath_eq z hz_β_false h_z_mem_encoder
              have hz_j : z ∈ J :=
                List.mem_toFinset.mpr (hpath_d_def ▸ hz_path)
              have hz_s : z ∈ S := h_j_sub_s hz_j
              have hz_lt : z < n := Finset.mem_range.mp (h_s hz_s)
              omega
            rw [hβ_none, hrest_none]; rfl
          rw [hfn]
        rw [h_lhs, h_rhs]
    -- Step D: replace the decoder input using equality of induced restrictions.
    have h_decoder_eq : beameDecoder f.val
        (mkAssignmentList S' bits' n) chunks =
        beameDecoder f.val encoder.1 chunks :=
      beameDecoder_eq_of_cr_none_eq f.val
        (mkAssignmentList S' bits' n) encoder.1 chunks h_mk_encoder_dead_eq
    rw [h_decoder_eq, hchunks_def]
    -- Step E: ⊆ and ⊇.
    apply Finset.Subset.antisymm
    · -- ⊆: every recovered var lies in J.
      intro w' hw'
      rw [List.mem_toFinset, List.mem_map] at hw'
      obtain ⟨⟨w'', bw⟩, hmem, rfl⟩ := hw'
      have hmem_decoded : w'' ∈ (beameDecoder f.val
          encoder.1 encoder.2).map Prod.fst :=
        List.mem_map.mpr ⟨(w'', bw), hmem, rfl⟩
      have hw_β_false : (β.any fun (z, _) => z == w'') = false := by
        rw [h_encoder_def] at hmem_decoded
        exact encoder_decoded_disjoint_β d f.val β f.property.2.1
          f.property.2.2.2 f.property.2.2.1 hβ_nodup_fst w'' hmem_decoded
      have h_encoder_factor : encodeRestrictionFromFormula d f.val β =
          beameEncoderAux
            (path.take d).length (path.take d) (dnfClauses f.val) β β := by
        simp only [encodeRestrictionFromFormula]
        simp only [← hdt_def, hpath_eq]
      have hw_recovered : ((beameDecoder f.val
          (beameEncoderAux (path.take d).length (path.take d)
            (dnfClauses f.val) β β).1
          (beameEncoderAux (path.take d).length (path.take d)
            (dnfClauses f.val) β β).2).map Prod.fst).contains w'' = true := by
        have hmem_decoded' := hmem_decoded
        rw [← h_encoder_raw] at hmem_decoded'
        rw [h_encoder_factor] at hmem_decoded'
        exact List.elem_eq_true_of_mem (a := w'') hmem_decoded'
      have hw_path : w'' ∈ (path.take d).map Prod.fst :=
        encoder_decoded_subset_path d f.val β f.property.2.1
          f.property.2.2.2 f.property.2.2.1 hβ_nodup_fst path hpath_eq w''
          hw_β_false hw_recovered
      rw [h_j_def, hpath_d_def, List.mem_toFinset]
      exact hw_path
    · -- ⊇: every J var is recovered.
      intro v' hv'_j
      rw [h_j_def, hpath_d_def, List.mem_toFinset, List.mem_map] at hv'_j
      obtain ⟨⟨v'', bv⟩, hmem_take, rfl⟩ := hv'_j
      have hv_β_false : (β.any fun (z, _) => z == v'') = false :=
        encoder_β_disj_path d f.val β f.property.2.1 path hpath_eq v'' bv
          hmem_take
      have h_spath_eq :
          ((encodeRestrictionFromFormula d f.val β).1.map Prod.fst).toFinset \
              (β.map Prod.fst).toFinset =
            ((path.take d).map Prod.fst).toFinset :=
        encoder_new_dead_vars_equal_path fDNF f.property.2.2.2 β hβ_nodup_fst d path
          hpath_eq
      have hv'_in_diff : v'' ∈
          ((encodeRestrictionFromFormula d f.val β).1.map Prod.fst).toFinset \
            (β.map Prod.fst).toFinset := by
        rw [h_spath_eq]
        exact List.mem_toFinset.mpr (List.mem_map.mpr
          ⟨(v'', bv), hmem_take, rfl⟩)
      have hv'_in_enc : v'' ∈
          (encodeRestrictionFromFormula d f.val β).1.map Prod.fst :=
        List.mem_toFinset.mp (Finset.mem_sdiff.mp hv'_in_diff).1
      have hv'_recovered : ((beameDecoder f.val
          (encodeRestrictionFromFormula d f.val β).1
          (encodeRestrictionFromFormula d f.val β).2).map Prod.fst).contains v''
            = true :=
        encoder_dead_vars_subset_recovered d f.val β f.property.2.1
          f.property.2.2.2 f.property.2.2.1
          (fun p hp w' b' hw_take => by
            have hp_eq : p = path := by
              rw [hp] at hpath_eq; exact Option.some.inj hpath_eq
            rw [hp_eq] at hw_take
            exact encoder_β_disj_path d f.val β f.property.2.1 path hpath_eq
              w' b' hw_take)
          v'' hv_β_false hv'_in_enc
      rw [List.mem_toFinset]
      exact h_encoder_def ▸ List.mem_of_elem_eq_true hv'_recovered
  -- (3g) Bits recovery from `h_j_recovery` and `hmk_eq_b`.
  have hbits_recovery :
      extractDeadBits (mkAssignment S' bits')
        (S' ∪
          ((beameDecoder f.val
            (mkAssignmentList S' bits' n)
            (splitByEndBits (positions.zip directions) ceb)).map
              Prod.fst).toFinset)
            n = bits := by
    rw [h_j_recovery, h_s'_j_eq_s]
    -- Goal: `extractDeadBits (mkAssignment S' bits') S n = bits`.
    have h_agree :
        extractDeadBits (mkAssignment S' bits') S n =
        extractDeadBits (mkAssignment S bits) S n := by
      rw [hmk_eq_b]
      simp only [extractDeadBits]
      apply List.filterMap_congr
      intro v hv
      rw [List.mem_range] at hv
      by_cases hv_s : v ∈ S
      · simp [hv_s]
      · simp only [if_neg hv_s]
        have hβ_ne : (β.any fun (z, _) => z == v) = true := by
          rw [List.any_eq_true]
          have hne : mkAssignment S bits v ≠ none := by
            intro h; exact hv_s (mkAssignment_none_imp_mem S bits n
              h_s hbits_len v hv h)
          simp only [mkAssignment, if_neg hv_s] at hne
          obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
          exact ⟨(v, b), hβ_def ▸ List.mem_filterMap.mpr ⟨v,
            List.mem_range.mpr hv, by simp only [if_neg hv_s, hb]⟩,
            by simp⟩
        have hβ_cr_ne : restrictionAsFunction β v ≠ none := by
          rw [← Option.isSome_iff_ne_none, ← list_any_eq_cr_none_isSome]
          exact hβ_ne
        rw [h_b_fn_def, hdead_def, h_encoder_dead_eq]
        simp only [restrictionAsFunction, List.find?_append]
        cases hfind : β.find? (fun p => p.1 == v) with
        | none =>
          exfalso
          apply hβ_cr_ne
          simp [restrictionAsFunction, hfind]
        | some p =>
          calc
            some p.2 = restrictionAsFunction β v := by
              simp [restrictionAsFunction, hfind]
            _ = restrictionAsFunction (mkAssignmentList S bits n) v := by
              rw [hβ_def]
            _ = mkAssignment S bits v :=
              cr_none_mkAssignmentList_eq S bits n v hv
    rw [h_agree]
    exact extractDeadBits_mkAssignment_eq S bits n h_s hbits_len
  -- (3h) Final assembly: decoder output = (S, bits).
  simp only [Prod.mk.injEq]
  -- Fold the match expression to path_d in the goal.
  simp only [hmatch_eq] at *
  refine ⟨?_, ?_⟩
  · rw [hadv_div, hadv_mod,
      show dir_boundary_idx = encodeBits (directions ++ ceb) from rfl,
      h_decoder_dir_ceb, List.take_left' hdir_len, List.drop_left' hdir_len,
      h_decoder_pos, h_decoder_bits', h_j_recovery, h_s'_j_eq_s]
  · rw [hadv_div, hadv_mod,
      show dir_boundary_idx = encodeBits (directions ++ ceb) from rfl,
      h_decoder_dir_ceb, List.take_left' hdir_len, List.drop_left' hdir_len,
      h_decoder_pos, h_decoder_bits']
    exact hbits_recovery

#print axioms beame_encoder_decoder_injection_roundtrip

end Circuits.CnfDnf.Restrictions
