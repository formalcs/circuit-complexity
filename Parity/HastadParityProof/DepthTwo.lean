/-
  Proper bottom-width and depth-two collapse lemmas.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.SimplifyConstants

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-- Build the De Morgan dual DNF of a proper CNF: a proper DNF of equal
    width that computes the negation of the CNF. -/
lemma exists_properDNF_dual_of_properCNF {n : Nat} (f : UnboundedFanInProperCNF n) :
    ∃ (fd : UnboundedFanInProperDNF n),
      dnfWidth fd.val = cnfWidth f.val ∧
      ∀ xs, xs.length = n →
        ufiFormulaEval fd.val xs = not (ufiFormulaEval f.val xs) := by
  obtain ⟨cnf, hlt, hcnf, hne, hnodup⟩ := f
  refine ⟨⟨cnfDual cnf, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [cnfDual_ufiLargestInput]; exact hlt
  · exact isDNF_cnfDual cnf hcnf
  · intro c hc
    rw [cnfDual_clauses cnf hcnf, List.mem_map] at hc
    obtain ⟨cc, hcc, rfl⟩ := hc
    have hccne : cc ≠ [] := hne cc hcc
    simpa using hccne
  · intro c hc
    rw [cnfDual_clauses cnf hcnf, List.mem_map] at hc
    obtain ⟨cc, hcc, rfl⟩ := hc
    have heq : ((cc.map (fun p => (p.1, !p.2))).map Prod.fst) = cc.map Prod.fst := by
      simp [List.map_map]
    rw [heq]
    exact hnodup cc hcc
  · exact cnfDual_width cnf hcnf
  · intro xs hxs
    apply cnfDual_eval cnf xs hcnf
    intro i hi
    have hle : i ≤ ufiLargestInput cnf := by
      exact mem_le_foldr_max hi
    omega

/-- Companion to `exists_narrow_dnf_from_good_restriction_dnf`: from a good
    restriction of a DNF `f`, produce a narrow DNF on the live
    coordinates computing the **negation** of `f`.  This is obtained by
    negating the canonical decision tree at the leaf level, which keeps
    depth (hence width) and the branching-variable set unchanged. -/
lemma exists_narrow_negated_dnf_from_good_restriction_dnf
    {n : Nat} (decisionTreeDepthBound : Nat) {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
    (hρ : ¬ isBadRestriction decisionTreeDepthBound n σ f ρ)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_dt_lt : decisionTreeDepthBound < live.length) :
    ∃ (g : UnboundedFanInDNF live.length),
      dnfWidth g.val ≤ decisionTreeDepthBound ∧
      ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        not (ufiFormulaEval f.val
            (assembleInput n live liveBits deadBits)) =
        ufiFormulaEval g.val liveBits := by
  set tree :=
    canonicalDecisionTree f.val
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) with htree
  have h_depth_le : DecisionTrees.decisionTreeDepth tree ≤ decisionTreeDepthBound := by
    unfold isBadRestriction at hρ
    rw [properDNFCanonicalDecisionTree_eq_canonicalDecisionTree, ← htree] at hρ
    have : ¬ (decisionTreeDepthBound < DecisionTrees.decisionTreeDepth tree) := by
      intro hlt
      apply hρ
      simpa [decide_eq_true_eq] using hlt
    omega
  set rawFormula₀ : UnboundedFanInFormula :=
    DecisionTrees.decisionTreeToDNF (dtNegate tree) with hg₀_raw
  have h_width_g₀ : dnfWidth rawFormula₀ ≤ decisionTreeDepthBound := by
    have h₁ := decisionTreeToDNF_dnfWidth_le_decisionTreeDepth (dtNegate tree)
    rw [dtNegate_depth] at h₁
    change dnfWidth (DecisionTrees.decisionTreeToDNF (dtNegate tree)) ≤ decisionTreeDepthBound
    omega
  have h_branch_in_live :=
    mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree f ρ live h_live_eq
  have h_g₀_vars_subset :
      ∀ i ∈ ufiCollectInputIndices rawFormula₀, i ∈ live := by
    intro i hi
    have h_dt : i ∈ DecisionTrees.dtCollectInputIndices (dtNegate tree) :=
      DecisionTrees.dnf_inputs_sub_dt_inputs (dtNegate tree) i hi
    rw [dtNegate_dtCollectInputIndices] at h_dt
    exact h_branch_in_live i h_dt
  have h_g₀_inputs_lt : ufiLargestInput rawFormula₀ < n := by
    unfold ufiLargestInput
    apply Nat.lt_of_le_of_lt
      (adder_foldr_max_le_of_all_le
        (l := ufiCollectInputIndices rawFormula₀) (k := n - 1) ?_)
    · omega
    · intro i hi
      have hi_live := h_g₀_vars_subset i hi
      have hi_lt : i < n := h_live_lt i hi_live
      omega
  have h_g₀_is_dnf : isDNF rawFormula₀ = true :=
    isDNF_decisionTreeToDNF (dtNegate tree)
  let g₀ : UnboundedFanInDNF n := ⟨rawFormula₀, h_g₀_inputs_lt, h_g₀_is_dnf⟩
  have h_g₀_vars_in_live :
      ∀ i ∈ ufiCollectInputIndices g₀.val, i ∈ live := h_g₀_vars_subset
  have h_live_pos : 0 < live.length := by omega
  obtain ⟨g, hg_width, hg_size, hg_eval₀⟩ :=
    exists_dnf_rekey_to_live live h_live_lt h_live_nodup h_live_pos g₀ decisionTreeDepthBound
      h_width_g₀ h_g₀_vars_in_live deadBits
  have h_size_g₀ :
      ufiFormulaCircuitSize rawFormula₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
    rw [hg₀_raw]
    have h₁ := decisionTreeToDNF_ufiFormulaCircuitSize_le (dtNegate tree)
    have h₂ := decisionTreeNodeCount_succ_le_pow (dtNegate tree)
    have hpow : (2 : Nat) ^ (DecisionTrees.decisionTreeDepth (dtNegate tree) + 1)
        ≤ 2 ^ (decisionTreeDepthBound + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [dtNegate_depth]; omega)
    calc ufiFormulaCircuitSize (DecisionTrees.decisionTreeToDNF (dtNegate tree))
        ≤ 1 + DecisionTrees.decisionTreeNodeCount (dtNegate tree)
            * (DecisionTrees.decisionTreeDepth (dtNegate tree) + 1) := h₁
      _ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
          apply Nat.add_le_add_left
          have hd : DecisionTrees.decisionTreeDepth (dtNegate tree) ≤ decisionTreeDepthBound := by
            rw [dtNegate_depth]; exact h_depth_le
          apply Nat.mul_le_mul <;> omega
  have h_size_g : ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) :=
    le_trans hg_size h_size_g₀
  refine ⟨g, hg_width, h_size_g, ?_⟩
  intro liveBits h_lb_len
  set xs := assembleInput n live liveBits deadBits with hxs
  have hxs_len : xs.length = n :=
    length_assembleInput n live liveBits deadBits
  have hxs_consistent :
      ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
        xs[i]? = some b := h_assemble liveBits h_lb_len
  have h_dt_eq :
      DecisionTrees.evalDecisionTree tree xs =
        ufiFormulaEval f.val xs :=
    canonicalDecisionTree_eval_eq f ρ xs hxs_len hxs_consistent
  have h_range_tree : ∀ i ∈ DecisionTrees.dtCollectInputIndices tree,
      i < xs.length := by
    intro i hi
    have hi_live := h_branch_in_live i hi
    have hi_lt : i < n := h_live_lt i hi_live
    rw [hxs_len]; exact hi_lt
  have h_range_ntree : ∀ i ∈ DecisionTrees.dtCollectInputIndices (dtNegate tree),
      i < xs.length := by
    intro i hi
    rw [dtNegate_dtCollectInputIndices] at hi
    exact h_range_tree i hi
  have h_ntree_eq :
      DecisionTrees.evalDecisionTree (dtNegate tree) xs =
        not (DecisionTrees.evalDecisionTree tree xs) :=
    dtNegate_eval tree xs h_range_tree
  have h_dnf_eq :
      ufiFormulaEval rawFormula₀ xs =
        DecisionTrees.evalDecisionTree (dtNegate tree) xs := by
    have := DecisionTrees.decisionTreeToDNF_eval_equiv (dtNegate tree) xs h_range_ntree
    exact this.symm
  have h_g_eq :
      ufiFormulaEval g₀.val xs = ufiFormulaEval g.val liveBits :=
    hg_eval₀ liveBits h_lb_len
  change not (ufiFormulaEval f.val xs) = ufiFormulaEval g.val liveBits
  rw [← h_g_eq]
  change not (ufiFormulaEval f.val xs) = ufiFormulaEval rawFormula₀ xs
  rw [h_dnf_eq, h_ntree_eq, h_dt_eq]

/-- CNF analogue of `exists_narrow_negated_dnf_from_good_restriction_dnf`: from a
    good restriction of a DNF `f`, produce a narrow **CNF** on the live
    coordinates computing the **negation** of `f`.  Obtained by negating
    the canonical decision tree (preserving depth, hence width, and the
    branching-variable set) and reading the negated tree as a CNF via
    `decisionTreeToCNF`. -/
lemma exists_narrow_negated_cnf_from_good_restriction_dnf
    {n : Nat} (decisionTreeDepthBound : Nat) {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
    (hρ : ¬ isBadRestriction decisionTreeDepthBound n σ f ρ)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_dt_lt : decisionTreeDepthBound < live.length) :
    ∃ (g : UnboundedFanInCNF live.length),
      cnfWidth g.val ≤ decisionTreeDepthBound ∧
      ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        not (ufiFormulaEval f.val
            (assembleInput n live liveBits deadBits)) =
        ufiFormulaEval g.val liveBits := by
  set tree :=
    canonicalDecisionTree f.val
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) with htree
  have h_depth_le : DecisionTrees.decisionTreeDepth tree ≤ decisionTreeDepthBound := by
    unfold isBadRestriction at hρ
    rw [properDNFCanonicalDecisionTree_eq_canonicalDecisionTree, ← htree] at hρ
    have : ¬ (decisionTreeDepthBound < DecisionTrees.decisionTreeDepth tree) := by
      intro hlt
      apply hρ
      simpa [decide_eq_true_eq] using hlt
    omega
  set rawFormula₀ : UnboundedFanInFormula :=
    decisionTreeToCNF (dtNegate tree) with hg₀_raw
  have h_width_g₀ : cnfWidth rawFormula₀ ≤ decisionTreeDepthBound := by
    have h₁ := decisionTreeToCNF_cnfWidth_le_decisionTreeDepth (dtNegate tree)
    rw [dtNegate_depth] at h₁
    change cnfWidth (decisionTreeToCNF (dtNegate tree)) ≤ decisionTreeDepthBound
    omega
  have h_branch_in_live :=
    mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree f ρ live h_live_eq
  have h_g₀_vars_subset :
      ∀ i ∈ ufiCollectInputIndices rawFormula₀, i ∈ live := by
    intro i hi
    have h_dt : i ∈ DecisionTrees.dtCollectInputIndices (dtNegate tree) :=
      mem_dtCollectInputIndices_of_mem_collect_decisionTreeToCNF (dtNegate tree) i hi
    rw [dtNegate_dtCollectInputIndices] at h_dt
    exact h_branch_in_live i h_dt
  have h_g₀_inputs_lt : ufiLargestInput rawFormula₀ < n := by
    unfold ufiLargestInput
    apply Nat.lt_of_le_of_lt
      (adder_foldr_max_le_of_all_le
        (l := ufiCollectInputIndices rawFormula₀) (k := n - 1) ?_)
    · omega
    · intro i hi
      have hi_live := h_g₀_vars_subset i hi
      have hi_lt : i < n := h_live_lt i hi_live
      omega
  have h_g₀_is_cnf : isCNF rawFormula₀ = true :=
    isCNF_decisionTreeToCNF (dtNegate tree)
  let g₀ : UnboundedFanInCNF n := ⟨rawFormula₀, h_g₀_inputs_lt, h_g₀_is_cnf⟩
  have h_g₀_vars_in_live :
      ∀ i ∈ ufiCollectInputIndices g₀.val, i ∈ live := h_g₀_vars_subset
  have h_live_pos : 0 < live.length := by omega
  obtain ⟨g, hg_width, hg_size, hg_eval₀⟩ :=
    exists_cnf_rekey_to_live live h_live_lt h_live_nodup h_live_pos g₀ decisionTreeDepthBound
      h_width_g₀ h_g₀_vars_in_live deadBits
  have h_size_g₀ :
      ufiFormulaCircuitSize rawFormula₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
    rw [hg₀_raw]
    have h₁ := decisionTreeToCNF_ufiFormulaCircuitSize_le (dtNegate tree)
    have h₂ := decisionTreeNodeCount_succ_le_pow (dtNegate tree)
    have hpow : (2 : Nat) ^ (DecisionTrees.decisionTreeDepth (dtNegate tree) + 1)
        ≤ 2 ^ (decisionTreeDepthBound + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [dtNegate_depth]; omega)
    calc ufiFormulaCircuitSize (decisionTreeToCNF (dtNegate tree))
        ≤ 1 + DecisionTrees.decisionTreeNodeCount (dtNegate tree)
            * (DecisionTrees.decisionTreeDepth (dtNegate tree) + 1) := h₁
      _ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
          apply Nat.add_le_add_left
          have hd : DecisionTrees.decisionTreeDepth (dtNegate tree) ≤ decisionTreeDepthBound := by
            rw [dtNegate_depth]; exact h_depth_le
          apply Nat.mul_le_mul <;> omega
  have h_size_g : ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) :=
    le_trans hg_size h_size_g₀
  refine ⟨g, hg_width, h_size_g, ?_⟩
  intro liveBits h_lb_len
  set xs := assembleInput n live liveBits deadBits with hxs
  have hxs_len : xs.length = n :=
    length_assembleInput n live liveBits deadBits
  have hxs_consistent :
      ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
        xs[i]? = some b := h_assemble liveBits h_lb_len
  have h_dt_eq :
      DecisionTrees.evalDecisionTree tree xs =
        ufiFormulaEval f.val xs :=
    canonicalDecisionTree_eval_eq f ρ xs hxs_len hxs_consistent
  have h_range_tree : ∀ i ∈ DecisionTrees.dtCollectInputIndices tree,
      i < xs.length := by
    intro i hi
    have hi_live := h_branch_in_live i hi
    have hi_lt : i < n := h_live_lt i hi_live
    rw [hxs_len]; exact hi_lt
  have h_range_ntree : ∀ i ∈ DecisionTrees.dtCollectInputIndices (dtNegate tree),
      i < xs.length := by
    intro i hi
    rw [dtNegate_dtCollectInputIndices] at hi
    exact h_range_tree i hi
  have h_ntree_eq :
      DecisionTrees.evalDecisionTree (dtNegate tree) xs =
        not (DecisionTrees.evalDecisionTree tree xs) :=
    dtNegate_eval tree xs h_range_tree
  have h_cnf_eq :
      ufiFormulaEval rawFormula₀ xs =
        DecisionTrees.evalDecisionTree (dtNegate tree) xs :=
    (decisionTreeToCNF_eval (dtNegate tree) xs h_range_ntree).symm
  have h_g_eq :
      ufiFormulaEval g₀.val xs = ufiFormulaEval g.val liveBits :=
    hg_eval₀ liveBits h_lb_len
  change not (ufiFormulaEval f.val xs) = ufiFormulaEval g.val liveBits
  rw [← h_g_eq]
  change not (ufiFormulaEval f.val xs) = ufiFormulaEval rawFormula₀ xs
  rw [h_cnf_eq, h_ntree_eq, h_dt_eq]

/-- **Single-CNF switching collapse, AND-rooted depth-2 case.**
    A `UnboundedFanInProperCNF n` on `n ≥ 3` inputs admits a single
    deterministic restriction `(live, deadBits)` such that the
    restricted formula equals a width-`w < live.length` DNF on
    `live.length` live coordinates.

    Strategy: dualize the CNF to a DNF `fd` computing the negation via
    De Morgan (`exists_properDNF_dual_of_properCNF`), of equal width.  Apply the
    switching machinery to `fd` (picking exact `σ := 2/n ≤ 1/5` and
    DT depth bound `decisionTreeDepthBound := 1`, exactly as in `exists_depth_two_dnf_collapse`), then
    convert the canonical decision tree of `fd` into a narrow DNF on the
    live coordinates computing `¬ fd = ¬¬ f = f` via
    `exists_narrow_negated_dnf_from_good_restriction_dnf`.  The width stays
    bounded because the negation is applied at the decision-tree level
    (flipping leaves preserves depth), not at the formula level. -/
lemma exists_depth_two_cnf_collapse
    (w : Nat) {n : Nat}
    (f : UnboundedFanInProperCNF n)
    (hwidth : cnfWidth f.val ≤ w)
    (h_thresh : 20 * (w + 1) < n) :
    ∃ (live : List Nat)
      (_h_live_lt : ∀ v ∈ live, v < n)
      (_h_live_nodup : live.Nodup)
      (_h_live_big : 2 ≤ live.length)
      (deadBits : List Bool)
      (w : Nat) (_hw : w < live.length)
      (g : UnboundedFanInDNF live.length),
      dnfWidth g.val ≤ w ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval f.val
            (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  -- Step 0: dualize to a DNF computing the negation, of equal width.
  obtain ⟨fd, hfd_width, hfd_eval⟩ := exists_properDNF_dual_of_properCNF f
  have hwd : dnfWidth fd.val ≤ w := by rw [hfd_width]; exact hwidth
  -- Step 1: construct exact σ := 2/n ≤ 1/5 with decisionTreeDepthBound := 1.
  have hn_pos_nat : 0 < n := by omega
  have hnq_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos_nat
  set σv : ℚ := 2 / (n : ℚ) with hσv_def
  have hσv_pos : 0 < σv := by rw [hσv_def]; positivity
  have hσv_lt_one : σv < 1 := by
    rw [hσv_def, div_lt_one hnq_pos]
    have h_twenty_lt_n : (20 : Nat) < n := by
      have h20le : 20 ≤ 20 * (w + 1) := by nlinarith
      omega
    exact_mod_cast (by omega : 2 < n)
  have hσv_le_fifth : σv ≤ 1 / 5 := by
    rw [hσv_def]
    rw [div_le_iff₀ hnq_pos]
    have h_twenty_lt_n : (20 : Nat) < n := by
      have h20le : 20 ≤ 20 * (w + 1) := by nlinarith
      omega
    have h10q : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 10 ≤ n)
    nlinarith
  set σ : OpenUnitIntervalQ := ⟨σv, hσv_pos, hσv_lt_one⟩ with hσ_def
  set decisionTreeDepthBound : Nat := 1 with hd_dt_def
  have hσn : σ.val * (n : ℚ) = 2 := by
    change σv * (n : ℚ) = 2
    rw [hσv_def]
    field_simp [ne_of_gt hnq_pos]
  have hs_exact : (Nat.ceil (σ.val * (n : ℚ)) : ℚ) = σ.val * (n : ℚ) := by
    rw [hσn]
    norm_num
  have h_ten_sigma_w : 10 * σ.val * ((w : Nat) : ℚ) = (20 * (w : ℚ)) / (n : ℚ) := by
    change 10 * σv * ((w : Nat) : ℚ) = (20 * (w : ℚ)) / (n : ℚ)
    rw [hσv_def]
    ring
  have h_base_lt_one : (20 * (w : ℚ)) / (n : ℚ) < 1 := by
    rw [div_lt_one hnq_pos]
    have hcast : (20 : ℚ) * ((w : ℚ) + 1) < (n : ℚ) := by
      have hth : (20 * (w + 1) : Nat) < n := h_thresh
      have : ((20 * (w + 1) : Nat) : ℚ) < ((n : Nat) : ℚ) := by exact_mod_cast hth
      push_cast at this ⊢
      linarith
    nlinarith
  have h_bound' : (10 * σ.val * ((w : Nat) : ℚ)) ^ decisionTreeDepthBound < 1 := by
    rw [h_ten_sigma_w, hd_dt_def]
    simpa using h_base_lt_one
  -- Step 2: switching-lemma pigeonhole on the dual DNF at width `w`.
  obtain ⟨ρ, hρ_not_bad⟩ :=
    exists_switching_lemma_pigeonhole_exact w decisionTreeDepthBound fd hwd σ hσv_le_fifth hs_exact h_bound'
  -- Step 3: convert ρ into the (live, deadBits) shape.
  obtain ⟨live, h_live_lt, h_live_nodup, deadBits, h_card, h_live_eq, h_assemble⟩ :=
    exists_assembled_restriction ρ
  -- Step 4: live-count bounds.
  have h_live_card : live.length = Nat.ceil (σ.val * (n : ℚ)) := by
    have h₁ : live.length = ρ.starAssignment.val.val.card := by
      have hcard := congrArg Multiset.card h_live_eq
      simp only [Multiset.coe_card] at hcard
      exact hcard
    rw [h₁, ρ.starAssignment.property]
  have h_live_big : 2 ≤ live.length := by
    rw [h_live_card, hσn]
    norm_num
  have h_dt_lt : decisionTreeDepthBound < live.length := by rw [hd_dt_def]; omega
  -- Step 5: invoke the negated analytic core, then undo the double
  -- negation to recover `f`.
  obtain ⟨g, hg_width, _, hg_eval⟩ :=
    exists_narrow_negated_dnf_from_good_restriction_dnf decisionTreeDepthBound fd ρ hρ_not_bad
      live h_live_lt h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
  refine ⟨live, h_live_lt, h_live_nodup, h_live_big, deadBits,
          decisionTreeDepthBound, h_dt_lt, g, hg_width, ?_⟩
  intro liveBits h_lb_len
  have hfde := hfd_eval (assembleInput n live liveBits deadBits)
    (length_assembleInput n live liveBits deadBits)
  have hge := hg_eval liveBits h_lb_len
  rw [← hge, hfde]
  cases h : ufiFormulaEval f.val
      (assembleInput n live liveBits deadBits) <;> rfl

/- The singleton OR-of-AND-of-`g` wrapper evaluates exactly as `g`.  Used to
   package a single literal (or constant) as a width-1 proper DNF. -/
lemma eval_or_and_singleton (g : UnboundedFanInFormula) (xs : List Bool) :
    ufiFormulaEval
        (UnboundedFanInFormula.orGate [UnboundedFanInFormula.andGate [g]]) xs
      = ufiFormulaEval g xs := by
  simp only [ufiFormulaEval]
  cases ufiFormulaEval g xs <;> rfl

/- Lookup of an assembled input at the first live index `idx` of the live
   list `[idx, other]` returns the head live bit. -/
lemma assemble_lookup_head
    (n idx other : Nat) (liveBits deadBits : List Bool) (hidx : idx < n) :
    (assembleInput n [idx, other] liveBits deadBits)[idx]?
      = some (liveBits.getD 0 false) := by
  rw [assembleInput_get_at n [idx, other] liveBits deadBits idx hidx]
  simp [assembleInputFn, List.findIdx?_cons]

/-- Bottom-gate **fan-in** (clause width) of a single subformula,
    used to express the bottom-fan-in invariant `HasBottomFanInLE`.

    For a proper depth-≤2 CNF/DNF this is exactly `cnfWidth`/`dnfWidth`
    (the maximum clause size); for a leaf (`inputGate`/`constant`/`notGate`)
    or a non-proper AND/OR it is bounded below by `1`.  The `max 1 …`
    floor gives leaf and non-proper branches a uniform positive budget,
    which is the only property the switching chain consumes.

    The crucial difference from `ufiFormulaCircuitSize` is that this is
    the bottom *fan-in* (max clause size), NOT the total circuit size: a
    canonical-decision-tree DNF of depth `t` has up to `2^t` clauses (so
    circuit size `~ t·2^t`), but each clause has width `≤ t`.  Hence the
    fan-in invariant is *maintained* by a switching round whereas the
    circuit-size one is not. -/
def ufiBottomFanIn : UnboundedFanInFormula → Nat
  | .andGate gates => max 1 (cnfWidth (.andGate gates))
  | .orGate gates => max 1 (dnfWidth (.orGate gates))
  | _ => 1

/- **Extraction-side bottom-fan-in bound.**  If `f` satisfies the
   `HasProperBottomWidthLE` invariant at level `lvl`, then every bottom
   subformula extracted by `extractBottomLayer lvl start f` has
   `ufiBottomFanIn ≤ t`. -/
mutual

theorem extractBottomLayer_bottoms_fanIn_le (t : Nat) (ht : 1 ≤ t) :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      HasProperBottomWidthLE f lvl t →
      ∀ g ∈ (extractBottomLayer lvl start f).1, ufiBottomFanIn g ≤ t
  | lvl, start, .inputGate x dd, _ => by
      intro g hg
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; unfold ufiBottomFanIn; exact ht
  | lvl, start, .constant x dd, _ => by
      intro g hg
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; unfold ufiBottomFanIn; exact ht
  | lvl, start, .notGate g₀, _ => by
      intro g hg
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; unfold ufiBottomFanIn; exact ht
  | lvl, start, .andGate gates, hw => by
      intro g hg
      by_cases hle : lvl ≤ 2
      · simp only [extractBottomLayer, hle, if_true, List.mem_singleton] at hg
        subst hg
        unfold HasProperBottomWidthLE at hw
        rw [if_pos hle] at hw
        unfold ufiBottomFanIn
        exact Nat.max_le.mpr ⟨ht, hw⟩
      · have hg' : g ∈ (extractBottomLayerList (lvl - 1) start gates).1 := by
          simpa only [extractBottomLayer, hle, if_false] using hg
        unfold HasProperBottomWidthLE at hw
        rw [if_neg hle] at hw
        exact extractBottomLayerList_bottoms_fanIn_le t ht (lvl - 1) start gates hw g hg'
  | lvl, start, .orGate gates, hw => by
      intro g hg
      by_cases hle : lvl ≤ 2
      · simp only [extractBottomLayer, hle, if_true, List.mem_singleton] at hg
        subst hg
        unfold HasProperBottomWidthLE at hw
        rw [if_pos hle] at hw
        unfold ufiBottomFanIn
        exact Nat.max_le.mpr ⟨ht, hw⟩
      · have hg' : g ∈ (extractBottomLayerList (lvl - 1) start gates).1 := by
          simpa only [extractBottomLayer, hle, if_false] using hg
        unfold HasProperBottomWidthLE at hw
        rw [if_neg hle] at hw
        exact extractBottomLayerList_bottoms_fanIn_le t ht (lvl - 1) start gates hw g hg'

theorem extractBottomLayerList_bottoms_fanIn_le (t : Nat) (ht : 1 ≤ t) :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      (∀ f ∈ gs, HasProperBottomWidthLE f lvl t) →
      ∀ g ∈ (extractBottomLayerList lvl start gs).1, ufiBottomFanIn g ≤ t
  | lvl, start, [], _ => by
      intro g hg
      simp only [extractBottomLayerList, List.not_mem_nil] at hg
  | lvl, start, f :: gs, hw => by
      intro g hg
      have htop : (extractBottomLayerList lvl start (f :: gs)).1
          = (extractBottomLayer lvl start f).1
            ++ (extractBottomLayerList lvl
                  (extractBottomLayer lvl start f).2.2 gs).1 := rfl
      rw [htop, List.mem_append] at hg
      rcases hg with h | h
      · exact extractBottomLayer_bottoms_fanIn_le t ht lvl start f
          (hw f (by simp)) g h
      · exact extractBottomLayerList_bottoms_fanIn_le t ht lvl
          (extractBottomLayer lvl start f).2.2 gs
          (fun f' hf' => hw f' (by simp [hf'])) g h

end

/- Extracted bottoms of an `HasProperBottomsAt` formula are themselves
   `HasProperBottomsAt` at level `2`: at the extraction cut (`lvl ≤ 2`) the bottom
   AND/OR gate keeps its proper-CNF/DNF shape, and `inputGate`/`constant` leaves
   are proper at any level.  Mirrors `extractBottomLayer_bottoms_fanIn_le`. -/
mutual
theorem hasProperBottomsAt_of_mem_extractBottomLayer :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      HasProperBottomsAt f lvl →
      ∀ g ∈ (extractBottomLayer lvl start f).1, HasProperBottomsAt g 2
  | lvl, start, .inputGate x dd, _ => by
      intro g hg
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; simp only [HasProperBottomsAt]
  | lvl, start, .constant x dd, _ => by
      intro g hg
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; simp only [HasProperBottomsAt]
  | lvl, start, .notGate g₀, hp => by
      unfold HasProperBottomsAt at hp; exact hp.elim
  | lvl, start, .andGate gates, hp => by
      intro g hg
      by_cases hle : lvl ≤ 2
      · simp only [extractBottomLayer, hle, if_true, List.mem_singleton] at hg
        subst hg
        unfold HasProperBottomsAt at hp ⊢
        rw [if_pos hle] at hp; rw [if_pos (le_refl 2)]; exact hp
      · have hg' : g ∈ (extractBottomLayerList (lvl - 1) start gates).1 := by
          simpa only [extractBottomLayer, hle, if_false] using hg
        unfold HasProperBottomsAt at hp
        rw [if_neg hle] at hp
        exact hasProperBottomsAt_of_mem_extractBottomLayerList (lvl - 1) start gates hp g hg'
  | lvl, start, .orGate gates, hp => by
      intro g hg
      by_cases hle : lvl ≤ 2
      · simp only [extractBottomLayer, hle, if_true, List.mem_singleton] at hg
        subst hg
        unfold HasProperBottomsAt at hp ⊢
        rw [if_pos hle] at hp; rw [if_pos (le_refl 2)]; exact hp
      · have hg' : g ∈ (extractBottomLayerList (lvl - 1) start gates).1 := by
          simpa only [extractBottomLayer, hle, if_false] using hg
        unfold HasProperBottomsAt at hp
        rw [if_neg hle] at hp
        exact hasProperBottomsAt_of_mem_extractBottomLayerList (lvl - 1) start gates hp g hg'

theorem hasProperBottomsAt_of_mem_extractBottomLayerList :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      (∀ f ∈ gs, HasProperBottomsAt f lvl) →
      ∀ g ∈ (extractBottomLayerList lvl start gs).1, HasProperBottomsAt g 2
  | lvl, start, [], _ => by
      intro g hg
      simp only [extractBottomLayerList, List.not_mem_nil] at hg
  | lvl, start, f :: gs, hp => by
      intro g hg
      have htop : (extractBottomLayerList lvl start (f :: gs)).1
          = (extractBottomLayer lvl start f).1
            ++ (extractBottomLayerList lvl
                  (extractBottomLayer lvl start f).2.2 gs).1 := rfl
      rw [htop, List.mem_append] at hg
      rcases hg with h | h
      · exact hasProperBottomsAt_of_mem_extractBottomLayer lvl start f (hp f (by simp)) g h
      · exact hasProperBottomsAt_of_mem_extractBottomLayerList lvl
          (extractBottomLayer lvl start f).2.2 gs
          (fun f' hf' => hp f' (by simp [hf'])) g h
end

/- inputGate indices of an extracted bottom are a subset of the original formula's
   input indices.  Used to transport `ufiLargestInput f < n` to a per-bottom
   `var < n` bound for the keystone. -/
mutual
theorem extractBottomLayer_bottoms_collect_subset :
    ∀ (lvl start : Nat) (f : UnboundedFanInFormula),
      ∀ g ∈ (extractBottomLayer lvl start f).1,
        ∀ x ∈ ufiCollectInputIndices g, x ∈ ufiCollectInputIndices f
  | lvl, start, .inputGate a b => by
      intro g hg x hx
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; exact hx
  | lvl, start, .constant a b => by
      intro g hg x hx
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; exact hx
  | lvl, start, .notGate g₀ => by
      intro g hg x hx
      simp only [extractBottomLayer, List.mem_singleton] at hg
      subst hg; exact hx
  | lvl, start, .andGate gates => by
      intro g hg x hx
      by_cases hle : lvl ≤ 2
      · simp only [extractBottomLayer, hle, if_true, List.mem_singleton] at hg
        subst hg; exact hx
      · have hg' : g ∈ (extractBottomLayerList (lvl - 1) start gates).1 := by
          simpa only [extractBottomLayer, hle, if_false] using hg
        unfold ufiCollectInputIndices
        exact extractBottomLayerList_bottoms_collect_subset (lvl - 1) start gates g hg' x hx
  | lvl, start, .orGate gates => by
      intro g hg x hx
      by_cases hle : lvl ≤ 2
      · simp only [extractBottomLayer, hle, if_true, List.mem_singleton] at hg
        subst hg; exact hx
      · have hg' : g ∈ (extractBottomLayerList (lvl - 1) start gates).1 := by
          simpa only [extractBottomLayer, hle, if_false] using hg
        unfold ufiCollectInputIndices
        exact extractBottomLayerList_bottoms_collect_subset (lvl - 1) start gates g hg' x hx

theorem extractBottomLayerList_bottoms_collect_subset :
    ∀ (lvl start : Nat) (gs : List UnboundedFanInFormula),
      ∀ g ∈ (extractBottomLayerList lvl start gs).1,
        ∀ x ∈ ufiCollectInputIndices g, x ∈ gs.flatMap ufiCollectInputIndices
  | lvl, start, [] => by
      intro g hg x hx
      simp only [extractBottomLayerList, List.not_mem_nil] at hg
  | lvl, start, f :: gs => by
      intro g hg x hx
      have htop : (extractBottomLayerList lvl start (f :: gs)).1
          = (extractBottomLayer lvl start f).1
            ++ (extractBottomLayerList lvl
                  (extractBottomLayer lvl start f).2.2 gs).1 := rfl
      rw [htop, List.mem_append] at hg
      rw [List.flatMap_cons, List.mem_append]
      rcases hg with h | h
      · exact Or.inl (extractBottomLayer_bottoms_collect_subset lvl start f g h x hx)
      · exact Or.inr (extractBottomLayerList_bottoms_collect_subset lvl
          (extractBottomLayer lvl start f).2.2 gs g h x hx)
end

section ProperBottomWidth
open UnboundedFanInFormula

/- Clause-size of a gate, as closed defs (so they can appear in lemma
   statements without capturing membership hypotheses in the match motive). -/
def clauseLengthCNF : UnboundedFanInFormula → Nat
  | orGate lits => lits.length
  | _ => 0

def clauseLengthDNF : UnboundedFanInFormula → Nat
  | andGate lits => lits.length
  | _ => 0

/- `cnfWidth`/`dnfWidth` as a bounded `foldl max` over clause sizes. -/
lemma cnfWidth_le_of_forall (gates : List UnboundedFanInFormula) (b : Nat)
    (h : ∀ g ∈ gates, clauseLengthCNF g ≤ b) :
    cnfWidth (andGate gates) ≤ b := by
  unfold cnfWidth
  apply Lists.ListLemmas.foldl_max_le_of_forall
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact h g hg

lemma le_cnfWidth_of_mem (gates : List UnboundedFanInFormula)
    (g : UnboundedFanInFormula) (hg : g ∈ gates) :
    clauseLengthCNF g ≤ cnfWidth (andGate gates) := by
  unfold cnfWidth
  apply Lists.ListLemmas.mem_le_foldl_max
  rw [List.mem_map]
  exact ⟨g, hg, rfl⟩

lemma dnfWidth_le_of_forall (gates : List UnboundedFanInFormula) (b : Nat)
    (h : ∀ g ∈ gates, clauseLengthDNF g ≤ b) :
    dnfWidth (orGate gates) ≤ b := by
  unfold dnfWidth
  apply Lists.ListLemmas.foldl_max_le_of_forall
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact h g hg

lemma le_dnfWidth_of_mem (gates : List UnboundedFanInFormula)
    (g : UnboundedFanInFormula) (hg : g ∈ gates) :
    clauseLengthDNF g ≤ dnfWidth (orGate gates) := by
  unfold dnfWidth
  apply Lists.ListLemmas.mem_le_foldl_max
  rw [List.mem_map]
  exact ⟨g, hg, rfl⟩

/- constant-tolerant base width bound (CNF): each produced child is either a
   clause of a proper-CNF sub (length ≤ t) or a `constant` (clause length 0). -/
lemma substFlatten_width_two_cnf_of_isProperSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula)
    (t : Nat) (gs : List UnboundedFanInFormula)
    (hgs : ∀ g ∈ gs, ∃ i b, g = inputGate i b ∧
      ((isCNF (sub i) = true ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses (sub i), (c.map Prod.fst).Nodup))
       ∨ (∃ bb m, sub i = constant bb m)))
    (hcw : ∀ i, cnfWidth (sub i) ≤ t) :
    cnfWidth (substFlatten sub (andGate gs)) ≤ t := by
  rw [substFlatten_and]
  apply cnfWidth_le_of_forall
  intro c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨g, hg, hcc⟩ := hc
  obtain ⟨i, b, rfl, hsub⟩ := hgs g hg
  rw [substFlatten] at hcc
  rcases hsub with ⟨hcnf, _, _⟩ | ⟨bb, m, hbm⟩
  · obtain ⟨inner, hinner⟩ := exists_eq_andGate_of_isCNF (sub i) hcnf
    rw [hinner] at hcc
    simp only [flattenAndChild] at hcc
    have h₁ := le_cnfWidth_of_mem inner c hcc
    rw [← hinner] at h₁
    exact le_trans h₁ (hcw i)
  · rw [hbm] at hcc
    simp only [flattenAndChild, List.mem_singleton] at hcc
    subst hcc
    simp only [clauseLengthCNF]
    exact Nat.zero_le t

/- constant-tolerant base width bound (DNF): dual. -/
lemma substFlatten_width_two_dnf_of_isProperSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula)
    (t : Nat) (gs : List UnboundedFanInFormula)
    (hgs : ∀ g ∈ gs, ∃ i b, g = inputGate i b ∧
      ((isDNF (sub i) = true ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses (sub i), (c.map Prod.fst).Nodup))
       ∨ (∃ bb m, sub i = constant bb m)))
    (hdw : ∀ i, dnfWidth (sub i) ≤ t) :
    dnfWidth (substFlatten sub (orGate gs)) ≤ t := by
  rw [substFlatten_or]
  apply dnfWidth_le_of_forall
  intro c hc
  rw [List.mem_flatMap] at hc
  obtain ⟨g, hg, hcc⟩ := hc
  obtain ⟨i, b, rfl, hsub⟩ := hgs g hg
  rw [substFlatten] at hcc
  rcases hsub with ⟨hdnf, _, _⟩ | ⟨bb, m, hbm⟩
  · obtain ⟨inner, hinner⟩ := exists_eq_orGate_of_isDNF (sub i) hdnf
    rw [hinner] at hcc
    simp only [flattenOrChild] at hcc
    have h₁ := le_dnfWidth_of_mem inner c hcc
    rw [← hinner] at h₁
    exact le_trans h₁ (hdw i)
  · rw [hbm] at hcc
    simp only [flattenOrChild, List.mem_singleton] at hcc
    subst hcc
    simp only [clauseLengthDNF]
    exact Nat.zero_le t

/- **constant-tolerant bottom-width producer.** For the relaxed
   `IsProperSubstitutionReadyWithConstants`
   skeleton: killed (constant) leaves at the splice base contribute width 0,
   so the uniform `cnfWidth`/`dnfWidth ≤ t` bound still lifts. -/
lemma hasProperBottomWidthLE_substFlatten_of_isProperSubstitutionReadyWithConstants (sub : Nat → UnboundedFanInFormula)
    (t : Nat) (hcw : ∀ i, cnfWidth (sub i) ≤ t) (hdw : ∀ i, dnfWidth (sub i) ≤ t)
    (g : UnboundedFanInFormula) :
    ∀ n, IsAndOr g → IsProperSubstitutionReadyWithConstants sub g n →
      HasProperBottomWidthLE (substFlatten sub g) (n + 1) t := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | const b m => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | notg g ih => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | andg gs ih =>
    intro n _ hsub
    by_cases hn : n ≤ 1
    · simp only [IsProperSubstitutionReadyWithConstants, if_pos hn] at hsub
      have hp := substFlatten_width_two_cnf_of_isProperSubstitutionReadyWithConstants sub t gs hsub hcw
      rw [substFlatten_and]
      rw [substFlatten_and] at hp
      simp only [HasProperBottomWidthLE, if_pos (show n + 1 ≤ 2 by omega)]
      exact hp
    · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hsub
      obtain ⟨hrec, hnoand, hleaf⟩ := hsub
      rw [substFlatten_and]
      simp only [HasProperBottomWidthLE, if_neg (show ¬ (n + 1 ≤ 2) by omega)]
      intro child hchild
      rw [Nat.add_sub_cancel]
      rw [List.mem_flatMap] at hchild
      obtain ⟨g', hg', hcc⟩ := hchild
      cases g' with
      | inputGate i b =>
        rcases hleaf i b hg' with ⟨x, d, hsi⟩ | ⟨bb, m, hsi⟩
        · have he : substFlatten sub (inputGate i b) = inputGate x d := by rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenAndChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomWidthLE]
        · have he : substFlatten sub (inputGate i b) = constant bb m := by
            rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenAndChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomWidthLE]
      | constant b m =>
        simp only [substFlatten, flattenAndChild, List.mem_singleton] at hcc
        subst hcc; simp only [HasProperBottomWidthLE]
      | notGate g₀ => have hf := hrec (notGate g₀) hg'; simp only [IsProperSubstitutionReadyWithConstants] at hf
      | andGate gs' => exact absurd hg' (hnoand gs')
      | orGate gs' =>
        have hih := ih (orGate gs') hg' (n - 1) (by simp [IsAndOr]) (hrec _ hg')
        rw [show n - 1 + 1 = n by omega, substFlatten_or] at hih
        rw [substFlatten_or] at hcc
        simp only [flattenAndChild, List.mem_singleton] at hcc
        subst hcc
        exact hih
  | org gs ih =>
    intro n _ hsub
    by_cases hn : n ≤ 1
    · simp only [IsProperSubstitutionReadyWithConstants, if_pos hn] at hsub
      have hp := substFlatten_width_two_dnf_of_isProperSubstitutionReadyWithConstants sub t gs hsub hdw
      rw [substFlatten_or]
      rw [substFlatten_or] at hp
      simp only [HasProperBottomWidthLE, if_pos (show n + 1 ≤ 2 by omega)]
      exact hp
    · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hsub
      obtain ⟨hrec, hnoor, hleaf⟩ := hsub
      rw [substFlatten_or]
      simp only [HasProperBottomWidthLE, if_neg (show ¬ (n + 1 ≤ 2) by omega)]
      intro child hchild
      rw [Nat.add_sub_cancel]
      rw [List.mem_flatMap] at hchild
      obtain ⟨g', hg', hcc⟩ := hchild
      cases g' with
      | inputGate i b =>
        rcases hleaf i b hg' with ⟨x, d, hsi⟩ | ⟨bb, m, hsi⟩
        · have he : substFlatten sub (inputGate i b) = inputGate x d := by rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenOrChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomWidthLE]
        · have he : substFlatten sub (inputGate i b) = constant bb m := by
            rw [substFlatten]; exact hsi
          rw [he] at hcc
          simp only [flattenOrChild, List.mem_singleton] at hcc
          subst hcc; simp only [HasProperBottomWidthLE]
      | constant b m =>
        simp only [substFlatten, flattenOrChild, List.mem_singleton] at hcc
        subst hcc; simp only [HasProperBottomWidthLE]
      | notGate g₀ => have hf := hrec (notGate g₀) hg'; simp only [IsProperSubstitutionReadyWithConstants] at hf
      | orGate gs' => exact absurd hg' (hnoor gs')
      | andGate gs' =>
        have hih := ih (andGate gs') hg' (n - 1) (by simp [IsAndOr]) (hrec _ hg')
        rw [show n - 1 + 1 = n by omega, substFlatten_and] at hih
        rw [substFlatten_and] at hcc
        simp only [flattenOrChild, List.mem_singleton] at hcc
        subst hcc
        exact hih

/- Empty gates satisfy the bottom-width invariant at any level. -/
lemma hasProperBottomWidthLE_orGate_nil (lvl t : Nat) :
    HasProperBottomWidthLE (orGate []) lvl t := by
  by_cases h : lvl ≤ 2
  · simp [HasProperBottomWidthLE, dnfWidth]
  · simp [HasProperBottomWidthLE, if_neg h]

lemma hasProperBottomWidthLE_andGate_nil (lvl t : Nat) :
    HasProperBottomWidthLE (andGate []) lvl t := by
  by_cases h : lvl ≤ 2
  · simp [HasProperBottomWidthLE, cnfWidth]
  · simp [HasProperBottomWidthLE, if_neg h]

/- The absorption pass never increases a clause's CNF/DNF size: folding only
   drops literals (filter) or collapses a clause to an empty gate (size 0). -/
lemma clauseLengthCNF_simplifyConstants_le (c : UnboundedFanInFormula) :
    clauseLengthCNF (simplifyConstants c) ≤ clauseLengthCNF c := by
  cases c with
  | inputGate x b => simp [simplifyConstants, clauseLengthCNF]
  | constant b m => simp only [simplifyConstants]; cases b <;> simp [clauseLengthCNF]
  | notGate g => simp [simplifyConstants, clauseLengthCNF]
  | andGate gs =>
      simp only [simplifyConstants]
      split <;> simp [clauseLengthCNF]
  | orGate lits =>
      simp only [simplifyConstants]
      split
      · simp [clauseLengthCNF]
      · simp only [clauseLengthCNF]
        calc ((simplifyConstantsList lits).filter (fun g => !isCanonicalFalse g)).length
            ≤ (simplifyConstantsList lits).length := List.length_filter_le _ _
          _ = lits.length := by rw [simplifyConstantsList_eq_map, List.length_map]

lemma clauseLengthDNF_simplifyConstants_le (c : UnboundedFanInFormula) :
    clauseLengthDNF (simplifyConstants c) ≤ clauseLengthDNF c := by
  cases c with
  | inputGate x b => simp [simplifyConstants, clauseLengthDNF]
  | constant b m => simp only [simplifyConstants]; cases b <;> simp [clauseLengthDNF]
  | notGate g => simp [simplifyConstants, clauseLengthDNF]
  | orGate gs =>
      simp only [simplifyConstants]
      split <;> simp [clauseLengthDNF]
  | andGate lits =>
      simp only [simplifyConstants]
      split
      · simp [clauseLengthDNF]
      · simp only [clauseLengthDNF]
        calc ((simplifyConstantsList lits).filter (fun g => !isCanonicalTrue g)).length
            ≤ (simplifyConstantsList lits).length := List.length_filter_le _ _
          _ = lits.length := by rw [simplifyConstantsList_eq_map, List.length_map]

/- **Bottom-width preservation under the absorption pass.**  Since folding
   only drops or shrinks clauses (and collapses to empty gates, which are
   width-0), the structural bottom-width invariant is maintained.  Composing
   with `extractBottomLayer_bottoms_fanIn_le` yields the required
   bottom-width bound for the simplified circuit. -/
mutual

theorem hasProperBottomWidthLE_simplifyConstants :
    ∀ (f : UnboundedFanInFormula) (lvl t : Nat),
      HasProperBottomWidthLE f lvl t → HasProperBottomWidthLE (simplifyConstants f) lvl t
  | inputGate x b, lvl, t, _ => by simp [simplifyConstants, HasProperBottomWidthLE]
  | constant b m, lvl, t, _ => by
      simp only [simplifyConstants]
      cases b
      · exact hasProperBottomWidthLE_orGate_nil lvl t
      · exact hasProperBottomWidthLE_andGate_nil lvl t
  | notGate g, lvl, t, h => by simp only [HasProperBottomWidthLE] at h
  | andGate gs, lvl, t, h => by
      simp only [simplifyConstants]
      split
      · exact hasProperBottomWidthLE_orGate_nil lvl t
      · by_cases hlvl : lvl ≤ 2
        · simp only [HasProperBottomWidthLE, if_pos hlvl] at h ⊢
          apply cnfWidth_le_of_forall
          intro s hs
          have hmemcs : s ∈ simplifyConstantsList gs := List.mem_of_mem_filter hs
          rw [simplifyConstantsList_eq_map, List.mem_map] at hmemcs
          obtain ⟨g₀, hg₀, rfl⟩ := hmemcs
          calc clauseLengthCNF (simplifyConstants g₀)
              ≤ clauseLengthCNF g₀ := clauseLengthCNF_simplifyConstants_le g₀
            _ ≤ cnfWidth (andGate gs) := le_cnfWidth_of_mem gs g₀ hg₀
            _ ≤ t := h
        · simp only [HasProperBottomWidthLE, if_neg hlvl] at h ⊢
          intro s hs
          have hmemcs : s ∈ simplifyConstantsList gs := List.mem_of_mem_filter hs
          exact hasProperBottomWidthLE_simplifyConstantsList gs (lvl - 1) t h s hmemcs
  | orGate gs, lvl, t, h => by
      simp only [simplifyConstants]
      split
      · exact hasProperBottomWidthLE_andGate_nil lvl t
      · by_cases hlvl : lvl ≤ 2
        · simp only [HasProperBottomWidthLE, if_pos hlvl] at h ⊢
          apply dnfWidth_le_of_forall
          intro s hs
          have hmemcs : s ∈ simplifyConstantsList gs := List.mem_of_mem_filter hs
          rw [simplifyConstantsList_eq_map, List.mem_map] at hmemcs
          obtain ⟨g₀, hg₀, rfl⟩ := hmemcs
          calc clauseLengthDNF (simplifyConstants g₀)
              ≤ clauseLengthDNF g₀ := clauseLengthDNF_simplifyConstants_le g₀
            _ ≤ dnfWidth (orGate gs) := le_dnfWidth_of_mem gs g₀ hg₀
            _ ≤ t := h
        · simp only [HasProperBottomWidthLE, if_neg hlvl] at h ⊢
          intro s hs
          have hmemcs : s ∈ simplifyConstantsList gs := List.mem_of_mem_filter hs
          exact hasProperBottomWidthLE_simplifyConstantsList gs (lvl - 1) t h s hmemcs

theorem hasProperBottomWidthLE_simplifyConstantsList :
    ∀ (gs : List UnboundedFanInFormula) (lvl t : Nat),
      (∀ g ∈ gs, HasProperBottomWidthLE g lvl t) →
      ∀ h ∈ simplifyConstantsList gs, HasProperBottomWidthLE h lvl t
  | [], lvl, t, _, h, hmem => by simp [simplifyConstantsList] at hmem
  | g₀ :: gs, lvl, t, hall, h, hmem => by
      rw [simplifyConstantsList_eq_map, List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hasProperBottomWidthLE_simplifyConstants g₀ lvl t (hall g₀ (by simp))
      · exact hasProperBottomWidthLE_simplifyConstantsList gs lvl t
          (fun g hg => hall g (List.mem_cons_of_mem _ hg)) h
          (by rw [simplifyConstantsList_eq_map]; exact hmem)

end

/- **Composed bottom-width brick.**  Substituting (with `constant`-killed
    leaves) into an alternating skeleton and then running the absorption pass
    preserves the bottom-width bound. This supplies the bottom-width field of
    `exists_switching_depth_reduction` for `circuit' = simplifyConstants (substFlatten sub top)`. -/
lemma hasProperBottomWidthLE_simplifyConstants_substFlatten
    (sub : Nat → UnboundedFanInFormula) (t : Nat)
    (hcw : ∀ i, cnfWidth (sub i) ≤ t) (hdw : ∀ i, dnfWidth (sub i) ≤ t)
    (g : UnboundedFanInFormula) (n : Nat)
    (h_and_or : IsAndOr g) (h_ready : IsProperSubstitutionReadyWithConstants sub g n) :
    HasProperBottomWidthLE (simplifyConstants (substFlatten sub g)) (n + 1) t :=
  hasProperBottomWidthLE_simplifyConstants (substFlatten sub g) (n + 1) t
    (hasProperBottomWidthLE_substFlatten_of_isProperSubstitutionReadyWithConstants sub t hcw hdw g n h_and_or h_ready)

lemma switchingGateBudget_flatMap_sum_le {α : Type*}
    (l : List α) (f : α → List UnboundedFanInFormula) (cost : α → Nat)
    (lvl : Nat)
    (h : ∀ x ∈ l, ((f x).map (switchingGateBudget lvl)).sum ≤ cost x) :
    ((l.flatMap f).map (switchingGateBudget lvl)).sum ≤ (l.map cost).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp))
        (ih (fun y hy => h y (by simp [hy])))

/-- Substitution can create arbitrarily large narrow formulas below the new
    frontier, but it cannot create a new *frontier gate*.  Live/dead literal
    substitutions have zero switching budget; opposite-polarity gate children
    recurse, and same-polarity gates are flattened away. -/
lemma substFlatten_switchingGateBudget_le
    (sub : Nat → UnboundedFanInFormula) (g : UnboundedFanInFormula) :
    ∀ n, IsAndOr g → IsProperSubstitutionReadyWithConstants sub g n →
      switchingGateBudget (n + 1) (substFlatten sub g) ≤
        ufiFormulaCircuitSize g := by
  induction g using UnboundedFanInFormula.induction with
  | input i b => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | const b m => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | notg g ih => intro n hand _; exact absurd hand (by simp [IsAndOr])
  | andg gs ih =>
      intro n _ hsub
      rw [substFlatten_and]
      by_cases hn : n ≤ 1
      · cases hout : gs.flatMap (fun g => flattenAndChild (substFlatten sub g)) with
        | nil => simp [switchingGateBudget, ufiFormulaCircuitSize]
        | cons x xs =>
            simp [switchingGateBudget, ufiFormulaCircuitSize,
              show n + 1 ≤ 2 by omega]
      · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hsub
        obtain ⟨hrec, hnoand, hleaf⟩ := hsub
        have hchild : ∀ g ∈ gs,
            ((flattenAndChild (substFlatten sub g)).map
              (switchingGateBudget n)).sum ≤ ufiFormulaCircuitSize g := by
          intro child hmem
          cases child with
          | inputGate i b =>
              rcases hleaf i b hmem with ⟨x, d, hs⟩ | ⟨bb, m, hs⟩ <;>
                simp [substFlatten, hs, flattenAndChild, switchingGateBudget,
                  ufiFormulaCircuitSize]
          | constant b m =>
              simp [substFlatten, flattenAndChild, switchingGateBudget,
                ufiFormulaCircuitSize]
          | notGate child =>
              have hf := hrec (.notGate child) hmem
              simp [IsProperSubstitutionReadyWithConstants] at hf
          | andGate inner => exact absurd hmem (hnoand inner)
          | orGate inner =>
              have hih := ih (.orGate inner) hmem (n - 1) (by simp [IsAndOr])
                (hrec _ hmem)
              rw [show n - 1 + 1 = n by omega] at hih
              rw [substFlatten_or] at hih ⊢
              simpa [flattenAndChild] using hih
        have hsum := switchingGateBudget_flatMap_sum_le gs
          (fun g => flattenAndChild (substFlatten sub g)) ufiFormulaCircuitSize n hchild
        cases hout : gs.flatMap (fun g => flattenAndChild (substFlatten sub g)) with
        | nil => simp [switchingGateBudget, ufiFormulaCircuitSize]
        | cons x xs =>
            rw [hout] at hsum
            simp only [switchingGateBudget, if_neg (show ¬ n + 1 ≤ 2 by omega),
              List.map_cons, List.sum_cons, ufiFormulaCircuitSize]
            exact Nat.add_le_add_right hsum 1
  | org gs ih =>
      intro n _ hsub
      rw [substFlatten_or]
      by_cases hn : n ≤ 1
      · cases hout : gs.flatMap (fun g => flattenOrChild (substFlatten sub g)) with
        | nil => simp [switchingGateBudget, ufiFormulaCircuitSize]
        | cons x xs =>
            simp [switchingGateBudget, ufiFormulaCircuitSize,
              show n + 1 ≤ 2 by omega]
      · simp only [IsProperSubstitutionReadyWithConstants, if_neg hn] at hsub
        obtain ⟨hrec, hnoor, hleaf⟩ := hsub
        have hchild : ∀ g ∈ gs,
            ((flattenOrChild (substFlatten sub g)).map
              (switchingGateBudget n)).sum ≤ ufiFormulaCircuitSize g := by
          intro child hmem
          cases child with
          | inputGate i b =>
              rcases hleaf i b hmem with ⟨x, d, hs⟩ | ⟨bb, m, hs⟩ <;>
                simp [substFlatten, hs, flattenOrChild, switchingGateBudget,
                  ufiFormulaCircuitSize]
          | constant b m =>
              simp [substFlatten, flattenOrChild, switchingGateBudget,
                ufiFormulaCircuitSize]
          | notGate child =>
              have hf := hrec (.notGate child) hmem
              simp [IsProperSubstitutionReadyWithConstants] at hf
          | orGate inner => exact absurd hmem (hnoor inner)
          | andGate inner =>
              have hih := ih (.andGate inner) hmem (n - 1) (by simp [IsAndOr])
                (hrec _ hmem)
              rw [show n - 1 + 1 = n by omega] at hih
              rw [substFlatten_and] at hih ⊢
              simpa [flattenOrChild] using hih
        have hsum := switchingGateBudget_flatMap_sum_le gs
          (fun g => flattenOrChild (substFlatten sub g)) ufiFormulaCircuitSize n hchild
        cases hout : gs.flatMap (fun g => flattenOrChild (substFlatten sub g)) with
        | nil => simp [switchingGateBudget, ufiFormulaCircuitSize]
        | cons x xs =>
            rw [hout] at hsum
            simp only [switchingGateBudget, if_neg (show ¬ n + 1 ≤ 2 by omega),
              List.map_cons, List.sum_cons, ufiFormulaCircuitSize]
            exact Nat.add_le_add_right hsum 1

end ProperBottomWidth

/-- **Terminal depth-two collapse.**  A properly leveled formula of depth at
    most two becomes a DNF narrower than its surviving live-variable set after
    one restriction, provided its bottom fan-in is bounded by `w` and
    `20 · (w + 1) < n`.

    The conclusion exhibits `live`, `deadBits`, a width witness `w'`, and a
    DNF `g` on the compact namespace `0, ..., live.length - 1`.  For every
    assignment `liveBits` of the correct length, evaluating `g` agrees with
    evaluating the original circuit after `assembleInput` restores the live
    bits to their original coordinates and inserts `deadBits` elsewhere.
    Moreover, `dnfWidth g.val ≤ w' < live.length`.

    The proof first recovers `HasProperBottomsAt circuit.val 2` from the fused
    leveling invariant, then dispatches on the root constructor:

    * `inputGate idx polarity`: keep `idx` and one distinct filler index live,
      rekey `idx` to live coordinate `0`, and return the singleton width-one
      DNF `orGate [andGate [inputGate 0 polarity]]`.
    * `constant b`: keep two arbitrary coordinates live and return the
      canonical width-zero DNF for `b` (`orGate []` for false or
      `orGate [andGate []]` for true).
    * `notGate`: impossible under proper leveling.
    * `orGate gates`: proper-bottom structure packages the root as a proper
      DNF.  The inequality `ufiBottomFanIn circuit.val ≤ w` implies its DNF
      width is at most `w`, so `exists_depth_two_dnf_collapse` applies.
    * `andGate gates`: similarly package the root as a proper CNF and invoke
      `exists_depth_two_cnf_collapse`.

    The `inputGate` and `constant` branches obtain `2 ≤ n` from the same global
    threshold used by the switching branches.  Since `w` is a natural number,
    `1 ≤ w + 1`, so `20 ≤ 20 · (w + 1) < n`; in fact the hypotheses imply
    `21 ≤ n`, although these branches only need `2 ≤ n`.  For an input this
    guarantees a coordinate distinct from `idx` (the proof chooses `1` when
    `idx = 0` and `0` otherwise), allowing a two-element live set and the
    strict width inequality `1 < 2`.  For a constant it puts both `0` and `1`
    in range, so `[0, 1]` meets the theorem's uniform requirement that at least
    two variables remain live even though the width-zero DNF reads neither.

    The DNF helper chooses the exact restriction density `σ = 2 / n` and
    canonical-decision-tree depth bound `1`.  The threshold implies the
    switching estimate `10 · σ · w < 1`, so some good restriction leaves
    exactly two live variables and has canonical decision-tree depth at most
    one.  Converting that tree to a DNF gives width at most one, hence width
    strictly less than the two-variable live set.

    This explains the numerical constant: `20 = 10 · 2`.  The exact
    switching lemma contributes `10` through its bound `(10 · σ · w)^d`, and
    the terminal construction contributes `2`, the least live count strictly
    larger than the chosen decision-tree depth `d = 1`.  Substituting
    `σ = 2 / n` turns the switching base into `20w / n`.  The slightly stronger
    assumption `20 · (w + 1) < n` implies this base is below one even at the
    edge case `w = 0`, and simultaneously supplies the size conditions on `n`
    needed for `σ` and for the degenerate root cases.

    For an AND-rooted CNF, `exists_depth_two_cnf_collapse` first takes its De
    Morgan dual, a proper DNF of the same width computing the negation.  It
    applies the same switching argument, negates the resulting decision tree
    by flipping leaves (which preserves depth), and converts the negated tree
    to a DNF.  The two negations cancel, so the final DNF computes the original
    CNF on every assembled restricted input.

    Here `w` is a bottom-fan-in bound, not the loose polynomial circuit-size
    bound `c · n^k`.  In the iterated proof it is instantiated with the small
    parameter `t` maintained by previous rounds.  This lemma is therefore the
    depth-two base case of `exists_iterated_switching_depth_collapse`; it does
    not spend another uniform `n ↦ n / (20t)` depth-reduction round. -/
lemma exists_depth_two_collapse
      {c k n : Nat}
      (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k 2)
      (h_inputs_bound : ufiLargestInput formula.val < n)
      (w : Nat)
      (h_node_w : ufiBottomFanIn formula.val ≤ w)
      (h_thresh : 20 * (w + 1) < n) :
  ∃ (live : List Nat)
    (_h_live_lt : ∀ v ∈ live, v < n)
    (_h_live_nodup : live.Nodup)
    (_h_live_big : 2 ≤ live.length)
    (deadBits : List Bool)
    (w : Nat) (_hw : w < live.length)
    (g : UnboundedFanInDNF live.length),
    dnfWidth g.val ≤ w ∧
    ∀ (liveBits : List Bool), liveBits.length = live.length →
      ufiFormulaEval formula.val
          (assembleInput n live liveBits deadBits) =
      ufiFormulaEval g.val liveBits := by
  -- Root-shape dispatch, delegating the two genuine depth-two forms to the
  -- matching analytic helper:
  --   orGate -> `exists_depth_two_dnf_collapse` (single-DNF switching).
  --   andGate -> `exists_depth_two_cnf_collapse` (CNF dual via De Morgan).
  -- inputGate and constant are possible because the subtype records an upper
  -- depth bound; they collapse directly.  Only notGate is forbidden by the
  -- proper-leveling invariant.
  -- Stash the projection so the `match` below is on a single value.
  have h_proper : HasProperBottomsAt formula.val 2 :=
    Circuits.Leveling.isProperlyLeveled_imp_proper _ _ formula.property.2.2.2.2
  set formula : UnboundedFanInFormula := formula.val with h_formula
  -- Move `h_inputs_bound`, `h_proper`, and the size bound to the
  -- `formula` form before the `clear_value` opaqueifies `formula`.
  have h_inputs_bound' : ufiLargestInput formula < n := h_inputs_bound
  have h_proper' : HasProperBottomsAt formula 2 := h_proper
  have h_size' : ufiBottomFanIn formula ≤ w := h_node_w
  clear_value formula
  -- Dispatch on the head of `formula`.
  match formula, h_inputs_bound', h_proper', h_size' with
  | UnboundedFanInFormula.inputGate idx bn, hib, _, _ =>
      -- Degenerate root: the formula computes a single literal `inputGate idx bn`.
      -- Make `idx` (plus one filler index) live and keep the rest dead; the
      -- width-1 singleton DNF `orGate [andGate [inputGate 0 bn]]` reads live
      -- coordinate `0`, reproducing the literal.
      have hidx : idx < n := by
        simpa [ufiLargestInput, ufiCollectInputIndices, List.foldr_cons, List.foldr_nil,
          Nat.max_zero] using hib
      -- The threshold is much stronger than this: because `w + 1 ≥ 1`,
      -- `20 ≤ 20 * (w + 1) < n`, hence actually `21 ≤ n`.  We retain only
      -- `2 ≤ n`, which guarantees a filler coordinate distinct from `idx`
      -- and makes the width-one target strictly narrower than the live set.
      have hn₂ : 2 ≤ n := by omega
      obtain ⟨other, hother_lt, hother_ne⟩ : ∃ o, o < n ∧ idx ≠ o := by
        rcases Nat.eq_zero_or_pos idx with h | h
        · exact ⟨1, by omega, by omega⟩
        · exact ⟨0, by omega, by omega⟩
      refine ⟨[idx, other], ?_, ?_, ?_, List.replicate (n - 2) false,
              1, ?_,
              ⟨UnboundedFanInFormula.orGate
                  [UnboundedFanInFormula.andGate
                    [UnboundedFanInFormula.inputGate 0 bn]], ?_, ?_⟩, ?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hidx
        · exact hother_lt
      · simp [hother_ne]
      · simp only [List.length_cons, List.length_nil]; omega
      · simp only [List.length_cons, List.length_nil]; omega
      · have hlm : ufiLargestInput (UnboundedFanInFormula.orGate
            [UnboundedFanInFormula.andGate
              [UnboundedFanInFormula.inputGate 0 bn]]) = 0 := by
          simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_cons, List.foldr_nil]
        rw [hlm]
        simp only [List.length_cons, List.length_nil]; omega
      · simp [isDNF, isAndOfInputsOnly, isInput]
      · simp only [dnfWidth, List.map_cons, List.map_nil, List.foldl_cons,
          List.foldl_nil, List.length_cons, List.length_nil]
        omega
      · intro lb hlb
        rw [eval_or_and_singleton]
        have h_a := assemble_lookup_head n idx other lb
            (List.replicate (n - 2) false) hidx
        have h_b : lb[0]? = some (lb.getD 0 false) := by
          cases lb with
          | nil => simp at hlb
          | cons a t => rfl
        unfold ufiFormulaEval
        rw [h_a, h_b]
  | UnboundedFanInFormula.constant bval _, _, _, _ =>
      -- Degenerate root: the formula computes the constant `bval`.  Any
      -- two-element live set works; the constant DNF reproduces `bval`
      -- without reading any live coordinate.
      -- Again `h_thresh` implies `20 < n`, hence `2 ≤ n`.  This puts both
      -- coordinates `0` and `1` in range.  They are retained only to satisfy
      -- the theorem's uniform lower bound `2 ≤ live.length`; the width-zero
      -- constant DNF does not inspect either coordinate.
      have hn₂ : 2 ≤ n := by omega
      cases bval with
      | true =>
        refine ⟨[0, 1], ?_, ?_, ?_, List.replicate (n - 2) false, 0, ?_,
                ⟨UnboundedFanInFormula.orGate
                    [UnboundedFanInFormula.andGate []], ?_, ?_⟩, ?_, ?_⟩
        · intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;> omega
        · decide
        · decide
        · decide
        · have hlm : ufiLargestInput (UnboundedFanInFormula.orGate
              [UnboundedFanInFormula.andGate []]) = 0 := by
            simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil]
          rw [hlm]; decide
        · decide
        · decide
        · intro lb hlb; simp [ufiFormulaEval]
      | false =>
        refine ⟨[0, 1], ?_, ?_, ?_, List.replicate (n - 2) false, 0, ?_,
                ⟨UnboundedFanInFormula.orGate [], ?_, ?_⟩, ?_, ?_⟩
        · intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;> omega
        · decide
        · decide
        · decide
        · have hlm : ufiLargestInput (UnboundedFanInFormula.orGate []) = 0 := by
            simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil]
          rw [hlm]; decide
        · decide
        · decide
        · intro lb hlb; simp [ufiFormulaEval]
  | UnboundedFanInFormula.notGate _, _, hp, _ =>
      simp only [HasProperBottomsAt] at hp
  | UnboundedFanInFormula.orGate gates, hib, hp, hsz =>
      -- DNF case: package as `UnboundedFanInProperDNF n`.
      have hp' :
          isDNF (UnboundedFanInFormula.orGate gates) = true ∧
          (∀ c ∈ Circuits.CnfDnf.dnfClauses (UnboundedFanInFormula.orGate gates),
              c ≠ []) ∧
          (∀ c ∈ Circuits.CnfDnf.dnfClauses (UnboundedFanInFormula.orGate gates),
              (c.map Prod.fst).Nodup) := by
        simp only [HasProperBottomsAt] at hp
        exact hp
      let f : UnboundedFanInProperDNF n :=
        ⟨UnboundedFanInFormula.orGate gates, hib, hp'.1, hp'.2.1, hp'.2.2⟩
      -- Derive the width bound directly from the bottom fan-in
      -- (`ufiBottomFanIn (orGate gates) = max 1 (dnfWidth …)`).
      have hwidth : dnfWidth f.val ≤ w := by
        have : ufiBottomFanIn (UnboundedFanInFormula.orGate gates) = max 1 (dnfWidth (.orGate gates)) := rfl
        rw [this] at hsz
        have : dnfWidth f.val = dnfWidth (UnboundedFanInFormula.orGate gates) := rfl
        omega
      exact exists_depth_two_dnf_collapse w f hwidth h_thresh
  | UnboundedFanInFormula.andGate gates, hib, hp, hsz =>
      -- CNF case: package as `UnboundedFanInProperCNF n`.
      have hp' :
          isCNF (UnboundedFanInFormula.andGate gates) = true ∧
          (∀ c ∈ Circuits.CnfDnf.cnfClauses (UnboundedFanInFormula.andGate gates),
              c ≠ []) ∧
          (∀ c ∈ Circuits.CnfDnf.cnfClauses (UnboundedFanInFormula.andGate gates),
              (c.map Prod.fst).Nodup) := by
        simp only [HasProperBottomsAt] at hp
        exact hp
      let f : UnboundedFanInProperCNF n :=
        ⟨UnboundedFanInFormula.andGate gates, hib, hp'⟩
      -- Derive the width bound directly from the bottom fan-in
      -- (`ufiBottomFanIn (andGate gates) = max 1 (cnfWidth …)`).
      have hwidth : cnfWidth f.val ≤ w := by
        have : ufiBottomFanIn (UnboundedFanInFormula.andGate gates) = max 1 (cnfWidth (.andGate gates)) := rfl
        rw [this] at hsz
        have : cnfWidth f.val = cnfWidth (UnboundedFanInFormula.andGate gates) := rfl
        omega
      exact exists_depth_two_cnf_collapse w f hwidth h_thresh

/-- A proof-directed switching-gate bottom has the same structural width as
    its source gate, hence is bounded by that gate's bottom fan-in. -/
theorem switchingGateBottom_width_le_ufiBottomFanIn
    (n : Nat) (g : UnboundedFanInFormula)
    (h_gate : IsSwitchingGate g) (h_inputs : ufiLargestInput g < n)
    (h_proper : HasProperBottomsAt g 2) :
    (switchingGateBottom n g h_gate h_inputs h_proper).width ≤ ufiBottomFanIn g := by
  cases g with
  | inputGate i b => simp [IsSwitchingGate] at h_gate
  | constant b label => simp [IsSwitchingGate] at h_gate
  | notGate g => simp [IsSwitchingGate] at h_gate
  | andGate gates =>
      change cnfWidth (.andGate gates) ≤ max 1 (cnfWidth (.andGate gates))
      omega
  | orGate gates =>
      change dnfWidth (.orGate gates) ≤ max 1 (dnfWidth (.orGate gates))
      omega

def HasBottomFanInLE (lvl : Nat) (circuit : UnboundedFanInFormula)
    (t : Nat) : Prop :=
  ∀ g ∈ (extractBottomLayer lvl 0 circuit).1, ufiBottomFanIn g ≤ t

/-- **Polarity-on-demand per-bottom proper conversion.**  Parameterised by a
    requested polarity `p`
    (CNF when `p = true`, DNF when `p = false`) and producing a proper
    form computing `f` **unconditionally** — for both polarities, using the
    DNF view directly or through its De Morgan dual. This is the
    dual-readability ingredient that lets the
    `buildKillAwareForms` substitution map emit a correct narrow form at every
    splice base regardless of the threaded `needCnf`, removing the
    `gf` polarity gate. -/
lemma exists_bottom_sub_proper_for_polarity
    {n : Nat} (decisionTreeDepthBound : Nat) {σ : OpenUnitIntervalQ} (p : Bool)
    (f : BottomFormula n)
    (fv : UnboundedFanInProperDNF n)
    (hfv : ∀ xs, xs.length = n → ufiFormulaEval fv.val xs =
            (if f.polarity then ufiFormulaEval f.toUFI xs
             else not (ufiFormulaEval f.toUFI xs)))
    (ρ : AssignedRandomRestriction σ n)
    (hρ : ¬ isBadRestriction decisionTreeDepthBound n σ fv ρ)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_dt_lt : decisionTreeDepthBound < live.length) :
    ∃ (g : UnboundedFanInFormula),
      ufiLargestInput g < live.length ∧
      (p = true → isCNF g = true ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses g, c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.cnfClauses g, (c.map Prod.fst).Nodup)) ∧
      (p = false → isDNF g = true ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses g, c ≠ []) ∧
        (∀ c ∈ Circuits.CnfDnf.dnfClauses g, (c.map Prod.fst).Nodup)) ∧
      (p = true → cnfWidth g ≤ max 1 decisionTreeDepthBound) ∧
      (p = false → dnfWidth g ≤ max 1 decisionTreeDepthBound) ∧
      ufiFormulaCircuitSize g ≤ 1 + (2 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1)) * (decisionTreeDepthBound + 2) ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval f.toUFI (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g liveBits := by
  have hpos : 0 < live.length := by omega
  by_cases hp : p = true
  · -- Requested CNF.  Read the (negated) canonical tree as a CNF computing `f`.
    obtain ⟨g₀, hg₀_bnd, hg₀_cnf, hg₀_w, hg₀_nc, hg₀_eval⟩ :
        ∃ g₀, ufiLargestInput g₀ < live.length ∧ isCNF g₀ = true ∧
          cnfWidth g₀ ≤ decisionTreeDepthBound ∧
          ufiFormulaCircuitSize g₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) ∧
          (∀ lb, lb.length = live.length →
            ufiFormulaEval f.toUFI (assembleInput n live lb deadBits) =
            ufiFormulaEval g₀ lb) := by
      by_cases hpol : f.polarity = true
      · obtain ⟨g₀, hgw, hgnc, hgeval⟩ :=
          exists_narrow_cnf_from_good_restriction_dnf decisionTreeDepthBound fv ρ hρ live h_live_lt
            h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
        refine ⟨g₀.val, g₀.property.1, g₀.property.2, hgw, hgnc, ?_⟩
        intro lb hlb
        have he := hgeval lb hlb
        have hf := hfv (assembleInput n live lb deadBits)
          (length_assembleInput n live lb deadBits)
        rw [if_pos hpol] at hf
        exact hf.symm.trans he
      · have hpf : f.polarity = false := by
          cases hb : f.polarity with
          | true => exact absurd hb hpol
          | false => rfl
        obtain ⟨g₀, hgw, hgnc, hgeval⟩ :=
          exists_narrow_negated_cnf_from_good_restriction_dnf decisionTreeDepthBound fv ρ hρ live h_live_lt
            h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
        refine ⟨g₀.val, g₀.property.1, g₀.property.2, hgw, hgnc, ?_⟩
        intro lb hlb
        have he := hgeval lb hlb
        have hf := hfv (assembleInput n live lb deadBits)
          (length_assembleInput n live lb deadBits)
        rw [if_neg hpol] at hf
        rw [← he, hf]
        generalize ufiFormulaEval f.toUFI (assembleInput n live lb deadBits) = b
        cases b <;> rfl
    obtain ⟨hcnf', hne', hnd', hbnd', heval'⟩ :=
      ProperizeProto.properize_narrow_cnf live.length hpos g₀ hg₀_cnf hg₀_bnd
    refine ⟨ProperizeProto.properizeCNF g₀, hbnd',
            fun _ => ⟨hcnf', hne', hnd'⟩, fun h => by simp [hp] at h,
            fun _ => ?_, fun h => by simp [hp] at h, ?_, ?_⟩
    · have hle := ProperizeProto.properizeCNF_width_le g₀ hg₀_cnf
      omega
    · -- circuit-size bound on the properized CNF
      have hnc_p := ProperizeProto.properizeCNF_circuit_size_le g₀
      have hsize := ProperizeProto.cnfSize_le_circuit_size g₀ hg₀_cnf
      have h_a : max 2 (cnfSize g₀) ≤ 2 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
        have hc : cnfSize g₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := le_trans hsize hg₀_nc
        omega
      have h_bw : max 1 (cnfWidth g₀) + 1 ≤ decisionTreeDepthBound + 2 := by omega
      calc ufiFormulaCircuitSize (ProperizeProto.properizeCNF g₀)
          ≤ 1 + max 2 (cnfSize g₀) := hnc_p
        _ ≤ 1 + max 2 (cnfSize g₀) * (max 1 (cnfWidth g₀) + 1) := by
              apply Nat.add_le_add_left
              calc max 2 (cnfSize g₀) = max 2 (cnfSize g₀) * 1 := by omega
                _ ≤ max 2 (cnfSize g₀) * (max 1 (cnfWidth g₀) + 1) :=
                  Nat.mul_le_mul_left _ (by omega)
        _ ≤ 1 + (2 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1)) * (decisionTreeDepthBound + 2) := by
              apply Nat.add_le_add_left
              exact Nat.mul_le_mul h_a h_bw
    · intro lb hlb
      exact (hg₀_eval lb hlb).trans (heval' lb hlb).symm
  · -- Requested DNF.  Read the (negated) canonical tree as a DNF computing `f`.
    have hpfalse : p = false := by
      cases hb : p with
      | true => exact absurd hb hp
      | false => rfl
    obtain ⟨g₀, hg₀_bnd, hg₀_dnf, hg₀_w, hg₀_nc, hg₀_eval⟩ :
        ∃ g₀, ufiLargestInput g₀ < live.length ∧ isDNF g₀ = true ∧
          dnfWidth g₀ ≤ decisionTreeDepthBound ∧
          ufiFormulaCircuitSize g₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) ∧
          (∀ lb, lb.length = live.length →
            ufiFormulaEval f.toUFI (assembleInput n live lb deadBits) =
            ufiFormulaEval g₀ lb) := by
      by_cases hpol : f.polarity = true
      · obtain ⟨g₀, hgw, hgnc, hgeval⟩ :=
          exists_narrow_dnf_from_good_restriction_dnf decisionTreeDepthBound fv ρ hρ live h_live_lt
            h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
        refine ⟨g₀.val, g₀.property.1, g₀.property.2, hgw, hgnc, ?_⟩
        intro lb hlb
        have he := hgeval lb hlb
        have hf := hfv (assembleInput n live lb deadBits)
          (length_assembleInput n live lb deadBits)
        rw [if_pos hpol] at hf
        exact hf.symm.trans he
      · have hpf : f.polarity = false := by
          cases hb : f.polarity with
          | true => exact absurd hb hpol
          | false => rfl
        obtain ⟨g₀, hgw, hgnc, hgeval⟩ :=
          exists_narrow_negated_dnf_from_good_restriction_dnf decisionTreeDepthBound fv ρ hρ live h_live_lt
            h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
        refine ⟨g₀.val, g₀.property.1, g₀.property.2, hgw, hgnc, ?_⟩
        intro lb hlb
        have he := hgeval lb hlb
        have hf := hfv (assembleInput n live lb deadBits)
          (length_assembleInput n live lb deadBits)
        rw [if_neg hpol] at hf
        rw [← he, hf]
        generalize ufiFormulaEval f.toUFI (assembleInput n live lb deadBits) = b
        cases b <;> rfl
    obtain ⟨hdnf', hne', hnd', hbnd', heval'⟩ :=
      ProperizeProto.properize_narrow_dnf live.length hpos g₀ hg₀_dnf hg₀_bnd
    refine ⟨ProperizeProto.properizeDNF g₀, hbnd',
            fun h => by simp [hpfalse] at h, fun _ => ⟨hdnf', hne', hnd'⟩,
            fun h => by simp [hpfalse] at h, fun _ => ?_, ?_, ?_⟩
    · have hle := ProperizeProto.properizeDNF_width_le g₀ hg₀_dnf
      omega
    · -- circuit-size bound on the properized DNF
      have hnc_p := ProperizeProto.properizeDNF_circuit_size_le g₀
      have hsize := ProperizeProto.dnfSize_le_circuit_size g₀ hg₀_dnf
      have h_a : max 2 (dnfSize g₀) ≤ 2 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
        have hc : dnfSize g₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := le_trans hsize hg₀_nc
        omega
      have h_bw : max 1 (dnfWidth g₀) + 1 ≤ decisionTreeDepthBound + 2 := by omega
      calc ufiFormulaCircuitSize (ProperizeProto.properizeDNF g₀)
          ≤ 1 + max 2 (dnfSize g₀) := hnc_p
        _ ≤ 1 + max 2 (dnfSize g₀) * (max 1 (dnfWidth g₀) + 1) := by
              apply Nat.add_le_add_left
              calc max 2 (dnfSize g₀) = max 2 (dnfSize g₀) * 1 := by omega
                _ ≤ max 2 (dnfSize g₀) * (max 1 (dnfWidth g₀) + 1) :=
                  Nat.mul_le_mul_left _ (by omega)
        _ ≤ 1 + (2 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1)) * (decisionTreeDepthBound + 2) := by
              apply Nat.add_le_add_left
              exact Nat.mul_le_mul h_a h_bw
    · intro lb hlb
      exact (hg₀_eval lb hlb).trans (heval' lb hlb).symm

/-- **DNF view of a bottom formula.**  Maps a polarity-tagged
    `BottomFormula n` to a *proper DNF* `fv` of width `≤ f.width` whose
    evaluation is `f` itself (DNF bottom) or its negation (CNF bottom,
    via the De Morgan dual `exists_properDNF_dual_of_properCNF`).  This is
    exactly the `(fv, hfv)` data consumed by
    `exists_bottom_sub_proper_for_polarity`; the `fv` values also form the
    input list expected by `exists_switching_round_restriction`. -/
lemma exists_bottomFormula_dnf_view {n : Nat} (f : BottomFormula n) :
    ∃ (fv : UnboundedFanInProperDNF n),
      dnfWidth fv.val ≤ f.width ∧
      ∀ xs, xs.length = n → ufiFormulaEval fv.val xs =
        (if f.polarity then ufiFormulaEval f.toUFI xs
         else not (ufiFormulaEval f.toUFI xs)) := by
  cases f with
  | dnf g =>
    refine ⟨g, le_refl _, ?_⟩
    intro xs _
    simp only [BottomFormula.polarity, BottomFormula.toUFI, if_true]
  | cnf g =>
    obtain ⟨fd, hw, he⟩ := exists_properDNF_dual_of_properCNF g
    refine ⟨fd, ?_, ?_⟩
    · rw [hw]; exact le_refl _
    · intro xs hxs
      simp only [BottomFormula.polarity, BottomFormula.toUFI, Bool.false_eq_true,
        if_false]
      exact he xs hxs

/-- A single literal `inputGate x b` wrapped as a *proper* one-clause CNF
    `andGate [orGate [inputGate x b]]`. -/
def litToProperCNF (x : Nat) (b : Bool) : UnboundedFanInFormula :=
  .andGate [.orGate [.inputGate x b]]

/-- A single literal `inputGate x b` wrapped as a *proper* one-clause DNF
    `orGate [andGate [inputGate x b]]`. -/
def litToProperDNF (x : Nat) (b : Bool) : UnboundedFanInFormula :=
  .orGate [.andGate [.inputGate x b]]

/-- `litToProperCNF x b` is a proper CNF (single non-empty `Nodup` clause),
    keeps the input bound, and computes the literal `inputGate x b`.  This is the
    splice-level (`IsSubstitutionProperForm`, `needCnf = true`) representation of an
    `inputGate` leaf that appears as a child of a depth-3 `andGate`. -/
lemma litToProperCNF_spec (x : Nat) (b : Bool) (m : Nat) (hx : x < m) :
    isCNF (litToProperCNF x b) = true ∧
    (∀ c ∈ Circuits.CnfDnf.cnfClauses (litToProperCNF x b), c ≠ []) ∧
    (∀ c ∈ Circuits.CnfDnf.cnfClauses (litToProperCNF x b), (c.map Prod.fst).Nodup) ∧
    ufiLargestInput (litToProperCNF x b) < m ∧
    ∀ inputs, ufiFormulaEval (litToProperCNF x b) inputs =
      ufiFormulaEval (.inputGate x b) inputs := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [litToProperCNF, isCNF, isOrOfInputsOnly, isInput]
  · intro c hc
    simp only [litToProperCNF, Circuits.CnfDnf.cnfClauses, List.map_cons,
      List.map_nil, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hc
    subst hc; simp
  · intro c hc
    simp only [litToProperCNF, Circuits.CnfDnf.cnfClauses, List.map_cons,
      List.map_nil, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hc
    subst hc; simp
  · simp [litToProperCNF, ufiLargestInput, ufiCollectInputIndices, List.foldr_cons, List.foldr_nil, hx]
  · intro inputs
    cases hv : ufiFormulaEval (.inputGate x b) inputs <;>
      simp [litToProperCNF, ufiFormulaEval, hv]

/-- `litToProperDNF x b` is a proper DNF (single non-empty `Nodup` clause),
    keeps the input bound, and computes the literal `inputGate x b`.  This is the
    splice-level (`IsSubstitutionProperForm`, `needCnf = false`) representation of an
    `inputGate` leaf that appears as a child of a depth-3 `orGate`. -/
lemma litToProperDNF_spec (x : Nat) (b : Bool) (m : Nat) (hx : x < m) :
    isDNF (litToProperDNF x b) = true ∧
    (∀ c ∈ Circuits.CnfDnf.dnfClauses (litToProperDNF x b), c ≠ []) ∧
    (∀ c ∈ Circuits.CnfDnf.dnfClauses (litToProperDNF x b), (c.map Prod.fst).Nodup) ∧
    ufiLargestInput (litToProperDNF x b) < m ∧
    ∀ inputs, ufiFormulaEval (litToProperDNF x b) inputs =
      ufiFormulaEval (.inputGate x b) inputs := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [litToProperDNF, isDNF, isAndOfInputsOnly, isInput]
  · intro c hc
    simp only [litToProperDNF, Circuits.CnfDnf.dnfClauses, List.map_cons,
      List.map_nil, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hc
    subst hc; simp
  · intro c hc
    simp only [litToProperDNF, Circuits.CnfDnf.dnfClauses, List.map_cons,
      List.map_nil, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hc
    subst hc; simp
  · simp [litToProperDNF, ufiLargestInput, ufiCollectInputIndices, List.foldr_cons, List.foldr_nil, hx]
  · intro inputs
    cases hv : ufiFormulaEval (.inputGate x b) inputs <;>
      simp [litToProperDNF, ufiFormulaEval, hv]

/-- Producer leaf ingredient: a `sub` whose value at `i` is the
    proper one-clause CNF `litToProperCNF j b` satisfies the
    splice-base CNF requirement `IsSubstitutionProperForm sub true i`.  Used when
    a splice-base child (child of a depth-3 `andGate`) is an `inputGate`
    literal. -/
lemma isSubstitutionProperForm_litToProperCNF
    (sub : Nat → UnboundedFanInFormula) (i j : Nat) (b : Bool)
    (hsub : sub i = litToProperCNF j b) : IsSubstitutionProperForm sub true i := by
  obtain ⟨hcnf, hne, hnd, _, _⟩ := litToProperCNF_spec j b (j + 1) (Nat.lt_succ_self j)
  rw [IsSubstitutionProperForm]
  simp only [if_true]
  rw [hsub]
  exact ⟨hcnf, hne, hnd⟩

/-- Producer leaf ingredient: a `sub` whose value at `i` is the
    proper one-clause DNF `litToProperDNF j b` satisfies the
    splice-base DNF requirement `IsSubstitutionProperForm sub false i`.  Used when
    a splice-base child (child of a depth-3 `orGate`) is an `inputGate`
    literal. -/
lemma isSubstitutionProperForm_litToProperDNF
    (sub : Nat → UnboundedFanInFormula) (i j : Nat) (b : Bool)
    (hsub : sub i = litToProperDNF j b) : IsSubstitutionProperForm sub false i := by
  obtain ⟨hdnf, hne, hnd, _, _⟩ := litToProperDNF_spec j b (j + 1) (Nat.lt_succ_self j)
  rw [IsSubstitutionProperForm]
  simp only [Bool.false_eq_true, if_false]
  rw [hsub]
  exact ⟨hdnf, hne, hnd⟩

end Circuits.HastadParity
