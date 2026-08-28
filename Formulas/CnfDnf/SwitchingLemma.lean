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
import Lists.ListLemmas
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Formulas.CnfDnf.EncoderDecoder

namespace Circuits.CnfDnf.Restrictions
open Circuits.CnfDnf.Families
open DecisionTrees
open Lists.ListLemmas

section
set_option linter.style.setOption false
set_option linter.flexible false

-- ============================================================
-- §2.  Auxiliary arithmetic lemmas
-- ============================================================

private lemma totalRestrictionCount_pos (n : Nat) (σ : OpenUnitIntervalQ) :
    0 < totalRestrictionCount n σ := by
  unfold totalRestrictionCount
  simp only []
  exact_mod_cast Nat.mul_pos (Nat.choose_pos (ceil_sigma_n_le σ n))
    (pow_pos (by norm_num : (0 : ℕ) < 2) _)

private lemma multiset_countP_bind
    {α β : Type*} (s : Multiset α) (t : α → Multiset β) (p : β → Prop)
    [DecidablePred p] :
    (s.bind t).countP p = (s.map fun a => (t a).countP p).sum := by
  rw [Multiset.countP_eq_card_filter, Multiset.filter_bind, Multiset.card_bind]
  simp [Function.comp, Multiset.countP_eq_card_filter]

/-- `allBitLists k` has no duplicate entries. -/
private lemma allBitLists_nodup (k : Nat) : (allBitLists k).Nodup := by
  induction k with
  | zero => simp [allBitLists]
  | succ k ih =>
    -- allBitLists (k+1) = (allBitLists k).flatMap (fun l => [zero :: l, one :: l])
    change ((allBitLists k).map fun l => [false :: l, true :: l]).flatten.Nodup
    -- flatten ∘ map = flatMap
    change ((allBitLists k).flatMap fun l => [false :: l, true :: l]).Nodup
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro l _
      simp only [List.nodup_cons, List.mem_cons, or_false, List.not_mem_nil,
        List.nodup_nil, and_true]
      exact ⟨fun h => by simp [List.cons.injEq] at h, not_false⟩
    · apply ih.pairwise_of_forall_ne
      intro a _ b _ hab
      simp only [Function.onFun, List.Disjoint]
      intro x hx₁ hx₂
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx₁ hx₂
      rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
      · exact hab (by rw [List.cons.injEq] at h; exact h.2 ▸ rfl)
      · simp only [List.cons.injEq] at h; exact absurd h.1 (by decide)
      · simp only [List.cons.injEq] at h; exact absurd h.1 (by decide)
      · exact hab (by rw [List.cons.injEq] at h; exact h.2 ▸ rfl)

/-- When all clauses are empty `[]`, `canonicalDecisionTreeAuxPreciseFull`
    returns a leaf with depth 0. -/
private lemma canonicalDecisionTreeAuxPreciseFull_all_nil_depth
    (fuel : Nat) (clauses : List (List (Nat × Bool)))
    (hempty : ∀ c ∈ clauses, c = []) :
    decisionTreeDepth (canonicalDecisionTreeAuxPreciseFull fuel clauses) = 0 := by
  have key : ∀ cl : List (List (Nat × Bool)), (∀ c ∈ cl, c = ([] : List (Nat × Bool))) →
      ∀ f : Nat, ∃ b, canonicalDecisionTreeAuxPreciseFull f cl = .dtLeaf b := by
    intro cl hcl f
    induction cl with
    | nil =>
      cases f with
      | zero => exact ⟨.false, by simp [canonicalDecisionTreeAuxPreciseFull]⟩
      | succ n => exact ⟨.false, by simp [canonicalDecisionTreeAuxPreciseFull]⟩
    | cons head tail _ =>
      specialize hcl head List.mem_cons_self
      subst hcl; cases f with
      | zero => exact ⟨.false, by simp [canonicalDecisionTreeAuxPreciseFull]⟩
      | succ n =>
        -- clauseToPathTreeFull [] = .dtLeaf .one
        -- graftOnZeroLeavesWithSimplificationFull (.dtLeaf .one) _ _ = .dtLeaf .one
        exact ⟨.true, by simp [canonicalDecisionTreeAuxPreciseFull,
          clauseToPathTreeFull, graftOnZeroLeavesWithSimplificationFull]⟩
  obtain ⟨b, hb⟩ := key clauses hempty fuel
  simp [hb, decisionTreeDepth]

/-- Width-0 DNFs: all clauses of the restricted DNF are empty. -/
private lemma restrict_width_zero_clauses_nil
    (circuit : UnboundedFanInFormula) (hdnf : isDNF circuit = true)
    (hwidth : dnfWidth circuit ≤ 0) (asgn : Nat → Option Bool) :
    ∀ c ∈ dnfClauses (simpleRestrictDNF asgn circuit), c = [] := by
  intro c hc
  match circuit, hdnf with
  | .orGate gates, hdnf =>
    simp only [simpleRestrictDNF, dnfClauses] at hc
    rw [List.mem_map] at hc
    obtain ⟨gate, hgate_mem, rfl⟩ := hc
    rw [List.mem_filterMap] at hgate_mem
    obtain ⟨orig, horig_mem, hsome⟩ := hgate_mem
    have h_aoi : isAndOfInputsOnly orig = true := by
      simp only [isDNF, List.all_eq_true] at hdnf; exact hdnf orig horig_mem
    match orig, h_aoi with
    | .andGate lits, _ =>
      have hlits_nil : lits = [] := by
        apply List.eq_nil_of_length_eq_zero; apply Nat.le_zero.mp
        exact le_trans
          (mem_le_foldl_max (List.mem_map.mpr ⟨.andGate lits, horig_mem, rfl⟩))
          hwidth
      subst hlits_nil
      simp only [simpleRestrictTerm, List.map_nil, List.any_nil, List.filter_nil] at hsome
      -- hsome : gate = .andGate [] or .andGate [] = gate
      subst_eqs; rfl

/-- Width-0 proper DNFs produce no bad restrictions. -/
private lemma width_zero_not_bad
    (n d : Nat) (f : UnboundedFanInProperDNF n) (σ : OpenUnitIntervalQ)
    (ρ : AssignedRandomRestriction σ n)
    (hwidth : dnfWidth f.val ≤ 0) :
    isBadRestriction d n σ f ρ = false := by
  change decide (decisionTreeDepth
    (canonicalDecisionTree f.val
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)) > d) = false
  simp only [gt_iff_lt, decide_eq_false_iff_not, Nat.not_lt]
  suffices h : decisionTreeDepth
      (canonicalDecisionTree f.val
        (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)) = 0 by
    omega
  change decisionTreeDepth
    (canonicalDecisionTreeAuxPreciseFull _ _) = 0
  exact canonicalDecisionTreeAuxPreciseFull_all_nil_depth _ _
    (restrict_width_zero_clauses_nil f.val f.property.2.1 hwidth _)

/-- The full-query canonical DT depth is at most |S|. -/
private lemma precise_dt_depth_le_live_card
    (n : Nat) (f : UnboundedFanInProperDNF n)
    (S : Finset Nat) (h_s : S ⊆ Finset.range n)
    (bits : List Bool) (hlen : S.card + bits.length = n) :
    decisionTreeDepth
      (canonicalDecisionTree f.val
        (mkAssignmentList S bits n)) ≤ S.card := by
  by_contra h_gt
  push Not at h_gt
  set β := mkAssignmentList S bits n with hβ_def
  set dt := canonicalDecisionTree f.val β
    with hdt_def
  have his := leftmostPathExceedingDepth_depth_gt_imp_isSome dt S.card h_gt
  obtain ⟨path, hpath_eq⟩ := Option.isSome_iff_exists.mp his
  have hpath_len := leftmostPathExceedingDepth_some_path_length_gt
    dt S.card path hpath_eq
  have hdi := canonicalDecisionTreeAuxPreciseFull_disjoint
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction β) f.val)).length
    (dnfClauses (simpleRestrictDNF
      (restrictionAsFunction β) f.val))
    (restrictDNF_preserves_clause_nodup f.val
      (restrictionAsFunction β) f.property.2.2.2)
  have hnodup_path := leftmostPathExceedingDepth_nodup_of_disjoint
    dt S.card hdi path (hdt_def ▸ hpath_eq)
  have hpath_in_s : ∀ v ∈ path.map Prod.fst, v ∈ S := by
    intro v hv_mem
    obtain ⟨⟨w, b⟩, hwmem, rfl⟩ := List.mem_map.mp hv_mem
    have hasgn_fn_none :=
      canonical_dt_path_var_none
        f.val β f.property.2.1 S.card path hpath_eq w b hwmem
    have hw_in_dt := leftmostPathExceedingDepth_vars_in_collect
      dt S.card path hpath_eq w b hwmem
    simp only [dt, canonicalDecisionTree] at hw_in_dt
    obtain ⟨c, hc_mem, hw_in_c⟩ :=
      canonicalDecisionTreeAuxPreciseFull_vars_in
        (dnfClauses (simpleRestrictDNF
          (restrictionAsFunction β) f.val)).length
        _ w hw_in_dt
    have hv_vars : w ∈ canonicalDTVarOrder
        (simpleRestrictDNF (restrictionAsFunction β) f.val) := by
      rw [canonicalDTVarOrder, mem_dedupFirst]
      exact List.mem_flatMap.mpr ⟨c, hc_mem, hw_in_c⟩
    have hv_inp := canonicalDTVarOrder_subset_inputs
      (simpleRestrictDNF (restrictionAsFunction β) f.val)
      (restrictDNF_preserves_dnf (restrictionAsFunction β)
        f.val f.property.2.1) w hv_vars
    have hv_orig := (restrictDNF_preserves_valid_inputs
      (restrictionAsFunction β) f.val f.property.2.1 w
      (List.mem_dedup.mpr hv_inp)).1
    have hw_lt_n : w < n :=
      Nat.lt_of_le_of_lt (adder_foldr_max_ge_of_mem (List.mem_dedup.mp hv_orig)) f.property.1
    have hasgn_none : mkAssignment S bits w = none := by
      rw [← cr_none_mkAssignmentList_eq S bits n w hw_lt_n]
      exact hasgn_fn_none
    exact mkAssignment_none_imp_mem S bits n h_s hlen w hw_lt_n hasgn_none
  have hsub : (path.map Prod.fst).toFinset ⊆ S := by
    intro v hv; exact hpath_in_s v (List.mem_toFinset.mp hv)
  have hcard_le := Finset.card_le_card hsub
  rw [List.card_toFinset, hnodup_path.dedup, List.length_map] at hcard_le
  omega

/-- **Razborov injection bound**: The number of bad restrictions is at most
    C(n, s−d) · (4w)^d · 2^(n−(s−d)).

    For each bad (S, b), the Beame-style encoding finds d variables J ⊆ S
    and records d (position, γ-bit) pairs as advice.
    The map (S, b) ↦ (S \ J, b, advice) with advice ∈ [(4w)]^d maps into
    a target set of size C(n,s−d) · (4w)^d · 2^(n−(s−d)).

    Combined with the binomial-ratio estimate
    `C(n,s−d) ≤ (5σ)^d · C(n,s)`, this gives
    `(40σw)^d · total` in the `ceil(σn)` model. -/
private lemma injection_bound
    (n w d : Nat) (f : UnboundedFanInProperDNF n)
    (hwidth : dnfWidth f.val ≤ w)
    (σ : OpenUnitIntervalQ)
    (hsd : d < Nat.ceil (σ.val * ↑n)) :
    badRestrictionCount n d f σ ≤
      ↑(Nat.choose n (Nat.ceil (σ.val * ↑n) - d) * (4 * w) ^ d
      * 2 ^ (n - (Nat.ceil (σ.val * ↑n) - d))) := by
  set s := Nat.ceil (σ.val * ↑n) with hs_def
  have hsn : s ≤ n := ceil_sigma_n_le σ n
  set F := (Finset.range n).powersetCard s
  set m := n - s with hm_def
  -- Step 1: Reduce the inequality to one about the ℕ-valued attach.sum
  -- The bad-restriction count is ↑(F.attach.sum countP) : ℚ.
  -- We prove the ℕ inequality and close via Nat.cast_le
  suffices h_nat : F.attach.sum (fun ⟨S, h_smem⟩ =>
      let h_s := Finset.mem_powersetCard.mp h_smem
      (allBitLists m).countP fun bits =>
        if h : S.card + bits.length = n then
          isBadRestriction d n σ f {
            starAssignment := ⟨⟨S, h_s.1⟩, h_s.2⟩
            varAssignments := bits
            non_starred_vars_fully_assigned := h
          }
        else false) ≤ Nat.choose n (s - d) * (4 * w) ^ d * 2 ^ (n - (s - d)) by
    -- The count is definitionally ↑(the_sum), so the goal is ↑a ≤ ↑b.
    -- After rw, Lean normalizes ↑(∑ f) → ∑ ↑f. We fold it back with map_sum.
    let g : { S // S ∈ F } → ℕ := fun ⟨S, h_smem⟩ =>
      let h_s := Finset.mem_powersetCard.mp h_smem
      (allBitLists m).countP fun bits =>
        if h : S.card + bits.length = n then
          isBadRestriction d n σ f {
            starAssignment := ⟨⟨S, h_s.1⟩, h_s.2⟩
            varAssignments := bits
            non_starred_vars_fully_assigned := h
          }
        else false
    have fold : F.attach.sum (fun x => (↑(g x) : ℚ)) = ↑(F.attach.sum g) :=
      (map_sum (Nat.castRingHom ℚ) g F.attach).symm
    rw [show badRestrictionCount n d f σ =
        F.attach.sum (fun x => (↑(g x) : ℚ)) from by
      unfold badRestrictionCount generateAllRestrictions
      rw [multiset_countP_bind, Nat.cast_multiset_sum, Multiset.map_map]
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro S h_s_mem
      cases S with
      | mk S h_smem =>
      simp only [Function.comp_apply, Multiset.coe_countP, List.countP_map, g]
      norm_cast
      rw [← List.countP_attach (l := allBitLists m)
        (p := fun bits =>
          if h : S.card + bits.length = n then
            isBadRestriction d n σ f {
              starAssignment := ⟨⟨S, (Finset.mem_powersetCard.mp h_smem).1⟩,
                (Finset.mem_powersetCard.mp h_smem).2⟩
              varAssignments := bits
              non_starred_vars_fully_assigned := h
            }
          else false)]
      apply List.countP_congr
      intro bits hbits
      have h_s_card : S.card = s := (Finset.mem_powersetCard.mp h_smem).2
      have hbits_len : (bits : List Bool).length = m :=
        allBitLists_mem_length _ _ bits.property
      have hlen : S.card + (bits : List Bool).length = n := by
        rw [h_s_card, hbits_len, hm_def]
        exact Nat.add_sub_of_le hsn
      simp [hlen], fold]
    exact_mod_cast h_nat
  -- Step 2: Handle w = 0 edge case
  by_cases hw : w = 0
  · subst hw
    -- With width 0, no restriction is bad, so the sum is 0
    suffices h : F.attach.sum (fun ⟨S, h_smem⟩ =>
        let h_s := Finset.mem_powersetCard.mp h_smem
        (allBitLists m).countP fun bits =>
          if h : S.card + bits.length = n then
            isBadRestriction d n σ f
              ⟨⟨⟨S, h_s.1⟩, h_s.2⟩, bits, h⟩
          else false) = 0 by
      rw [h]; exact Nat.zero_le _
    apply Finset.sum_eq_zero
    intro ⟨S, h_smem⟩ _
    rw [List.countP_eq_zero]
    intro bits _ h_abs
    split at h_abs
    · -- S.card + bits.length = n holds
      rename_i h
      have hnotbad := width_zero_not_bad n d f σ
        ⟨⟨⟨S, (Finset.mem_powersetCard.mp h_smem).1⟩,
          (Finset.mem_powersetCard.mp h_smem).2⟩, bits, h⟩ hwidth
      rw [hnotbad] at h_abs; exact absurd h_abs (by decide)
    · exact absurd h_abs (by decide)
  · -- Main case: w > 0
    have hw_pos : 0 < w := Nat.pos_of_ne_zero hw
    -- Step 3: Define standalone bad-pair predicate (independent of membership proof)
    let bad_pred : Finset Nat → List Bool → Bool := fun S bits =>
      if h_s_sub : S ⊆ Finset.range n then
        if h_s_card : S.card = s then
          if h : S.card + bits.length = n then
            isBadRestriction d n σ f ⟨⟨⟨S, h_s_sub⟩, h_s_card⟩, bits, h⟩
          else false
        else false
      else false
    -- Step 4: Rewrite the attach.sum as a plain sum over F
    have hpred_eq : ∀ S (h_smem : S ∈ F),
        (allBitLists m).countP (fun bits =>
          if h : S.card + bits.length = n then
            isBadRestriction d n σ f
              ⟨⟨⟨S, (Finset.mem_powersetCard.mp h_smem).1⟩,
              (Finset.mem_powersetCard.mp h_smem).2⟩, bits, h⟩
          else false) =
        (allBitLists m).countP (bad_pred S) := by
      intro S h_smem
      congr 1; ext bits; simp only [bad_pred]
      have h_s := Finset.mem_powersetCard.mp h_smem
      simp [h_s.1, h_s.2]
    have hsum_eq : F.attach.sum (fun ⟨S, h_smem⟩ =>
        let h_s := Finset.mem_powersetCard.mp h_smem
        (allBitLists m).countP (fun bits =>
          if h : S.card + bits.length = n then
            isBadRestriction d n σ f
              ⟨⟨⟨S, h_s.1⟩, h_s.2⟩, bits, h⟩
          else false)) =
      F.sum (fun S => (allBitLists m).countP (bad_pred S)) := by
      conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro ⟨S, h_smem⟩ _
      exact hpred_eq S h_smem
    rw [hsum_eq]
    -- Step 5: Build sigma Finset D and show D.card = the sum
    set D := F.sigma (fun S => ((allBitLists m).filter (bad_pred S)).toFinset)
    have h_d_eq_sum : D.card = F.sum (fun S => (allBitLists m).countP (bad_pred S)) := by
      rw [Finset.card_sigma]
      exact Finset.sum_congr rfl (fun S _ => by
        have hnd := (allBitLists_nodup m).filter (bad_pred S)
        rw [List.card_toFinset, hnd.dedup, List.countP_eq_length_filter])
    rw [← h_d_eq_sum]
    -- Step 6: Build injection φ : D → injectionTargetSet and conclude
    -- Helper: extract membership data from sigma membership
    have h_d_mem_data : ∀ x : (Σ _ : Finset Nat, List Bool), x ∈ D →
        x.1 ⊆ Finset.range n ∧ x.1.card = s ∧
        x.2 ∈ allBitLists m ∧ bad_pred x.1 x.2 = true := by
      intro ⟨S, bits⟩ hx
      rw [Finset.mem_sigma] at hx
      have h_smem := Finset.mem_powersetCard.mp hx.1
      have hbits := List.mem_toFinset.mp hx.2
      rw [List.mem_filter] at hbits
      exact ⟨h_smem.1, h_smem.2, hbits.1, hbits.2⟩
    -- Helper: extract bad_pred as the structured bad-restriction predicate.
    have hbad_pred_iff : ∀ S bits (h_s_sub : S ⊆ Finset.range n)
        (h_s_card : S.card = s) (h : S.card + bits.length = n),
        bad_pred S bits = true →
        isBadRestriction d n σ f
          ⟨⟨⟨S, h_s_sub⟩, h_s_card⟩, bits, h⟩ = true := by
      intro S bits h_s_sub h_s_card h hbp
      simp only [bad_pred, h_s_sub, h_s_card, dite_true] at hbp
      have h' : s + bits.length = n := by omega
      simp only [h', dite_true] at hbp
      change decide
        (decisionTreeDepth
          (canonicalDecisionTree f.val
            (mkAssignmentList S bits n)) > d) = true
      exact hbp
    -- Define the injection map φ via beameEncoderMap.
    -- This map uses `isBadRestriction` directly.
    let φ : (Σ _ : Finset Nat, List Bool) → Finset Nat × Nat × Nat := fun ⟨S, bits⟩ =>
      if h_s_sub : S ⊆ Finset.range n then
        if h_s_card : S.card = s then
          if h : s + bits.length = n then
            have hbits_len : S.card + bits.length = n := by rw [h_s_card]; exact h
            if hbad : isBadRestriction d n σ f
                ⟨⟨⟨S, h_s_sub⟩, h_s_card⟩, bits, hbits_len⟩ = true then
              (beameEncoderMap d n f w hwidth hw_pos σ hsd
                S h_s_sub h_s_card bits hbits_len hbad).val
            else (∅, 0, 0)
          else (∅, 0, 0)
        else (∅, 0, 0)
      else (∅, 0, 0)
    rw [← injection_target_card]
    apply Finset.card_le_card_of_injOn φ
    · -- MapsTo: φ maps D into injectionTargetSet n s d w
      intro ⟨S, bits⟩ hx
      obtain ⟨h_s_sub, h_s_card, _, hbp⟩ := h_d_mem_data ⟨S, bits⟩ hx
      have hbits_len : S.card + bits.length = n := by
        have hbl := allBitLists_mem_length m bits (h_d_mem_data ⟨S, bits⟩ hx).2.2.1
        rw [h_s_card, hbl, hm_def]; omega
      have hbad := hbad_pred_iff S bits h_s_sub h_s_card hbits_len hbp
      have hbits_len' : s + bits.length = n := by rw [← h_s_card]; exact hbits_len
      simp only [φ, h_s_sub, h_s_card, hbits_len', dite_true, hbad]
      exact (beameEncoderMap d n f w hwidth hw_pos σ hsd
        S h_s_sub h_s_card bits hbits_len hbad).property
    · -- InjOn: φ is injective on D
      intro ⟨S₁, bits₁⟩ h1 ⟨S₂, bits₂⟩ h2 hφ_eq
      obtain ⟨h_s1_sub, h_s1_card, _, hbp1⟩ := h_d_mem_data ⟨S₁, bits₁⟩ h1
      obtain ⟨h_s2_sub, h_s2_card, _, hbp2⟩ := h_d_mem_data ⟨S₂, bits₂⟩ h2
      have hbl1 : S₁.card + bits₁.length = n := by
        have := allBitLists_mem_length m bits₁ (h_d_mem_data ⟨S₁, bits₁⟩ h1).2.2.1
        rw [h_s1_card, this, hm_def]; omega
      have hbl2 : S₂.card + bits₂.length = n := by
        have := allBitLists_mem_length m bits₂ (h_d_mem_data ⟨S₂, bits₂⟩ h2).2.2.1
        rw [h_s2_card, this, hm_def]; omega
      have hbad1 := hbad_pred_iff S₁ bits₁ h_s1_sub h_s1_card hbl1 hbp1
      have hbad2 := hbad_pred_iff S₂ bits₂ h_s2_sub h_s2_card hbl2 hbp2
      have hbl1' : s + bits₁.length = n := by rw [← h_s1_card]; exact hbl1
      have hbl2' : s + bits₂.length = n := by rw [← h_s2_card]; exact hbl2
      -- Simplify φ on both sides using the membership data
      simp only [φ, h_s1_sub, h_s1_card, hbl1', dite_true, hbad1,
        h_s2_sub, h_s2_card, hbl2', hbad2] at hφ_eq
      -- hφ_eq now says the two beameEncoderMap outputs are equal.
      -- Use roundtrip: decode ∘ encode = id to conclude (S₁, bits₁) = (S₂, bits₂).
      have hrt1 :=
        beame_encoder_decoder_injection_roundtrip
          d n f w hwidth hw_pos σ hsd
          S₁ h_s1_sub h_s1_card bits₁ hbl1 hbad1
      have hrt2 :=
        beame_encoder_decoder_injection_roundtrip
          d n f w hwidth hw_pos σ hsd
          S₂ h_s2_sub h_s2_card bits₂ hbl2 hbad2
      dsimp only [] at hrt1 hrt2
      let decode_triple := fun (t : Finset Nat × Nat × Nat) =>
        beameDecoderMap d n f w σ t.1 t.2.1 t.2.2
      have h_decoder : decode_triple
          (beameEncoderMap d n f w hwidth hw_pos σ hsd
            S₁ h_s1_sub h_s1_card bits₁ hbl1 hbad1).val =
        decode_triple
          (beameEncoderMap d n f w hwidth hw_pos σ hsd
            S₂ h_s2_sub h_s2_card bits₂ hbl2 hbad2).val :=
        congr_arg decode_triple hφ_eq
      have hpair : (S₁, bits₁) = (S₂, bits₂) :=
        hrt1.symm.trans (h_decoder.trans hrt2)
      exact Sigma.ext (congr_arg Prod.fst hpair)
        (heq_of_eq (congr_arg Prod.snd hpair))

/-- Binomial-ratio bound for the exact-size presentation where the live-set
    size is exactly `s = σ n`.

    In this model
    `C(n,s-d)/C(n,s) ≤ (σ/(1-σ))^d ≤ ((5/4)σ)^d`
    for `σ ≤ 1/5`. -/
private lemma choose_ratio_bound_exact (n s d : Nat) (σ : OpenUnitIntervalQ)
    (hσ : σ.val ≤ 1 / 5)
    (hs_exact : (s : ℚ) = σ.val * ↑n)
    (hsd : d < s) (hsn : s ≤ n) :
    (Nat.choose n (s - d) : ℚ) ≤ ((5 / 4) * σ.val) ^ d * Nat.choose n s := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hsd' : d < s := by omega
    suffices hstep : (Nat.choose n (s - (d + 1)) : ℚ) ≤
        (5 / 4) * σ.val * Nat.choose n (s - d) by
      calc (Nat.choose n (s - (d + 1)) : ℚ)
          ≤ (5 / 4) * σ.val * Nat.choose n (s - d) := hstep
        _ ≤ (5 / 4) * σ.val *
              (((5 / 4) * σ.val) ^ d * Nat.choose n s) := by
            gcongr
            · exact le_of_lt (mul_pos (by norm_num : (0 : ℚ) < 5 / 4) σ.property.1)
            · exact ih hsd'
        _ = ((5 / 4) * σ.val) ^ (d + 1) * Nat.choose n s := by ring
    have hsd1 : s - (d + 1) = s - d - 1 := by omega
    rw [hsd1]
    have hk_eq : s - d - 1 + 1 = s - d := by omega
    have hn_sub : n - (s - d - 1) = n - s + d + 1 := by omega
    have hident := Nat.choose_succ_right_eq n (s - d - 1)
    rw [hk_eq, hn_sub] at hident
    have hdenom_pos : (0 : ℚ) < ↑(n - s + d + 1) := by positivity
    have hident_q : (Nat.choose n (s - d) : ℚ) * ↑(s - d) =
        ↑(Nat.choose n (s - d - 1)) * ↑(n - s + d + 1) := by
      exact_mod_cast hident
    rw [show (Nat.choose n (s - d - 1) : ℚ) =
        ↑(Nat.choose n (s - d)) * ↑(s - d) / ↑(n - s + d + 1) from by
      rw [eq_div_iff (ne_of_gt hdenom_pos)]; linarith [hident_q]]
    have hchoose_pos : (0 : ℚ) < ↑(Nat.choose n (s - d)) := by
      exact_mod_cast Nat.choose_pos (by omega : s - d ≤ n)
    rw [div_le_iff₀ hdenom_pos, ← sub_nonneg]
    rw [show ((5 / 4) * σ.val * ↑(Nat.choose n (s - d)) * ↑(n - s + d + 1) -
        ↑(Nat.choose n (s - d)) * ↑(s - d) =
        ↑(Nat.choose n (s - d)) *
          ((5 / 4) * σ.val * ↑(n - s + d + 1) - ↑(s - d))) by ring]
    apply mul_nonneg (le_of_lt hchoose_pos)
    have hσ_pos : 0 < σ.val := σ.property.1
    have hsd_le_s : (↑(s - d) : ℚ) ≤ s := by
      exact_mod_cast (show s - d ≤ s from by omega)
    calc (0 : ℚ)
        ≤ (5 / 4) * σ.val * ↑(n - s + d + 1) - ↑s := by
            have hcast : (↑(n - s + d + 1) : ℚ) = ↑n - ↑s + ↑d + 1 := by
              rw [show n - s + d + 1 = n - s + (d + 1) from by omega]
              push_cast
              rw [Nat.cast_sub hsn]
              ring
            rw [hcast, hs_exact]
            nlinarith [hσ, hσ_pos, sq_nonneg σ.val]
      _ ≤ (5 / 4) * σ.val * ↑(n - s + d + 1) - ↑(s - d) := by
            linarith [hsd_le_s]

/-- Exact-size variant matching O'Donnell's lecture-note constant.  The extra
    hypothesis says the repository's `ceil(σn)` live-set size has no rounding
    loss, so the sharper ratio
    `C(n,s-d)/C(n,s) ≤ ((5/4)σ)^d` is available. -/
private lemma badRestrictionCount_le_exact
    (n w d : Nat) (f : UnboundedFanInProperDNF n)
    (hwidth : dnfWidth f.val ≤ w)
    (σ : OpenUnitIntervalQ) (hσ : σ.val ≤ 1 / 5)
    (hs_exact : (Nat.ceil (σ.val * ↑n) : ℚ) = σ.val * ↑n) :
    badRestrictionCount n d f σ ≤
      (10 * σ.val * ↑w) ^ d * totalRestrictionCount n σ := by
  set s := Nat.ceil (σ.val * ↑n) with hs_def
  by_cases hσw : 1 ≤ 10 * σ.val * ↑w
  · unfold badRestrictionCount
    calc (↑((generateAllRestrictions n σ).countP fun ρ =>
            isBadRestriction d n σ f ρ) : ℚ)
        ≤ ↑(generateAllRestrictions n σ).card := by
            exact_mod_cast (Multiset.countP_le_card
              (fun ρ => isBadRestriction d n σ f ρ = true)
              (generateAllRestrictions n σ))
      _ = totalRestrictionCount n σ := by
            unfold generateAllRestrictions totalRestrictionCount
            rw [Multiset.card_bind]
            simp [allBitLists_length]
            refine Multiset.card_attach.trans ?_
            change ((Finset.range n).powersetCard
              (Nat.ceil (σ.val * ↑n))).card =
                Nat.choose n (Nat.ceil (σ.val * ↑n))
            rw [Finset.card_powersetCard, Finset.card_range]
      _ ≤ (10 * σ.val * ↑w) ^ d * totalRestrictionCount n σ :=
            le_mul_of_one_le_left (le_of_lt (totalRestrictionCount_pos n σ))
              (one_le_pow₀ hσw)
  · push Not at hσw
    have hrhs_nonneg : 0 ≤ (10 * σ.val * ↑w) ^ d * totalRestrictionCount n σ :=
      mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_of_lt σ.property.1))
        (Nat.cast_nonneg w)) d) (le_of_lt (totalRestrictionCount_pos n σ))
    by_cases hsd : s ≤ d
    · have hgood : ∀ (ρ : AssignedRandomRestriction σ n),
          isBadRestriction d n σ f ρ = false := by
        intro ρ
        simp only [isBadRestriction, gt_iff_lt,
          decide_eq_false_iff_not, Nat.not_lt]
        calc decisionTreeDepth
              (canonicalDecisionTree f.val
                (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n))
            ≤ ρ.starAssignment.val.val.card :=
              precise_dt_depth_le_live_card n f
                ρ.starAssignment.val.val
                ρ.starAssignment.val.property
                ρ.varAssignments
                ρ.non_starred_vars_fully_assigned
          _ = s := ρ.starAssignment.property
          _ ≤ d := hsd
      suffices h : badRestrictionCount n d f σ = 0 by rw [h]; exact hrhs_nonneg
      unfold badRestrictionCount
      norm_cast
      apply Multiset.countP_eq_zero.mpr
      intro ρ _ hbad
      rw [hgood ρ] at hbad
      exact absurd hbad (by decide)
    · push Not at hsd
      have hsn : s ≤ n := ceil_sigma_n_le σ n
      have hinj := injection_bound n w d f hwidth σ hsd
      have hratio := choose_ratio_bound_exact n s d σ hσ (by simpa [hs_def] using hs_exact) hsd hsn
      calc badRestrictionCount n d f σ
          ≤ ↑(Nat.choose n (s - d) * (4 * w) ^ d * 2 ^ (n - (s - d))) := by
              simpa [hs_def] using hinj
        _ = ↑(Nat.choose n (s - d)) * ↑((4 * w) ^ d) * ↑(2 ^ (n - (s - d))) := by
            push_cast; ring
        _ ≤ (((5 / 4) * σ.val) ^ d * ↑(Nat.choose n s)) * ↑((4 * w) ^ d) *
              ↑(2 ^ (n - (s - d))) := by
            gcongr
        _ = (10 * σ.val * ↑w) ^ d * totalRestrictionCount n σ := by
            suffices h : ∀ (a c : ℚ) (b : ℕ),
                ((5 / 4) * a) ^ d * c * (4 * b) ^ d * (2 : ℚ) ^ (n - (s - d)) =
                (10 * a * b) ^ d * (c * 2 ^ (n - s)) by
              unfold totalRestrictionCount; simp only [← hs_def]
              push_cast; exact h _ _ _
            intro a c b
            have h2d : (2 : ℚ) ^ (n - (s - d)) = 2 ^ d * 2 ^ (n - s) := by
              rw [← pow_add]; congr 1; omega
            rw [h2d]
            rw [show (10 : ℚ) * a * ↑b = ((5 / 4) * a) * (4 * ↑b) * 2 from by ring]
            rw [mul_pow (((5 / 4) * a) * (4 * ↑b)) 2 d,
              mul_pow ((5 / 4) * a) (4 * ↑b) d]
            ring

private lemma generateAllRestrictions_card (n : Nat) (σ : OpenUnitIntervalQ) :
    (generateAllRestrictions n σ).card =
      Nat.choose n (Nat.ceil (σ.val * ↑n)) *
        2 ^ (n - Nat.ceil (σ.val * ↑n)) := by
  unfold generateAllRestrictions
  rw [Multiset.card_bind]
  simp_rw [Function.comp_apply, Multiset.coe_card, List.length_map,
    List.length_attach, allBitLists_length]
  simp only [Multiset.map_const', Multiset.sum_replicate]
  change ((Finset.range n).powersetCard (Nat.ceil (σ.val * ↑n))).attach.card *
    2 ^ (n - Nat.ceil (σ.val * ↑n)) = _
  rw [Finset.card_attach, Finset.card_powersetCard, Finset.card_range]

lemma generateAllRestrictions_card_eq_totalRestrictionCount (n : Nat) (σ : OpenUnitIntervalQ) :
    (generateAllRestrictions n σ).card = totalRestrictionCount n σ :=
by
  rw [generateAllRestrictions_card]
  unfold totalRestrictionCount
  simp

-- ============================================================
-- §4.  Main theorem
-- ============================================================

/-- Exact-size version of Håstad's Switching Lemma, matching the constant in
    O'Donnell's lecture notes.  The existing restriction model chooses exactly
    `ceil(σn)` live variables; the extra hypothesis `hs_exact` says this equals
    `σn`, so the lecture-note ratio calculation applies without ceiling loss. -/
theorem switching_lemma_exact
    (n w d : Nat)
    (f : UnboundedFanInProperDNF n)
    (hwidth : dnfWidth f.val ≤ w)
    (σ : OpenUnitIntervalQ)
    (hσ : σ.val ≤ 1 / 5)
    (hs_exact : (Nat.ceil (σ.val * n) : ℚ) = σ.val * n) :
    (badRestrictionCount n d f σ) / (totalRestrictionCount n σ)
      ≤ (10 * σ.val * w) ^ d := by
  rw [div_le_iff₀ (totalRestrictionCount_pos n σ)]
  exact badRestrictionCount_le_exact n w d f hwidth σ hσ hs_exact

end -- section for set_option

end Circuits.CnfDnf.Restrictions
