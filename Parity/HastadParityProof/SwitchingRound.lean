/-
  Counting and pigeonhole lemmas for one switching round.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.BottomLayer

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-! The parity-only input assembly and restriction lemmas are provided by
    `Parity.ParityProperties`. -/

/-! ### Generic counting helpers for the switching-round union bound -/

lemma list_sum_map_ratCast {α : Type*} (l : List α) (g : α → ℕ) :
    ((l.map (fun a => ((g a : ℕ) : ℚ))).sum : ℚ) = (((l.map g).sum : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    ring

/-! ### Restriction to a narrow DNF

    The switching development constructs a good restriction that collapses
    an AC0 circuit to a narrow DNF on the live variables.

    This is the analytical heart: it bundles together
      - choosing per-layer survival probabilities σ₁,…,σ_{d−1}
        small enough that the switching-lemma bound (40σw)^d < 1 holds
        with room to spare across a union bound over the (at most
        polynomially many) depth-2 subcircuits, AND
      - extracting a *deterministic* witness restriction from the
        pigeonhole / probabilistic existence argument.

    The shape below is intentionally minimal: we only commit to
    existence of a width-`w` DNF on the live bits that agrees with `F`
    on every input compatible with the restriction.

    ### Main components

    The proof uses the following named lemmas:

      * `exists_switching_lemma_pigeonhole_exact` converts the exact-size
          ratio-bound of `switching_lemma_exact` into a deterministic
          existence statement for a *single* DNF when `(10σw)^d < 1`
          and `ceil(σn) = σn` (no random witness is needed: at least
          one of the finitely many restrictions is good).

      * `exists_switching_lemma_pigeonhole_list` is the union-bound version
          for a list of DNFs all on the same `n` variables.
          Used to simultaneously make every depth-2 subcircuit shrink
          under a single restriction.

      * `exists_iterated_switching_depth_collapse` is the inductive heart
          of the state-based iterated switching argument.
          Given a depth-`d` UFI formula on `n` variables of circuit-size
          ≤ `s`, choose σ₁,…,σ_{d−1} so that the iterated bound
          collapses, using the list union bound at each round, and exhibit
          a deterministic sequence of restrictions
          whose composition yields a width-`w` DNF on the live
          variables with `w < live.length` and `2 ≤ live.length`.

      The input-size requirements are carried explicitly by the switching
      round's threshold hypotheses and discharged by the upstream parameter
      lemmas; no separate asymptotic threshold adapter is needed here.

    Upstream parameter lemmas supply the threshold hypotheses consumed by
    the iterated collapse theorem. -/

/-- Exact-size switching-lemma pigeonhole result with the improved
    `(10·σ·w)^d` bound when `ceil(σn) = σn`. -/
lemma exists_switching_lemma_pigeonhole_exact
    {n : Nat} (w d : Nat) (f : UnboundedFanInProperDNF n)
    (hwidth : dnfWidth f.val ≤ w)
    (σ : OpenUnitIntervalQ) (hσ : σ.val ≤ 1 / 5)
    (hs_exact : (Nat.ceil (σ.val * (n : ℚ)) : ℚ) = σ.val * (n : ℚ))
    (hbound : (10 * σ.val * (w : ℚ)) ^ d < 1) :
    ∃ ρ : AssignedRandomRestriction σ n,
      ¬ isBadRestriction d n σ f ρ := by
  by_contra hall
  push Not at hall
  set s := Nat.ceil (σ.val * (n : ℚ)) with hs_def
  have hsn : s ≤ n := ceil_sigma_n_le σ n
  have h_inner :
      ∀ (starSet : Finset Nat) (h_star_set_mem : starSet ∈ (Finset.range n).powersetCard s),
        ((allBitLists (n - s)).countP fun bits =>
          if h : starSet.card + bits.length = n then
            isBadRestriction d n σ f
              { starAssignment :=
                  ⟨⟨starSet, (Finset.mem_powersetCard.mp h_star_set_mem).1⟩,
                    (Finset.mem_powersetCard.mp h_star_set_mem).2⟩
                varAssignments := bits
                non_starred_vars_fully_assigned := h }
          else false)
        = 2 ^ (n - s) := by
    intro starSet h_star_set_mem
    have h_star_set_card : starSet.card = s := (Finset.mem_powersetCard.mp h_star_set_mem).2
    rw [List.countP_eq_length.mpr ?_, allBitLists_length]
    intro bits hbits
    have hbits_len : bits.length = n - s := allBitLists_mem_length (n - s) bits hbits
    have hsum : starSet.card + bits.length = n := by
      rw [h_star_set_card, hbits_len]; omega
    simp only [hsum, dif_pos]
    exact hall _
  have h_eq_total :
      badRestrictionCount n d f σ = totalRestrictionCount n σ := by
    unfold badRestrictionCount
    rw [Multiset.countP_eq_card.mpr]
    · exact_mod_cast generateAllRestrictions_card_eq_totalRestrictionCount n σ
    · intro ρ hρ
      exact hall ρ
  have hsw := switching_lemma_exact n w d f hwidth σ hσ hs_exact
  rw [h_eq_total] at hsw
  have htotal_pos : 0 < totalRestrictionCount n σ := by
    unfold totalRestrictionCount
    simp only [← hs_def]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hsn)
      (pow_pos (by norm_num : (0:ℕ) < 2) _)
  rw [div_self (ne_of_gt htotal_pos)] at hsw
  exact absurd (lt_of_le_of_lt hsw hbound) (lt_irrefl 1)

/-- Union-bound version of `exists_switching_lemma_pigeonhole_exact`: a single deterministic
    restriction simultaneously avoids the bad set of every DNF in the
    list, provided the aggregated analytic bound is below `1`.

    The factor `fs.length` counts the depth-2 subcircuits we need to
    control simultaneously, and equals the number of "second-from-bottom"
    gates of the AC0 formula in the application below. -/
lemma exists_switching_lemma_pigeonhole_list
    {n : Nat} (w d : Nat) (fs : List (UnboundedFanInProperDNF n))
    (hwidth : ∀ f ∈ fs, dnfWidth f.val ≤ w)
    (σ : OpenUnitIntervalQ) (hσ : σ.val ≤ 1 / 5)
    (hs_exact : (Nat.ceil (σ.val * (n : ℚ)) : ℚ) = σ.val * (n : ℚ))
    (hbound : (fs.length : ℚ) * (10 * σ.val * (w : ℚ)) ^ d < 1) :
    ∃ ρ : AssignedRandomRestriction σ n,
      ∀ f ∈ fs, ¬ isBadRestriction d n σ f ρ := by
  -- Proof strategy:
  -- (i)  Aggregate bound: each f contributes at most (10σw)^d · total
  --      bad restrictions, so the *list-sum* of bad counts is at most
  --      `fs.length · (10σw)^d · totalRestrictionCount n σ`, which is
  --      strictly less than `totalRestrictionCount n σ` by `hbound`.
  -- (ii) If the goal is false, every (S, bits) pair is bad for *some*
  --      f, so each pair is counted at least once across the list,
  --      giving `totalRestrictionCount n σ ≤ list_sum_of_bad_counts`.
  -- (i) ∧ ¬(ii)-conclusion is a strict contradiction.
  by_contra hall
  push Not at hall
  -- `hall : ∀ ρ, ∃ f ∈ fs, isBadRestriction d n σ f ρ`
  set s := Nat.ceil (σ.val * (n : ℚ)) with hs_def
  have hsn : s ≤ n := ceil_sigma_n_le σ n
  -- ── Aggregate `badSum`: the ℚ-sum of
  -- `badRestrictionCount` over `fs`.
  set badSum : ℚ :=
    (fs.map (fun f => badRestrictionCount n d f σ)).sum with h_s_bad_def
  have htotal_pos : 0 < totalRestrictionCount n σ := by
    unfold totalRestrictionCount
    simp only [← hs_def]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hsn)
      (pow_pos (by norm_num : (0:ℕ) < 2) _)
  -- ── (i) Upper bound on badSum via the exact switching lemma applied per-f.
  have h_upper : badSum ≤
      (fs.length : ℚ) * ((10 * σ.val * (w : ℚ)) ^ d) * totalRestrictionCount n σ := by
    have h_each : ∀ f ∈ fs,
        badRestrictionCount n d f σ
          ≤ (10 * σ.val * (w : ℚ)) ^ d * totalRestrictionCount n σ := by
      intro f hf
      have hsw := switching_lemma_exact n w d f (hwidth f hf) σ hσ hs_exact
      rwa [div_le_iff₀ htotal_pos] at hsw
    -- list-sum-of-bounded ≤ length · bound
    have hbound_pos : 0 ≤ (10 * σ.val * (w : ℚ)) ^ d * totalRestrictionCount n σ :=
      mul_nonneg (pow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt σ.property.1))
          (Nat.cast_nonneg w)) d) (le_of_lt htotal_pos)
    calc badSum
        = (fs.map (fun f => badRestrictionCount n d f σ)).sum := h_s_bad_def
      _ ≤ (fs.map (fun _ : UnboundedFanInProperDNF n =>
              (10 * σ.val * (w : ℚ)) ^ d * totalRestrictionCount n σ)).sum := by
            apply List.sum_le_sum
            intro f hf
            exact h_each f hf
      _ = (fs.length : ℚ) *
            ((10 * σ.val * (w : ℚ)) ^ d * totalRestrictionCount n σ) := by
            rw [List.map_const', List.sum_replicate]
            simp [mul_comm]
      _ = (fs.length : ℚ) *
            ((10 * σ.val * (w : ℚ)) ^ d) * totalRestrictionCount n σ := by ring
  -- ── badSum < total (combine h_upper with hbound).
  have h_lt : badSum < totalRestrictionCount n σ := by
    calc badSum
        ≤ (fs.length : ℚ) * ((10 * σ.val * (w : ℚ)) ^ d) *
              totalRestrictionCount n σ := h_upper
      _ < 1 * totalRestrictionCount n σ := by
            exact mul_lt_mul_of_pos_right hbound htotal_pos
      _ = totalRestrictionCount n σ := one_mul _
  -- ── (ii) Lower bound: every generated restriction is bad for at
  -- least one member of `fs`, so its contribution to the list-sum of
  -- bad counts is at least one.
  let restrictions := generateAllRestrictions n σ
  let badIndicator (f : UnboundedFanInProperDNF n)
      (ρ : AssignedRandomRestriction σ n) : Nat :=
    if isBadRestriction d n σ f ρ then 1 else 0
  have hone : ∀ ρ, 1 ≤ (fs.map fun f => badIndicator f ρ).sum := by
    intro ρ
    obtain ⟨f, hf, hbad⟩ := hall ρ
    have hmem : badIndicator f ρ ∈
        (fs.map fun g => badIndicator g ρ) :=
      List.mem_map.mpr ⟨f, hf, rfl⟩
    have hone_f : badIndicator f ρ = 1 := by
      simp [badIndicator, hbad]
    rw [← hone_f]
    exact List.single_le_sum (by simp) _ hmem
  have hcover :
      restrictions.card ≤
        (restrictions.map fun ρ =>
          (fs.map fun f => badIndicator f ρ).sum).sum := by
    induction restrictions using Multiset.induction_on with
    | empty => simp
    | @cons ρ rs ih =>
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      have := hone ρ
      omega
  have hswap :
      (restrictions.map fun ρ =>
          (fs.map fun f => badIndicator f ρ).sum).sum =
        (fs.map fun f =>
          restrictions.countP fun ρ => isBadRestriction d n σ f ρ).sum := by
    induction restrictions using Multiset.induction_on with
    | empty => simp [badIndicator]
    | @cons ρ rs ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        Multiset.countP_cons]
      rw [ih, ← List.sum_map_add]
      apply congr_arg List.sum
      apply List.map_congr_left
      intro f _
      simp [badIndicator, Nat.add_comm]
  have h_lower_nat :
      restrictions.card ≤
        (fs.map fun f =>
          restrictions.countP fun ρ => isBadRestriction d n σ f ρ).sum :=
    hcover.trans_eq hswap
  have h_lower : totalRestrictionCount n σ ≤ badSum := by
    have htotal :
        totalRestrictionCount n σ = (restrictions.card : ℚ) := by
      simpa [restrictions] using
        (generateAllRestrictions_card_eq_totalRestrictionCount n σ).symm
    have hbad_sum :
        badSum =
          (((fs.map fun f =>
            restrictions.countP fun ρ =>
              isBadRestriction d n σ f ρ).sum : Nat) : ℚ) := by
      rw [h_s_bad_def]
      unfold badRestrictionCount
      simpa [restrictions] using list_sum_map_ratCast fs
        (fun f => (generateAllRestrictions n σ).countP fun ρ =>
          isBadRestriction d n σ f ρ)
    rw [htotal, hbad_sum]
    exact_mod_cast h_lower_nat
  exact absurd (lt_of_le_of_lt h_lower h_lt) (lt_irrefl _)

/-- **Switching round capstone.**  One round of the exact switching lemma at
    density `σ = ⌊n/(20·t)⌋/n`: given a list of proper bottom DNFs each of
    width `≤ t`, with `t ≥ 2`, the size invariant `c·n^k < 2^t`, the
    count bound `fs.length ≤ c·n^k`, and the per-round `n`-threshold
    `20·t·(t+1) ≤ n`, there is a single restriction `ρ` of density `σ`
    that is good (not bad at depth `t`) for *every* bottom DNF
    simultaneously, leaving a live set of size `> t` (hence `≥ 3`).

    This is the switching-round counterpart of the Round-0 fan-in reduction, using the
    switching pigeonhole rather than the first-moment kill-wide-gates
    bound.  The live count exceeds the bottom fan-in `t`, which is
    exactly the narrowness invariant needed to feed the next round (and
    ultimately `narrow_dnf_misclassifies_parity`).  The arithmetic is the
    The exact-size hypothesis is automatic because
    `σ·n = ⌊n/(20·t)⌋` is an integer. -/
lemma exists_switching_round_restriction
      (c k t : Nat)
      {n : Nat}
      (fs : List (UnboundedFanInProperDNF n))
      (ht : 2 ≤ t)
      (hwidth : ∀ f ∈ fs, dnfWidth f.val ≤ t)
      (hcount : fs.length ≤ c * n ^ k)
      (ht_s : c * n ^ k < 2 ^ t)
      (hn : 20 * t * (t + 1) ≤ n) :
  ∃ (σ : OpenUnitIntervalQ) (ρ : AssignedRandomRestriction σ n),
    (∀ f ∈ fs, ¬ isBadRestriction t n σ f ρ) ∧
    t < Nat.ceil (σ.val * (n : ℚ)) ∧
    σ.val = ((n / (20 * t) : Nat) : ℚ) / (n : ℚ) := by
  -- σ = ⌊n/(20·t)⌋/n, so exactly `⌊n/(20·t)⌋` variables survive.
  have hn_pos_nat : 0 < n := by
    have : 0 < 20 * t * (t + 1) :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    exact lt_of_lt_of_le this hn
  have hnq_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos_nat
  have hden_nat_pos : 0 < 20 * t := by omega
  have hs_live_gt_t : t < n / (20 * t) := by
    have hle : t + 1 ≤ n / (20 * t) := by
      rw [Nat.le_div_iff_mul_le hden_nat_pos]
      have heq : (t + 1) * (20 * t) = 20 * t * (t + 1) := by ring
      rw [heq]
      exact hn
    omega
  have hs_live_pos : 0 < n / (20 * t) := by exact lt_trans (by omega : 0 < t) hs_live_gt_t
  have hs_live_lt_n : n / (20 * t) < n := by
    exact Nat.div_lt_self hn_pos_nat (by omega : 1 < 20 * t)
  have htq : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (by omega : 0 < t)
  set sLive : Nat := n / (20 * t) with hs_live_def
  have hσv_pos : (0 : ℚ) < ((sLive : Nat) : ℚ) / (n : ℚ) := by
    apply div_pos
    · exact_mod_cast (by rw [hs_live_def]; exact hs_live_pos)
    · exact hnq_pos
  have hσv_lt_one : ((sLive : Nat) : ℚ) / (n : ℚ) < 1 := by
    rw [div_lt_one hnq_pos]
    exact_mod_cast (by rw [hs_live_def]; exact hs_live_lt_n)
  let σ : OpenUnitIntervalQ := ⟨((sLive : Nat) : ℚ) / (n : ℚ), hσv_pos, hσv_lt_one⟩
  have hσval : σ.val = ((n / (20 * t) : Nat) : ℚ) / (n : ℚ) := by
    change ((sLive : Nat) : ℚ) / (n : ℚ) = ((n / (20 * t) : Nat) : ℚ) / (n : ℚ)
    rw [hs_live_def]
  have hσn : σ.val * (n : ℚ) = (n / (20 * t) : Nat) := by
    rw [hσval]
    field_simp [ne_of_gt hnq_pos]
  have hs_exact : (Nat.ceil (σ.val * (n : ℚ)) : ℚ) = σ.val * (n : ℚ) := by
    rw [hσn]
    norm_num
  -- σ ≤ 1/5.
  have hσ_le : σ.val ≤ 1 / 5 := by
    rw [hσval]
    have hfloor : ((n / (20 * t) : Nat) : ℚ) * (20 * (t : ℚ)) ≤ (n : ℚ) := by
      have hmul := Nat.div_mul_le_self n (20 * t)
      have hcast : ((n / (20 * t) : Nat) : ℚ) * (20 * (t : ℚ))
          = ((n / (20 * t) * (20 * t) : Nat) : ℚ) := by push_cast; ring
      rw [hcast]
      exact_mod_cast hmul
    field_simp [ne_of_gt hnq_pos]
    have h_two_le_tq : (2 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
    have hfactor : (5 : ℚ) ≤ 20 * (t : ℚ) := by nlinarith
    have hs_nonneg : (0 : ℚ) ≤ (n / (20 * t) : Nat) := by positivity
    nlinarith
  -- Pigeonhole bound `fs.length · (10·σ·t)^t < 1`; `10·σ·t ≤ 1/2`.
  have hbound : (fs.length : ℚ) * (10 * σ.val * (t : ℚ)) ^ t < 1 := by
    rw [hσval]
    have hbase_le : 10 * (((n / (20 * t) : Nat) : ℚ) / (n : ℚ)) * (t : ℚ)
        ≤ (1 : ℚ) / 2 := by
      have hfloor : ((n / (20 * t) : Nat) : ℚ) * (20 * (t : ℚ)) ≤ (n : ℚ) := by
        have hmul := Nat.div_mul_le_self n (20 * t)
        have hcast : ((n / (20 * t) : Nat) : ℚ) * (20 * (t : ℚ))
            = ((n / (20 * t) * (20 * t) : Nat) : ℚ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast hmul
      field_simp [ne_of_gt hnq_pos]
      nlinarith [hfloor]
    have hbase_nonneg :
        0 ≤ 10 * (((n / (20 * t) : Nat) : ℚ) / (n : ℚ)) * (t : ℚ) := by
      positivity
    have hpow_le :
        (10 * (((n / (20 * t) : Nat) : ℚ) / (n : ℚ)) * (t : ℚ)) ^ t
          ≤ ((1 : ℚ) / 2) ^ t :=
      pow_le_pow_left₀ hbase_nonneg hbase_le _
    have hhalf_bound : (fs.length : ℚ) * ((1 : ℚ) / 2) ^ t < 1 := by
      have hpow : ((1 : ℚ) / 2) ^ t = 1 / (2 : ℚ) ^ t := by rw [div_pow, one_pow]
      rw [hpow, mul_one_div, div_lt_one (by positivity)]
      have h_llt : fs.length < 2 ^ t := lt_of_le_of_lt hcount ht_s
      exact_mod_cast h_llt
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hpow_le (by exact_mod_cast Nat.zero_le fs.length))
      hhalf_bound
  -- One restriction good for all bottom DNFs.
  obtain ⟨ρ, hρ⟩ :=
    exists_switching_lemma_pigeonhole_list t t fs hwidth σ hσ_le hs_exact hbound
  -- The live count `⌈σ·n⌉ = ⌊n/(20·t)⌋` exceeds the bottom fan-in `t`.
  have hlive_gt : t < Nat.ceil (σ.val * (n : ℚ)) := by
    rw [hσn]
    norm_num
    exact hs_live_gt_t
  exact ⟨σ, ρ, hρ, hlive_gt, hσval⟩

end Circuits.HastadParity
