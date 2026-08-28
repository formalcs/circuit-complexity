/-
  One-fifth-live specialization of the density-neutral restriction proof.
-/

import Parity.HastadParityProof.Restriction
import Parity.FaninReduction.OneFifth

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-- Polynomial growth is eventually dominated by exponential growth. -/
lemma exists_forall_ge_pow_le_two_pow (q : ℕ) :
    ∃ m₀, ∀ m, m₀ ≤ m → m ^ q ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt q
    (show (1 : ℝ) < 2 by norm_num)
  rw [Metric.tendsto_atTop] at h
  obtain ⟨m₀, hm₀⟩ := h 1 (by norm_num)
  refine ⟨m₀, fun m hm => le_of_lt ?_⟩
  have hd := hm₀ m hm
  simp only [Real.dist_eq, sub_zero] at hd
  have hpos : (0 : ℝ) ≤ (m : ℝ) ^ q / 2 ^ m := by positivity
  rw [abs_of_nonneg hpos] at hd
  have h₂ : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [div_lt_one h₂] at hd
  exact_mod_cast hd

/-- A fixed polynomial in `log₂ n` is eventually bounded by `n`. -/
lemma exists_forall_gt_polylog_le_self (d e : ℕ) :
    ∃ n₀, ∀ n, n₀ < n → d * (Nat.log 2 n + 1) ^ e ≤ n := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_ge_pow_le_two_pow (e + 1)
  set dPow := d * 2 ^ e with hd_pow
  set threshold := max m₀ (max dPow 1) with h_threshold
  refine ⟨2 ^ threshold, fun n hn => ?_⟩
  have hn₀ : n ≠ 0 := by
    have hp : 0 < 2 ^ threshold := pow_pos (by norm_num) threshold
    omega
  set m := Nat.log 2 n with hmdef
  have h_mle : threshold ≤ m := by
    rw [hmdef, Nat.le_log_iff_pow_le (by norm_num) hn₀]
    exact le_of_lt hn
  have hpow_le : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn₀
  have hm₀_le_m : m₀ ≤ m := le_trans (le_max_left _ _) h_mle
  have hm_dp : dPow ≤ m :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h_mle
  have hm₁ : 1 ≤ m :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h_mle
  calc d * (m + 1) ^ e
      ≤ d * (2 * m) ^ e :=
        Nat.mul_le_mul (le_refl d) (Nat.pow_le_pow_left (by omega) e)
    _ = d * (2 ^ e * m ^ e) := by rw [Nat.mul_pow]
    _ = dPow * m ^ e := by rw [hd_pow]; ring
    _ ≤ m * m ^ e := Nat.mul_le_mul hm_dp (le_refl _)
    _ = m ^ (e + 1) := by ring
    _ ≤ 2 ^ m := hm₀ m hm₀_le_m
    _ ≤ n := hpow_le

/-- For polynomial size and fixed depth, the one-fifth calibration admits a
cutoff satisfying the Round-0 count, bottom-budget, and live-reserve bounds. -/
lemma exists_round_zero_parameters (c k d : Nat) (hd : 1 ≤ d) :
    ∃ n₀, 5 ≤ n₀ ∧ ∀ n, n₀ < n → ∃ t, 2 ≤ t ∧
      (((c * n ^ k : ℕ) : ℚ) * (3 / 5) ^ (t + 1) < 1) ∧
      (c * n ^ k < 2 ^ t) ∧
      ((20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ n / 5) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  set dConst := 5 * (20 ^ (e + 2) * (2 * k + 4) ^ (e + 2)) with hd_const
  obtain ⟨n₀, hn₀⟩ := exists_forall_gt_polylog_le_self dConst (e + 2)
  refine ⟨max 5 (max c (n₀ + 1)), le_max_left _ _, ?_⟩
  intro n hn
  have h_five_le_n : 5 ≤ n := by omega
  have hcn : c ≤ n := by omega
  have h_n0n : n₀ < n := by omega
  have hmaster := hn₀ n h_n0n
  set logN := Nat.log 2 n with h_log_n
  set logSize := Nat.log 2 (c * n ^ k) with h_log_size
  set t := max 2 (2 * logSize + 1) with ht
  have h_two_le_t : 2 ≤ t := le_max_left _ _
  have h_one_le_log_n : 1 ≤ logN := by
    rw [h_log_n, Nat.le_log_iff_pow_le (by norm_num) (by omega), pow_one]
    omega
  have hlt : c * n ^ k < 2 ^ (logSize + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (c * n ^ k)
    rw [← h_log_size] at h
    exact h
  refine ⟨t, h_two_le_t, ?_, ?_, ?_⟩
  · have h2mle : 2 * (logSize + 1) ≤ t + 1 := by
      have ht' : 2 * logSize + 1 ≤ t := le_max_right _ _
      omega
    have h_q₁ : ((c * n ^ k : ℕ) : ℚ) < (2 : ℚ) ^ (logSize + 1) := by
      exact_mod_cast hlt
    have h_q₂ : (2 : ℚ) ^ (logSize + 1) ≤
        (5 / 3 : ℚ) ^ (2 * (logSize + 1)) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) (logSize + 1)
    have h_q₃ : (5 / 3 : ℚ) ^ (2 * (logSize + 1)) ≤
        (5 / 3 : ℚ) ^ (t + 1) :=
      pow_le_pow_right₀ (by norm_num) h2mle
    have h_q : ((c * n ^ k : ℕ) : ℚ) < (5 / 3 : ℚ) ^ (t + 1) :=
      lt_of_lt_of_le h_q₁ (le_trans h_q₂ h_q₃)
    have hpos : (0 : ℚ) < (3 / 5 : ℚ) ^ (t + 1) := by positivity
    calc ((c * n ^ k : ℕ) : ℚ) * (3 / 5) ^ (t + 1)
        < (5 / 3 : ℚ) ^ (t + 1) * (3 / 5) ^ (t + 1) :=
          mul_lt_mul_of_pos_right h_q hpos
      _ = ((5 / 3 : ℚ) * (3 / 5)) ^ (t + 1) := by rw [mul_pow]
      _ = 1 := by
        rw [show (5 / 3 : ℚ) * (3 / 5) = 1 by norm_num, one_pow]
  · have h_lt : logSize + 1 ≤ t :=
      le_trans (by omega) (le_max_right _ _)
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) h_lt)
  · have hnlt : n < 2 ^ (logN + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [← h_log_n] at h
      exact h
    have hcnk : c * n ^ k ≤ n ^ (k + 1) := by
      calc c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul hcn (le_refl _)
        _ = n ^ (k + 1) := by ring
    have hnk₁ : n ^ (k + 1) ≤ 2 ^ ((k + 1) * (logN + 1)) := by
      calc n ^ (k + 1) ≤ (2 ^ (logN + 1)) ^ (k + 1) :=
            Nat.pow_le_pow_left (le_of_lt hnlt) (k + 1)
        _ = 2 ^ ((logN + 1) * (k + 1)) := by rw [← pow_mul]
        _ = 2 ^ ((k + 1) * (logN + 1)) := by
          rw [Nat.mul_comm (logN + 1) (k + 1)]
    have h_lbound : logSize ≤ (k + 1) * (logN + 1) := by
      calc logSize = Nat.log 2 (c * n ^ k) := h_log_size
        _ ≤ Nat.log 2 (n ^ (k + 1)) := Nat.log_mono_right hcnk
        _ ≤ Nat.log 2 (2 ^ ((k + 1) * (logN + 1))) :=
          Nat.log_mono_right hnk₁
        _ = (k + 1) * (logN + 1) := Nat.log_pow (by norm_num) _
    have ht_b : t + 1 ≤ (2 * k + 4) * (logN + 1) := by
      have h_pq : (2 * k + 4) * (logN + 1) =
          2 * ((k + 1) * (logN + 1)) + 2 * (logN + 1) := by ring
      omega
    have h_exp : (e + 1) - 2 ≤ e := by omega
    apply le_trans
      (Nat.mul_le_mul_right (20 * t * (t + 1))
        (Nat.pow_le_pow_right (by omega : 0 < 20 * t) h_exp))
    have hkey : (20 * t) ^ e * (20 * t * (t + 1)) ≤
        (20 * (t + 1)) ^ (e + 2) := by
      have h₁ : (20 * t) ^ e ≤ (20 * (t + 1)) ^ e :=
        Nat.pow_le_pow_left (by omega) e
      have h₂ : 20 * t * (t + 1) ≤
          (20 * (t + 1)) * (20 * (t + 1)) := by
        apply Nat.mul_le_mul <;> omega
      calc (20 * t) ^ e * (20 * t * (t + 1))
          ≤ (20 * (t + 1)) ^ e *
              ((20 * (t + 1)) * (20 * (t + 1))) := Nat.mul_le_mul h₁ h₂
        _ = (20 * (t + 1)) ^ (e + 2) := by ring
    have hmain : (20 * t) ^ e * (20 * t * (t + 1)) ≤
        20 ^ (e + 2) * (2 * k + 4) ^ (e + 2) *
          (logN + 1) ^ (e + 2) := by
      calc (20 * t) ^ e * (20 * t * (t + 1))
          ≤ (20 * (t + 1)) ^ (e + 2) := hkey
        _ = 20 ^ (e + 2) * (t + 1) ^ (e + 2) := by rw [Nat.mul_pow]
        _ ≤ 20 ^ (e + 2) *
            ((2 * k + 4) * (logN + 1)) ^ (e + 2) :=
          Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left ht_b (e + 2))
        _ = 20 ^ (e + 2) * (2 * k + 4) ^ (e + 2) *
            (logN + 1) ^ (e + 2) := by
          rw [Nat.mul_pow]
          ring
    have h_cbig : (20 * t) ^ e * (20 * t * (t + 1)) * 5 ≤
        dConst * (logN + 1) ^ (e + 2) := by
      calc (20 * t) ^ e * (20 * t * (t + 1)) * 5
          ≤ (20 ^ (e + 2) * (2 * k + 4) ^ (e + 2) *
              (logN + 1) ^ (e + 2)) * 5 :=
            Nat.mul_le_mul hmain (le_refl 5)
        _ = dConst * (logN + 1) ^ (e + 2) := by
          rw [hd_const]
          ring
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
    exact le_trans h_cbig hmaster

/-- One-fifth-live complete restriction-to-narrow-DNF reduction. -/
lemma exists_good_restriction_reduces_ac0_to_narrow_dnf_of_parameters
    {c k d n t : Nat} (hd : 1 ≤ d) (h_five_le_n : 5 ≤ n)
    (ht : 2 ≤ t)
    (hcount_m : (((c * n ^ k : ℕ) : ℚ) * (3 / 5) ^ (t + 1) < 1))
    (h_bot_m : c * n ^ k < 2 ^ t)
    (h_thresh_m : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ n / 5)
    (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k d) :
    ∃ (live : List Nat)
      (deadBits : List Bool)
      (_h_live_lt : ∀ v ∈ live, v < n)
      (_h_live_nodup : live.Nodup)
      (_h_card : deadBits.length + live.length = n)
      (g : UnboundedFanInProperDNF live.length),
      dnfWidth g.val < live.length ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval formula.val (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  exact exists_good_restriction_reduces_ac0_to_narrow_dnf_of_parameters_core
    (q := 3 / 5) (s := n / 5) hd ht hcount_m h_bot_m h_thresh_m
    (FaninReduction.roundZeroCalibration_one_fifth n h_five_le_n) formula

/-- Asymptotic one-fifth-live restriction-to-narrow-DNF reduction. -/
lemma exists_good_restriction_reduces_ac0_to_narrow_dnf
    (c k d : Nat) (hd : 1 ≤ d) :
    ∃ n₀, ∀ n, n₀ < n → ∀
      (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k d),
      ∃ (live : List Nat)
        (deadBits : List Bool)
        (_h_live_lt : ∀ v ∈ live, v < n)
        (_h_live_nodup : live.Nodup)
        (_h_card : deadBits.length + live.length = n)
        (g : UnboundedFanInProperDNF live.length),
        dnfWidth g.val < live.length ∧
        ∀ (liveBits : List Bool), liveBits.length = live.length →
          ufiFormulaEval formula.val (assembleInput n live liveBits deadBits) =
          ufiFormulaEval g.val liveBits := by
  obtain ⟨n₀, _hn₀_five, hn₀⟩ := exists_round_zero_parameters c k d hd
  refine ⟨n₀, ?_⟩
  intro n hn₀n formula
  have h_five_le_n : 5 ≤ n := by omega
  obtain ⟨t, ht, hcount_m, h_bot_m, h_thresh_m⟩ := hn₀ n hn₀n
  exact exists_good_restriction_reduces_ac0_to_narrow_dnf_of_parameters
    hd h_five_le_n ht hcount_m h_bot_m h_thresh_m formula

end Circuits.HastadParity
