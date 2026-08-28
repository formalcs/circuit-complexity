import Parity.FaninReductionBridge

/-! Round-0 fan-in reduction specialized to one-third liveness. -/

open Circuits
open Circuits.CnfDnf Circuits.CnfDnf.Restrictions

namespace Circuits.HastadParity.FaninReduction

/-- For `n ≥ 3`, calibrate `σ` to retain exactly `⌊n/3⌋` variables with
literal-survival bound `2/3`. -/
theorem exists_sigma_round0_one_third (n : Nat) (hn : 3 ≤ n) :
    ∃ (s : Nat) (σ : OpenUnitIntervalQ),
      0 < s ∧ s < n ∧
      Nat.ceil (σ.val * (n : ℚ)) = s ∧
      (1 + (s : ℚ) / n) / 2 ≤ 2 / 3 ∧ s = n / 3 := by
  have hn0 : 0 < n := by omega
  have hn_q : (0 : ℚ) < n := by exact_mod_cast hn0
  refine ⟨n / 3, ⟨((n / 3 : Nat) : ℚ) / n, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, rfl⟩
  · have h1 : (0 : ℚ) < ((n / 3 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < n / 3)
    exact div_pos h1 hn_q
  · rw [div_lt_one hn_q]
    exact_mod_cast (by omega : n / 3 < n)
  · omega
  · omega
  · have : ((n / 3 : Nat) : ℚ) / n * n = ((n / 3 : Nat) : ℚ) := by
      field_simp
    rw [this, Nat.ceil_natCast]
  · have h3n : 3 * (n / 3 : Nat) ≤ n := by omega
    have hle : ((n / 3 : Nat) : ℚ) / n ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hn_q (by norm_num : (0 : ℚ) < 3)]
      have : (3 : ℚ) * (n / 3 : Nat) ≤ n := by exact_mod_cast h3n
      linarith
    linarith

/-- The one-third-live calibration used by the density-neutral Round-0
structural proof. -/
theorem roundZeroCalibration_one_third (n : Nat) (hn : 3 ≤ n) :
    RoundZeroCalibration (2 / 3) n (n / 3) := by
  refine {
    q_pos := by norm_num
    q_le_one := by norm_num
    n_pos := by omega
    live_le := by omega
    sigma_exists := ?_
  }
  obtain ⟨s, σ, _hs0, _hsltn, hceil, hsurvival, hs⟩ :=
    exists_sigma_round0_one_third n hn
  exact ⟨σ, by simpa [hs] using hceil, by simpa [hs] using hsurvival⟩

end Circuits.HastadParity.FaninReduction
