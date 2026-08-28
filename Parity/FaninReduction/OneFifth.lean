import Parity.FaninReductionBridge

/-! Round-0 fan-in reduction specialized to one-fifth liveness. -/

open Circuits
open Circuits.CnfDnf Circuits.CnfDnf.Restrictions

namespace Circuits.HastadParity.FaninReduction

/-- For `n ≥ 5`, calibrate `σ` to retain exactly `⌊n/5⌋` variables with
literal-survival bound `3/5`. -/
theorem exists_sigma_round0 (n : Nat) (hn : 5 ≤ n) :
    ∃ (s : Nat) (σ : OpenUnitIntervalQ),
      0 < s ∧ s < n ∧
      Nat.ceil (σ.val * (n : ℚ)) = s ∧
      (1 + (s : ℚ) / n) / 2 ≤ 3 / 5 ∧ s = n / 5 := by
  have hn0 : 0 < n := by omega
  have hn_q : (0 : ℚ) < n := by exact_mod_cast hn0
  refine ⟨n / 5, ⟨((n / 5 : Nat) : ℚ) / n, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, rfl⟩
  · have h1 : (0 : ℚ) < ((n / 5 : Nat) : ℚ) := by
      exact_mod_cast (by omega : 0 < n / 5)
    exact div_pos h1 hn_q
  · rw [div_lt_one hn_q]
    exact_mod_cast (by omega : n / 5 < n)
  · omega
  · omega
  · have : ((n / 5 : Nat) : ℚ) / n * n = ((n / 5 : Nat) : ℚ) := by
      field_simp
    rw [this, Nat.ceil_natCast]
  · have h5n : 5 * (n / 5 : Nat) ≤ n := by omega
    have hle : ((n / 5 : Nat) : ℚ) / n ≤ 1 / 5 := by
      rw [div_le_div_iff₀ hn_q (by norm_num : (0 : ℚ) < 5)]
      have : (5 : ℚ) * (n / 5 : Nat) ≤ n := by exact_mod_cast h5n
      linarith
    linarith

/-- The one-fifth-live calibration used by the density-neutral Round-0
structural proof. -/
theorem roundZeroCalibration_one_fifth (n : Nat) (hn : 5 ≤ n) :
    RoundZeroCalibration (3 / 5) n (n / 5) := by
  refine {
    q_pos := by norm_num
    q_le_one := by norm_num
    n_pos := by omega
    live_le := by omega
    sigma_exists := ?_
  }
  obtain ⟨s, σ, _hs0, _hsltn, hceil, hsurvival, hs⟩ :=
    exists_sigma_round0 n hn
  exact ⟨σ, by simpa [hs] using hceil, by simpa [hs] using hsurvival⟩

end Circuits.HastadParity.FaninReduction
