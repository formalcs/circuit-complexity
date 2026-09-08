import ACC.Asymptotics.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

namespace Circuits.ACC.SmolenskyBridge

open Filter Asymptotics

/-! ## Polylogarithmic bounds used in Smolensky's argument -/

private theorem eventually_polynomial_sq_add_le_pow_pred (c e r : ℕ) :
    ∀ᶠ L : ℕ in atTop, (c * L ^ e) ^ 2 + r + 1 ≤ 2 ^ L.pred := by
  let ε : ℝ := 1 / (4 * ((c : ℝ) ^ 2 + r + 2))
  have hε : 0 < ε := by positivity
  have hp := (isLittleO_pow_const_const_pow_of_one_lt
    (R := ℝ) (2 * e) (r := 2) (by norm_num)).bound hε
  have hc := (isLittleO_pow_const_const_pow_of_one_lt
    (R := ℝ) 0 (r := 2) (by norm_num)).bound hε
  filter_upwards [hp, hc, eventually_ge_atTop 1] with L hp hc hL
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) from Nat.cast_nonneg L),
    pow_zero, abs_one] at hp hc
  have htwo : (0 : ℝ) ≤ 2 ^ L := by positivity
  have hp2 : (L : ℝ) ^ (2 * e) ≤ ε * 2 ^ L := by
    norm_num at hp
    exact hp
  have hc2 : (1 : ℝ) ≤ ε * 2 ^ L := by
    norm_num at hc
    exact hc
  have hp' : (c : ℝ) ^ 2 * (L : ℝ) ^ (2 * e) ≤
      (c : ℝ) ^ 2 * (ε * 2 ^ L) :=
    mul_le_mul_of_nonneg_left hp2 (sq_nonneg (c : ℝ))
  have hc' : (r + 1 : ℝ) ≤ (r + 1 : ℝ) * (ε * 2 ^ L) := by
    nlinarith [mul_le_mul_of_nonneg_left hc2
      (show (0 : ℝ) ≤ r + 1 by positivity)]
  have hcoeff : ((c : ℝ) ^ 2 + r + 1) * ε ≤ 1 / 2 := by
    dsimp [ε]
    have hden : 0 < 4 * ((c : ℝ) ^ 2 + r + 2) := by positivity
    have hdiv : ((c : ℝ) ^ 2 + r + 1) /
        (4 * ((c : ℝ) ^ 2 + r + 2)) ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg (c : ℝ)]
    simpa [div_eq_mul_inv] using hdiv
  have hreal : (((c * L ^ e) ^ 2 + r + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ L / 2 := by
    push_cast
    have hsum : (c : ℝ) ^ 2 * (L : ℝ) ^ (2 * e) + (r + 1) ≤
        (((c : ℝ) ^ 2 + r + 1) * ε) * 2 ^ L := by
      calc
        _ ≤ (c : ℝ) ^ 2 * (ε * 2 ^ L) +
            (r + 1 : ℝ) * (ε * 2 ^ L) := add_le_add hp' hc'
        _ = _ := by ring
    calc
      ((c : ℝ) * (L : ℝ) ^ e) ^ 2 + r + 1 =
          (c : ℝ) ^ 2 * (L : ℝ) ^ (2 * e) + (r + 1) := by ring
      _ ≤ _ := hsum
      _ ≤ (1 / 2 : ℝ) * 2 ^ L :=
        mul_le_mul_of_nonneg_right hcoeff htwo
      _ = 2 ^ L / 2 := by ring
  have hpowpred : (2 : ℕ) ^ L = 2 * 2 ^ L.pred := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  have hpowpredR : (2 : ℝ) ^ L = 2 * 2 ^ L.pred := by
    exact_mod_cast hpowpred
  rw [hpowpredR] at hreal
  norm_num at hreal
  exact_mod_cast hreal

/-- Every fixed polylogarithm (also after a fixed input shift) is eventually
at most the square root of the unshifted input length. -/
theorem eventually_polylogarithmicBound_le_sqrt (shift c e : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n > n₀ →
      ((polylogarithmicBound (n + shift) c e : ℕ) : ℝ) ≤
        Real.sqrt n := by
  have hevent := eventually_polynomial_sq_add_le_pow_pred c e shift
  rw [eventually_atTop] at hevent
  obtain ⟨L₀, hL₀⟩ := hevent
  refine ⟨2 ^ L₀, ?_⟩
  intro n hn
  let L := logInputSize (n + shift)
  have hL : L₀ ≤ L := by
    dsimp [L, logInputSize]
    rw [← Nat.clog_pow 2 L₀ (by omega)]
    apply Nat.clog_mono_right
    omega
  have hbound := hL₀ L hL
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ L₀).trans hn
  have harg : 1 < n + shift + 1 := by omega
  have hpowlt : 2 ^ L.pred < n + shift + 1 := by
    simpa [L, logInputSize] using
      (Nat.pow_pred_clog_lt_self (b := 2) (by omega) harg)
  have hsquare : (polylogarithmicBound (n + shift) c e) ^ 2 ≤ n := by
    dsimp [polylogarithmicBound, L] at hbound hpowlt ⊢
    omega
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast hsquare

end Circuits.ACC.SmolenskyBridge
