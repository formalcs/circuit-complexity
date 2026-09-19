/-
Sharp fixed-depth PARITY lower bounds. The linear depth-two reserve saves
one power of the switching cutoff; the arithmetic uses exactly d-2 rounds.
-/
import Parity.HastadParityProof.LowerBounds.OneThird

namespace Circuits.HastadParity
open Circuits Circuits.CnfDnf Circuits.CnfDnf.Families Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula
set_option linter.style.longLine false

/-- One-third-live parity misclassification bound for explicitly leveled formulas. -/
lemma parity_misclassified_of_explicit_leveled_bounds_sharp
      {c k d n t : Nat}
      (hd : 1 ≤ d)
      (h_three_le_n : 3 ≤ n)
      (ht : 2 ≤ t)
      (hcount_m : (((c * n ^ k : ℕ) : ℚ) * (2 / 3) ^ (t + 1) < 1))
      (h_bot_m : c * n ^ k < 2 ^ t)
      (h_thresh_m : (20 * t) ^ (d - 2) * (40 * (t + 1)) ≤ n / 3)
      (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k d) :
  ∃ (inputs : List Bool),
    inputs.length = n ∧
      ((ufiFormulaEval formula.val inputs == false ∧
          Odd (inputs.countP (· == true)))
        ∨
        (ufiFormulaEval formula.val inputs == true ∧
          ¬ Odd (inputs.countP (· == true)))) := by
  obtain ⟨live, deadBits, h_live_lt, h_live_nodup, h_card, g, hgw, h_eq⟩ :=
    exists_good_restriction_reduces_ac0_to_narrow_dnf_of_parameters_sharp
      hd h_three_le_n ht hcount_m h_bot_m h_thresh_m formula
  obtain ⟨offset, hoff⟩ := exists_offset_odd_countP_assembleInput_iff n live deadBits
      h_live_lt h_live_nodup h_card
  obtain ⟨ξ, hξ_len, hξ_bad⟩ :=
    narrow_dnf_misclassifies_parity live.length g hgw offset
  refine ⟨assembleInput n live ξ deadBits, length_assembleInput n live ξ deadBits, ?_⟩
  have heval := h_eq ξ hξ_len
  have hoff_ξ := hoff ξ hξ_len
  set assembledInput := assembleInput n live ξ deadBits with h_assembled_input
  have h_peq : Odd (assembledInput.countP (· == true)) =
      (Odd (ξ.countP (· == true)) ↔ offset = false) := propext hoff_ξ
  have key : (ufiFormulaEval g.val ξ = true) ≠
      Odd (assembledInput.countP (· == true)) := by
    rw [h_peq]
    exact hξ_bad
  rw [heval]
  cases hv : ufiFormulaEval g.val ξ with
  | false =>
      rw [hv] at key
      have h_odd : Odd (assembledInput.countP (· == true)) := by
        by_contra hno
        exact key (propext ⟨fun h => absurd h (by decide), fun h => absurd h hno⟩)
      exact Or.inl ⟨rfl, h_odd⟩
  | true =>
      rw [hv] at key
      have h_not : ¬ Odd (assembledInput.countP (· == true)) := by
        intro h_odd
        exact key (propext ⟨fun _ => h_odd, fun _ => rfl⟩)
      exact Or.inr ⟨rfl, h_not⟩

#print axioms parity_misclassified_of_explicit_leveled_bounds_sharp

/-- One-third-live base-2 lower bound with independent exponent and switching
cutoff parameters. -/
theorem leveled_formula_parity_size_lower_bound_binary_of_parameters_sharp
    (n d r t : Nat)
    (ht : 2 ≤ t)
    (h_decay : (2 : ℚ) ^ r * (2 / 3 : ℚ) ^ (t + 1) < 1)
    (h_thresh : (20 * t) ^ (d - 2) * (40 * (t + 1)) ≤ n / 3)
    (formula : UnboundedFanInFormula)
    (h_inputs : ufiLargestInput formula < n)
    (h_depth : ufiFormulaDepth formula ≤ d)
    (h_leveled : Circuits.Leveling.IsProperlyLeveled formula d)
    (h_parity : FormulaComputesParity n formula) :
    (2 : ℚ) ^ r ≤ (ufiFormulaCircuitSize formula : ℚ) := by
  have h_reserve_pos :
      0 < (20 * t) ^ (d - 2) * (40 * (t + 1)) := by positivity
  have h_three_le_n : 3 ≤ n := by
    have : 0 < n / 3 := lt_of_lt_of_le h_reserve_pos h_thresh
    omega
  have hd : 1 ≤ d := by
    have h_formula_depth :=
      two_le_depth_of_formula_computes_parity n (by omega) formula h_parity
    omega
  have hrt : r ≤ t :=
    exponent_le_cutoff_of_half_le_density r t (2 / 3 : ℚ) (by norm_num) h_decay
  let S := ufiFormulaCircuitSize formula
  let packaged :
      LeveledUFIFormulaOfSizePolyNAndDepthD n S 0 d :=
    ⟨formula, h_inputs, h_depth, by simp [S], hd, h_leveled⟩
  by_contra h_lower
  push Not at h_lower
  have h_decay_pos : (0 : ℚ) < (2 / 3 : ℚ) ^ (t + 1) := by positivity
  have hcount : ((S : ℚ) * (2 / 3 : ℚ) ^ (t + 1)) < 1 :=
    lt_trans (mul_lt_mul_of_pos_right h_lower h_decay_pos) h_decay
  have h_gate_q : (S : ℚ) < (2 : ℚ) ^ t :=
    lt_of_lt_of_le h_lower (two_pow_mono_rat hrt)
  have h_gate : S < 2 ^ t := by exact_mod_cast h_gate_q
  have hcount_pack :
      ((((S * n ^ 0 : Nat) : ℚ) * (2 / 3) ^ (t + 1)) < 1) := by
    simpa using hcount
  have h_gate_pack : S * n ^ 0 < 2 ^ t := by simpa using h_gate
  obtain ⟨inputs, hlen, hbad⟩ :=
    parity_misclassified_of_explicit_leveled_bounds_sharp hd h_three_le_n ht
      hcount_pack h_gate_pack h_thresh packaged
  have hcorrect := h_parity inputs hlen
  rcases hbad with ⟨heval_zero, h_odd⟩ | ⟨heval_one, h_not_odd⟩
  · have hzero : ufiFormulaEval formula inputs = false := by simpa using heval_zero
    have hparity_one : parityBit inputs = true :=
      (odd_countP_iff_parityBit inputs).mp h_odd
    rw [hzero, hparity_one] at hcorrect
    contradiction
  · have hone : ufiFormulaEval formula inputs = true := by simpa using heval_one
    have hparity_one : parityBit inputs = true := by rw [← hcorrect, hone]
    exact h_not_odd ((odd_countP_iff_parityBit inputs).mpr hparity_one)

/-- Integer exponent with the sharp root degree `d-1`. -/
def parityFormulaRootExponentSharp (n d : Nat) : Nat :=
  Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2)))

lemma parityFormulaRootExponentSharp_spec
    (n d : Nat) (hd : 2 ≤ d) (hn : 360 * 40 ^ (d - 2) ≤ n) :
    1 ≤ parityFormulaRootExponentSharp n d ∧
      (20 * (2 * parityFormulaRootExponentSharp n d)) ^ (d - 2) *
        (40 * (2 * parityFormulaRootExponentSharp n d + 1)) ≤ n / 3 := by
  let C := 360 * 40 ^ (d - 2)
  let r := parityFormulaRootExponentSharp n d
  have h_c_pos : 0 < C := by positivity
  have h_div_pos : 1 ≤ n / C := by
    rw [Nat.le_div_iff_mul_le h_c_pos]
    simpa [C] using hn
  have h_degree : d - 1 ≠ 0 := by omega
  have hr_pow : r ^ (d - 1) ≤ n / C := by
    dsimp [r, parityFormulaRootExponentSharp]
    exact Nat.pow_nthRoot_le (.inl h_degree)
  have hr : 1 ≤ r := by
    dsimp [r, parityFormulaRootExponentSharp]
    rw [Nat.le_nthRoot_iff h_degree]
    simpa using h_div_pos
  have h_reserve_coeff :
      3 * ((20 * (2 * r)) ^ (d - 2) * (40 * (2 * r + 1))) ≤
        C * r ^ (d - 1) := by
    calc
      3 * ((20 * (2 * r)) ^ (d - 2) * (40 * (2 * r + 1))) ≤
          3 * ((40 * r) ^ (d - 2) * (40 * (3 * r))) := by
            rw [show 20 * (2 * r) = 40 * r by omega]
            gcongr
            omega
      _ = C * r ^ (d - 1) := by
        dsimp [C]
        rw [show d - 1 = (d - 2) + 1 by omega, pow_succ, mul_pow]
        ring
  have h_root_to_n : C * r ^ (d - 1) ≤ n := by
    calc
      C * r ^ (d - 1) ≤ C * (n / C) := Nat.mul_le_mul_left C hr_pow
      _ ≤ n := by simpa [Nat.mul_comm] using Nat.div_mul_le_self n C
  refine ⟨hr, ?_⟩
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
  simpa [r, Nat.mul_comm] using h_reserve_coeff.trans h_root_to_n

/-- Sharp root bound for properly leveled formulas. -/
theorem leveled_formula_parity_size_lower_bound_root_sharp
    (n d : Nat) (hd : 2 ≤ d)
    (hn : 360 * 40 ^ (d - 2) ≤ n)
    (formula : UnboundedFanInFormula)
    (h_inputs : ufiLargestInput formula < n)
    (h_depth : ufiFormulaDepth formula ≤ d)
    (h_leveled : Circuits.Leveling.IsProperlyLeveled formula d)
    (h_parity : FormulaComputesParity n formula) :
    (2 : ℚ) ^ Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) ≤
      (ufiFormulaCircuitSize formula : ℚ) := by
  have h_spec := parityFormulaRootExponentSharp_spec n d hd hn
  exact leveled_formula_parity_size_lower_bound_binary_of_parameters_sharp
    n d (parityFormulaRootExponentSharp n d) (2 * parityFormulaRootExponentSharp n d)
    (by omega) (two_pow_mul_two_thirds_pow_two_mul_add_one_lt_one _)
    h_spec.2 formula h_inputs h_depth h_leveled h_parity

/-- One-third-live explicit root bound for an arbitrary depth-`d` formula,
before absorbing the normalization overhead into the exponent. -/
theorem formula_parity_size_lower_bound_root_of_large_sharp
    (n d : Nat)
    (hn : 360 * 40 ^ (d - 2) ≤ n)
    (formula : UnboundedFanInFormula)
    (h_inputs : ufiLargestInput formula < n)
    (h_depth : ufiFormulaDepth formula ≤ d)
    (h_parity : FormulaComputesParity n formula) :
    (2 : ℚ) ^ Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) ≤
      ((80 * (ufiFormulaCircuitSize formula + 1) *
          (ufiFormulaCircuitSize formula + 1) * n ^ 2 : Nat) : ℚ) := by
  have h_two_le_n : 2 ≤ n := by
    have h_pow_pos : 0 < 40 ^ (d - 2) := by positivity
    omega
  have hd : 2 ≤ d :=
    le_trans
      (two_le_depth_of_formula_computes_parity n h_two_le_n formula h_parity)
      h_depth
  let S := ufiFormulaCircuitSize formula
  have h_size : ufiFormulaCircuitSize formula ≤ S * n ^ 0 := by simp [S]
  obtain ⟨g, hg_depth, hg_largest, hg_proper, hg_size, h_agree, _h_cf⟩ :=
    Circuits.Leveling.exists_strictly_leveled_proper_form_core_explicit
      S 0 d hd n formula h_inputs h_depth h_size
  have hg_parity : FormulaComputesParity n g := by
    intro inputs hlen
    rw [← h_agree inputs hlen]
    exact h_parity inputs hlen
  have hg_lower :
      (2 : ℚ) ^ Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) ≤
        (ufiFormulaCircuitSize g : ℚ) :=
    leveled_formula_parity_size_lower_bound_root_sharp n d hd hn
      g hg_largest hg_depth hg_proper hg_parity
  have hg_size' : ufiFormulaCircuitSize g ≤
      80 * (S + 1) * (S + 1) * n ^ 2 := by
    simpa using hg_size
  calc
    (2 : ℚ) ^ Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) ≤
        (ufiFormulaCircuitSize g : ℚ) := hg_lower
    _ ≤ ((80 * (S + 1) * (S + 1) * n ^ 2 : Nat) : ℚ) := by
      exact_mod_cast hg_size'
    _ = ((80 * (ufiFormulaCircuitSize formula + 1) *
          (ufiFormulaCircuitSize formula + 1) * n ^ 2 : Nat) : ℚ) := by simp [S]

#print axioms formula_parity_size_lower_bound_root_of_large_sharp

/-- **Direct root lower bound for ordinary formulas.**

    This additive theorem uses the one-third-live Round-0 argument with `360`
    inside the root. The `/4` loss absorbs the proper-leveling normalization
    overhead. -/
theorem formula_parity_size_lower_bound_root_sharp
    (d : Nat) (hd : 2 ≤ d) :
    ∃ N, ∀ n, N ≤ n →
      ∀ (formula : UnboundedFanInFormula),
        ufiLargestInput formula < n →
        ufiFormulaDepth formula ≤ d →
        FormulaComputesParity n formula →
        2 ^ (Nat.nthRoot (d - 1)
            (n / (360 * 40 ^ (d - 2))) / 4) ≤
          ufiFormulaCircuitSize formula := by
  let C := 360 * 40 ^ (d - 2)
  obtain ⟨n₀, hn₀⟩ :=
    exists_forall_gt_polylog_le_self (C * 18 ^ (d - 1)) (d - 1)
  refine ⟨max C (n₀ + 1), ?_⟩
  intro n hn circuit h_inputs h_depth h_parity
  have h_c_le_n : C ≤ n := le_trans (le_max_left _ _) hn
  have hn₀n : n₀ < n := by omega
  have h_polylog := hn₀ n hn₀n
  let m := Nat.log 2 n + 1
  let r := Nat.nthRoot (d - 1) (n / C)
  let e := r / 4
  have h_c_pos : 0 < C := by positivity
  have h_degree : d - 1 ≠ 0 := by omega
  have hm_pos : 1 ≤ m := by simp [m]
  have h_root_lower : 4 * m + 14 ≤ r := by
    rw [show r = Nat.nthRoot (d - 1) (n / C) by rfl,
      Nat.le_nthRoot_iff h_degree]
    rw [Nat.le_div_iff_mul_le h_c_pos]
    calc
      (4 * m + 14) ^ (d - 1) * C
          ≤ (18 * m) ^ (d - 1) * C := by gcongr; omega
      _ = (C * 18 ^ (d - 1)) * m ^ (d - 1) := by
        rw [Nat.mul_pow]
        ring
      _ ≤ n := by simpa [m] using h_polylog
  have h_exponent : 7 + 2 * e + 2 * m ≤ r := by
    have h_first : 2 * e ≤ r / 2 := by
      dsimp [e]
      omega
    have h_second : 2 * m + 7 ≤ r / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
      omega
    omega
  have hn_pow : n < 2 ^ m := by
    simpa [m] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  by_contra h_lower
  push Not at h_lower
  have h_size : ufiFormulaCircuitSize circuit < 2 ^ e := h_lower
  have h_size_succ : ufiFormulaCircuitSize circuit + 1 ≤ 2 ^ e := by omega
  have h_normalized_lt :
      80 * (ufiFormulaCircuitSize circuit + 1) *
          (ufiFormulaCircuitSize circuit + 1) * n ^ 2 < 2 ^ r := by
    calc
      80 * (ufiFormulaCircuitSize circuit + 1) *
          (ufiFormulaCircuitSize circuit + 1) * n ^ 2
          ≤ 80 * 2 ^ e * 2 ^ e * n ^ 2 := by gcongr
      _ < 2 ^ 7 * 2 ^ e * 2 ^ e * (2 ^ m) ^ 2 := by
        gcongr
        norm_num
      _ = 2 ^ (7 + 2 * e + 2 * m) := by
        have h_square (k : Nat) : 2 ^ k * 2 ^ k = (2 ^ 2) ^ k := by
          calc
            2 ^ k * 2 ^ k = (2 ^ k) ^ 2 := by rw [pow_two]
            _ = 2 ^ (k * 2) := by rw [← pow_mul]
            _ = 2 ^ (2 * k) := by rw [Nat.mul_comm k 2]
            _ = (2 ^ 2) ^ k := by rw [pow_mul]
        simp only [pow_add, pow_mul]
        calc
          2 ^ 7 * 2 ^ e * 2 ^ e * (2 ^ m) ^ 2 =
              2 ^ 7 * (2 ^ e * 2 ^ e) * (2 ^ m * 2 ^ m) := by
            rw [pow_two]
            ring
          _ = 2 ^ 7 * (2 ^ 2) ^ e * (2 ^ 2) ^ m := by
            rw [h_square e, h_square m]
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) h_exponent
  have h_normalized_lower :=
    formula_parity_size_lower_bound_root_of_large_sharp
      n d (by simpa [C] using h_c_le_n) circuit h_inputs h_depth h_parity
  have h_normalized_lower_nat :
      2 ^ Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) ≤
        80 * (ufiFormulaCircuitSize circuit + 1) *
          (ufiFormulaCircuitSize circuit + 1) * n ^ 2 := by
    exact_mod_cast h_normalized_lower
  exact (not_lt_of_ge h_normalized_lower_nat) h_normalized_lt

#print axioms formula_parity_size_lower_bound_root_sharp

end Circuits.HastadParity
