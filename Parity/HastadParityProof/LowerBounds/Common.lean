/-
  Arithmetic helpers shared by all live-density lower-bound instantiations.
-/

import Parity.HastadParityProof.Core

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

lemma two_pow_mono_rat {r t : Nat} (hrt : r ≤ t) :
    (2 : ℚ) ^ r ≤ (2 : ℚ) ^ t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hrt
  rw [pow_add]
  have h_one_le : (1 : ℚ) ≤ (2 : ℚ) ^ u := one_le_pow₀ (by norm_num)
  nlinarith [show (0 : ℚ) ≤ (2 : ℚ) ^ r by positivity]

/-- If the surviving density is at least one half, Round-0 decay already
    forces the lower-bound exponent `r` not to exceed the switching cutoff
    `t`.  Thus `r ≤ t` need not be carried as a separate hypothesis. -/
lemma exponent_le_cutoff_of_half_le_density
    (r t : Nat) (density : ℚ) (h_half : (1 / 2 : ℚ) ≤ density)
    (h_decay : (2 : ℚ) ^ r * density ^ (t + 1) < 1) :
    r ≤ t := by
  by_contra hrt
  have htr : t + 1 ≤ r := by omega
  have h_two_nat : 2 ^ (t + 1) ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by omega) htr
  have h_two : (2 : ℚ) ^ (t + 1) ≤ (2 : ℚ) ^ r := by
    exact_mod_cast h_two_nat
  have h_density : (1 / 2 : ℚ) ^ (t + 1) ≤ density ^ (t + 1) := by
    gcongr
  have h_one : (1 : ℚ) ≤ (2 : ℚ) ^ r * density ^ (t + 1) := by
    calc
      (1 : ℚ) = (2 : ℚ) ^ (t + 1) * (1 / 2 : ℚ) ^ (t + 1) := by
        rw [← mul_pow]
        norm_num
      _ ≤ (2 : ℚ) ^ r * density ^ (t + 1) := by
        exact mul_le_mul h_two h_density (by positivity) (by positivity)
  exact (not_lt_of_ge h_one) h_decay

/-- A reserve with exponent `d - 1` implies the sharper reserve with
`d - 2`, matching the number of switching rounds used by the core. -/
lemma switching_reserve_sub_two_le_of_sub_one
    (d t : Nat) (ht : 1 ≤ t) :
    (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤
      (20 * t) ^ (d - 1) * (20 * t * (t + 1)) := by
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by omega) (by omega)

end Circuits.HastadParity
