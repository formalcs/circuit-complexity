import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Circuits.ACC

/-! ## Explicit asymptotic bounds used by ACC simulations -/

/-- The logarithmic input-size parameter used in explicit bounds. -/
def logInputSize (n : Nat) : Nat :=
  Nat.clog 2 (n + 1)

/-- An explicit representative of a `2^((log n)^O(1))` bound. -/
def quasipolynomialSizeBound (n coefficient exponent : Nat) : Nat :=
  2 ^ (coefficient * logInputSize n ^ exponent)

/-- An explicit representative of a `(log n)^O(1)` bound. -/
def polylogarithmicBound (n coefficient exponent : Nat) : Nat :=
  coefficient * logInputSize n ^ exponent

/-- An explicit representative of an `n^O(1)` bound. -/
def polynomialBound (n coefficient exponent : Nat) : Nat :=
  coefficient * n ^ exponent

theorem one_le_logInputSize (n : Nat) (hn : 0 < n) :
    1 ≤ logInputSize n := by
  have h_log := Nat.clog_pos (b := 2) (n := n + 1) (by omega) (by omega)
  dsimp [logInputSize]
  omega

theorem n_le_two_pow_logInputSize (n : Nat) :
    n ≤ 2 ^ logInputSize n := by
  exact (Nat.le_add_right n 1).trans
    (by simpa [logInputSize] using Nat.le_pow_clog (by omega) (n + 1))

theorem succ_le_two_pow_self_of_pos (n : Nat) (hn : 0 < n) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
          calc
            n + 3 ≤ 2 * (n + 2) := by omega
            _ ≤ 2 * 2 ^ (n + 1) := by
              exact Nat.mul_le_mul_left 2 (ih (by omega))
            _ = 2 ^ (n + 2) := by rw [pow_succ]; ring

theorem logInputSize_le (n : Nat) (hn : 0 < n) :
    logInputSize n ≤ n := by
  apply Nat.clog_le_of_le_pow
  exact succ_le_two_pow_self_of_pos n hn

theorem nat_le_two_pow_self (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
          calc
            n + 2 ≤ 2 * (n + 1) := by omega
            _ ≤ 2 * 2 ^ (n + 1) := by gcongr
            _ = 2 ^ (n + 2) := by rw [pow_succ]; ring

end Circuits.ACC
