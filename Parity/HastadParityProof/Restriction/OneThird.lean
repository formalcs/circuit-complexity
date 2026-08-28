/-
  One-third-live specialization of the density-neutral restriction proof.
-/

import Parity.HastadParityProof.Restriction
import Parity.FaninReduction.OneThird

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-- One-third-live version of the complete restriction-to-narrow-DNF reduction. -/
lemma exists_good_restriction_reduces_ac0_to_narrow_dnf_of_parameters_one_third
    {c k d n t : Nat} (hd : 1 ≤ d) (h_three_le_n : 3 ≤ n)
    (ht : 2 ≤ t)
    (hcount_m : (((c * n ^ k : ℕ) : ℚ) * (2 / 3) ^ (t + 1) < 1))
    (h_bot_m : c * n ^ k < 2 ^ t)
    (h_thresh_m : (20 * t) ^ (d - 2) * (20 * t * (t + 1)) ≤ n / 3)
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
    (q := 2 / 3) (s := n / 3) hd ht hcount_m h_bot_m h_thresh_m
    (FaninReduction.roundZeroCalibration_one_third n h_three_le_n) formula

end Circuits.HastadParity
