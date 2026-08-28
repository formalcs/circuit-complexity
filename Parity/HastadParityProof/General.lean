/-
  Public general-formula Håstad parity lower bounds.
-/

import Parity.HastadParityProof.LowerBounds.OneThird
import Parity.Leveling.ExistsLeveledForm

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/- ===================================================================
   General-AC0 → strictly-leveled bridge
   ===================================================================

   `hastad_parity_lower_bound_from_circuit_pieces` is stated for the *strictly
   leveled* circuit subtype, which bundles the input bound and proper
   leveling data.  The top-level
   general lower bound, however, quantifies over the
   *general* (unleveled) AC0 subtype
   `UFIFormulaOfSizeAtMostPolyNAndDepthAtMostD`.

   To connect the two we need a depth/input-count-preserving
   *normalization* that turns an arbitrary AC0 formula into an
   equivalent strictly-leveled, proper one whose size stays polynomial
   in `n` with a *uniform* polynomial bound `c'·n^{k'}` depending only
   on `(c, k, d)` (not on the individual circuit — this uniformity is
   essential, because the threshold `n₀` produced by the circuit reduction
   depends on `c'` and `k'`).

   The construction itself (UFI → strictly-assigned-leveled, proper
   CNF/DNF bottoms, constant elimination) is supplied by the leveling
   pipeline and bridged here by `exists_leveled_form`. -/

lemma exists_leveled_form (c k d : Nat) (hd : 2 ≤ d) :
    ∃ c' k' : Nat, ∀ (n : Nat)
      (circuit :
        UFIFormulaOfSizeAtMostPolyNAndDepthAtMostD n c k d),
      ∃ (lc :
          LeveledUFIFormulaOfSizePolyNAndDepthD n c' k' d),
        ufiLargestInput lc.val < n ∧
        IsConstantFree lc.val ∧
        Circuits.Leveling.AgreesOn circuit.val lc.val n := by
  obtain ⟨c', k', hcore⟩ :=
    Circuits.Leveling.exists_strictly_leveled_proper_form_core
      c k d hd
  refine ⟨c', k', ?_⟩
  intro n circuit
  have hlarge : ufiLargestInput circuit.val < n := circuit.property.2.2.2
  obtain ⟨g, hg_depth, hg_largest, hg_proper, hg_size, hagree, h_cf⟩ :=
    hcore n circuit.val hlarge circuit.property.1 circuit.property.2.1
  refine ⟨⟨g, hg_largest, hg_depth, hg_size, by omega, hg_proper⟩,
    hg_largest, h_cf, hagree⟩

#print axioms exists_leveled_form

/-- Top-level Håstad lower bound for the **general** (unleveled) AC0
    formula subtype.  Obtained by normalizing each general formula into
    an equivalent strictly-leveled, proper one (`exists_leveled_form`)
    and applying `hastad_parity_lower_bound_from_circuit_pieces`, transferring
    the misclassification witness back along the evaluation equality. -/
lemma hastad_parity_lower_bound_general (c k d : Nat) (hd : 2 ≤ d) :
    ∃ n₀, ∀ n, n₀ < n →
      ∀ (circuit :
          UFIFormulaOfSizeAtMostPolyNAndDepthAtMostD n c k d),
      ∃ (inputs : List Bool), inputs.length = n ∧
        ((ufiFormulaEval circuit.val inputs == false ∧
            Odd (inputs.countP (· == true)))
          ∨
          (ufiFormulaEval circuit.val inputs == true ∧
            ¬ Odd (inputs.countP (· == true)))) := by
  obtain ⟨c', k', hlev⟩ := exists_leveled_form c k d hd
  obtain ⟨n₀, hn₀⟩ := hastad_parity_lower_bound_from_circuit_pieces c' k' d (by omega : 1 ≤ d)
  refine ⟨n₀, ?_⟩
  intro n hn₀n circuit
  obtain ⟨lc, _hib, _h_cf, heq⟩ := hlev n circuit
  obtain ⟨inputs, hlen, hbad⟩ := hn₀ n hn₀n lc
  refine ⟨inputs, hlen, ?_⟩
  rw [heq inputs hlen]
  exact hbad

#print axioms hastad_parity_lower_bound_general

/-- A direct proof of the general Håstad parity lower bound from
    `formula_parity_size_lower_bound_root_one_third`.  Unlike
    `hastad_parity_lower_bound_general`, this direct proof does not normalize the
    formula and has no separate lower-bound hypothesis on `d`: for fixed
    `c`, `k`, and `d`, the root-exponential lower bound eventually exceeds
    the bundled polynomial upper bound `c * n^k`. -/
lemma hastad_parity_lower_bound_general_direct (c k d : Nat) :
  ∃ n₀, ∀ n,
    n₀ < n →
      ∀ (circuit : UFIFormulaOfSizeAtMostPolyNAndDepthAtMostD n c k d),
        ∃ (inputs : List Bool),
          inputs.length = n ∧
          ((ufiFormulaEval circuit.val inputs == false ∧
              Odd (inputs.countP (· == true)))
            ∨
            (ufiFormulaEval circuit.val inputs == true ∧
              ¬ Odd (inputs.countP (· == true)))) := by
  obtain ⟨nRoot, hn_root⟩ := formula_parity_size_lower_bound_root_one_third d
  let C := 360 * 40 ^ (d - 1)
  let A := 4 * (k + 2)
  obtain ⟨nPolylog, hn_polylog⟩ :=
    exists_forall_gt_polylog_le_self (C * A ^ (d + 1)) (d + 1)
  refine ⟨max nRoot (max nPolylog (max c 1)), ?_⟩
  intro n hn circuit
  have hn_root_le : nRoot ≤ n := by omega
  have hn_polylog_lt : nPolylog < n := by omega
  have hc_le_n : c ≤ n := by omega
  have hn_ne_zero : n ≠ 0 := by omega
  have h_not_parity : ¬ FormulaComputesParity n circuit.val := by
    intro h_parity
    have h_root_lower := hn_root n hn_root_le circuit.val
      circuit.property.2.2.2 circuit.property.1 h_parity
    let m := Nat.log 2 n + 1
    let r := Nat.nthRoot (d + 1) (n / C)
    let e := r / 4
    have h_c_pos : 0 < C := by positivity
    have h_degree : d + 1 ≠ 0 := by omega
    have hm_pos : 1 ≤ m := by simp [m]
    have h_root_scale : A * m ≤ r := by
      rw [show r = Nat.nthRoot (d + 1) (n / C) by rfl,
        Nat.le_nthRoot_iff h_degree]
      rw [Nat.le_div_iff_mul_le h_c_pos]
      calc
        (A * m) ^ (d + 1) * C =
            (C * A ^ (d + 1)) * m ^ (d + 1) := by
              rw [Nat.mul_pow]
              ring
        _ ≤ n := by simpa [m] using hn_polylog n hn_polylog_lt
    have h_exponent_scale : (k + 2) * m ≤ e := by
      rw [show e = r / 4 by rfl, Nat.le_div_iff_mul_le (by omega : 0 < 4)]
      simpa [A, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_root_scale
    let logSize := Nat.log 2 (c * n ^ k)
    have hn_lt_pow : n < 2 ^ m := by
      simpa [m] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have h_size_poly : c * n ^ k ≤ n ^ (k + 1) := by
      calc
        c * n ^ k ≤ n * n ^ k := Nat.mul_le_mul hc_le_n (le_refl _)
        _ = n ^ (k + 1) := by ring
    have h_pow_bound : n ^ (k + 1) ≤ 2 ^ ((k + 1) * m) := by
      calc
        n ^ (k + 1) ≤ (2 ^ m) ^ (k + 1) :=
          Nat.pow_le_pow_left (le_of_lt hn_lt_pow) (k + 1)
        _ = 2 ^ (m * (k + 1)) := by rw [← pow_mul]
        _ = 2 ^ ((k + 1) * m) := by rw [Nat.mul_comm m (k + 1)]
    have h_log_size : logSize ≤ (k + 1) * m := by
      calc
        logSize = Nat.log 2 (c * n ^ k) := rfl
        _ ≤ Nat.log 2 (n ^ (k + 1)) := Nat.log_mono_right h_size_poly
        _ ≤ Nat.log 2 (2 ^ ((k + 1) * m)) := Nat.log_mono_right h_pow_bound
        _ = (k + 1) * m := Nat.log_pow (by norm_num) _
    have h_log_succ : logSize + 1 ≤ e := by
      apply le_trans (show logSize + 1 ≤ (k + 2) * m by
        calc
          logSize + 1 ≤ (k + 1) * m + 1 := Nat.add_le_add_right h_log_size 1
          _ ≤ (k + 1) * m + m := Nat.add_le_add_left hm_pos _
          _ = (k + 2) * m := by ring)
      exact h_exponent_scale
    have h_poly_lt : c * n ^ k < 2 ^ e := by
      have h_log_lt : c * n ^ k < 2 ^ (logSize + 1) := by
        simpa [logSize] using
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (c * n ^ k)
      exact lt_of_lt_of_le h_log_lt
        (Nat.pow_le_pow_right (by norm_num) h_log_succ)
    have h_circuit_lt : ufiFormulaCircuitSize circuit.val < 2 ^ e :=
      lt_of_le_of_lt circuit.property.2.1 h_poly_lt
    have h_root_lower' :
        2 ^ e ≤ ufiFormulaCircuitSize circuit.val := by
      simpa [C, r, e] using h_root_lower
    exact (not_lt_of_ge h_root_lower') h_circuit_lt
  unfold FormulaComputesParity at h_not_parity
  push Not at h_not_parity
  obtain ⟨inputs, hlen, hneq⟩ := h_not_parity
  refine ⟨inputs, hlen, ?_⟩
  cases heval : ufiFormulaEval circuit.val inputs <;>
      cases hparity : parityBit inputs
  · exact (hneq (by rw [heval, hparity])).elim
  · exact Or.inl ⟨by simp,
      (odd_countP_iff_parityBit inputs).mpr hparity⟩
  · refine Or.inr ⟨by simp, ?_⟩
    intro h_odd
    have := (odd_countP_iff_parityBit inputs).mp h_odd
    rw [hparity] at this
    contradiction
  · exact (hneq (by rw [heval, hparity])).elim

#print axioms hastad_parity_lower_bound_general_direct

end Circuits.HastadParity
