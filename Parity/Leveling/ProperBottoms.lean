import Parity.Leveling.Invariants
import Parity.Leveling.BottomNorm
import Parity.Leveling.Dedup

/-!
# Leveling pipeline — Stage 3: proper CNF/DNF bottoms

The third stage takes a `notGate`-free, strictly assigned-leveled
formula and makes it **proper-leveled** (`HasProperBottomsAt · d`): every
depth-≤2 AND/OR subformula becomes a proper CNF/DNF (correct shape, no
empty clause, no repeated variable in a clause). Bare `constant` leaves
are left unchanged and are vacuously proper; the final normalization stage
in `ExistsLeveledForm` absorbs them and establishes `IsConstantFree`.

The full stage contract is `proper_bottoms_contract_explicit`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.Leveling
open Circuits
open UnboundedFanInFormula
open Circuits.HastadParity.BottomNorm

/-- **Stage-3 contract.**

    From a strictly assigned-leveled, `n`-input formula of
    depth ≤ `d` with all indices `< n` and circuit size ≤ `a · n^b`, produce
    an equivalent formula that is additionally **proper-leveled** at level
    `d` (proper CNF/DNF bottoms), preserving strict leveling, with a uniform
    polynomial circuit-size bound. This contract does not claim that its
    output is constant-free. -/
theorem proper_bottoms_contract_explicit (d : Nat) (hd : 2 ≤ d)
    (a b n : Nat) (f : UnboundedFanInFormula) :
      IsAlternatingAndLeveledAt f d →
      ufiLargestInput f < n →
      ufiFormulaDepth f ≤ d →
      ufiFormulaCircuitSize f ≤ a * n ^ b →
      ∃ g : UnboundedFanInFormula,
        IsAlternatingAndLeveledAt g d ∧
        HasProperBottomsAt g d ∧
        ufiLargestInput g < n ∧
        ufiFormulaDepth g ≤ d ∧
        ufiFormulaCircuitSize g ≤
          (80 * (a + 1) * (a + 1)) * n ^ (2 * (b + 1)) ∧
        AgreesOn f g n := by
  intro hstrict hlarge hdepth hsize
  have hnn : HasNoNotGates f :=
    isAlternatingAndLeveledAt_hasNoNotGates f d hstrict
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0` is vacuous: `ufiLargestInput f < 0` is impossible.
    subst hn0
    exact absurd hlarge (Nat.not_lt_zero _)
  · let f0 := dedupChildren f
    have hf0nn : HasNoNotGates f0 := dedupChildren_hasNoNotGates f hnn
    have hf0strict : IsAlternatingAndLeveledAt f0 d :=
      dedupChildren_alternating f d hstrict
    have hf0depth : ufiFormulaDepth f0 ≤ d :=
      le_trans (dedupChildren_depth_le f) hdepth
    have hf0large : ufiLargestInput f0 < n := dedupChildren_largest_input_lt hlarge
    have hf0size : ufiFormulaCircuitSize f0 ≤ a * n ^ b :=
      le_trans (dedupChildren_circuit_size_le f) hsize
    have hbound : ∀ i ∈ ufiCollectInputIndices f0, i < n := by
      intro i hi
      have hle : i ≤ ufiLargestInput f0 := by
        simp only [ufiLargestInput]
        exact mem_le_foldr_max hi
      omega
    have hg0strict := strict_properizeTree d f0 hf0strict hd hf0depth
    have hg0proper := proper_properizeTree d f0 hf0nn
    have hg0depth := depth_properizeTree_le d f0 hd hf0depth
    have hg0vars := vars_properizeTree d f0 n hn hbound
    have hg0large : ufiLargestInput (properizeTree d f0) < n := by
      unfold ufiLargestInput
      exact Circuits.HastadParity.ProperizeProto.foldr_max_lt_of_forall_lt hn hg0vars
    have hf0occ := locallyNodup_input_occurrences_le n hn f0
      (dedupChildren_locallyNodup f) hbound
    have hmasspoly : ufiFormulaCircuitSize f0 +
        (ufiCollectInputIndices f0).length ≤
        4 * (a + 1) * n ^ (b + 1) := by
      calc
        ufiFormulaCircuitSize f0 + (ufiCollectInputIndices f0).length
            ≤ a * n ^ b + (2 * n * (a * n ^ b) + 1) :=
          Nat.add_le_add hf0size (le_trans hf0occ
            (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * n) hf0size) 1))
        _ ≤ 4 * (a + 1) * n ^ (b + 1) := by
          rw [pow_succ]
          have hnb : 1 ≤ n ^ b := Nat.one_le_pow _ _ hn
          nlinarith
    have hsq := Nat.mul_le_mul hmasspoly hmasspoly
    have hg0size : ufiFormulaCircuitSize (properizeTree d f0)
        ≤ (80 * (a + 1) * (a + 1)) * n ^ (2 * (b + 1)) := by
      calc
        ufiFormulaCircuitSize (properizeTree d f0)
            ≤ 3 * ((ufiFormulaCircuitSize f0 +
                (ufiCollectInputIndices f0).length) *
              (ufiFormulaCircuitSize f0 +
                (ufiCollectInputIndices f0).length)) :=
              properizeTree_circuit_size_le d f0
        _ ≤ 5 * ((4 * (a + 1) * n ^ (b + 1)) *
              (4 * (a + 1) * n ^ (b + 1))) := Nat.mul_le_mul (by omega) hsq
        _ = (80 * (a + 1) * (a + 1)) * n ^ (2 * (b + 1)) := by
              rw [show 2 * (b + 1) = (b + 1) + (b + 1) by omega, pow_add]
              ring
    refine ⟨properizeTree d f0, hg0strict, hg0proper, hg0large, hg0depth,
      hg0size, ?_⟩
    intro inputs hlen
    calc
      ufiFormulaEval f inputs = ufiFormulaEval f0 inputs :=
        (dedupChildren_eval f inputs).symm
      _ = ufiFormulaEval (properizeTree d f0) inputs :=
        (eval_properizeTree inputs d f0 hf0nn hf0strict hd hf0depth
        (by omega) (by simpa [hlen] using hbound)).symm

end Circuits.Leveling
