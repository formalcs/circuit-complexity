import Parity.Leveling.NotGateElimination
import Parity.Leveling.Levelize
import Parity.Leveling.ProperBottoms
import Parity.HastadParityProof.SimplifyConstants

/-!
# Leveling pipeline — composition

This file composes the three structural transformation stages
(`elimNotGates_contract`, `levelize_contract`, and
`proper_bottoms_contract_explicit`) into the single normalization core
`exists_strictly_leveled_proper_form_core`, then absorbs constants with
`simplifyConstants` so the result is syntactically constant-free.

The composition threads each stage's *uniform* polynomial bound `(aᵢ, bᵢ)`
into the next stage and chains the
`AgreesOn` evaluation guarantees by transitivity.

`Parity/HastadParityProof/General.lean` consumes this core to discharge the
top-level `exists_leveled_form`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.Leveling
open Circuits
open UnboundedFanInFormula
open Circuits.HastadParity

/-- Explicit-constant form of the general normalization core.  A formula of
    size at most `c * n^k` is normalized to an equivalent, properly leveled,
    constant-free formula with size at most
    `80 * (c+1)^2 * n^(2*(k+1))`. -/
theorem exists_strictly_leveled_proper_form_core_explicit
    (c k d : Nat) (hd : 2 ≤ d) (n : Nat)
    (circuit : UnboundedFanInFormula)
    (hlarge : ufiLargestInput circuit < n)
    (hdepth : ufiFormulaDepth circuit ≤ d)
    (hbound : ufiFormulaCircuitSize circuit ≤ c * n ^ k) :
    ∃ g : UnboundedFanInFormula,
      ufiFormulaDepth g ≤ d ∧
        ufiLargestInput g < n ∧
        IsProperlyLeveled g d ∧
      ufiFormulaCircuitSize g ≤
        (80 * (c + 1) * (c + 1)) * n ^ (2 * (k + 1)) ∧
      AgreesOn circuit g n ∧
      IsConstantFree g := by
  have h1 := elimNotGates_contract d (by omega : 1 ≤ d) c k
  obtain ⟨g1, hno1, hl1, hd1, hb1, he1⟩ :=
    h1 n circuit hlarge hdepth hbound
  obtain ⟨g2, hslev2, hl2, hd2, hg2size, he2⟩ :=
    levelize_contract d n g1 hno1 hl1 hd1
  have hb2 : ufiFormulaCircuitSize g2 ≤ c * n ^ k :=
    le_trans hg2size hb1
  obtain ⟨g3, hslev3, hprop3, hl3, hd3, hb3, he3⟩ :=
    proper_bottoms_contract_explicit d hd c k n g2 hslev2 hl2 hd2 hb2
  let g4 := simplifyConstants g3
  have hslev4 : IsAlternatingAndLeveledAt g4 d :=
    isAlternatingAndLeveledAt_simplifyConstants g3 d hslev3
  have hprop4 : HasProperBottomsAt g4 d :=
    hasProperBottomsAt_simplifyConstants g3 d hprop3
  have hl4 : ufiLargestInput g4 < n :=
    simplifyConstants_ufiLargestInput_lt hl3
  have hd4 : ufiFormulaDepth g4 ≤ d :=
    proper_leveled_depth_le g4 d hd hprop4
  have hb4 : ufiFormulaCircuitSize g4 ≤
      (80 * (c + 1) * (c + 1)) * n ^ (2 * (k + 1)) :=
    le_trans (simplifyConstants_ufiFormulaCircuitSize_le g3) hb3
  have he4 : AgreesOn g3 g4 n := by
    intro inputs _
    exact (simplifyConstants_eval g3 inputs).symm
  refine ⟨g4, hd4, hl4, isProperlyLeveled_of_strict_proper g4 d hslev4 hprop4,
    hb4, ?_, isConstantFree_simplifyConstants g3⟩
  exact AgreesOn.trans (AgreesOn.trans (AgreesOn.trans he1 he2) he3) he4

/-- **General-AC0 → strictly-leveled-and-proper normalization core.**

    For every `(c, k, d)` with `2 ≤ d`, there are *uniform* constants such
    that every depth-≤`d`, `n`-input formula of circuit size `≤ c · n^k`
    **with canonical input layout** (`ufiLargestInput · < n`)
    is equivalent (`AgreesOn`) to a formula of depth at most `d`, with all
    inputs indexed below `n`, properly leveled at level `d`, and of circuit
    size at most `80(c+1)² n^(2(k+1))`.

    The canonical-layout precondition is inherited from the stage-1
    contract (`elimNotGates_contract`), which mirrors the circuit-level
    convention of *assuming* and *preserving* canonical input ids rather
    than establishing them.

    Obtained by composing the three structural pipeline stages and then
    absorbing constants without increasing size or depth. -/
theorem exists_strictly_leveled_proper_form_core (c k d : Nat) (hd : 2 ≤ d) :
    ∃ c' k' : Nat, ∀ (n : Nat) (circuit : UnboundedFanInFormula),
      ufiLargestInput circuit < n →
      ufiFormulaDepth circuit ≤ d →
      ufiFormulaCircuitSize circuit ≤ c * n ^ k →
      ∃ g : UnboundedFanInFormula,
        ufiFormulaDepth g ≤ d ∧
          ufiLargestInput g < n ∧
          IsProperlyLeveled g d ∧
        ufiFormulaCircuitSize g ≤ c' * n ^ k' ∧
        AgreesOn circuit g n ∧
        IsConstantFree g := by
  refine ⟨80 * (c + 1) * (c + 1), 2 * (k + 1), ?_⟩
  intro n circuit hlarge hdepth hbound
  obtain ⟨g, hg_depth, hg_largest, hg_proper, hg_size, hg_agree, hg_constant_free⟩ :=
    exists_strictly_leveled_proper_form_core_explicit
      c k d hd n circuit hlarge hdepth hbound
  exact ⟨g, hg_depth, hg_largest, hg_proper, hg_size, hg_agree, hg_constant_free⟩

end Circuits.Leveling
