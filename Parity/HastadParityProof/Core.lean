/-
  Density-independent parity wiring.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.Restriction.OneFifth

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-! ### Narrow-DNF parity lower bound
    The required lower bound is provided by
    `Circuits.CnfDnf.Families.narrow_dnf_misclassifies_parity` from
    `Formulas.CnfDnf.ParityDNF`. -/

/-! ### Wiring the three lower-bound ingredients

    The proof is a straightforward combination:
    1. Apply `exists_good_restriction_reduces_ac0_to_narrow_dnf` to get
       `live`, `deadBits`, and a narrow DNF `g`.
    2. Apply `exists_offset_odd_countP_assembleInput_iff` to get the
       parity offset induced by `deadBits`.
    3. Apply `narrow_dnf_misclassifies_parity` to get a live-bit input `ξ`
       on which `g` disagrees with parity XOR the offset.
    4. Lift `ξ` through `assembleInput` to obtain an `n`-bit input on
       which the AC0 circuit disagrees with parity. -/

/-- The reduction lemma exposing the wiring of the three proof ingredients. -/
lemma hastad_parity_lower_bound_from_circuit_pieces
    (c k d : Nat) (hd : 1 ≤ d) :
    ∃ n₀, ∀ n, n₀ < n → ∀
      (formula :
        LeveledUFIFormulaOfSizePolyNAndDepthD n c k d),
      ∃ (inputs : List Bool), inputs.length = n ∧
        ((ufiFormulaEval formula.val inputs == false ∧
            Odd (inputs.countP (· == true)))
          ∨
          (ufiFormulaEval formula.val inputs == true ∧
            ¬ Odd (inputs.countP (· == true)))) := by
  obtain ⟨n₀, hn₀⟩ := exists_good_restriction_reduces_ac0_to_narrow_dnf c k d hd
  refine ⟨n₀, ?_⟩
  intro n hn₀n formula
  obtain ⟨live, deadBits, h_live_lt, h_live_nodup, h_card, g, hgw, h_eq⟩ :=
    hn₀ n hn₀n formula
  obtain ⟨offset, hoff⟩ := exists_offset_odd_countP_assembleInput_iff n live deadBits
      h_live_lt h_live_nodup h_card
  obtain ⟨ξ, hξ_len, hξ_bad⟩ :=
    narrow_dnf_misclassifies_parity live.length g hgw offset
  refine ⟨assembleInput n live ξ deadBits, ?_, ?_⟩
  · -- length of the assembled input is `n`.
    exact length_assembleInput n live ξ deadBits
  · -- the assembled input is a parity-misclassification witness.
    have heval := h_eq ξ hξ_len
    have hoff_ξ := hoff ξ hξ_len
    -- combine `hξ_bad` (disagreement of `g` vs parity-XOR-offset on `ξ`)
    -- with `heval` (`F`(assembled) = `g`(ξ)) and `hoff_ξ` (parity on
    -- assembled equals parity-XOR-offset on `ξ`) to land on either the
    -- left or right disjunct.
    set assembledInput := assembleInput n live ξ deadBits with h_assembled_input
    -- The assembled-input popcount parity equals the live-bit parity-XOR-offset.
    have h_peq : Odd (assembledInput.countP (· == true)) =
        (Odd (ξ.countP (· == true)) ↔ offset = false) := propext hoff_ξ
    -- Hence `g`'s value on `ξ` disagrees with the assembled-input parity.
    have key : (ufiFormulaEval g.val ξ = true) ≠ Odd (assembledInput.countP (· == true)) := by
      rw [h_peq]; exact hξ_bad
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

#print axioms hastad_parity_lower_bound_from_circuit_pieces

end Circuits.HastadParity
