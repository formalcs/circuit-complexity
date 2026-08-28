import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import Formulas.CircuitFamilies
import Formulas.CnfDnf.CnfDnfBasic
import Formulas.NotGateFree

/-!
# Leveling pipeline — shared invariants

This file collects the *public* predicates used to specify the
individual transformation stages of the general-AC0 → strictly-leveled
normalization (`exists_leveled_form`). Keeping them here lets each
transformation live in its own file while sharing a common vocabulary.

The stages are:

1. `Parity/Leveling/NotGateElimination.lean` — push `notGate`s to the
   leaves (De Morgan) and canonicalize input indices, establishing
   `HasNoNotGates` and `ufiLargestInput · < n`.
2. `Parity/Leveling/Levelize.lean` — enforce strict AND/OR alternation,
   establishing `UnboundedFanInFormula.IsAlternatingAndLeveledAt · d`.
3. `Parity/Leveling/ProperBottoms.lean` — make every depth-≤2 bottom a
   proper CNF/DNF, establishing `HasProperBottomsAt · d`; the final
   `simplifyConstants` boundary absorbs any remaining `constant` leaves.

Each stage contract carries the size bound needed for the three stages to
compose into a single uniform polynomial bound depending only on `(c, k, d)`.

The fused predicate `IsProperlyLeveled` and its projection/construction
lemmas live in `Formulas/Properties.lean`, where circuit-family definitions
can use them without introducing an import cycle. The composition lives in
`Parity/Leveling/ExistsLeveledForm.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.Leveling
open Circuits
open UnboundedFanInFormula

/-! ### Strict leveling excludes `notGate`s -/

mutual
/-- A strictly alternating, occurrence-leveled formula contains no `notGate`.
    Thus `HasNoNotGates` need not be carried as a separate hypothesis once
    `IsAlternatingAndLeveledAt` is known. -/
theorem isAlternatingAndLeveledAt_hasNoNotGates
    (f : UnboundedFanInFormula) (lvl : Nat)
    (h : IsAlternatingAndLeveledAt f lvl) : HasNoNotGates f := by
  cases f with
  | inputGate i b => simp only [HasNoNotGates]
  | constant c l => simp only [HasNoNotGates]
  | notGate g => simp only [IsAlternatingAndLeveledAt] at h
  | andGate gates =>
      simp only [IsAlternatingAndLeveledAt] at h
      simp only [HasNoNotGates]
      exact isAlternatingAndLeveledAt_list_hasNoNotGates gates (lvl - 1) h.2.2
  | orGate gates =>
      simp only [IsAlternatingAndLeveledAt] at h
      simp only [HasNoNotGates]
      exact isAlternatingAndLeveledAt_list_hasNoNotGates gates (lvl - 1) h.2.2
termination_by sizeOf f

theorem isAlternatingAndLeveledAt_list_hasNoNotGates
    (gates : List UnboundedFanInFormula) (lvl : Nat)
    (h : ∀ g ∈ gates, IsAlternatingAndLeveledAt g lvl) :
    ∀ g ∈ gates, HasNoNotGates g := by
  cases gates with
  | nil => intro g hg; simp only [List.not_mem_nil] at hg
  | cons g gates =>
      intro x hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl he =>
          subst x
          exact isAlternatingAndLeveledAt_hasNoNotGates g lvl (h g (by simp))
      | inr hmem =>
          exact isAlternatingAndLeveledAt_list_hasNoNotGates gates lvl
            (fun y hy => h y (by simp [hy])) x hmem
termination_by sizeOf gates
end

/-- Two formulas are **equivalent on `n`-bit inputs** when they agree on
    every length-`n` input list. This is the evaluation guarantee
    preserved by every stage of the pipeline. -/
def AgreesOn (f g : UnboundedFanInFormula) (n : Nat) : Prop :=
  ∀ inputs : List Bool, inputs.length = n →
    ufiFormulaEval f inputs = ufiFormulaEval g inputs

theorem AgreesOn.trans {f g h : UnboundedFanInFormula} {n : Nat}
    (hfg : AgreesOn f g n) (hgh : AgreesOn g h n) : AgreesOn f h n :=
  fun inputs hlen => (hfg inputs hlen).trans (hgh inputs hlen)

end Circuits.Leveling
