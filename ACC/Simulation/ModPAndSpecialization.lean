import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import ACC.Formula.NormalForm.ModPAnd
import ACC.Formula.Probabilistic.Properties

namespace Circuits.ACC

/-! ## Specializing probabilistic `MOD_p`-AND circuits

This module fixes a random seed, produces an ordinary `MOD_p`-AND circuit,
and proves the pointwise and average-case properties of specialization.
-/

/-- A deterministic `MOD_p`-AND circuit at every positive input length. -/
structure DeterministicModPAndCircuitFamily (p : Nat) where
  circuit : (n : PNat) → ModPAndCircuit p

/-- The Boolean value of a possibly negated random literal. -/
def fixedRandomLiteralValue (randomBits : List Bool) (idx : Nat)
    (negated : Bool) : Bool :=
  let value := randomBits[idx]?.getD false
  if negated then !value else value

/-- Specialize a list of probabilistic literals at a fixed random string.
External literals are retained, true random literals disappear from the
conjunction, and a false random literal deletes the entire conjunction. -/
def specializeModPAndLiterals {p : Nat} (randomBits : List Bool) :
    List (ProbabilisticACCFormula p) → Option (List (ACCFormula p))
  | [] => some []
  | .input (.external idx) negated :: literals =>
      (specializeModPAndLiterals randomBits literals).map
        (ACCFormula.input idx negated :: ·)
  | .input (.random idx) negated :: literals =>
      if fixedRandomLiteralValue randomBits idx negated then
        specializeModPAndLiterals randomBits literals
      else
        none
  | _ :: _ => none

/-- Specialize one conjunction in a probabilistic `MOD_p`-AND circuit. -/
def specializeModPAndConjunction {p : Nat} (randomBits : List Bool) :
    ProbabilisticACCFormula p → Option (ACCFormula p)
  | .andGate literals =>
      (specializeModPAndLiterals randomBits literals).map ACCFormula.andGate
  | _ => none

/-- Fix the random string of a probabilistic `MOD_p`-AND formula.  Malformed
input is sent to the empty modulo gate; this fallback is unreachable for a
`ProbabilisticModPAndCircuit`. -/
def specializeProbabilisticModPAndFormula {p : Nat}
    (formula : ProbabilisticACCFormula p) (randomBits : List Bool) :
    ACCFormula p :=
  match formula with
  | .modGate conjunctions =>
      .modGate (conjunctions.filterMap
        (specializeModPAndConjunction randomBits))
  | _ => .modGate []

private theorem eval_andGate_cons {p : Nat} (literal : ACCFormula p)
    (literals : List (ACCFormula p)) (inputs : List Bool) :
    ACCFormula.eval (.andGate (literal :: literals)) inputs =
      (ACCFormula.eval literal inputs &&
        ACCFormula.eval (.andGate literals) inputs) := by
  simp [ACCFormula.eval]

private theorem probabilistic_eval_andGate_cons {p : Nat}
    (literal : ProbabilisticACCFormula p)
    (literals : List (ProbabilisticACCFormula p)) (inputs randomBits : List Bool) :
    ProbabilisticACCFormula.eval (.andGate (literal :: literals)) inputs
        randomBits =
      (ProbabilisticACCFormula.eval literal inputs randomBits &&
        ProbabilisticACCFormula.eval (.andGate literals) inputs randomBits) := by
  simp [ProbabilisticACCFormula.eval]

private theorem specializeModPAndLiterals_properties {p : Nat}
    (randomBits : List Bool) (literals : List (ProbabilisticACCFormula p))
    (fixedLiterals : List (ACCFormula p))
    (h_fixed : specializeModPAndLiterals randomBits literals =
      some fixedLiterals) :
    (∀ literal ∈ fixedLiterals, IsModPAndLiteral literal) ∧
    fixedLiterals.length ≤ literals.length ∧
    ∀ inputs : List Bool,
      ACCFormula.eval (.andGate fixedLiterals) inputs =
        ProbabilisticACCFormula.eval (.andGate literals) inputs randomBits := by
  induction literals generalizing fixedLiterals with
  | nil =>
      simp [specializeModPAndLiterals] at h_fixed
      subst fixedLiterals
      simp [ACCFormula.eval, ProbabilisticACCFormula.eval]
  | cons literal literals ih =>
      cases literal with
      | input inputRef negated =>
          cases inputRef with
          | external idx =>
              simp only [specializeModPAndLiterals] at h_fixed
              cases h_tail : specializeModPAndLiterals randomBits literals with
              | none => simp [h_tail] at h_fixed
              | some fixedTail =>
                  simp only [h_tail, Option.map, Option.some.injEq] at h_fixed
                  subst fixedLiterals
                  have h_ih := ih fixedTail h_tail
                  refine ⟨?_, Nat.succ_le_succ h_ih.2.1, ?_⟩
                  · intro fixedLiteral h_mem
                    simp only [List.mem_cons] at h_mem
                    rcases h_mem with rfl | h_mem
                    · simp [IsModPAndLiteral]
                    · exact h_ih.1 fixedLiteral h_mem
                  · intro inputs
                    rw [eval_andGate_cons, probabilistic_eval_andGate_cons]
                    rw [h_ih.2.2 inputs]
                    simp [ACCFormula.eval, ProbabilisticACCFormula.eval]
          | random idx =>
              simp only [specializeModPAndLiterals] at h_fixed
              split at h_fixed
              next h_value =>
                cases h_tail : specializeModPAndLiterals randomBits literals with
                | none => simp [h_tail] at h_fixed
                | some fixedTail =>
                    simp only [h_tail, Option.some.injEq] at h_fixed
                    subst fixedLiterals
                    have h_ih := ih fixedTail h_tail
                    refine ⟨h_ih.1, h_ih.2.1.trans (Nat.le_succ _), ?_⟩
                    intro inputs
                    have h_literal_value :
                        (if negated then !randomBits[idx]?.getD false
                          else randomBits[idx]?.getD false) = true := by
                      simpa [fixedRandomLiteralValue] using h_value
                    rw [probabilistic_eval_andGate_cons, h_ih.2.2 inputs]
                    have h_probabilistic_literal :
                        ProbabilisticACCFormula.eval
                            ((.input (.random idx) negated) :
                              ProbabilisticACCFormula p) inputs randomBits =
                          true := by
                      simpa [ProbabilisticACCFormula.eval] using h_literal_value
                    rw [h_probabilistic_literal]
                    simp
              next h_value => simp at h_fixed
      | constant value label => simp [specializeModPAndLiterals] at h_fixed
      | notGate formula => simp [specializeModPAndLiterals] at h_fixed
      | andGate formulas => simp [specializeModPAndLiterals] at h_fixed
      | orGate formulas => simp [specializeModPAndLiterals] at h_fixed
      | modGate formulas => simp [specializeModPAndLiterals] at h_fixed

private theorem specializeModPAndLiterals_none_eval {p : Nat}
    (randomBits : List Bool) (literals : List (ProbabilisticACCFormula p))
    (h_literals : ∀ literal ∈ literals,
      IsProbabilisticModPAndLiteral literal)
    (h_fixed : specializeModPAndLiterals randomBits literals = none) :
    ∀ inputs : List Bool,
      ProbabilisticACCFormula.eval (.andGate literals) inputs randomBits =
        false := by
  induction literals with
  | nil => simp [specializeModPAndLiterals] at h_fixed
  | cons literal literals ih =>
      have h_literal := h_literals literal (by simp)
      have h_tail : ∀ child ∈ literals,
          IsProbabilisticModPAndLiteral child := by
        intro child h_child
        exact h_literals child (by simp [h_child])
      cases literal with
      | input inputRef negated =>
          cases inputRef with
          | external idx =>
              simp only [specializeModPAndLiterals] at h_fixed
              cases h_specialized :
                  specializeModPAndLiterals randomBits literals with
              | none =>
                  intro inputs
                  rw [probabilistic_eval_andGate_cons,
                    ih h_tail h_specialized inputs]
                  simp
              | some fixedTail => simp [h_specialized] at h_fixed
          | random idx =>
              simp only [specializeModPAndLiterals] at h_fixed
              split at h_fixed
              next h_value =>
                intro inputs
                rw [probabilistic_eval_andGate_cons,
                  ih h_tail h_fixed inputs]
                simp
              next h_value =>
                intro inputs
                rw [probabilistic_eval_andGate_cons]
                have h_literal_value :
                    (if negated then !randomBits[idx]?.getD false
                      else randomBits[idx]?.getD false) = false := by
                  have : fixedRandomLiteralValue randomBits idx negated =
                      false := Bool.eq_false_of_not_eq_true h_value
                  simpa [fixedRandomLiteralValue] using this
                have h_probabilistic_literal :
                    ProbabilisticACCFormula.eval
                        ((.input (.random idx) negated) :
                          ProbabilisticACCFormula p) inputs randomBits =
                      false := by
                  simpa [ProbabilisticACCFormula.eval] using h_literal_value
                rw [h_probabilistic_literal]
                simp
      | constant value label =>
          simp [IsProbabilisticModPAndLiteral] at h_literal
      | notGate formula =>
          simp [IsProbabilisticModPAndLiteral] at h_literal
      | andGate formulas =>
          simp [IsProbabilisticModPAndLiteral] at h_literal
      | orGate formulas =>
          simp [IsProbabilisticModPAndLiteral] at h_literal
      | modGate formulas =>
          simp [IsProbabilisticModPAndLiteral] at h_literal

private theorem specializeModPAndConjunction_properties {p : Nat}
    (randomBits : List Bool) (conjunction : ProbabilisticACCFormula p)
    (fixedConjunction : ACCFormula p)
    (h_conjunction : IsAndOfProbabilisticModPAndLiterals conjunction)
    (h_fixed : specializeModPAndConjunction randomBits conjunction =
      some fixedConjunction) :
    IsAndOfModPAndLiterals fixedConjunction ∧
    ACCFormula.circuitSize fixedConjunction ≤
      ProbabilisticACCFormula.circuitSize conjunction ∧
    (∀ r : Nat, ProbabilisticACCFormula.IsOfOrder conjunction r →
      ACCFormula.IsOfOrder fixedConjunction r) ∧
    ∀ inputs : List Bool,
      ACCFormula.eval fixedConjunction inputs =
        ProbabilisticACCFormula.eval conjunction inputs randomBits := by
  cases conjunction with
  | andGate literals =>
      simp only [specializeModPAndConjunction] at h_fixed
      cases h_literals : specializeModPAndLiterals randomBits literals with
      | none => simp [h_literals] at h_fixed
      | some fixedLiterals =>
          simp only [h_literals, Option.map, Option.some.injEq] at h_fixed
          subst fixedConjunction
          have h_properties := specializeModPAndLiterals_properties randomBits
            literals fixedLiterals h_literals
          have h_source_sizes :
              (literals.map ProbabilisticACCFormula.circuitSize).sum = 0 := by
            apply List.sum_eq_zero
            intro size h_size
            obtain ⟨literal, h_literal, rfl⟩ := List.mem_map.mp h_size
            have h_input := h_conjunction literal h_literal
            cases literal <;> simp_all [IsProbabilisticModPAndLiteral,
              ProbabilisticACCFormula.circuitSize]
          have h_fixed_sizes :
              (fixedLiterals.map ACCFormula.circuitSize).sum = 0 := by
            apply List.sum_eq_zero
            intro size h_size
            obtain ⟨literal, h_literal, rfl⟩ := List.mem_map.mp h_size
            have h_input := h_properties.1 literal h_literal
            cases literal <;> simp_all [IsModPAndLiteral,
              ACCFormula.circuitSize]
          refine ⟨h_properties.1, ?_, ?_, h_properties.2.2⟩
          · simp [ACCFormula.circuitSize,
              ProbabilisticACCFormula.circuitSize, h_source_sizes,
              h_fixed_sizes]
          · intro r h_order
            simp only [ProbabilisticACCFormula.IsOfOrder] at h_order
            simp only [ACCFormula.IsOfOrder]
            refine ⟨h_properties.2.1.trans h_order.1, ?_⟩
            intro literal h_literal
            have h_input := h_properties.1 literal h_literal
            cases literal <;> simp_all [IsModPAndLiteral,
              ACCFormula.IsOfOrder]
  | input inputRef negated =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | constant value label =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | notGate formula =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | orGate formulas =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | modGate formulas =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction

private theorem specializeModPAndConjunction_none_eval {p : Nat}
    (randomBits : List Bool) (conjunction : ProbabilisticACCFormula p)
    (h_conjunction : IsAndOfProbabilisticModPAndLiterals conjunction)
    (h_fixed : specializeModPAndConjunction randomBits conjunction = none) :
    ∀ inputs : List Bool,
      ProbabilisticACCFormula.eval conjunction inputs randomBits = false := by
  cases conjunction with
  | andGate literals =>
      simp only [specializeModPAndConjunction] at h_fixed
      cases h_literals : specializeModPAndLiterals randomBits literals with
      | none =>
          exact specializeModPAndLiterals_none_eval randomBits literals
            h_conjunction h_literals
      | some fixedLiterals => simp [h_literals] at h_fixed
  | input inputRef negated =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | constant value label =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | notGate formula =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | orGate formulas =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | modGate formulas =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction

private theorem specializeModPAndConjunctions_eval_sum {p : Nat}
    (randomBits inputs : List Bool)
    (conjunctions : List (ProbabilisticACCFormula p))
    (h_conjunctions : ∀ conjunction ∈ conjunctions,
      IsAndOfProbabilisticModPAndLiterals conjunction) :
    (((conjunctions.filterMap (specializeModPAndConjunction randomBits)).map
        (fun conjunction => ACCFormula.eval conjunction inputs)).map
      Bool.toNat).sum =
    (((conjunctions.map (fun conjunction =>
        ProbabilisticACCFormula.eval conjunction inputs randomBits))).map
      Bool.toNat).sum := by
  induction conjunctions with
  | nil => simp
  | cons conjunction conjunctions ih =>
      have h_conjunction := h_conjunctions conjunction (by simp)
      have h_tail : ∀ child ∈ conjunctions,
          IsAndOfProbabilisticModPAndLiterals child := by
        intro child h_child
        exact h_conjunctions child (by simp [h_child])
      cases h_fixed : specializeModPAndConjunction randomBits conjunction with
      | none =>
          have h_eval := specializeModPAndConjunction_none_eval randomBits
            conjunction h_conjunction h_fixed inputs
          have h_ih := ih h_tail
          simp only [List.map_map] at h_ih ⊢
          simp [h_fixed, h_eval, h_ih]
      | some fixedConjunction =>
          have h_eval :=
            (specializeModPAndConjunction_properties randomBits conjunction
              fixedConjunction h_conjunction h_fixed).2.2.2 inputs
          have h_ih := ih h_tail
          simp only [List.map_map] at h_ih ⊢
          simp [h_fixed, h_eval, h_ih]

private theorem probabilistic_and_circuitSize_eq_one {p : Nat}
    (conjunction : ProbabilisticACCFormula p)
    (h_conjunction : IsAndOfProbabilisticModPAndLiterals conjunction) :
    ProbabilisticACCFormula.circuitSize conjunction = 1 := by
  cases conjunction with
  | andGate literals =>
      simp only [ProbabilisticACCFormula.circuitSize, add_eq_right]
      apply List.sum_eq_zero
      intro size h_size
      obtain ⟨literal, h_literal, rfl⟩ := List.mem_map.mp h_size
      have h_input := h_conjunction literal h_literal
      cases literal <;> simp_all [IsProbabilisticModPAndLiteral,
        ProbabilisticACCFormula.circuitSize]
  | input inputRef negated =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | constant value label =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | notGate formula =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | orGate formulas =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction
  | modGate formulas =>
      simp [IsAndOfProbabilisticModPAndLiterals] at h_conjunction

private theorem deterministic_and_circuitSize_eq_one {p : Nat}
    (conjunction : ACCFormula p)
    (h_conjunction : IsAndOfModPAndLiterals conjunction) :
    ACCFormula.circuitSize conjunction = 1 := by
  cases conjunction with
  | andGate literals =>
      simp only [ACCFormula.circuitSize, add_eq_right]
      apply List.sum_eq_zero
      intro size h_size
      obtain ⟨literal, h_literal, rfl⟩ := List.mem_map.mp h_size
      have h_input := h_conjunction literal h_literal
      cases literal <;> simp_all [IsModPAndLiteral, ACCFormula.circuitSize]
  | input idx negated => simp [IsAndOfModPAndLiterals] at h_conjunction
  | constant value label => simp [IsAndOfModPAndLiterals] at h_conjunction
  | notGate formula => simp [IsAndOfModPAndLiterals] at h_conjunction
  | orGate formulas => simp [IsAndOfModPAndLiterals] at h_conjunction
  | modGate formulas => simp [IsAndOfModPAndLiterals] at h_conjunction

private theorem sum_map_eq_length_of_eq_one {alpha : Type}
    (measure : alpha → Nat) (values : List alpha)
    (h_measure : ∀ value ∈ values, measure value = 1) :
    (values.map measure).sum = values.length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp [h_measure value (by simp), ih (by
        intro tailValue h_tailValue
        exact h_measure tailValue (by simp [h_tailValue])), Nat.add_comm]

/-- Fixing a random string preserves the deterministic `MOD_p`-AND syntax. -/
theorem specializeProbabilisticModPAndFormula_isModPAndCircuit {p : Nat}
    (formula : ProbabilisticACCFormula p) (randomBits : List Bool)
    (h_formula : IsProbabilisticModPAndCircuit formula) :
    IsModPAndCircuit
      (specializeProbabilisticModPAndFormula formula randomBits) := by
  cases formula with
  | modGate conjunctions =>
      simp only [specializeProbabilisticModPAndFormula, IsModPAndCircuit]
      intro fixedConjunction h_fixedConjunction
      obtain ⟨conjunction, h_conjunction, h_fixed⟩ :=
        List.mem_filterMap.mp h_fixedConjunction
      exact (specializeModPAndConjunction_properties randomBits conjunction
        fixedConjunction (h_formula conjunction h_conjunction) h_fixed).1
  | input inputRef negated =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | constant value label =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | notGate formula =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | andGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | orGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula

/-- Fixing a random string cannot increase circuit size. -/
theorem specializeProbabilisticModPAndFormula_circuitSize_le {p : Nat}
    (formula : ProbabilisticACCFormula p) (randomBits : List Bool)
    (h_formula : IsProbabilisticModPAndCircuit formula) :
    ACCFormula.circuitSize
        (specializeProbabilisticModPAndFormula formula randomBits) ≤
      ProbabilisticACCFormula.circuitSize formula := by
  cases formula with
  | modGate conjunctions =>
      let fixedConjunctions := conjunctions.filterMap
        (specializeModPAndConjunction randomBits)
      have h_fixed_syntax : ∀ conjunction ∈ fixedConjunctions,
          IsAndOfModPAndLiterals conjunction := by
        intro fixedConjunction h_fixedConjunction
        obtain ⟨conjunction, h_conjunction, h_fixed⟩ :=
          List.mem_filterMap.mp h_fixedConjunction
        exact (specializeModPAndConjunction_properties randomBits conjunction
          fixedConjunction (h_formula conjunction h_conjunction) h_fixed).1
      have h_fixed_sum :
          (fixedConjunctions.map ACCFormula.circuitSize).sum =
            fixedConjunctions.length :=
        sum_map_eq_length_of_eq_one ACCFormula.circuitSize fixedConjunctions
          (fun conjunction h_conjunction =>
            deterministic_and_circuitSize_eq_one conjunction
              (h_fixed_syntax conjunction h_conjunction))
      have h_source_sum :
          (conjunctions.map ProbabilisticACCFormula.circuitSize).sum =
            conjunctions.length :=
        sum_map_eq_length_of_eq_one ProbabilisticACCFormula.circuitSize
          conjunctions (fun conjunction h_conjunction =>
            probabilistic_and_circuitSize_eq_one conjunction
              (h_formula conjunction h_conjunction))
      simpa [specializeProbabilisticModPAndFormula,
        ACCFormula.circuitSize, ProbabilisticACCFormula.circuitSize,
        fixedConjunctions, h_fixed_sum, h_source_sum] using
          Nat.succ_le_succ
            (List.length_filterMap_le
              (specializeModPAndConjunction randomBits) conjunctions)
  | input inputRef negated =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | constant value label =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | notGate formula =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | andGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | orGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula

/-- Fixing a random string cannot increase the maximum AND fan-in. -/
theorem specializeProbabilisticModPAndFormula_isOfOrder {p : Nat}
    (formula : ProbabilisticACCFormula p) (randomBits : List Bool) (r : Nat)
    (h_formula : IsProbabilisticModPAndCircuit formula)
    (h_order : ProbabilisticACCFormula.IsOfOrder formula r) :
    ACCFormula.IsOfOrder
      (specializeProbabilisticModPAndFormula formula randomBits) r := by
  cases formula with
  | modGate conjunctions =>
      simp only [ProbabilisticACCFormula.IsOfOrder] at h_order
      simp only [specializeProbabilisticModPAndFormula, ACCFormula.IsOfOrder]
      intro fixedConjunction h_fixedConjunction
      obtain ⟨conjunction, h_conjunction, h_fixed⟩ :=
        List.mem_filterMap.mp h_fixedConjunction
      exact (specializeModPAndConjunction_properties randomBits conjunction
        fixedConjunction (h_formula conjunction h_conjunction) h_fixed).2.2.1 r
          (h_order conjunction h_conjunction)
  | input inputRef negated =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | constant value label =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | notGate formula =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | andGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | orGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula

/-- Evaluation after fixing a random string equals probabilistic evaluation at
that string. -/
theorem specializeProbabilisticModPAndFormula_eval {p : Nat}
    (formula : ProbabilisticACCFormula p) (randomBits inputs : List Bool)
    (h_formula : IsProbabilisticModPAndCircuit formula) :
    ACCFormula.eval
        (specializeProbabilisticModPAndFormula formula randomBits) inputs =
      ProbabilisticACCFormula.eval formula inputs randomBits := by
  cases formula with
  | modGate conjunctions =>
      have h_sum := specializeModPAndConjunctions_eval_sum randomBits inputs
        conjunctions h_formula
      simp only [specializeProbabilisticModPAndFormula, ACCFormula.eval,
        ProbabilisticACCFormula.eval]
      rw [h_sum]
  | input inputRef negated =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | constant value label =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | notGate formula =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | andGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | orGate formulas =>
      simp [IsProbabilisticModPAndCircuit] at h_formula

/-- At a fixed random seed, count the external inputs on which a probabilistic
formula disagrees with a prescribed Boolean function. -/
def fixedSeedDisagreementCount {p n : Nat}
    (formula : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (expected : (Fin n → Bool) → Bool)
    (randomBits : Fin randomBitCount → Bool) : Nat :=
  ((Finset.univ : Finset (Fin n → Bool)).filter fun inputs =>
    ProbabilisticACCFormula.eval formula (List.ofFn inputs)
        (List.ofFn randomBits) ≠ expected inputs).card

private theorem sum_errorCount_eq_sum_fixedSeedDisagreementCount {p n : Nat}
    (formula : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (expected : (Fin n → Bool) → Bool) :
    ∑ inputs : Fin n → Bool,
        ProbabilisticACCFormula.errorCount formula randomBitCount
          (List.ofFn inputs) (expected inputs) =
      ∑ randomBits : Fin randomBitCount → Bool,
        fixedSeedDisagreementCount formula randomBitCount expected
          randomBits := by
  simp only [ProbabilisticACCFormula.errorCount,
    fixedSeedDisagreementCount, Finset.card_filter]
  exact Finset.sum_comm

/-- Finite averaging: a pointwise `n⁻ᵏ` probabilistic error bound yields a
single random seed that errs on at most a `n⁻ᵏ` fraction of all length-`n`
inputs. -/
theorem exists_seed_with_few_disagreements {p n : Nat}
    (formula : ProbabilisticACCFormula p) (randomBitCount k : Nat)
    (expected : (Fin n → Bool) → Bool) (hn : 0 < n)
    (h_error : ∀ inputs : Fin n → Bool,
      ProbabilisticACCFormula.errorProbability formula randomBitCount
          (List.ofFn inputs) (expected inputs) ≤
        1 / (n : ℚ) ^ k) :
    ∃ randomBits : Fin randomBitCount → Bool,
      fixedSeedDisagreementCount formula randomBitCount expected randomBits *
          n ^ k ≤
        2 ^ n := by
  have h_pointwise : ∀ inputs : Fin n → Bool,
      ProbabilisticACCFormula.errorCount formula randomBitCount
          (List.ofFn inputs) (expected inputs) * n ^ k ≤
        2 ^ randomBitCount := by
    intro inputs
    have h_random_positive : (0 : ℚ) < (2 : ℚ) ^ randomBitCount := by
      positivity
    have h_n_positive : (0 : ℚ) < (n : ℚ) ^ k := by
      positivity
    have h := h_error inputs
    rw [ProbabilisticACCFormula.errorProbability] at h
    have h_cross := (div_le_div_iff₀ h_random_positive h_n_positive).mp h
    norm_num at h_cross
    exact_mod_cast h_cross
  have h_total :
      (∑ randomBits : Fin randomBitCount → Bool,
          fixedSeedDisagreementCount formula randomBitCount expected randomBits *
            n ^ k) ≤
        ∑ randomBits : Fin randomBitCount → Bool, 2 ^ n := by
    calc
      (∑ randomBits : Fin randomBitCount → Bool,
          fixedSeedDisagreementCount formula randomBitCount expected randomBits *
            n ^ k) =
          (∑ randomBits : Fin randomBitCount → Bool,
            fixedSeedDisagreementCount formula randomBitCount expected
              randomBits) * n ^ k := by rw [Finset.sum_mul]
      _ = (∑ inputs : Fin n → Bool,
            ProbabilisticACCFormula.errorCount formula randomBitCount
              (List.ofFn inputs) (expected inputs)) * n ^ k := by
            rw [sum_errorCount_eq_sum_fixedSeedDisagreementCount]
      _ = ∑ inputs : Fin n → Bool,
            ProbabilisticACCFormula.errorCount formula randomBitCount
                (List.ofFn inputs) (expected inputs) * n ^ k := by
            rw [Finset.sum_mul]
      _ ≤ ∑ inputs : Fin n → Bool, 2 ^ randomBitCount := by
            exact Finset.sum_le_sum fun inputs _ => h_pointwise inputs
      _ = 2 ^ n * 2 ^ randomBitCount := by
            simp
      _ = 2 ^ randomBitCount * 2 ^ n := by rw [Nat.mul_comm]
      _ = ∑ randomBits : Fin randomBitCount → Bool, 2 ^ n := by
            simp
  have h_nonempty :
      (Finset.univ : Finset (Fin randomBitCount → Bool)).Nonempty := by
    exact Finset.univ_nonempty
  obtain ⟨randomBits, _, h_randomBits⟩ :=
    Finset.exists_le_of_sum_le h_nonempty h_total
  exact ⟨randomBits, h_randomBits⟩

/-- The deterministic specialization at a good seed agrees with the target
function on at least `2^n * (1 - n⁻ᵏ)` inputs. -/
theorem specializeProbabilisticModPAndFormula_agreement_bound {p n : Nat}
    (formula : ProbabilisticACCFormula p) (randomBitCount k : Nat)
    (expected : (Fin n → Bool) → Bool)
    (randomBits : Fin randomBitCount → Bool) (hn : 0 < n)
    (h_formula : IsProbabilisticModPAndCircuit formula)
    (h_randomBits :
      fixedSeedDisagreementCount formula randomBitCount expected randomBits *
          n ^ k ≤
        2 ^ n) :
    (((Finset.univ : Finset (Fin n → Bool)).filter fun inputs =>
        ACCFormula.eval
            (specializeProbabilisticModPAndFormula formula
              (List.ofFn randomBits))
            (List.ofFn inputs) = expected inputs).card : ℚ) ≥
      ((2 ^ n : Nat) : ℚ) * (1 - 1 / (n : ℚ) ^ k) := by
  let agreement :=
    ((Finset.univ : Finset (Fin n → Bool)).filter fun inputs =>
      ACCFormula.eval
          (specializeProbabilisticModPAndFormula formula
            (List.ofFn randomBits))
          (List.ofFn inputs) = expected inputs)
  let disagreement :=
    fixedSeedDisagreementCount formula randomBitCount expected randomBits
  have h_disagreement :
      ((Finset.univ : Finset (Fin n → Bool)).filter fun inputs =>
        ¬ACCFormula.eval
            (specializeProbabilisticModPAndFormula formula
              (List.ofFn randomBits))
            (List.ofFn inputs) = expected inputs).card = disagreement := by
    dsimp [disagreement, fixedSeedDisagreementCount]
    congr 1
    ext inputs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [specializeProbabilisticModPAndFormula_eval formula
      (List.ofFn randomBits) (List.ofFn inputs) h_formula]
  have h_partition_nat : agreement.card + disagreement = 2 ^ n := by
    have h_partition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n → Bool)))
      (p := fun inputs =>
        ACCFormula.eval
            (specializeProbabilisticModPAndFormula formula
              (List.ofFn randomBits))
            (List.ofFn inputs) = expected inputs)
    rw [h_disagreement] at h_partition
    simpa [agreement, Fintype.card_fun] using h_partition
  have h_n_pow_positive : (0 : ℚ) < (n : ℚ) ^ k := by positivity
  have h_randomBits_rat :
      (disagreement : ℚ) * (n : ℚ) ^ k ≤ ((2 ^ n : Nat) : ℚ) := by
    exact_mod_cast h_randomBits
  have h_disagreement_rat :
      (disagreement : ℚ) ≤ ((2 ^ n : Nat) : ℚ) / (n : ℚ) ^ k :=
    (le_div_iff₀ h_n_pow_positive).2 h_randomBits_rat
  have h_partition_rat :
      (agreement.card : ℚ) + disagreement = ((2 ^ n : Nat) : ℚ) := by
    exact_mod_cast h_partition_nat
  change (agreement.card : ℚ) ≥
    ((2 ^ n : Nat) : ℚ) * (1 - 1 / (n : ℚ) ^ k)
  calc
    ((2 ^ n : Nat) : ℚ) * (1 - 1 / (n : ℚ) ^ k) =
        ((2 ^ n : Nat) : ℚ) -
          ((2 ^ n : Nat) : ℚ) / (n : ℚ) ^ k := by ring
    _ ≤ agreement.card := by linarith


end Circuits.ACC
