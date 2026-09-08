import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Prime.Basic
import ACC.Formula.Family
import ACC.Simulation.ProbabilisticModPAnd

namespace Circuits.ACC

/-! ## Quasipolynomial-size depth-five ACC formula families

This file states the depth-reduction theorem for polynomial-size ACC formula
families.  The bound `2^((log n)^O(1))` is represented by the explicit
constant witnesses in `quasipolynomialSizeBound`.
-/

/-- The exact derandomization fact used by the depth-five corollary.

If a probabilistic ACC formula family has quasipolynomial circuit size,
depth at most `d`, and pointwise error at most `n⁻ᵏ`, then it has an exact
deterministic ACC formula simulation over the same modulus.  The deterministic
formula has circuit size polynomial in the circuit size of the probabilistic
formula and depth at most `d + 2`.

The conclusion also records the well-formedness and input-width properties
needed to package the deterministic formulas as a family. -/
def ProbabilisticACCFormulaFamiliesHaveExactDerandomizations : Prop :=
  ∀ (p sizeCoefficient sizeExponent d k : Nat),
    p.Prime →
    ∀ (probabilisticFamily : (n : PNat) → ProbabilisticACCFormula p)
      (randomBitCount : PNat → Nat)
      (targetFamily : (n : PNat) → List Bool → Bool),
      (∀ n : PNat,
        ProbabilisticACCFormula.circuitSize (probabilisticFamily n) ≤
            quasipolynomialSizeBound n.val sizeCoefficient sizeExponent ∧
        ProbabilisticACCFormula.depth (probabilisticFamily n) ≤ d ∧
        ∀ inputs : List Bool,
          inputs.length = n.val →
            ProbabilisticACCFormula.errorProbability
                (probabilisticFamily n) (randomBitCount n) inputs
                (targetFamily n inputs) ≤ 1 / (n.val : ℚ) ^ k) →
      ∃ deterministicFamily : (n : PNat) → ACCFormula p,
      ∃ sizePower : Nat,
        0 < sizePower ∧
        ∀ n : PNat,
          ACCFormula.WellFormed (deterministicFamily n) ∧
          ACCFormula.numInputs (deterministicFamily n) ≤ n.val ∧
          ACCFormula.circuitSize (deterministicFamily n) ≤
            ProbabilisticACCFormula.circuitSize
                (probabilisticFamily n) ^ sizePower ∧
          ACCFormula.depth (deterministicFamily n) ≤ d + 2 ∧
          ∀ inputs : List Bool,
            inputs.length = n.val →
              ACCFormula.eval (deterministicFamily n) inputs =
                targetFamily n inputs

/-- A source ACC formula family has an exact, quasipolynomial-size simulation
by ACC formulas over the same modulus and of depth at most five.

Formula size is measured by `ACCFormula.circuitSize`.  The simulation is
required to agree with the source on every Boolean input of every positive
input length. -/
def HasQuasipolynomialSizeDepthFiveACCFormulaSimulation
    {p sourceCoefficient sourceExponent sourceDepth : Nat}
    (sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
      sourceExponent sourceDepth) : Prop :=
  ∃ simulationFamily : (n : PNat) → ACCFormula p,
  ∃ sizeCoefficient sizeExponent : Nat,
    0 < sizeCoefficient ∧
    ∀ n : PNat,
      ACCFormula.WellFormed (simulationFamily n) ∧
      ACCFormula.numInputs (simulationFamily n) ≤ n.val ∧
      ACCFormula.circuitSize (simulationFamily n) ≤
        quasipolynomialSizeBound n.val sizeCoefficient sizeExponent ∧
      ACCFormula.depth (simulationFamily n) ≤ 5 ∧
      ∀ inputs : List Bool,
        inputs.length = n.val →
          ACCFormula.eval (simulationFamily n) inputs =
            ACCFormula.eval (sourceFamily n).val inputs

/-- Formal statement of the exact depth-five simulation theorem: for every
prime modulus and every polynomial-size, constant-depth ACC formula family,
there is a quasipolynomial-size ACC formula family over the same modulus, of
depth at most five, computing exactly the same Boolean function at every input
length. -/
def PolynomialSizeACCFormulaFamiliesHaveQuasipolynomialSizeDepthFiveSimulations :
    Prop :=
  ∀ (p sourceCoefficient sourceExponent sourceDepth : Nat),
    p.Prime →
    ∀ sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
        sourceExponent sourceDepth,
      HasQuasipolynomialSizeDepthFiveACCFormulaSimulation sourceFamily

private theorem max_map_le_of_forall {α : Type} (values : List α)
    (measure : α → Nat) (bound : Nat)
    (h_values : ∀ value ∈ values, measure value ≤ bound) :
    (values.map measure).max?.getD 0 ≤ bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have h_tail : ∀ child ∈ values, measure child ≤ bound := by
        intro child h_child
        exact h_values child (by simp [h_child])
      simp only [List.map_cons]
      rw [show (measure value :: values.map measure).max?.getD 0 =
        max (measure value) ((values.map measure).max?.getD 0) by
          cases values <;> simp [List.max?_cons]]
      exact max_le (h_values value (by simp)) (ih h_tail)

/-- A probabilistic `MOD_p`-AND circuit has at most three formula layers.
With the depth convention used by `ProbabilisticACCFormula.depth`, the sharper
bound is two; the weaker bound three matches the depth parameter in the
depth-five corollary. -/
private theorem probabilisticModPAndCircuit_depth_le_three {p : Nat}
    (circuit : ProbabilisticModPAndCircuit p) :
    ProbabilisticACCFormula.depth circuit.val ≤ 3 := by
  obtain ⟨formula, h_formula⟩ := circuit
  cases formula with
  | modGate conjunctions =>
      have h_conjunction_depth : ∀ conjunction ∈ conjunctions,
          ProbabilisticACCFormula.depth conjunction ≤ 1 := by
        intro conjunction h_conjunction
        have h_literals := h_formula conjunction h_conjunction
        cases conjunction with
        | andGate literals =>
            have h_literal_depth : ∀ literal ∈ literals,
                ProbabilisticACCFormula.depth literal ≤ 0 := by
              intro literal h_literal
              have h_syntax := h_literals literal h_literal
              cases literal <;>
                simp_all [IsProbabilisticModPAndLiteral,
                  ProbabilisticACCFormula.depth]
            have h_max := max_map_le_of_forall literals
              ProbabilisticACCFormula.depth 0 h_literal_depth
            simp only [ProbabilisticACCFormula.depth]
            omega
        | input inputRef negated =>
            simp [IsAndOfProbabilisticModPAndLiterals] at h_literals
        | constant value label =>
            simp [IsAndOfProbabilisticModPAndLiterals] at h_literals
        | notGate child =>
            simp [IsAndOfProbabilisticModPAndLiterals] at h_literals
        | orGate children =>
            simp [IsAndOfProbabilisticModPAndLiterals] at h_literals
        | modGate children =>
            simp [IsAndOfProbabilisticModPAndLiterals] at h_literals
      have h_max := max_map_le_of_forall conjunctions
        ProbabilisticACCFormula.depth 1 h_conjunction_depth
      simp only [ProbabilisticACCFormula.depth]
      omega
  | input inputRef negated =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | constant value label =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | notGate child =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | andGate children =>
      simp [IsProbabilisticModPAndCircuit] at h_formula
  | orGate children =>
      simp [IsProbabilisticModPAndCircuit] at h_formula

/-- The exact depth-five theorem follows from the probabilistic depth-three
reduction and exact derandomization with polynomial size overhead and two
additional levels of depth. -/
theorem polynomial_size_acc_formula_families_have_quasipolynomial_size_depth_five_simulations
    (h_derandomize :
      ProbabilisticACCFormulaFamiliesHaveExactDerandomizations) :
    PolynomialSizeACCFormulaFamiliesHaveQuasipolynomialSizeDepthFiveSimulations := by
  intro p sourceCoefficient sourceExponent sourceDepth hp sourceFamily
  obtain ⟨probabilisticFamily, sizeCoefficient, sizeExponent,
      _orderCoefficient, _orderExponent, _randomCoefficient, _randomExponent,
      h_sizeCoefficient, _h_orderCoefficient, _h_randomCoefficient,
      h_probabilistic⟩ :=
    polynomial_size_acc_formula_families_have_probabilistic_mod_p_and_circuit_simulations
      p sourceCoefficient sourceExponent sourceDepth hp sourceFamily 1
  obtain ⟨deterministicFamily, sizePower, h_sizePower, h_deterministic⟩ :=
    h_derandomize p sizeCoefficient sizeExponent 3 1 hp
      (fun n => (probabilisticFamily.circuit n).val)
      probabilisticFamily.randomBitCount
      (fun n inputs => ACCFormula.eval (sourceFamily n).val inputs) (by
        intro n
        refine ⟨(h_probabilistic n).1, ?_, ?_⟩
        · exact probabilisticModPAndCircuit_depth_le_three
            (probabilisticFamily.circuit n)
        · intro inputs h_length
          exact (h_probabilistic n).2.2.2 inputs h_length)
  refine ⟨deterministicFamily, sizeCoefficient * sizePower, sizeExponent,
    Nat.mul_pos h_sizeCoefficient h_sizePower, ?_⟩
  intro n
  have h_size_power :
      ProbabilisticACCFormula.circuitSize
            (probabilisticFamily.circuit n).val ^ sizePower ≤
        quasipolynomialSizeBound n.val sizeCoefficient sizeExponent ^
          sizePower := by
    exact Nat.pow_le_pow_left (h_probabilistic n).1 sizePower
  refine ⟨(h_deterministic n).1, (h_deterministic n).2.1, ?_, ?_, ?_⟩
  · apply (h_deterministic n).2.2.1.trans h_size_power |>.trans_eq
    unfold quasipolynomialSizeBound
    calc
      (2 ^ (sizeCoefficient * logInputSize n.val ^ sizeExponent)) ^
          sizePower =
        2 ^ ((sizeCoefficient * logInputSize n.val ^ sizeExponent) *
          sizePower) := by rw [← pow_mul]
      _ = 2 ^ ((sizeCoefficient * sizePower) *
          logInputSize n.val ^ sizeExponent) := by
        congr 1
        ring
  · simpa using (h_deterministic n).2.2.2.1
  · intro inputs h_length
    exact (h_deterministic n).2.2.2.2 inputs h_length

end Circuits.ACC
