import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Prime.Basic
import ACC.Formula.Family
import ACC.Formula.NormalForm.ModPAnd
import ACC.Formula.Probabilistic.OrElimination.Interface
import ACC.Formula.Transform.AndNotElimination
import ACC.Formula.Probabilistic.AndModNormalization.Bounds
import ACC.Asymptotics.Bounds

namespace Circuits.ACC

/-! ## Probabilistic `MOD_p-AND` circuit families

This module states the family-level probabilistic simulation theorem targeted
by the transformations in `ACC.Formula`.  The asymptotic notation in the
paper statement is represented by explicit constant witnesses:

* `2^((log n)^O(1))` is `quasipolynomialSizeBound n c q`;
* `(log n)^O(1)` is `polylogarithmicBound n c q`; and
* `n^O(1)` is `polynomialBound n c q`.

We use `clog 2 (n + 1)` so the bounds also behave sensibly at the positive
input length `n = 1`.  Changing the logarithm base or this small-input
convention only changes the witnessed constants.
-/

/-- A probabilistic `MOD_p-AND` circuit family together with the number of
uniform random bits supplied to each member. -/
structure ProbabilisticModPAndCircuitFamily (p : Nat) where
  circuit : (n : PNat) → ProbabilisticModPAndCircuit p
  randomBitCount : PNat → Nat

/-- Coefficient of the logarithmic repetition bound after deterministic
preprocessing. -/
def simulationRepetitionCoefficient
    (sourceCoefficient sourceExponent k : Nat) : Nat :=
  Nat.clog 2 (2 * sourceCoefficient) + sourceExponent + k

/-- Constant depth after deterministic preprocessing. -/
def simulationPreprocessedDepth (sourceDepth : Nat) : Nat :=
  2 * sourceDepth

/-- Constant factor in the intermediate probabilistic formula's node bound. -/
def simulationIntermediateNodeConstant
    (sourceCoefficient sourceExponent sourceDepth k : Nat) : Nat :=
  2 * sourceCoefficient *
    (3 * (simulationRepetitionCoefficient sourceCoefficient sourceExponent k + 1)) ^
      simulationPreprocessedDepth sourceDepth

/-- Coefficient in the power-of-two node-count bound for the intermediate
probabilistic formula. -/
def simulationIntermediateNodeCoefficient
    (sourceCoefficient sourceExponent sourceDepth k : Nat) : Nat :=
  Nat.clog 2 (simulationIntermediateNodeConstant sourceCoefficient
    sourceExponent sourceDepth k) + sourceExponent + 1

/-- Polylogarithmic order coefficient immediately after OR elimination. -/
def simulationIntermediateOrderCoefficient
    (sourceCoefficient sourceExponent k : Nat) : Nat :=
  simulationRepetitionCoefficient sourceCoefficient sourceExponent k + 2

/-- Coefficient in the quasipolynomial size bound after global AND/MOD
normalization. -/
def simulationSizeCoefficient (p sourceCoefficient sourceExponent sourceDepth
    k : Nat) : Nat :=
  (3 * p + 2) *
    (Nat.clog 2 (2 * p) +
      simulationIntermediateNodeCoefficient sourceCoefficient sourceExponent
        sourceDepth k + 1) *
    (simulationIntermediateOrderCoefficient sourceCoefficient sourceExponent k +
      3 * p) ^ (4 * simulationPreprocessedDepth sourceDepth + 1)

/-- Exponent in the quasipolynomial size bound after normalization. -/
def simulationSizeExponent (sourceDepth : Nat) : Nat :=
  simulationPreprocessedDepth sourceDepth + 1 +
    (4 * simulationPreprocessedDepth sourceDepth + 1)

/-- Coefficient in the polylogarithmic AND-order bound after normalization. -/
def simulationOrderCoefficient (p sourceCoefficient sourceExponent sourceDepth
    k : Nat) : Nat :=
  p * (simulationIntermediateOrderCoefficient sourceCoefficient sourceExponent k +
    3 * p) ^ (4 * simulationPreprocessedDepth sourceDepth + 1)

/-- Exponent in the polylogarithmic AND-order bound after normalization. -/
def simulationOrderExponent (sourceDepth : Nat) : Nat :=
  4 * simulationPreprocessedDepth sourceDepth + 1

/-- Coefficient in the polynomial random-bit bound. -/
def simulationRandomCoefficient
    (sourceCoefficient sourceExponent k : Nat) : Nat :=
  simulationRepetitionCoefficient sourceCoefficient sourceExponent k *
    (2 * sourceCoefficient)

/-- Exponent in the polynomial random-bit bound. -/
def simulationRandomExponent (sourceExponent : Nat) : Nat :=
  sourceExponent + 1

/-- A fixed polynomial-size, constant-depth ACC formula family has a
probabilistic `MOD_p-AND` simulation with the requested error exponent and
the stated asymptotic resource bounds.

For every input of length `n`, `errorProbability` measures disagreement with
the Boolean value of the source formula. Thus the final clause simultaneously
states completeness and soundness for the same language, with two-sided error
at most `n⁻ᵏ`. -/
def HasProbabilisticModPAndCircuitSimulation
    {p sourceCoefficient sourceExponent sourceDepth : Nat}
    (sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
      sourceExponent sourceDepth) (k : Nat) : Prop :=
  ∃ simulationFamily : ProbabilisticModPAndCircuitFamily p,
  ∃ sizeCoefficient sizeExponent orderCoefficient orderExponent
      randomCoefficient randomExponent : Nat,
    0 < sizeCoefficient ∧
    0 < orderCoefficient ∧
    0 < randomCoefficient ∧
    ∀ n : PNat,
      ProbabilisticACCFormula.circuitSize
          (simulationFamily.circuit n).val ≤
        quasipolynomialSizeBound n.val sizeCoefficient sizeExponent ∧
      ProbabilisticACCFormula.IsOfOrder
          (simulationFamily.circuit n).val
          (polylogarithmicBound n.val orderCoefficient orderExponent) ∧
      simulationFamily.randomBitCount n ≤
        polynomialBound n.val randomCoefficient randomExponent ∧
      ∀ inputs : List Bool,
        inputs.length = n.val →
          ProbabilisticACCFormula.errorProbability
              (simulationFamily.circuit n).val
              (simulationFamily.randomBitCount n)
              inputs
              (ACCFormula.eval (sourceFamily n).val inputs) ≤
            1 / (n.val : ℚ) ^ k

/-- Deterministic preprocessing followed by randomized OR elimination. -/
def probabilisticAndModIntermediate {p : Nat} (formula : ACCFormula p)
    (n k : Nat) : ProbabilisticACCFormula p :=
  ACCFormula.probabilisticOrElimination
    (ACCFormula.eliminateAndNotGates formula) n k

/-- The pointwise circuit used by the family simulation. -/
def probabilisticModPAndSimulationFormula {p : Nat}
    (formula : ACCFormula p) (n k : Nat) : ProbabilisticACCFormula p :=
  ProbabilisticACCFormula.normalizeAndMod
    (probabilisticAndModIntermediate formula n k)

/-- Package the normalized formula with its proved depth-three syntax. -/
def probabilisticModPAndSimulationCircuit {p : Nat}
    (formula : ACCFormula p) (n k : Nat) : ProbabilisticModPAndCircuit p :=
  ⟨probabilisticModPAndSimulationFormula formula n k,
    ProbabilisticACCFormula.normalizeAndMod_isProbabilisticModPAndCircuit _
      (ACCFormula.probabilisticOrElimination_hasOnlyAndModGates _ _ _
        (ACCFormula.eliminateAndNotGates_hasOnlyOrAndModGates formula))⟩

/-- Randomness used by the pointwise circuit. Normalization introduces no
new random leaves. -/
def probabilisticModPAndSimulationRandomBitCount {p : Nat}
    (formula : ACCFormula p) (n k : Nat) : Nat :=
  ACCFormula.probabilisticOrEliminationRandomBitCount
    (ACCFormula.eliminateAndNotGates formula) n k

/-- Pointwise resource bounds for the probabilistic AND/MOD intermediate
formula.  The first bound is deliberately expressed as a power of two so its
logarithm can be consumed directly by global normalization. -/
theorem probabilisticAndModIntermediate_bounds {p : Nat}
    (formula : ACCFormula p) (n sourceCoefficient sourceExponent
      sourceDepth k : Nat) (hn : 0 < n) (h_coefficient : 0 < sourceCoefficient)
    (h_size : formula.nodeCount ≤ sourceCoefficient * n ^ sourceExponent)
    (h_depth : formula.depth ≤ sourceDepth) :
    let intermediate := probabilisticAndModIntermediate formula n k
    intermediate.nodeCount ≤
        2 ^ (simulationIntermediateNodeCoefficient sourceCoefficient
          sourceExponent sourceDepth k *
            logInputSize n ^ (simulationPreprocessedDepth sourceDepth + 1)) ∧
    intermediate.IsOfOrder
        (simulationIntermediateOrderCoefficient sourceCoefficient
          sourceExponent k * logInputSize n) ∧
    intermediate.depth ≤ 4 * simulationPreprocessedDepth sourceDepth ∧
    probabilisticModPAndSimulationRandomBitCount formula n k ≤
      simulationRepetitionCoefficient sourceCoefficient sourceExponent k *
        (2 * sourceCoefficient) * n ^ (sourceExponent + 1) := by
  dsimp only
  let preprocessed := ACCFormula.eliminateAndNotGates formula
  let repetitions := ACCFormula.orEliminationRepetitions preprocessed n k
  let logarithm := logInputSize n
  let repetitionCoefficient :=
    simulationRepetitionCoefficient sourceCoefficient sourceExponent k
  let preprocessedDepth := simulationPreprocessedDepth sourceDepth
  let nodeConstant := simulationIntermediateNodeConstant sourceCoefficient
    sourceExponent sourceDepth k
  let nodeCoefficient := simulationIntermediateNodeCoefficient sourceCoefficient
    sourceExponent sourceDepth k
  have h_logarithm : 1 ≤ logarithm := by
    simpa [logarithm] using one_le_logInputSize n hn
  have h_preprocessed_nodes : preprocessed.nodeCount ≤
      2 * sourceCoefficient * n ^ sourceExponent := by
    calc
      preprocessed.nodeCount ≤ 2 * formula.nodeCount := by
        simpa [preprocessed] using ACCFormula.eliminateAndNotGates_nodeCount_le formula
      _ ≤ 2 * (sourceCoefficient * n ^ sourceExponent) := by gcongr
      _ = 2 * sourceCoefficient * n ^ sourceExponent := by ring
  have h_repetitions : repetitions ≤ repetitionCoefficient * logarithm := by
    change ACCFormula.orEliminationRepetitions preprocessed n k ≤ _
    simpa only [repetitionCoefficient, simulationRepetitionCoefficient,
      logarithm, logInputSize] using
        ACCFormula.orEliminationRepetitions_le_of_nodeCount_le preprocessed n
          (2 * sourceCoefficient) sourceExponent k hn (by positivity)
          h_preprocessed_nodes
  have h_preprocessed_depth : preprocessed.depth ≤ preprocessedDepth := by
    calc
      preprocessed.depth ≤ 2 * formula.depth := by
        simpa [preprocessed] using ACCFormula.eliminateAndNotGates_depth_le formula
      _ ≤ 2 * sourceDepth := by gcongr
      _ = preprocessedDepth := by rfl
  have h_scale : 3 * (repetitions + 1) ≤
      3 * (repetitionCoefficient + 1) * logarithm := by
    calc
      3 * (repetitions + 1) ≤
          3 * (repetitionCoefficient * logarithm + 1) := by gcongr
      _ ≤ 3 * ((repetitionCoefficient + 1) * logarithm) := by
        gcongr
        nlinarith
      _ = 3 * (repetitionCoefficient + 1) * logarithm := by ring
  have h_intermediate_nodes_raw :
      (probabilisticAndModIntermediate formula n k).nodeCount ≤
        nodeConstant * logarithm ^ preprocessedDepth * n ^ sourceExponent := by
    have h_scale_pos : 1 ≤
        3 * (repetitionCoefficient + 1) * logarithm := by
      calc
        1 ≤ 3 * (repetitionCoefficient + 1) := by omega
        _ ≤ 3 * (repetitionCoefficient + 1) * logarithm :=
          Nat.le_mul_of_pos_right _ h_logarithm
    have h_gate_power : (3 * (repetitions + 1)) ^ preprocessed.depth ≤
        (3 * (repetitionCoefficient + 1) * logarithm) ^
          preprocessedDepth := by
      calc
        (3 * (repetitions + 1)) ^ preprocessed.depth ≤
            (3 * (repetitionCoefficient + 1) * logarithm) ^
              preprocessed.depth := Nat.pow_le_pow_left h_scale _
        _ ≤ (3 * (repetitionCoefficient + 1) * logarithm) ^
              preprocessedDepth := Nat.pow_le_pow_right h_scale_pos
                h_preprocessed_depth
    calc
      (probabilisticAndModIntermediate formula n k).nodeCount ≤
          (3 * (repetitions + 1)) ^ preprocessed.depth *
            preprocessed.nodeCount := by
        change (ACCFormula.eliminateOrGates repetitions preprocessed).nodeCount ≤ _
        exact ACCFormula.eliminateOrGates_nodeCount_le repetitions preprocessed
      _ ≤ (3 * (repetitionCoefficient + 1) * logarithm) ^
            preprocessedDepth *
          (2 * sourceCoefficient * n ^ sourceExponent) :=
        Nat.mul_le_mul h_gate_power h_preprocessed_nodes
      _ = nodeConstant * logarithm ^ preprocessedDepth *
          n ^ sourceExponent := by
        rw [mul_pow]
        simp only [nodeConstant, simulationIntermediateNodeConstant,
          preprocessedDepth, repetitionCoefficient]
        ring
  have h_node_constant_pos : 0 < nodeConstant := by
    dsimp [nodeConstant, simulationIntermediateNodeConstant]
    positivity
  have h_n_power : n ^ sourceExponent ≤
      2 ^ (logarithm * sourceExponent) := by
    calc
      n ^ sourceExponent ≤ (2 ^ logarithm) ^ sourceExponent := by
        gcongr
        simpa [logarithm] using n_le_two_pow_logInputSize n
      _ = 2 ^ (logarithm * sourceExponent) := by rw [Nat.pow_mul]
  have h_nodes_power : nodeConstant * logarithm ^ preprocessedDepth *
      n ^ sourceExponent ≤
      2 ^ (Nat.clog 2 nodeConstant + logarithm ^ preprocessedDepth +
        logarithm * sourceExponent) := by
    have h_constant : nodeConstant ≤ 2 ^ Nat.clog 2 nodeConstant :=
      Nat.le_pow_clog (by omega) nodeConstant
    have h_log_power : logarithm ^ preprocessedDepth ≤
        2 ^ (logarithm ^ preprocessedDepth) := nat_le_two_pow_self _
    calc
      nodeConstant * logarithm ^ preprocessedDepth * n ^ sourceExponent ≤
          2 ^ Nat.clog 2 nodeConstant *
            2 ^ (logarithm ^ preprocessedDepth) *
              2 ^ (logarithm * sourceExponent) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul h_constant h_log_power) h_n_power
      _ = 2 ^ (Nat.clog 2 nodeConstant + logarithm ^ preprocessedDepth +
          logarithm * sourceExponent) := by
        rw [pow_add, pow_add]
  have h_log_power : logarithm ≤ logarithm ^ (preprocessedDepth + 1) := by
    calc
      logarithm = 1 * logarithm := by simp
      _ ≤ logarithm ^ preprocessedDepth * logarithm := by
        gcongr
        exact Nat.one_le_pow _ _ h_logarithm
      _ = logarithm ^ (preprocessedDepth + 1) := by rw [pow_succ]
  have h_depth_power : logarithm ^ preprocessedDepth ≤
      logarithm ^ (preprocessedDepth + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ h_logarithm
  have h_constant_power : Nat.clog 2 nodeConstant ≤
      Nat.clog 2 nodeConstant * logarithm ^ (preprocessedDepth + 1) := by
    calc
      Nat.clog 2 nodeConstant = Nat.clog 2 nodeConstant * 1 := by omega
      _ ≤ _ := by gcongr; exact Nat.one_le_pow _ _ (by omega)
  have h_exponent : Nat.clog 2 nodeConstant + logarithm ^ preprocessedDepth +
      logarithm * sourceExponent ≤
      nodeCoefficient * logarithm ^ (preprocessedDepth + 1) := by
    dsimp [nodeCoefficient, simulationIntermediateNodeCoefficient]
    calc
      Nat.clog 2 nodeConstant + logarithm ^ preprocessedDepth +
          logarithm * sourceExponent ≤
        Nat.clog 2 nodeConstant * logarithm ^ (preprocessedDepth + 1) +
          logarithm ^ (preprocessedDepth + 1) +
            logarithm ^ (preprocessedDepth + 1) * sourceExponent := by
        gcongr
      _ = (Nat.clog 2 nodeConstant + sourceExponent + 1) *
          logarithm ^ (preprocessedDepth + 1) := by ring
  have h_intermediate_nodes :
      (probabilisticAndModIntermediate formula n k).nodeCount ≤
        2 ^ (nodeCoefficient * logarithm ^ (preprocessedDepth + 1)) :=
    h_intermediate_nodes_raw.trans
      (h_nodes_power.trans (Nat.pow_le_pow_right (by omega) h_exponent))
  have h_intermediate_order :=
    ACCFormula.probabilisticOrElimination_isOfOrder preprocessed n k
      (ACCFormula.eliminateAndNotGates_hasOnlyOrAndModGates formula)
  have h_order_number : max 2 repetitions ≤
      simulationIntermediateOrderCoefficient sourceCoefficient sourceExponent k *
        logarithm := by
    change max 2 repetitions ≤ (repetitionCoefficient + 2) * logarithm
    apply max_le
    · calc
        2 ≤ repetitionCoefficient + 2 := by omega
        _ ≤ (repetitionCoefficient + 2) * logarithm :=
          Nat.le_mul_of_pos_right _ h_logarithm
    · exact h_repetitions.trans
        (Nat.mul_le_mul_right logarithm (Nat.le_add_right repetitionCoefficient 2))
  have h_intermediate_depth :
      (probabilisticAndModIntermediate formula n k).depth ≤
        4 * preprocessedDepth := by
    calc
      (probabilisticAndModIntermediate formula n k).depth ≤
          4 * preprocessed.depth := by
        change (ACCFormula.eliminateOrGates repetitions preprocessed).depth ≤ _
        exact ACCFormula.eliminateOrGates_depth_le repetitions preprocessed
      _ ≤ 4 * preprocessedDepth := by gcongr
  have h_random := ACCFormula.eliminateOrGatesRandomBitCount_le repetitions preprocessed
  have h_random_bound : probabilisticModPAndSimulationRandomBitCount formula n k ≤
      repetitionCoefficient * (2 * sourceCoefficient) *
        n ^ (sourceExponent + 1) := by
    calc
      probabilisticModPAndSimulationRandomBitCount formula n k ≤
          repetitions * preprocessed.nodeCount := by
        change ACCFormula.eliminateOrGatesRandomBitCount repetitions preprocessed ≤ _
        exact h_random
      _ ≤ (repetitionCoefficient * logarithm) *
          (2 * sourceCoefficient * n ^ sourceExponent) := by gcongr
      _ ≤ (repetitionCoefficient * n) *
          (2 * sourceCoefficient * n ^ sourceExponent) := by
        gcongr
        simpa [logarithm] using logInputSize_le n hn
      _ = repetitionCoefficient * (2 * sourceCoefficient) *
          n ^ (sourceExponent + 1) := by rw [pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [nodeCoefficient, logarithm, preprocessedDepth] using
      h_intermediate_nodes
  · exact ProbabilisticACCFormula.isOfOrder_mono _ h_intermediate_order
      h_order_number
  · simpa [preprocessedDepth] using h_intermediate_depth
  · simpa [repetitionCoefficient] using h_random_bound

/-- Global normalization converts power-of-two node bounds, logarithmic
order, and constant depth into explicit quasipolynomial size and
polylogarithmic order bounds. -/
theorem normalizeAndMod_resource_bounds {p : Nat} (hp : 2 ≤ p)
    (formula : ProbabilisticACCFormula p) (n nodeCoefficient nodeExponent
      orderCoefficient depthBound : Nat) (hn : 0 < n)
    (h_formula : formula.HasOnlyAndModGates)
    (h_nodes : formula.nodeCount ≤
      2 ^ (nodeCoefficient * logInputSize n ^ nodeExponent))
    (h_order : formula.IsOfOrder (orderCoefficient * logInputSize n))
    (h_depth : formula.depth ≤ depthBound) :
    ProbabilisticACCFormula.circuitSize
        (ProbabilisticACCFormula.normalizeAndMod formula) ≤
      2 ^ ((3 * p + 2) *
        (Nat.clog 2 (2 * p) + nodeCoefficient + 1) *
        (orderCoefficient + 3 * p) ^ (depthBound + 1) *
        logInputSize n ^ (nodeExponent + (depthBound + 1))) ∧
    (ProbabilisticACCFormula.normalizeAndMod formula).IsOfOrder
      (p * (orderCoefficient + 3 * p) ^ (depthBound + 1) *
        logInputSize n ^ (depthBound + 1)) := by
  let logarithm := logInputSize n
  let nodePower := logarithm ^ nodeExponent
  let largeBase := (orderCoefficient + 3 * p) * logarithm
  have h_logarithm : 1 ≤ logarithm := by
    simpa [logarithm] using one_le_logInputSize n hn
  have h_node_power : 1 ≤ nodePower := by
    exact Nat.one_le_pow _ _ h_logarithm
  have h_factor : 2 * p ≤ 2 ^ Nat.clog 2 (2 * p) :=
    Nat.le_pow_clog (by omega) (2 * p)
  have h_product : 2 * p * formula.nodeCount ≤
      2 ^ (Nat.clog 2 (2 * p) + nodeCoefficient * nodePower) := by
    calc
      2 * p * formula.nodeCount ≤
          2 ^ Nat.clog 2 (2 * p) *
            2 ^ (nodeCoefficient * nodePower) :=
        Nat.mul_le_mul h_factor (by simpa [logarithm, nodePower] using h_nodes)
      _ = 2 ^ (Nat.clog 2 (2 * p) + nodeCoefficient * nodePower) := by
        rw [pow_add]
  have h_clog : Nat.clog 2 (2 * p * formula.nodeCount) ≤
      Nat.clog 2 (2 * p) + nodeCoefficient * nodePower :=
    Nat.clog_le_of_le_pow h_product
  have h_clog_factor : Nat.clog 2 (2 * p * formula.nodeCount) + 1 ≤
      (Nat.clog 2 (2 * p) + nodeCoefficient + 1) * nodePower := by
    calc
      Nat.clog 2 (2 * p * formula.nodeCount) + 1 ≤
          Nat.clog 2 (2 * p) + nodeCoefficient * nodePower + 1 := by gcongr
      _ ≤ Nat.clog 2 (2 * p) * nodePower +
          nodeCoefficient * nodePower + 1 * nodePower := by
        exact Nat.add_le_add
          (Nat.add_le_add
            (Nat.le_mul_of_pos_right _ h_node_power)
            (Nat.le_refl _))
          (by simpa using h_node_power)
      _ = (Nat.clog 2 (2 * p) + nodeCoefficient + 1) * nodePower := by ring
  have h_large_base : 1 ≤ largeBase := by
    dsimp [largeBase]
    have : 1 ≤ orderCoefficient + 3 * p := by omega
    exact (this.trans (Nat.le_mul_of_pos_right _ h_logarithm))
  have h_max_base : max (orderCoefficient * logarithm) (3 * p) ≤
      largeBase := by
    dsimp [largeBase]
    apply max_le
    · exact Nat.mul_le_mul_right logarithm (Nat.le_add_right _ _)
    · calc
        3 * p ≤ 3 * p * logarithm :=
          Nat.le_mul_of_pos_right _ h_logarithm
        _ ≤ (orderCoefficient + 3 * p) * logarithm :=
          Nat.mul_le_mul_right logarithm (Nat.le_add_left _ _)
  have h_rank_power :
      (max (orderCoefficient * logarithm) (3 * p)) ^
          (formula.depth + 1) ≤
        (orderCoefficient + 3 * p) ^ (depthBound + 1) *
          logarithm ^ (depthBound + 1) := by
    calc
      (max (orderCoefficient * logarithm) (3 * p)) ^
          (formula.depth + 1) ≤ largeBase ^ (formula.depth + 1) :=
        Nat.pow_le_pow_left h_max_base _
      _ ≤ largeBase ^ (depthBound + 1) := by
        exact Nat.pow_le_pow_right h_large_base (by omega)
      _ = (orderCoefficient + 3 * p) ^ (depthBound + 1) *
          logarithm ^ (depthBound + 1) := by
        rw [mul_pow]
  have h_size_raw :=
    ProbabilisticACCFormula.normalizeAndMod_circuitSize_le_two_pow hp formula
      (orderCoefficient * logarithm) h_formula h_order
  have h_size_exponent :
      (3 * p + 2) *
          (Nat.clog 2 (2 * p * formula.nodeCount) + 1) *
          (max (orderCoefficient * logarithm) (3 * p)) ^
            (formula.depth + 1) ≤
        (3 * p + 2) *
          (Nat.clog 2 (2 * p) + nodeCoefficient + 1) *
          (orderCoefficient + 3 * p) ^ (depthBound + 1) *
          logarithm ^ (nodeExponent + (depthBound + 1)) := by
    calc
      (3 * p + 2) *
          (Nat.clog 2 (2 * p * formula.nodeCount) + 1) *
          (max (orderCoefficient * logarithm) (3 * p)) ^
            (formula.depth + 1) ≤
        (3 * p + 2) *
          ((Nat.clog 2 (2 * p) + nodeCoefficient + 1) * nodePower) *
          ((orderCoefficient + 3 * p) ^ (depthBound + 1) *
            logarithm ^ (depthBound + 1)) := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.le_refl _) h_clog_factor) h_rank_power
      _ = (3 * p + 2) *
          (Nat.clog 2 (2 * p) + nodeCoefficient + 1) *
          (orderCoefficient + 3 * p) ^ (depthBound + 1) *
          logarithm ^ (nodeExponent + (depthBound + 1)) := by
        dsimp [nodePower]
        rw [pow_add]
        ring
  constructor
  · exact h_size_raw.trans (Nat.pow_le_pow_right (by omega) (by
      simpa [logarithm] using h_size_exponent))
  · have h_degree := ProbabilisticACCFormula.compilationDegree_le_rank formula
    have h_rank := ProbabilisticACCFormula.compilationRank_le hp formula
      (orderCoefficient * logarithm) h_formula h_order
    have h_normalized_order :=
      ProbabilisticACCFormula.normalizeAndMod_isOfOrder formula h_formula
    apply ProbabilisticACCFormula.isOfOrder_mono _ h_normalized_order
    calc
      (p - 1) * ProbabilisticACCFormula.compilationDegree formula ≤
          p * ProbabilisticACCFormula.compilationRank formula :=
        Nat.mul_le_mul (Nat.sub_le p 1) h_degree
      _ ≤ p *
          (max (orderCoefficient * logarithm) (3 * p)) ^
            (formula.depth + 1) := Nat.mul_le_mul_left p h_rank
      _ ≤ p * ((orderCoefficient + 3 * p) ^ (depthBound + 1) *
          logarithm ^ (depthBound + 1)) := Nat.mul_le_mul_left p h_rank_power
      _ = p * (orderCoefficient + 3 * p) ^ (depthBound + 1) *
          logInputSize n ^ (depthBound + 1) := by simp [logarithm]; ring

/-- Formal statement of the probabilistic `MOD_p-AND` simulation theorem:
for every prime modulus, every polynomial-size ACC formula family, and every
error exponent `k`, a simulation satisfying
`HasProbabilisticModPAndCircuitSimulation` exists. -/
def PolynomialSizeACCFormulaFamiliesHaveProbabilisticModPAndCircuitSimulations :
    Prop :=
  ∀ (p sourceCoefficient sourceExponent sourceDepth : Nat),
    p.Prime →
    ∀ sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
        sourceExponent sourceDepth,
    ∀ k : Nat,
      HasProbabilisticModPAndCircuitSimulation sourceFamily k

/-- Every polynomial-size, constant-depth ACC formula family over a prime
modulus has a quasipolynomial-size probabilistic `MOD_p-AND` simulation of
polylogarithmic order, using polynomially many random bits and having
pointwise error at most `n⁻ᵏ`. -/
theorem polynomial_size_acc_formula_families_have_probabilistic_mod_p_and_circuit_simulations :
    PolynomialSizeACCFormulaFamiliesHaveProbabilisticModPAndCircuitSimulations := by
  intro p sourceCoefficient sourceExponent sourceDepth hp sourceFamily k
  have h_source_coefficient : 0 < sourceCoefficient := by
    let one : PNat := ⟨1, by omega⟩
    have h_size := (sourceFamily one).property.2.2.2.1
    have h_nodes := ACCFormula.nodeCount_pos (sourceFamily one).val
    dsimp [one] at h_size
    simpa using h_nodes.trans_le h_size
  let sizeCoefficient := simulationSizeCoefficient p sourceCoefficient
    sourceExponent sourceDepth k
  let sizeExponent := simulationSizeExponent sourceDepth
  let orderCoefficient := simulationOrderCoefficient p sourceCoefficient
    sourceExponent sourceDepth k
  let orderExponent := simulationOrderExponent sourceDepth
  let randomCoefficient := simulationRandomCoefficient sourceCoefficient
    sourceExponent k
  let randomExponent := simulationRandomExponent sourceExponent
  let simulationFamily : ProbabilisticModPAndCircuitFamily p :=
    { circuit := fun n => probabilisticModPAndSimulationCircuit
        (sourceFamily n).val n.val k
      randomBitCount := fun n => probabilisticModPAndSimulationRandomBitCount
        (sourceFamily n).val n.val k }
  have h_size_coefficient : 0 < sizeCoefficient := by
    dsimp [sizeCoefficient, simulationSizeCoefficient]
    have hp_pos : 0 < p := hp.pos
    exact Nat.mul_pos
      (Nat.mul_pos (by omega) (by omega))
      (Nat.pow_pos (by omega))
  have h_order_coefficient : 0 < orderCoefficient := by
    dsimp [orderCoefficient, simulationOrderCoefficient]
    have hp_pos : 0 < p := hp.pos
    positivity
  have h_repetition_coefficient :
      0 < simulationRepetitionCoefficient sourceCoefficient sourceExponent k := by
    dsimp [simulationRepetitionCoefficient]
    have h_clog := Nat.clog_pos (b := 2) (n := 2 * sourceCoefficient)
      (by omega) (by omega)
    omega
  have h_random_coefficient : 0 < randomCoefficient := by
    dsimp [randomCoefficient, simulationRandomCoefficient]
    positivity
  refine ⟨simulationFamily, sizeCoefficient, sizeExponent,
    orderCoefficient, orderExponent, randomCoefficient, randomExponent,
    h_size_coefficient, h_order_coefficient, h_random_coefficient, ?_⟩
  intro n
  let source := (sourceFamily n).val
  let intermediate := probabilisticAndModIntermediate source n.val k
  let nodeCoefficient := simulationIntermediateNodeCoefficient sourceCoefficient
    sourceExponent sourceDepth k
  let nodeExponent := simulationPreprocessedDepth sourceDepth + 1
  let intermediateOrderCoefficient :=
    simulationIntermediateOrderCoefficient sourceCoefficient sourceExponent k
  let depthBound := 4 * simulationPreprocessedDepth sourceDepth
  have h_source_size : source.nodeCount ≤
      sourceCoefficient * n.val ^ sourceExponent :=
    (sourceFamily n).property.2.2.2.1
  have h_source_depth : source.depth ≤ sourceDepth :=
    (sourceFamily n).property.2.2.1
  have h_intermediate := probabilisticAndModIntermediate_bounds source n.val
    sourceCoefficient sourceExponent sourceDepth k n.pos h_source_coefficient
    h_source_size h_source_depth
  have h_intermediate_only : intermediate.HasOnlyAndModGates := by
    dsimp [intermediate, probabilisticAndModIntermediate]
    exact ACCFormula.probabilisticOrElimination_hasOnlyAndModGates _ _ _
      (ACCFormula.eliminateAndNotGates_hasOnlyOrAndModGates source)
  have h_normalized := normalizeAndMod_resource_bounds hp.two_le intermediate n.val
    nodeCoefficient nodeExponent intermediateOrderCoefficient depthBound n.pos
    h_intermediate_only (by
      simpa [intermediate, nodeCoefficient, nodeExponent] using h_intermediate.1)
    (by simpa [intermediate, intermediateOrderCoefficient] using h_intermediate.2.1)
    (by simpa [intermediate, depthBound] using h_intermediate.2.2.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [simulationFamily, probabilisticModPAndSimulationCircuit,
      probabilisticModPAndSimulationFormula, intermediate, nodeCoefficient,
      nodeExponent, intermediateOrderCoefficient, depthBound, sizeCoefficient,
      sizeExponent, simulationSizeCoefficient, simulationSizeExponent,
      quasipolynomialSizeBound] using h_normalized.1
  · simpa [simulationFamily, probabilisticModPAndSimulationCircuit,
      probabilisticModPAndSimulationFormula, intermediate,
      intermediateOrderCoefficient, depthBound, orderCoefficient,
      orderExponent, simulationOrderCoefficient, simulationOrderExponent,
      polylogarithmicBound] using h_normalized.2
  · simpa [simulationFamily, randomCoefficient, randomExponent,
      simulationRandomCoefficient, simulationRandomExponent,
      polynomialBound] using h_intermediate.2.2.2
  · intro inputs _h_length
    have h_preprocessed :=
      ACCFormula.eliminateAndNotGates_hasOnlyOrAndModGates source
    have h_error := ACCFormula.probabilisticOrElimination_errorProbability_le
      hp.one_lt (ACCFormula.eliminateAndNotGates source) n.val k inputs n.pos
      h_preprocessed
    rw [ACCFormula.eliminateAndNotGates_eval hp.one_lt source inputs] at h_error
    have h_normalize_error :=
      ProbabilisticACCFormula.normalizeAndMod_errorProbability_eq hp intermediate
        (probabilisticModPAndSimulationRandomBitCount source n.val k) inputs
        (ACCFormula.eval source inputs) h_intermediate_only
    simpa [simulationFamily, probabilisticModPAndSimulationCircuit,
      probabilisticModPAndSimulationFormula, intermediate,
      probabilisticAndModIntermediate,
      probabilisticModPAndSimulationRandomBitCount, source] using
        h_normalize_error.trans_le h_error

end Circuits.ACC
