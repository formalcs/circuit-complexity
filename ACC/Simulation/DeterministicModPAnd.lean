import ACC.Formula.Family
import ACC.Simulation.ProbabilisticModPAnd
import ACC.Simulation.ModPAndSpecialization

namespace Circuits.ACC

/-! ## Deterministic average-case `MOD_p`-AND simulations -/

/-- The number of length-`n` inputs on which a deterministic simulation agrees
with its source ACC formula. -/
def deterministicAgreementCount {p : Nat}
    {sourceCoefficient sourceExponent sourceDepth : Nat}
    (sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
      sourceExponent sourceDepth)
    (simulationFamily : DeterministicModPAndCircuitFamily p)
    (n : PNat) : Nat :=
  ((Finset.univ : Finset (Fin n.val → Bool)).filter fun inputs =>
    ACCFormula.eval (simulationFamily.circuit n).val (List.ofFn inputs) =
      ACCFormula.eval (sourceFamily n).val (List.ofFn inputs)).card

/-- A fixed polynomial-size, constant-depth ACC formula family has a
deterministic `MOD_p`-AND simulation of quasipolynomial size and
polylogarithmic order that is correct on at least a `1 - n⁻ᵏ` fraction of
the inputs at every positive input length `n`.

The four resource-bound witnesses may depend on the modulus, the source family,
and the requested error exponent, but are independent of `n`. -/
def HasDeterministicModPAndCircuitAverageCaseSimulation
    {p sourceCoefficient sourceExponent sourceDepth : Nat}
    (sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
      sourceExponent sourceDepth) (k : Nat) : Prop :=
  ∃ simulationFamily : DeterministicModPAndCircuitFamily p,
  ∃ sizeCoefficient sizeExponent orderCoefficient orderExponent : Nat,
    0 < sizeCoefficient ∧
    0 < orderCoefficient ∧
    ∀ n : PNat,
      ACCFormula.circuitSize (simulationFamily.circuit n).val ≤
          quasipolynomialSizeBound n.val sizeCoefficient sizeExponent ∧
      ACCFormula.IsOfOrder (simulationFamily.circuit n).val
          (polylogarithmicBound n.val orderCoefficient orderExponent) ∧
      (deterministicAgreementCount sourceFamily simulationFamily n : ℚ) ≥
        ((2 ^ n.val : Nat) : ℚ) * (1 - 1 / (n.val : ℚ) ^ k)

/-- Formal statement of the deterministic average-case simulation theorem:
for every prime modulus, every polynomial-size constant-depth ACC formula
family, and every `k`, there is a deterministic quasipolynomial-size
`MOD_p`-AND family of polylogarithmic order agreeing with the source on at
least `2^n * (1 - n⁻ᵏ)` inputs of every length `n`. -/
def PolynomialSizeACCFormulaFamiliesHaveDeterministicModPAndCircuitAverageCaseSimulations :
    Prop :=
  ∀ (p sourceCoefficient sourceExponent sourceDepth : Nat),
    p.Prime →
    ∀ sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
        sourceExponent sourceDepth,
    ∀ k : Nat,
      HasDeterministicModPAndCircuitAverageCaseSimulation sourceFamily k

/-- Every polynomial-size, constant-depth ACC formula family over a prime
modulus has a deterministic quasipolynomial-size `MOD_p`-AND simulation of
polylogarithmic order that is correct on a `1 - n⁻ᵏ` fraction of the inputs
at every input length. -/
theorem
  polynomial_size_acc_formula_families_have_deterministic_mod_p_and_circuit_average_case_simulations
    :
    PolynomialSizeACCFormulaFamiliesHaveDeterministicModPAndCircuitAverageCaseSimulations := by
  intro p sourceCoefficient sourceExponent sourceDepth hp sourceFamily k
  obtain ⟨probabilisticFamily, sizeCoefficient, sizeExponent,
      orderCoefficient, orderExponent, randomCoefficient, randomExponent,
      h_sizeCoefficient, h_orderCoefficient, _h_randomCoefficient,
      h_probabilistic⟩ :=
    polynomial_size_acc_formula_families_have_probabilistic_mod_p_and_circuit_simulations
      p sourceCoefficient sourceExponent sourceDepth hp sourceFamily k
  have h_seed_exists : ∀ n : PNat,
      ∃ randomBits : Fin (probabilisticFamily.randomBitCount n) → Bool,
        fixedSeedDisagreementCount (probabilisticFamily.circuit n).val
            (probabilisticFamily.randomBitCount n)
            (fun inputs : Fin n.val → Bool =>
              ACCFormula.eval (sourceFamily n).val (List.ofFn inputs))
            randomBits * n.val ^ k ≤
          2 ^ n.val := by
    intro n
    apply exists_seed_with_few_disagreements
      (probabilisticFamily.circuit n).val
      (probabilisticFamily.randomBitCount n) k
      (fun inputs : Fin n.val → Bool =>
        ACCFormula.eval (sourceFamily n).val (List.ofFn inputs))
      n.pos
    intro inputs
    exact (h_probabilistic n).2.2.2 (List.ofFn inputs) (by simp)
  let chosenSeed : (n : PNat) →
      (Fin (probabilisticFamily.randomBitCount n) → Bool) :=
    fun n => Classical.choose (h_seed_exists n)
  have h_chosenSeed : ∀ n : PNat,
      fixedSeedDisagreementCount (probabilisticFamily.circuit n).val
          (probabilisticFamily.randomBitCount n)
          (fun inputs : Fin n.val → Bool =>
            ACCFormula.eval (sourceFamily n).val (List.ofFn inputs))
          (chosenSeed n) * n.val ^ k ≤
        2 ^ n.val := by
    intro n
    exact Classical.choose_spec (h_seed_exists n)
  let deterministicFamily : DeterministicModPAndCircuitFamily p :=
    { circuit := fun n =>
        ⟨specializeProbabilisticModPAndFormula
            (probabilisticFamily.circuit n).val
            (List.ofFn (chosenSeed n)),
          specializeProbabilisticModPAndFormula_isModPAndCircuit
            (probabilisticFamily.circuit n).val
            (List.ofFn (chosenSeed n))
            (probabilisticFamily.circuit n).property⟩ }
  refine ⟨deterministicFamily, sizeCoefficient, sizeExponent,
    orderCoefficient, orderExponent, h_sizeCoefficient, h_orderCoefficient,
    ?_⟩
  intro n
  refine ⟨?_, ?_, ?_⟩
  · exact (specializeProbabilisticModPAndFormula_circuitSize_le
      (probabilisticFamily.circuit n).val (List.ofFn (chosenSeed n))
      (probabilisticFamily.circuit n).property).trans (h_probabilistic n).1
  · exact specializeProbabilisticModPAndFormula_isOfOrder
      (probabilisticFamily.circuit n).val (List.ofFn (chosenSeed n))
      (polylogarithmicBound n.val orderCoefficient orderExponent)
      (probabilisticFamily.circuit n).property (h_probabilistic n).2.1
  · have h_agreement :=
      specializeProbabilisticModPAndFormula_agreement_bound
        (probabilisticFamily.circuit n).val
        (probabilisticFamily.randomBitCount n) k
        (fun inputs : Fin n.val → Bool =>
          ACCFormula.eval (sourceFamily n).val (List.ofFn inputs))
        (chosenSeed n) n.pos (probabilisticFamily.circuit n).property
        (h_chosenSeed n)
    simpa [deterministicAgreementCount, deterministicFamily] using h_agreement

end Circuits.ACC
