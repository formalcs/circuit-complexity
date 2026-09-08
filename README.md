# Introduction

This is a repository for Lean formalizations in circuit complexity.
It contains a complete formalization of PARITY circuit lower bounds and the Razborov-Smolensky ACC lower bound.

## PARITY Lower Bound Formalization Reading Guide

### PARITY lower and upper bounds

The current circuit complexity development formalizes lower and upper bounds
for the Boolean PARITY function. Its main lower-bound result proves that PARITY
is not computed by polynomial-size, constant-depth families of
unbounded-fan-in circuits. The proof follows Håstad's switching-lemma argument,
including the finite counting argument, repeated depth reduction,
normalization of general formulas, and the transfer from shared-gate circuits
to formulas. The development also constructs a polynomial-size,
logarithmic-depth bounded-fan-in formula family for PARITY.

This development uses Lean 4.33.1 and the corresponding Mathlib release. To
check its lower bounds and bounded-fan-in upper-bound construction, run:

```console
lake build
lake build Formulas.Parity
```

### PARITY lower bounds reading guide

The shortest route through the mathematical argument is to read the final
wiring lemma first and then follow its three inputs. In outline, the proof is:

```text
general AC⁰ circuit
  → unfold sharing to obtain a formula
  → normalize to a strictly leveled formula with proper bottom gates
  → restrict wide bottom gates in a separate round zero
  → apply the switching lemma repeatedly to collapse the depth
  → obtain a DNF narrower than the remaining live-variable set
  → use the parity-under-restriction and narrow-DNF lemmas
  → lift the resulting counterexample to the original circuit
```

### 1. Start with the conceptual core

Read [`Parity/HastadParityProof/Core.lean`](Parity/HastadParityProof/Core.lean)
first. It is short and exposes the mathematical heart of the lower bound in
`hastad_parity_lower_bound_from_circuit_pieces`. The theorem combines:

1. a restriction that reduces the formula to a narrow DNF;
2. the fact that restricted PARITY is PARITY on the live variables, possibly
   XOR a fixed offset; and
3. the fact that a DNF narrower than its input set misclassifies PARITY or its
   complement.

The parity-specific ingredients are separated from the structural depth
reduction:

- [`Parity/ParityProperties.lean`](Parity/ParityProperties.lean) defines
  `parityBit`, `FormulaComputesParity`, and `BFIFormulaComputesParity`, and
  proves `exists_offset_odd_countP_assembleInput_iff`.
- [`Formulas/CnfDnf/ParityDNF.lean`](Formulas/CnfDnf/ParityDNF.lean) culminates
  in `narrow_dnf_misclassifies_parity`.

### 2. Learn the formula and restriction interfaces

The basic syntax, measures, and semantics are in:

- [`Formulas/Basic.lean`](Formulas/Basic.lean), which defines bounded- and
  unbounded-fan-in formulas, depth, size, and input-index measures;
- [`Formulas/Eval.lean`](Formulas/Eval.lean), which defines evaluation; and
- [`Formulas/CircuitFamilies.lean`](Formulas/CircuitFamilies.lean), which
  packages polynomial-size, bounded-depth formula families.

For the switching argument, continue with:

- [`Formulas/CnfDnf/CnfDnfBasic.lean`](Formulas/CnfDnf/CnfDnfBasic.lean) for
  CNF/DNF shape, properness, clauses, and width;
- [`Formulas/CnfDnf/CnfDnfFamilies.lean`](Formulas/CnfDnf/CnfDnfFamilies.lean)
  for the bundled proper-DNF type; and
- [`Formulas/CnfDnf/RandomRestriction.lean`](Formulas/CnfDnf/RandomRestriction.lean)
  for exact-cardinality restrictions and their action on formulas.

### 3. Read the switching lemma from its public theorem inward

The public result is `switching_lemma_exact` near the end of
[`Formulas/CnfDnf/SwitchingLemma.lean`](Formulas/CnfDnf/SwitchingLemma.lean).
It bounds the fraction of bad exact-cardinality restrictions by
`(10 * σ * w)^d`. Reading that theorem and its immediately preceding counting
lemmas gives the high-level probabilistic argument before the encoding details.

The implementation is divided as follows:

- [`DecisionTrees/DecisionTree.lean`](DecisionTrees/DecisionTree.lean) provides
  decision trees, evaluation, and depth.
- [`Formulas/CnfDnf/SwitchingLemmaBasic.lean`](Formulas/CnfDnf/SwitchingLemmaBasic.lean)
  contains the shared combinatorial definitions.
- [`Formulas/CnfDnf/SwitchingLemmaCanonicalDT.lean`](Formulas/CnfDnf/SwitchingLemmaCanonicalDT.lean)
  constructs the canonical decision tree and proves its semantic and path
  invariants.
- [`Formulas/CnfDnf/SwitchingLemmaCore.lean`](Formulas/CnfDnf/SwitchingLemmaCore.lean)
  defines bad restrictions, enumerates the finite restriction space, and states
  its exact cardinality.
- [`Formulas/CnfDnf/EncoderDecoder.lean`](Formulas/CnfDnf/EncoderDecoder.lean)
  contains the Beame-style injection and its round-trip theorem
  `beame_encoder_decoder_injection_roundtrip`.
- [`Formulas/CnfDnf/SwitchingLemma.lean`](Formulas/CnfDnf/SwitchingLemma.lean)
  turns the injection into the final counting and probability bounds.

`SwitchingLemmaCanonicalDT.lean` and `EncoderDecoder.lean` contain most of the
low-level bookkeeping. They are best read after the public theorem unless the
goal is to audit the injection proof itself.

### 4. Follow normalization and iterative depth reduction

[`Parity/Leveling/ExistsLeveledForm.lean`](Parity/Leveling/ExistsLeveledForm.lean)
is the public normalization interface. Its supporting modules under
[`Parity/Leveling/`](Parity/Leveling/) eliminate explicit NOT gates, simplify
constants, assign alternating levels, establish proper bottom gates, remove
duplicates, and control size.

The restriction and depth-reduction pipeline is then organized into:

- [`Parity/HastadParityProof/BottomLayer.lean`](Parity/HastadParityProof/BottomLayer.lean)
  for extracting and replacing bottom formulas;
- [`Parity/HastadParityProof/SwitchingRound.lean`](Parity/HastadParityProof/SwitchingRound.lean)
  for choosing one restriction that is good for all bottom gates;
- [`Parity/HastadParityProof/DepthReduction.lean`](Parity/HastadParityProof/DepthReduction.lean)
  for `SwitchingRoundState`, one-round depth reduction, composition of
  restrictions, and `exists_iterated_switching_depth_collapse`; and
- [`Parity/HastadParityProof/Restriction.lean`](Parity/HastadParityProof/Restriction.lean)
  for rekeying live variables, the special round-zero fan-in reduction, and the
  density-independent capstone.

The one-third-live calibration used by the strongest public bound is in
[`Parity/HastadParityProof/Restriction/OneThird.lean`](Parity/HastadParityProof/Restriction/OneThird.lean).

### 5. Finish the formula lower bound

[`Parity/HastadParityProof/LowerBounds/OneThird.lean`](Parity/HastadParityProof/LowerBounds/OneThird.lean)
derives the explicit root-exponential lower bound. Its main formula-level
endpoint is `formula_parity_size_lower_bound_root_one_third`.

[`Parity/HastadParityProof/General.lean`](Parity/HastadParityProof/General.lean)
then exposes two eventual lower bounds for general formulas:

- `hastad_parity_lower_bound_general` normalizes a formula before applying the
  leveled proof; and
- `hastad_parity_lower_bound_general_direct` applies the quantitative
  root-form theorem directly.

### 6. Lift the result from formulas to circuits

The shared-gate circuit model and its well-formedness conditions are defined in
[`Circuits/Circuit.lean`](Circuits/Circuit.lean), with evaluation in
[`Circuits/CircuitEval.lean`](Circuits/CircuitEval.lean). The conversion
`Circuit.toUFIByPos` and its correctness proof are in
[`Circuits/Conversion/CircuitToFormula.lean`](Circuits/Conversion/CircuitToFormula.lean).

[`Parity/CircuitParityLowerBounds.lean`](Parity/CircuitParityLowerBounds.lean)
proves that unfolding a well-formed circuit preserves evaluation while
controlling formula depth, size, and input indices. Finally,
[`Parity/CircuitParityLowerBoundsOneThird.lean`](Parity/CircuitParityLowerBoundsOneThird.lean)
proves `circuit_parity_size_lower_bound_root_one_third` and the repository's
main lower-bound theorem:

```lean
theorem parity_does_not_have_ac0_circuits :
    ∀ (c k d : Nat),
      ∃ N,
        ∀ (n : PNat) (circuitFamily : AC0CircuitFamily c k d),
          n.val > N →
            ¬ CircuitComputesParity n.val (circuitFamily n).val
```

### 7. Read the matching upper-bound construction

[`Formulas/Parity.lean`](Formulas/Parity.lean) constructs a balanced
bounded-fan-in XOR tree. The theorem `parityCircuit_is_correct` states its
correctness using `BFIFormulaComputesParity`, and `parityNC1FormulaFamily`
packages its polynomial-size and logarithmic-depth bounds as an `NC1` formula
family.

### Suggested PARITY lower bounds reading routes

For a conceptual overview, read `Core.lean`, `ParityProperties.lean`,
`ParityDNF.lean`, the final theorem of `SwitchingLemma.lean`,
`LowerBounds/OneThird.lean`, `General.lean`, and
`CircuitParityLowerBoundsOneThird.lean`, in that order.

To audit the switching lemma, read `RandomRestriction.lean`,
`SwitchingLemmaCanonicalDT.lean`, `SwitchingLemmaCore.lean`,
`EncoderDecoder.lean`, and finally `SwitchingLemma.lean`.

To audit the engineering needed for arbitrary circuits, follow the modules in
`Parity/Leveling/`, then `DepthReduction.lean`, `Restriction.lean`,
`CircuitToFormula.lean`, and `CircuitParityLowerBounds.lean`.

## Smolensky ACC Lower-Bound Formalization Reading Guide

The target theorem is `smolensky_mod_eventually_disagrees`: if `p` is prime
and `r > 1` is coprime to `p`, every polynomial-size, constant-depth family of
`ACC[p]` circuits disagrees with `MOD_r` on some input at every sufficiently
large input length. The proof has the following shape:

```text
polynomial-size, constant-depth ACC[p] circuit family
  → unfold sharing to obtain an ACC[p] formula family
  → approximate the formula on most inputs by a polylog-degree polynomial
  → append an r-bit residue-selecting suffix and restrict once per residue
  → extend coefficients to a finite field with a nontrivial r-th root of unity
  → apply the Boolean-degree rank bound and count low-degree monomials
  → force at least 2^n / 10 residue-class errors
  → contradict the polynomial approximation's error budget
  → remove the r-input shift and transfer the disagreement back to circuits
```

### 1. Start with the circuit-level endpoint

Read [`ACC/LowerBounds/Smolensky/Circuit.lean`](ACC/LowerBounds/Smolensky/Circuit.lean)
first. The proof of `smolensky_mod_eventually_disagrees` is a short wrapper
around two results: `DAG.ACCCircuit.exists_accFormula_family_exact` unfolds the
circuit family into an equivalent formula family, and
`smolensky_mod_formula_eventually_disagrees` supplies the formula-level
counterexample. The final calculation transfers that counterexample through
the evaluation-equivalence theorem.

Reading this file before following its imports fixes the statement, the roles
of the two moduli, and the exact endpoint of every branch below.

### 2. Read the quantitative formula argument

The mathematical assembly point is
[`ACC/LowerBounds/Smolensky/Formula.lean`](ACC/LowerBounds/Smolensky/Formula.lean).
Begin with `smolensky_mod_eventually_disagrees_shifted`, which works at length
`n + r`. Its first four witnesses are also a map of the proof:

1. `exists_nontrivial_rootOfUnity_galoisField` supplies the character used by
   the algebraic lower bound;
2. `lowDegree_polynomials_disagree_with_mod` supplies that lower bound;
3. `exists_average_case_multilinear_polynomial_family` approximates the ACC
   formula by a low-degree polynomial; and
4. `eventually_polylogarithmicBound_le_sqrt` puts its polylogarithmic degree
   below the lower bound's `sqrt n` threshold.

On a first pass, skip the cardinality arithmetic after these witnesses and
identify the objects `q`, `F`, `agreement`, `errors`, and `residueErrors`.
Return to that arithmetic in step 6. The later theorem
`smolensky_mod_formula_eventually_disagrees` removes the fixed shift, while
`smolensky_mod_lower_bound` packages the usual formula-family lower bound.

The function being separated is defined in
[`ACC/Functions/Mod.lean`](ACC/Functions/Mod.lean). In particular, both
`modFunction` and `modFunctionList` are true when the input's Hamming weight is
zero modulo `r`, matching the convention for `ACCFormula.modGate`.

### 3. Follow the polynomial-approximation branch

First read the target depth-three syntax in
[`ACC/Formula/NormalForm/ModPAnd.lean`](ACC/Formula/NormalForm/ModPAnd.lean): a
`ModPAndCircuit p` is a `MOD_p` gate above AND gates of input literals. Then
read [`ACC/Polynomial/Multilinear.lean`](ACC/Polynomial/Multilinear.lean) for
the expanded multilinear-polynomial representation, Boolean evaluation, and
degree interface.

The two meet in
[`ACC/Simulation/PolynomialApproximation.lean`](ACC/Simulation/PolynomialApproximation.lean):

- `exists_multilinear_polynomial` represents an order-`d` deterministic
  `MOD_p`-AND circuit exactly by a polynomial of degree at most `(p - 1) * d`;
- `exists_average_case_multilinear_polynomial_family` combines this with the
  simulation theorem to approximate an ACC formula family with fixed
  polylogarithmic degree and agreement at least `1 - n⁻ᵏ`. The Smolensky
  proof uses `k = 1`.

To see where that average-case simulation comes from, read these modules in
order:

1. [`ACC/Simulation/ProbabilisticModPAnd.lean`](ACC/Simulation/ProbabilisticModPAnd.lean)
   gives a pointwise probabilistic `MOD_p`-AND simulation;
2. [`ACC/Simulation/ModPAndSpecialization.lean`](ACC/Simulation/ModPAndSpecialization.lean)
   proves `exists_seed_with_few_disagreements` by finite averaging and shows
   that fixing a seed preserves the normal form; and
3. [`ACC/Simulation/DeterministicModPAnd.lean`](ACC/Simulation/DeterministicModPAnd.lean)
   chooses such a seed at each length and packages the deterministic
   average-case family.

For a first reading, the public theorems near the ends of these files are
enough. To audit the construction itself, follow
[`ACC/Formula/Transform/AndNotElimination.lean`](ACC/Formula/Transform/AndNotElimination.lean),
[`ACC/Formula/Probabilistic/OrElimination/Interface.lean`](ACC/Formula/Probabilistic/OrElimination/Interface.lean),
and
[`ACC/Formula/Probabilistic/AndModNormalization/Bounds.lean`](ACC/Formula/Probabilistic/AndModNormalization/Bounds.lean).
They respectively leave only OR and modulo gates, replace OR gates with
amplified randomized tests, and compile the resulting AND/MOD formula into
the required `MOD_p`-AND form while controlling size and order.

### 4. Read the algebraic obstruction from its public theorem inward

The public lower bound is `lowDegree_polynomials_disagree_with_mod` in
[`ACC/LowerBounds/PolynomialMod.lean`](ACC/LowerBounds/PolynomialMod.lean).
It says that, for sufficiently large `n`, any `r` multilinear polynomials of
degree at most `sqrt n` over a suitable characteristic-`p` field must jointly
miscompute their `r` residue-class indicators on at least `2^n / 10` Boolean
inputs.

Its three main inputs are deliberately separated:

- [`ACC/LowerBounds/FiniteFieldRootsOfUnity.lean`](ACC/LowerBounds/FiniteFieldRootsOfUnity.lean)
  constructs a finite extension of `ZMod p` containing a nontrivial `r`-th
  root of unity `ω`;
- [`ACC/LowerBounds/BooleanDegree.lean`](ACC/LowerBounds/BooleanDegree.lean)
  develops degree spaces on the Boolean cube. The conceptual core is
  `twist_transverse`, and `lowDegreeMonomials_card_le_error` converts it into
  an error-set rank bound; and
- [`ACC/LowerBounds/MultilinearMonomialCount.lean`](ACC/LowerBounds/MultilinearMonomialCount.lean)
  proves `lowDegreeMonomials_card_le`, the quantitative estimate that at most
  nine tenths of all multilinear monomials lie below the chosen middle-degree
  cutoff.

After reading those statements, return to `PolynomialMod.lean`. Its weighted
sum `P = ∑ i, ω^i F_i` agrees away from the error set with the character
`x ↦ ω^|x|`; the Boolean-degree rank bound and the monomial count then force
the claimed number of errors.

### 5. Understand the residue-restriction bridge

[`ACC/LowerBounds/Smolensky/Restriction.lean`](ACC/LowerBounds/Smolensky/Restriction.lean)
connects the approximating polynomial, which has `n + r` variables, to the
`r` residue-indicator polynomials required by the algebraic lower bound.
Read it in this order:

1. `residueExtension`, `residueExtension_weight`, and
   `residueExtension_mod_iff`: append `r - i` ones so that the extended input
   has weight zero modulo `r` exactly when the original input has residue `i`;
2. `restrictedPolynomial_eval`: restrict the suffix and extend coefficients
   from `ZMod p` to the finite extension field; and
3. `restrictedPolynomial_totalDegree_le` and
   `restrictedPolynomial_multilinear`: verify that restriction preserves the
   two hypotheses needed by `lowDegree_polynomials_disagree_with_mod`.

The remaining analytic comparison is isolated as
`eventually_polylogarithmicBound_le_sqrt` in
[`ACC/Asymptotics/Polylogarithmic.lean`](ACC/Asymptotics/Polylogarithmic.lean).

### 6. Return to the counting contradiction

Now reread `smolensky_mod_eventually_disagrees_shifted` in
[`ACC/LowerBounds/Smolensky/Formula.lean`](ACC/LowerBounds/Smolensky/Formula.lean).
Assuming the formula computes `MOD_r` on every input of length `n + r`, the
approximation theorem with `k = 1` bounds the polynomial's error set by
roughly `2^(n + r) / (n + r)`. For each residue `i`, `residueExtension` injects
the errors of the restricted polynomial into this common error set. A union
bound over `Fin r` therefore makes `disagreementInputs F` at most `r` times
that error count.

For sufficiently large `n`, this upper bound is strictly less than
`2^n / 10`, contradicting the lower bound from `PolynomialMod.lean`. The proof
then subtracts `r` from an arbitrary sufficiently large positive input length
to turn the shifted result into
`smolensky_mod_formula_eventually_disagrees`.

### 7. Audit the circuit-to-formula lift

The formula syntax, evaluation, family bounds, and `ComputesAtLength`
interface are in
[`ACC/Formula/Basic.lean`](ACC/Formula/Basic.lean),
[`ACC/Formula/Semantics.lean`](ACC/Formula/Semantics.lean), and
[`ACC/Formula/Family.lean`](ACC/Formula/Family.lean). The corresponding circuit
interfaces are in
[`ACC/Circuit/Basic.lean`](ACC/Circuit/Basic.lean),
[`ACC/Circuit/Semantics.lean`](ACC/Circuit/Semantics.lean), and
[`ACC/Circuit/Family.lean`](ACC/Circuit/Family.lean).

For the conversion proof, follow the modules under
[`ACC/Conversion/CircuitToFormula/`](ACC/Conversion/CircuitToFormula/) in
dependency order: `Basic.lean`, `Eval.lean`, `Inputs.lean`, `Depth.lean`,
`Size.lean`, and `Family.lean`. The last file culminates in
`exists_accFormula_family_exact`, which preserves evaluation while keeping
the unrolled family polynomial-size and constant-depth. With that theorem in
hand, reread the short proof in `ACC/LowerBounds/Smolensky/Circuit.lean`.

### Suggested Smolensky reading routes

For a conceptual overview, read the statement and proof skeleton in
`Smolensky/Circuit.lean`, the shifted theorem in `Smolensky/Formula.lean`, the
public endpoints in `PolynomialApproximation.lean` and `PolynomialMod.lean`,
then `Smolensky/Restriction.lean`, and finally return to `Formula.lean` and
`Circuit.lean`.

To audit polynomial approximation, follow `AndNotElimination.lean`, the
`OrElimination/` modules, the `AndModNormalization/` modules,
`ProbabilisticModPAnd.lean`, `ModPAndSpecialization.lean`,
`DeterministicModPAnd.lean`, `Multilinear.lean`, and
`PolynomialApproximation.lean`.

To audit the algebraic lower bound, read `FiniteFieldRootsOfUnity.lean`,
`BooleanDegree.lean`, `MultilinearMonomialCount.lean`, `PolynomialMod.lean`,
and `Smolensky/Restriction.lean`, in that order.

To audit the lift from shared-gate circuits, read the six modules under
`ACC/Conversion/CircuitToFormula/` in dependency order and finish with
`Smolensky/Circuit.lean`.
