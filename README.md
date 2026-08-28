# cslib

`cslib` is a repository for Lean formalizations in theoretical computer
science.

## Formalizations

### Circuit complexity: PARITY lower and upper bounds

The current circuit-complexity development formalizes lower and upper bounds
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

## Circuit-complexity reading guide

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

## Suggested circuit-complexity reading routes

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
