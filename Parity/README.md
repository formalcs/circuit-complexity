# PARITY Lower Bound Formalization Reading Guide

## PARITY lower and upper bounds

The current circuit complexity development formalizes lower and upper bounds
for the Boolean PARITY function. For every fixed computation depth `d ≥ 2`,
it proves that PARITY requires size `exp(Ω_d(n^(1/(d-1))))`, matching the
classical upper bound up to constants in the exponent. This holds for both
formulas and circuits with shared gates and implies that PARITY is not
computed by polynomial-size, constant-depth families of unbounded-fan-in
circuits. The quantitative bound uses a one-third-live round-zero restriction.
The proof follows Håstad's switching-lemma argument,
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

The default build includes the quantitative circuit theorem. To check that
endpoint explicitly, run `lake build Parity.CircuitParityLowerBoundsSharp`.

## PARITY lower bounds reading guide

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

Read [`HastadParityProof/Core.lean`](HastadParityProof/Core.lean)
first. It is short and exposes the mathematical heart of the lower bound in
`hastad_parity_lower_bound_from_circuit_pieces`. The theorem combines:

1. a restriction that reduces the formula to a narrow DNF;
2. the fact that restricted PARITY is PARITY on the live variables, possibly
   XOR a fixed offset; and
3. the fact that a DNF narrower than its input set misclassifies PARITY or its
   complement.

The parity-specific ingredients are separated from the structural depth
reduction:

- [`ParityProperties.lean`](ParityProperties.lean) defines
  `parityBit`, `FormulaComputesParity`, and `BFIFormulaComputesParity`, and
  proves `exists_offset_odd_countP_assembleInput_iff`.
- [`../Formulas/CnfDnf/ParityDNF.lean`](../Formulas/CnfDnf/ParityDNF.lean) culminates
  in `narrow_dnf_misclassifies_parity`.

### 2. Learn the formula and restriction interfaces

The basic syntax, measures, and semantics are in:

- [`../Formulas/Basic.lean`](../Formulas/Basic.lean), which defines bounded- and
  unbounded-fan-in formulas, depth, size, and input-index measures;
- [`../Formulas/Eval.lean`](../Formulas/Eval.lean), which defines evaluation; and
- [`../Formulas/CircuitFamilies.lean`](../Formulas/CircuitFamilies.lean), which
  packages polynomial-size, bounded-depth formula families.

For the switching argument, continue with:

- [`../Formulas/CnfDnf/CnfDnfBasic.lean`](../Formulas/CnfDnf/CnfDnfBasic.lean) for
  CNF/DNF shape, properness, clauses, and width;
- [`../Formulas/CnfDnf/CnfDnfFamilies.lean`](../Formulas/CnfDnf/CnfDnfFamilies.lean)
  for the bundled proper-DNF type; and
- [`../Formulas/CnfDnf/RandomRestriction.lean`](../Formulas/CnfDnf/RandomRestriction.lean)
  for exact-cardinality restrictions and their action on formulas.

### 3. Read the switching lemma from its public theorem inward

The public result is `switching_lemma_exact` near the end of
[`../Formulas/CnfDnf/SwitchingLemma.lean`](../Formulas/CnfDnf/SwitchingLemma.lean).
It bounds the fraction of bad exact-cardinality restrictions by
`(10 * σ * w)^d`. Reading that theorem and its immediately preceding counting
lemmas gives the high-level probabilistic argument before the encoding details.

The implementation is divided as follows:

- [`../DecisionTrees/DecisionTree.lean`](../DecisionTrees/DecisionTree.lean) provides
  decision trees, evaluation, and depth.
- [`../Formulas/CnfDnf/SwitchingLemmaBasic.lean`](../Formulas/CnfDnf/SwitchingLemmaBasic.lean)
  contains the shared combinatorial definitions.
- [`../Formulas/CnfDnf/SwitchingLemmaCanonicalDT.lean`](../Formulas/CnfDnf/SwitchingLemmaCanonicalDT.lean)
  constructs the canonical decision tree and proves its semantic and path
  invariants.
- [`../Formulas/CnfDnf/SwitchingLemmaCore.lean`](../Formulas/CnfDnf/SwitchingLemmaCore.lean)
  defines bad restrictions, enumerates the finite restriction space, and states
  its exact cardinality.
- [`../Formulas/CnfDnf/EncoderDecoder.lean`](../Formulas/CnfDnf/EncoderDecoder.lean)
  contains the Beame-style injection and its round-trip theorem
  `beame_encoder_decoder_injection_roundtrip`.
- [`../Formulas/CnfDnf/SwitchingLemma.lean`](../Formulas/CnfDnf/SwitchingLemma.lean)
  turns the injection into the final counting and probability bounds.

`SwitchingLemmaCanonicalDT.lean` and `EncoderDecoder.lean` contain most of the
low-level bookkeeping. They are best read after the public theorem unless the
goal is to audit the injection proof itself.

### 4. Follow normalization and iterative depth reduction

[`Leveling/ExistsLeveledForm.lean`](Leveling/ExistsLeveledForm.lean)
is the public normalization interface. Its supporting modules under
[`Leveling/`](Leveling/) eliminate explicit NOT gates, simplify
constants, assign alternating levels, establish proper bottom gates, remove
duplicates, and control size.

The restriction and depth-reduction pipeline is then organized into:

- [`HastadParityProof/BottomLayer.lean`](HastadParityProof/BottomLayer.lean)
  for extracting and replacing bottom formulas;
- [`HastadParityProof/SwitchingRound.lean`](HastadParityProof/SwitchingRound.lean)
  for choosing one restriction that is good for all bottom gates;
- [`HastadParityProof/DepthReduction.lean`](HastadParityProof/DepthReduction.lean)
  for `SwitchingRoundState`, one-round depth reduction, composition of
  restrictions, and `exists_iterated_switching_depth_collapse_sharp`; and
- [`HastadParityProof/Restriction.lean`](HastadParityProof/Restriction.lean)
  for rekeying live variables, the special round-zero fan-in reduction, and the
  density-independent capstone.

The one-third-live calibration used by the strongest public bound is in
[`HastadParityProof/Restriction/OneThird.lean`](HastadParityProof/Restriction/OneThird.lean).

### 5. Finish the formula lower bound

[`HastadParityProof/LowerBounds/Sharp.lean`](HastadParityProof/LowerBounds/Sharp.lean)
derives the exponent `1/(d-1)` using the one-third-live calibration. Its main
formula-level endpoint is `formula_parity_size_lower_bound_root_sharp`.
The terminal depth-two step requires only the linear live-variable reserve
`40 * (t + 1)`. Together with `d - 2` nonterminal rounds, this gives the
reserve `(20 * t)^(d - 2) * (40 * (t + 1))` and saves one power of the
switching cutoff.

[`HastadParityProof/LowerBounds/OneThird.lean`](HastadParityProof/LowerBounds/OneThird.lean)
provides the earlier quantitative bound and supporting one-third arithmetic.

[`HastadParityProof/General.lean`](HastadParityProof/General.lean)
then exposes two eventual lower bounds for general formulas:

- `hastad_parity_lower_bound_general` normalizes a formula before applying the
  leveled proof; and
- `hastad_parity_lower_bound_general_direct` applies the quantitative
  root-form theorem directly.

### 6. Lift the result from formulas to circuits

The shared-gate circuit model and its well-formedness conditions are defined in
[`../Circuits/Circuit.lean`](../Circuits/Circuit.lean), with evaluation in
[`../Circuits/CircuitEval.lean`](../Circuits/CircuitEval.lean). The conversion
`Circuit.toUFIByPos` and its correctness proof are in
[`../Circuits/Conversion/CircuitToFormula.lean`](../Circuits/Conversion/CircuitToFormula.lean).

[`CircuitParityLowerBounds.lean`](CircuitParityLowerBounds.lean)
proves that unfolding a well-formed circuit preserves evaluation while
controlling formula depth, size, and input indices.
[`NormalizeNullary.lean`](NormalizeNullary.lean) replaces nullary
AND/OR gates with depth-zero constants, preserving evaluation and node count.
This lets the circuit-to-formula transfer preserve computation depth.

[`CircuitParityLowerBoundsSharp.lean`](CircuitParityLowerBoundsSharp.lean)
proves the quantitative circuit theorem in the namespace
`Circuits.CircuitParityLowerBounds`:

```lean
theorem circuit_parity_size_lower_bound_root_sharp (d : Nat) (hd : 2 ≤ d) :
    ∃ N, ∀ n, N ≤ n →
      ∀ (circuit : Circuit),
        circuit.inputWidth = n →
        circuit.depth ≤ d + 1 →
        CircuitComputesParity n circuit →
        2 ^ (Nat.nthRoot (d - 1) (n / (360 * 40 ^ (d - 2))) /
            (8 * (d + 3))) ≤ circuit.circuitSize
```

Here `d` counts computation layers. `Circuit.depth` also counts the output
wire, which accounts for `d + 1` in the hypothesis. The integer root and
quotient give an explicit bound of the form `exp(Ω_d(n^(1/(d-1))))` for
sufficiently large `n`.

[`CircuitParityLowerBoundsOneThird.lean`](CircuitParityLowerBoundsOneThird.lean)
retains `circuit_parity_size_lower_bound_root_one_third` and the qualitative
family-level corollary:

```lean
theorem parity_does_not_have_ac0_circuits :
    ∀ (c k d : Nat),
      ∃ N,
        ∀ (n : PNat) (circuitFamily : AC0CircuitFamily c k d),
          n.val > N →
            ¬ CircuitComputesParity n.val (circuitFamily n).val
```

### 7. Read the NC^1 upper-bound construction

[`../Formulas/Parity.lean`](../Formulas/Parity.lean) constructs a balanced
bounded-fan-in XOR tree. The theorem `parityCircuit_is_correct` states its
correctness using `BFIFormulaComputesParity`, and `parityNC1FormulaFamily`
packages its polynomial-size and logarithmic-depth bounds as an `NC1` formula
family.

## Suggested PARITY lower bounds reading routes

For a conceptual overview, read `Core.lean`, `ParityProperties.lean`,
`ParityDNF.lean`, the final theorem of `SwitchingLemma.lean`,
`LowerBounds/Sharp.lean`, `NormalizeNullary.lean`, and
`CircuitParityLowerBoundsSharp.lean`, in that order. For the qualitative
family-level corollaries, continue with `General.lean` and
`CircuitParityLowerBoundsOneThird.lean`.

To audit the switching lemma, read `RandomRestriction.lean`,
`SwitchingLemmaCanonicalDT.lean`, `SwitchingLemmaCore.lean`,
`EncoderDecoder.lean`, and finally `SwitchingLemma.lean`.

To audit the engineering needed for arbitrary circuits, follow the modules in
`Leveling/`, then `DepthReduction.lean`, `Restriction.lean`,
`CircuitToFormula.lean`, `CircuitParityLowerBounds.lean`,
`NormalizeNullary.lean`, and `CircuitParityLowerBoundsSharp.lean`.
