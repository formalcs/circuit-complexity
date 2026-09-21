# Razborov-Smolensky ACC[p] Lower-Bound Formalization Reading Guide for Prime p

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

## 1. Start with the circuit-level endpoint

Read [`LowerBounds/Smolensky/Circuit.lean`](LowerBounds/Smolensky/Circuit.lean)
first. The proof of `smolensky_mod_eventually_disagrees` is a short wrapper
around two results: `DAG.ACCCircuit.exists_accFormula_family_exact` unfolds the
circuit family into an equivalent formula family, and
`smolensky_mod_formula_eventually_disagrees` supplies the formula-level
counterexample. The final calculation transfers that counterexample through
the evaluation-equivalence theorem.

Reading this file before following its imports fixes the statement, the roles
of the two moduli, and the exact endpoint of every branch below.

## 2. Read the quantitative formula argument

The mathematical assembly point is
[`LowerBounds/Smolensky/Formula.lean`](LowerBounds/Smolensky/Formula.lean).
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
[`Functions/Mod.lean`](Functions/Mod.lean). In particular, both
`modFunction` and `modFunctionList` are true when the input's Hamming weight is
zero modulo `r`, matching the convention for `ACCFormula.modGate`.

## 3. Follow the polynomial-approximation branch

First read the target depth-three syntax in
[`Formula/NormalForm/ModPAnd.lean`](Formula/NormalForm/ModPAnd.lean): a
`ModPAndCircuit p` is a `MOD_p` gate above AND gates of input literals. Then
read [`Polynomial/Multilinear.lean`](Polynomial/Multilinear.lean) for
the expanded multilinear-polynomial representation, Boolean evaluation, and
degree interface.

The two meet in
[`Simulation/PolynomialApproximation.lean`](Simulation/PolynomialApproximation.lean):

- `exists_multilinear_polynomial` represents an order-`d` deterministic
  `MOD_p`-AND circuit exactly by a polynomial of degree at most `(p - 1) * d`;
- `exists_average_case_multilinear_polynomial_family` combines this with the
  simulation theorem to approximate an ACC formula family with fixed
  polylogarithmic degree and agreement at least `1 - n⁻ᵏ`. The Smolensky
  proof uses `k = 1`.

To see where that average-case simulation comes from, read these modules in
order:

1. [`Simulation/ProbabilisticModPAnd.lean`](Simulation/ProbabilisticModPAnd.lean)
   gives a pointwise probabilistic `MOD_p`-AND simulation;
2. [`Simulation/ModPAndSpecialization.lean`](Simulation/ModPAndSpecialization.lean)
   proves `exists_seed_with_few_disagreements` by finite averaging and shows
   that fixing a seed preserves the normal form; and
3. [`Simulation/DeterministicModPAnd.lean`](Simulation/DeterministicModPAnd.lean)
   chooses such a seed at each length and packages the deterministic
   average-case family.

For a first reading, the public theorems near the ends of these files are
enough. To audit the construction itself, follow
[`Formula/Transform/AndNotElimination.lean`](Formula/Transform/AndNotElimination.lean),
[`Formula/Probabilistic/OrElimination/Interface.lean`](Formula/Probabilistic/OrElimination/Interface.lean),
and
[`Formula/Probabilistic/AndModNormalization/Bounds.lean`](Formula/Probabilistic/AndModNormalization/Bounds.lean).
They respectively leave only OR and modulo gates, replace OR gates with
amplified randomized tests, and compile the resulting AND/MOD formula into
the required `MOD_p`-AND form while controlling size and order.

## 4. Read the algebraic obstruction from its public theorem inward

The public lower bound is `lowDegree_polynomials_disagree_with_mod` in
[`LowerBounds/PolynomialMod.lean`](LowerBounds/PolynomialMod.lean).
It says that, for sufficiently large `n`, any `r` multilinear polynomials of
degree at most `sqrt n` over a suitable characteristic-`p` field must jointly
miscompute their `r` residue-class indicators on at least `2^n / 10` Boolean
inputs.

Its three main inputs are deliberately separated:

- [`LowerBounds/FiniteFieldRootsOfUnity.lean`](LowerBounds/FiniteFieldRootsOfUnity.lean)
  constructs a finite extension of `ZMod p` containing a nontrivial `r`-th
  root of unity `ω`;
- [`LowerBounds/BooleanDegree.lean`](LowerBounds/BooleanDegree.lean)
  develops degree spaces on the Boolean cube. The conceptual core is
  `twist_transverse`, and `lowDegreeMonomials_card_le_error` converts it into
  an error-set rank bound; and
- [`LowerBounds/MultilinearMonomialCount.lean`](LowerBounds/MultilinearMonomialCount.lean)
  proves `lowDegreeMonomials_card_le`, the quantitative estimate that at most
  nine tenths of all multilinear monomials lie below the chosen middle-degree
  cutoff.

After reading those statements, return to `PolynomialMod.lean`. Its weighted
sum `P = ∑ i, ω^i F_i` agrees away from the error set with the character
`x ↦ ω^|x|`; the Boolean-degree rank bound and the monomial count then force
the claimed number of errors.

## 5. Understand the residue-restriction bridge

[`LowerBounds/Smolensky/Restriction.lean`](LowerBounds/Smolensky/Restriction.lean)
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
[`Asymptotics/Polylogarithmic.lean`](Asymptotics/Polylogarithmic.lean).

## 6. Return to the counting contradiction

Now reread `smolensky_mod_eventually_disagrees_shifted` in
[`LowerBounds/Smolensky/Formula.lean`](LowerBounds/Smolensky/Formula.lean).
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

## 7. Audit the circuit-to-formula lift

The formula syntax, evaluation, family bounds, and `ComputesAtLength`
interface are in
[`Formula/Basic.lean`](Formula/Basic.lean),
[`Formula/Semantics.lean`](Formula/Semantics.lean), and
[`Formula/Family.lean`](Formula/Family.lean). The corresponding circuit
interfaces are in
[`Circuit/Basic.lean`](Circuit/Basic.lean),
[`Circuit/Semantics.lean`](Circuit/Semantics.lean), and
[`Circuit/Family.lean`](Circuit/Family.lean).

For the conversion proof, follow the modules under
[`Conversion/CircuitToFormula/`](Conversion/CircuitToFormula/) in
dependency order: `Basic.lean`, `Eval.lean`, `Inputs.lean`, `Depth.lean`,
`Size.lean`, and `Family.lean`. The last file culminates in
`exists_accFormula_family_exact`, which preserves evaluation while keeping
the unrolled family polynomial-size and constant-depth. With that theorem in
hand, reread the short proof in `LowerBounds/Smolensky/Circuit.lean`.

## Suggested Smolensky reading routes

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
`Conversion/CircuitToFormula/` in dependency order and finish with
`Smolensky/Circuit.lean`.

## ACC module layout

The implementation is organized by dependency layer:

- `Circuit/` and `Formula/` contain the two representations, their semantics,
  and family definitions.
- `Formula/Transform/` and `Formula/Probabilistic/` contain formula-local
  transformations.
- `Conversion/CircuitToFormula/` contains the DAG-to-formula conversion and
  its correctness and resource bounds.
- `Asymptotics/` contains shared explicit bounds that do not depend on a
  simulation proof.
- `Polynomial/` contains the reusable expanded multilinear-polynomial algebra.
- `Simulation/` contains family-level simulation and polynomial-approximation
  theorems.
- `LowerBounds/` contains the algebraic lower-bound infrastructure and the
  formula- and circuit-level Smolensky theorems.

Modules should import the narrowest implementation module they use. Import-only
umbrellas and the former flat compatibility paths have been removed, so use the
hierarchical paths directly; for example, import
`ACC.LowerBounds.Smolensky.Circuit` for the circuit-level Smolensky theorem.
