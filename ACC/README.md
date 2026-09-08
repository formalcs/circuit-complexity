# ACC module layout

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
