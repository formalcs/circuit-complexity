# Introduction

This is a repository for Lean formalizations in circuit complexity.
It contains a complete formalization of PARITY circuit lower bounds and the Razborov-Smolensky ACC[p] lower bound for prime p.

This development uses Lean 4.33.1 and the corresponding Mathlib release. To
build the full project, run:

```console
lake build
```

## PARITY lower and upper bounds

For every fixed computation depth `d ≥ 2`, the development proves that
PARITY requires size `exp(Ω_d(n^(1/(d-1))))`, matching the classical upper
bound up to constants in the exponent, for both formulas and circuits with
shared gates. This implies that PARITY is not computed by polynomial-size,
constant-depth families of unbounded-fan-in circuits. The proof follows
Håstad's switching-lemma argument. The development also constructs a
matching polynomial-size, logarithmic-depth bounded-fan-in formula family
for PARITY.

See [`Parity/README.md`](Parity/README.md) for the full reading guide and
build instructions for this part of the development.

## Razborov-Smolensky ACC[p] lower bound for prime p

For prime `p` and `r > 1` coprime to `p`, the development proves that every
polynomial-size, constant-depth family of `ACC[p]` circuits disagrees with
`MOD_r` on some input at every sufficiently large input length. The proof
approximates ACC formulas by low-degree polynomials and derives a
contradiction from an algebraic lower bound on multilinear polynomials
computing residues.

See [`ACC/README.md`](ACC/README.md) for the full reading guide and module
layout for this part of the development.
