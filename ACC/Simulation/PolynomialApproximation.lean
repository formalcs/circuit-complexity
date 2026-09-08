import ACC.Polynomial.Multilinear
import ACC.Formula.NormalForm.ModPAnd
import ACC.Simulation.DeterministicModPAnd

namespace Circuits.ACC

/-! ## Polynomial approximation of deterministic `MOD_p`-AND circuits -/

namespace ModPAndCircuit

open MultilinearPolynomial

/-- The multilinear polynomial for one (possibly negated) input literal.
Out-of-range inputs have the same default value (`false`) as `ACCFormula.eval`.
-/
def literalPolynomial (p n idx : Nat) (negated : Bool) :
    MultilinearPolynomial p n :=
  if h : idx < n then
    if negated then
      add (one p n) (neg (X p ⟨idx, h⟩))
    else X p ⟨idx, h⟩
  else if negated then one p n else zero p n

/-- Multiply the polynomials of a list of input literals. -/
def literalsPolynomial {p : Nat} (n : Nat) :
    List (ACCFormula p) → MultilinearPolynomial p n
  | [] => one p n
  | .input idx negated :: literals =>
      mul (literalPolynomial p n idx negated) (literalsPolynomial n literals)
  | _ :: literals => literalsPolynomial n literals

/-- The polynomial of an AND gate over input literals. -/
def conjunctionPolynomial {p : Nat} (n : Nat) :
    ACCFormula p → MultilinearPolynomial p n
  | .andGate literals => literalsPolynomial n literals
  | _ => zero p n

/-- Sum the polynomials represented by the children of a modulo gate. -/
def conjunctionsPolynomial {p : Nat} (n : Nat) :
    List (ACCFormula p) → MultilinearPolynomial p n
  | [] => zero p n
  | conjunction :: conjunctions =>
      add (conjunctionPolynomial n conjunction)
        (conjunctionsPolynomial n conjunctions)

/-- The Fermat zero-indicator polynomial associated to a `MOD_p-AND`
circuit. -/
def representingPolynomial {p : Nat} (n : Nat) :
    ACCFormula p → MultilinearPolynomial p n
  | .modGate conjunctions =>
      add (one p n)
        (neg (pow (conjunctionsPolynomial n conjunctions) (p - 1)))
  | _ => zero p n

private theorem literalPolynomial_eval {p n idx : Nat} (negated : Bool)
    (x : Fin n → Bool) :
    MultilinearPolynomial.eval (literalPolynomial p n idx negated) x =
      ((ACCFormula.eval (p := p) (.input idx negated)
        (List.ofFn x)).toNat : ZMod p) := by
  simp only [literalPolynomial, ACCFormula.eval]
  by_cases h : idx < n
  · simp only [h, dite_true]
    have hlookup : (List.ofFn x)[idx]?.getD false = x ⟨idx, h⟩ := by
      simp [h]
    rw [hlookup]
    cases negated <;> cases hx : x ⟨idx, h⟩ <;> simp [hx]
  · simp only [h, dite_false]
    have hlength : (List.ofFn x).length ≤ idx := by simp; omega
    have hlookup : (List.ofFn x)[idx]? = none :=
      List.getElem?_eq_none hlength
    rw [hlookup]
    cases negated <;> simp

private theorem all_cast {p : Nat} (values : List Bool) :
    ((if values.all (· == true) then true else false).toNat : ZMod p) =
      (values.map fun value => (value.toNat : ZMod p)).prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      cases value <;> simp_all

private theorem eval_andGate_cast {p : Nat} (formulas : List (ACCFormula p))
    (inputs : List Bool) :
    ((ACCFormula.eval (.andGate formulas) inputs).toNat : ZMod p) =
      (formulas.map fun formula =>
        ((ACCFormula.eval formula inputs).toNat : ZMod p)).prod := by
  convert all_cast (p := p) (formulas.map fun formula =>
    ACCFormula.eval formula inputs) using 1
  · simp only [ACCFormula.eval]
  · rw [List.map_map]
    rfl

private theorem literalsPolynomial_eval {p n : Nat}
    (literals : List (ACCFormula p))
    (hliterals : ∀ literal ∈ literals, IsModPAndLiteral literal)
    (x : Fin n → Bool) :
    MultilinearPolynomial.eval (literalsPolynomial n literals) x =
      ((ACCFormula.eval (.andGate literals) (List.ofFn x)).toNat : ZMod p) := by
  induction literals with
  | nil => simp [literalsPolynomial, ACCFormula.eval]
  | cons literal literals ih =>
      have hliteral := hliterals literal (by simp)
      have htail : ∀ child ∈ literals, IsModPAndLiteral child := by
        intro child hchild
        exact hliterals child (by simp [hchild])
      cases literal with
      | input idx negated =>
          rw [literalsPolynomial, MultilinearPolynomial.eval_mul,
            literalPolynomial_eval, ih htail]
          symm
          rw [eval_andGate_cast]
          rw [eval_andGate_cast]
          simp
      | constant value label => simp [IsModPAndLiteral] at hliteral
      | notGate formula => simp [IsModPAndLiteral] at hliteral
      | andGate formulas => simp [IsModPAndLiteral] at hliteral
      | orGate formulas => simp [IsModPAndLiteral] at hliteral
      | modGate formulas => simp [IsModPAndLiteral] at hliteral

private theorem conjunctionPolynomial_eval {p n : Nat}
    (formula : ACCFormula p) (hformula : IsAndOfModPAndLiterals formula)
    (x : Fin n → Bool) :
    MultilinearPolynomial.eval (conjunctionPolynomial n formula) x =
      ((ACCFormula.eval formula (List.ofFn x)).toNat : ZMod p) := by
  cases formula with
  | andGate literals =>
      exact literalsPolynomial_eval literals hformula x
  | input idx negated => simp [IsAndOfModPAndLiterals] at hformula
  | constant value label => simp [IsAndOfModPAndLiterals] at hformula
  | notGate formula => simp [IsAndOfModPAndLiterals] at hformula
  | orGate formulas => simp [IsAndOfModPAndLiterals] at hformula
  | modGate formulas => simp [IsAndOfModPAndLiterals] at hformula

private theorem conjunctionsPolynomial_eval {p n : Nat}
    (formulas : List (ACCFormula p))
    (hformulas : ∀ formula ∈ formulas, IsAndOfModPAndLiterals formula)
    (x : Fin n → Bool) :
    MultilinearPolynomial.eval (conjunctionsPolynomial n formulas) x =
      (formulas.map fun formula =>
        ((ACCFormula.eval formula (List.ofFn x)).toNat : ZMod p)).sum := by
  induction formulas with
  | nil => simp [conjunctionsPolynomial]
  | cons formula formulas ih =>
      rw [conjunctionsPolynomial, MultilinearPolynomial.eval_add,
        conjunctionPolynomial_eval formula (hformulas formula (by simp)),
        ih (by
          intro child hchild
          exact hformulas child (by simp [hchild]))]
      simp

private theorem eval_modGate_eq_true_iff {p : Nat}
    (formulas : List (ACCFormula p)) (inputs : List Bool) :
    ACCFormula.eval (.modGate formulas) inputs = true ↔
      (formulas.map fun formula =>
        ((ACCFormula.eval formula inputs).toNat : ZMod p)).sum = 0 := by
  rw [show ACCFormula.eval (.modGate formulas) inputs = true ↔
      ((formulas.map fun formula => ACCFormula.eval formula inputs).map
        Bool.toNat).sum % p = 0 by simp [ACCFormula.eval]]
  rw [← Nat.dvd_iff_mod_eq_zero,
    ← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_list_sum, List.map_map, List.map_map]
  rfl

private theorem eval_modGate_cast {p : Nat} (hp : p.Prime)
    (formulas : List (ACCFormula p)) (inputs : List Bool) :
    ((ACCFormula.eval (.modGate formulas) inputs).toNat : ZMod p) =
      1 - (formulas.map fun formula =>
        ((ACCFormula.eval formula inputs).toNat : ZMod p)).sum ^ (p - 1) := by
  let total := (formulas.map fun formula =>
    ((ACCFormula.eval formula inputs).toNat : ZMod p)).sum
  by_cases htotal : total = 0
  · have heval := (eval_modGate_eq_true_iff formulas inputs).2 htotal
    rw [heval]
    simp [total, htotal, Nat.sub_ne_zero_of_lt hp.one_lt]
  · let _ : Fact p.Prime := ⟨hp⟩
    have hpow : total ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one htotal
    have heval : ACCFormula.eval (.modGate formulas) inputs = false := by
      cases h : ACCFormula.eval (.modGate formulas) inputs with
      | false => rfl
      | true => exact False.elim (htotal
          ((eval_modGate_eq_true_iff formulas inputs).1 h))
    rw [heval, hpow]
    simp

private theorem literalPolynomial_degree {p n idx : Nat} (negated : Bool) :
    DegreeAtMost (literalPolynomial p n idx negated) 1 := by
  simp only [literalPolynomial]
  split
  next h =>
    cases negated
    · exact degreeAtMost_variable _
    · exact degreeAtMost_add
        (degreeAtMost_one (d := 1))
        (degreeAtMost_neg (degreeAtMost_variable _))
  next h =>
    cases negated
    · exact degreeAtMost_zero
    · exact degreeAtMost_one

private theorem literalsPolynomial_degree {p n : Nat}
    (literals : List (ACCFormula p))
    (hliterals : ∀ literal ∈ literals, IsModPAndLiteral literal) :
    DegreeAtMost (literalsPolynomial n literals) literals.length := by
  induction literals with
  | nil => simpa [literalsPolynomial] using
      (degreeAtMost_one (p := p) (n := n) (d := 0))
  | cons literal literals ih =>
      have hliteral := hliterals literal (by simp)
      have htail : ∀ child ∈ literals, IsModPAndLiteral child := by
        intro child hchild
        exact hliterals child (by simp [hchild])
      cases literal with
      | input idx negated =>
          simpa [literalsPolynomial, Nat.add_comm] using
            degreeAtMost_mul (literalPolynomial_degree (p := p) (n := n)
              (idx := idx) negated) (ih htail)
      | constant value label => simp [IsModPAndLiteral] at hliteral
      | notGate formula => simp [IsModPAndLiteral] at hliteral
      | andGate formulas => simp [IsModPAndLiteral] at hliteral
      | orGate formulas => simp [IsModPAndLiteral] at hliteral
      | modGate formulas => simp [IsModPAndLiteral] at hliteral

private theorem conjunctionPolynomial_degree {p n d : Nat}
    (formula : ACCFormula p) (hliterals : IsAndOfModPAndLiterals formula)
    (horder : ACCFormula.IsOfOrder formula d) :
    DegreeAtMost (conjunctionPolynomial n formula) d := by
  cases formula with
  | andGate literals =>
      simp only [ACCFormula.IsOfOrder] at horder
      exact degreeAtMost_mono (literalsPolynomial_degree literals hliterals)
        horder.1
  | input idx negated => simp [IsAndOfModPAndLiterals] at hliterals
  | constant value label => simp [IsAndOfModPAndLiterals] at hliterals
  | notGate formula => simp [IsAndOfModPAndLiterals] at hliterals
  | orGate formulas => simp [IsAndOfModPAndLiterals] at hliterals
  | modGate formulas => simp [IsAndOfModPAndLiterals] at hliterals

private theorem conjunctionsPolynomial_degree {p n d : Nat}
    (formulas : List (ACCFormula p))
    (hliterals : ∀ formula ∈ formulas, IsAndOfModPAndLiterals formula)
    (horder : ∀ formula ∈ formulas, ACCFormula.IsOfOrder formula d) :
    DegreeAtMost (conjunctionsPolynomial n formulas) d := by
  induction formulas with
  | nil => exact degreeAtMost_zero
  | cons formula formulas ih =>
      apply degreeAtMost_add
      · exact conjunctionPolynomial_degree formula
          (hliterals formula (by simp)) (horder formula (by simp))
      · apply ih
        · intro child hchild
          exact hliterals child (by simp [hchild])
        · intro child hchild
          exact horder child (by simp [hchild])

/-- Every order-`d` `MOD_p-AND` circuit on `n` Boolean variables is computed
by a multilinear polynomial over `GF(p) = ZMod p` of degree at most
`(p - 1) * d`.

The polynomial is evaluated only on Boolean assignments; multiplication uses
`X_i^2 = X_i` to keep the representation multilinear. -/
theorem exists_multilinear_polynomial {p n d : Nat} (hp : p.Prime)
    (circuit : ModPAndCircuit p)
    (horder : ACCFormula.IsOfOrder circuit.1 d) :
    ∃ q : MultilinearPolynomial p n,
      DegreeAtMost q ((p - 1) * d) ∧
      ∀ x : Fin n → Bool,
        MultilinearPolynomial.eval q x =
          ((ACCFormula.eval circuit.1 (List.ofFn x)).toNat : ZMod p) := by
  rcases circuit with ⟨formula, hshape⟩
  change ACCFormula.IsOfOrder formula d at horder
  change ∃ q : MultilinearPolynomial p n,
    DegreeAtMost q ((p - 1) * d) ∧
    ∀ x : Fin n → Bool,
      MultilinearPolynomial.eval q x =
        ((ACCFormula.eval formula (List.ofFn x)).toNat : ZMod p)
  cases formula with
  | modGate conjunctions =>
      simp only [ACCFormula.IsOfOrder] at horder
      refine ⟨representingPolynomial n (.modGate conjunctions), ?_, ?_⟩
      · simp only [representingPolynomial]
        apply degreeAtMost_add
        · exact degreeAtMost_one
        · exact degreeAtMost_neg (degreeAtMost_pow
            (conjunctionsPolynomial_degree conjunctions hshape horder)
            (p - 1))
      · intro x
        rw [representingPolynomial, MultilinearPolynomial.eval_add,
          MultilinearPolynomial.eval_one, MultilinearPolynomial.eval_neg,
          MultilinearPolynomial.eval_pow,
          conjunctionsPolynomial_eval conjunctions hshape,
          eval_modGate_cast hp]
        ring
  | input idx negated => simp [IsModPAndCircuit] at hshape
  | constant value label => simp [IsModPAndCircuit] at hshape
  | notGate formula => simp [IsModPAndCircuit] at hshape
  | andGate formulas => simp [IsModPAndCircuit] at hshape
  | orGate formulas => simp [IsModPAndCircuit] at hshape

/-- The number of length-`n` inputs on which a multilinear polynomial agrees
with the Boolean function computed by an ACC formula family. -/
def multilinearPolynomialAgreementCount
    {p sourceCoefficient sourceExponent sourceDepth : Nat}
    (sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
      sourceExponent sourceDepth)
    (polynomialFamily : (n : PNat) → MultilinearPolynomial p n.val)
    (n : PNat) : Nat :=
  ((Finset.univ : Finset (Fin n.val → Bool)).filter fun inputs =>
    MultilinearPolynomial.eval (polynomialFamily n) inputs =
      ((ACCFormula.eval (sourceFamily n).val
        (List.ofFn inputs)).toNat : ZMod p)).card

/-- Average-case polynomial simulation of polynomial-size ACC formulas.

For every prime modulus `p`, every polynomial-size constant-depth ACC formula
family, and every error exponent `k`, there is a family of multilinear
polynomials over `GF(p) = ZMod p`.  At length `n`, its degree is bounded by a
fixed polylogarithm in `n`, and it agrees with the source formula on at least
`2^n * (1 - n⁻ᵏ)` Boolean inputs.  The degree-bound witnesses may depend on
the source family, `p`, and `k`, but not on `n`. -/
theorem exists_average_case_multilinear_polynomial_family
    (p sourceCoefficient sourceExponent sourceDepth : Nat) (hp : p.Prime)
    (sourceFamily : ACCFormula.ACCFormulaFamily p sourceCoefficient
      sourceExponent sourceDepth) (k : Nat) :
    ∃ polynomialFamily : (n : PNat) → MultilinearPolynomial p n.val,
    ∃ degreeCoefficient degreeExponent : Nat,
      0 < degreeCoefficient ∧
      ∀ n : PNat,
        DegreeAtMost (polynomialFamily n)
            (polylogarithmicBound n.val degreeCoefficient degreeExponent) ∧
        (multilinearPolynomialAgreementCount sourceFamily polynomialFamily n : ℚ) ≥
          ((2 ^ n.val : Nat) : ℚ) *
            (1 - 1 / (n.val : ℚ) ^ k) := by
  obtain ⟨simulationFamily, sizeCoefficient, sizeExponent, orderCoefficient,
      orderExponent, hsizeCoefficient, horderCoefficient, hsimulation⟩ :=
  polynomial_size_acc_formula_families_have_deterministic_mod_p_and_circuit_average_case_simulations
      p sourceCoefficient sourceExponent sourceDepth hp sourceFamily k
  have hpolynomial : ∀ n : PNat,
      ∃ q : MultilinearPolynomial p n.val,
        DegreeAtMost q
            ((p - 1) *
              polylogarithmicBound n.val orderCoefficient orderExponent) ∧
        ∀ inputs : Fin n.val → Bool,
          MultilinearPolynomial.eval q inputs =
            ((ACCFormula.eval (simulationFamily.circuit n).val
              (List.ofFn inputs)).toNat : ZMod p) := by
    intro n
    exact exists_multilinear_polynomial (n := n.val) hp
      (simulationFamily.circuit n) (hsimulation n).2.1
  let polynomialFamily : (n : PNat) → MultilinearPolynomial p n.val :=
    fun n => Classical.choose (hpolynomial n)
  have hpolynomial_spec : ∀ n : PNat,
      DegreeAtMost (polynomialFamily n)
          ((p - 1) *
            polylogarithmicBound n.val orderCoefficient orderExponent) ∧
      ∀ inputs : Fin n.val → Bool,
        MultilinearPolynomial.eval (polynomialFamily n) inputs =
          ((ACCFormula.eval (simulationFamily.circuit n).val
            (List.ofFn inputs)).toNat : ZMod p) := by
    intro n
    exact Classical.choose_spec (hpolynomial n)
  let degreeCoefficient := (p - 1) * orderCoefficient
  refine ⟨polynomialFamily, degreeCoefficient, orderExponent, ?_, ?_⟩
  · dsimp [degreeCoefficient]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) horderCoefficient
  · intro n
    refine ⟨?_, ?_⟩
    · simpa [degreeCoefficient, polylogarithmicBound, Nat.mul_assoc] using
        (hpolynomial_spec n).1
    · have hagreement :
          multilinearPolynomialAgreementCount sourceFamily polynomialFamily n =
            deterministicAgreementCount sourceFamily simulationFamily n := by
        unfold multilinearPolynomialAgreementCount deterministicAgreementCount
        congr 1
        ext inputs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [(hpolynomial_spec n).2 inputs]
        let _ : Fact p.Prime := ⟨hp⟩
        generalize hleft :
          ACCFormula.eval (simulationFamily.circuit n).val
            (List.ofFn inputs) = left
        generalize hright :
          ACCFormula.eval (sourceFamily n).val (List.ofFn inputs) = right
        cases left <;> cases right <;> simp
      simpa only [hagreement] using (hsimulation n).2.2

end ModPAndCircuit

end Circuits.ACC
