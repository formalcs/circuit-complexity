import ACC.Formula.Probabilistic.AndModNormalization.PolynomialCompilation

namespace Circuits.ACC.ProbabilisticACCFormula

/-! ## Correctness of global AND/MOD normalization -/

/-- Turn an AND/MOD formula into a single modulo gate above AND gates of
input literals. -/
def normalizeAndMod {p : Nat} (formula : ProbabilisticACCFormula p) :
    ProbabilisticACCFormula p :=
  .modGate ((zeroIndicatorPolynomial p
    (compileValuePolynomial formula)).map .andGate)

/-- Evaluation of an expanded polynomial in `ZMod p`. -/
def polynomialEval {p : Nat} (polynomial : BooleanPolynomial p)
    (inputs randomBits : List Bool) : ZMod p :=
  (polynomial.map fun monomial =>
    (monomial.map fun literal =>
      ((eval literal inputs randomBits).toNat : ZMod p)).prod).sum

theorem polynomialEval_append {p : Nat}
    (left right : BooleanPolynomial p) (inputs randomBits : List Bool) :
    polynomialEval (left ++ right) inputs randomBits =
      polynomialEval left inputs randomBits +
        polynomialEval right inputs randomBits := by
  simp [polynomialEval]

theorem polynomialEval_mul {p : Nat}
    (left right : BooleanPolynomial p) (inputs randomBits : List Bool) :
    polynomialEval (polynomialMul left right) inputs randomBits =
      polynomialEval left inputs randomBits *
        polynomialEval right inputs randomBits := by
  induction left with
  | nil => simp [polynomialMul, polynomialEval]
  | cons monomial monomials ih =>
      rw [show polynomialMul (monomial :: monomials) right =
        right.map (monomial ++ ·) ++ polynomialMul monomials right by rfl]
      rw [polynomialEval_append, ih]
      simp only [polynomialEval, List.map_cons, List.sum_cons, add_mul]
      congr 1
      rw [List.map_map]
      change
        (right.map fun rightMonomial =>
          ((monomial ++ rightMonomial).map fun literal =>
            ((eval literal inputs randomBits).toNat : ZMod p)).prod).sum = _
      simp only [List.map_append, List.prod_append]
      exact List.sum_map_mul_left right
        (fun rightMonomial =>
          ((rightMonomial.map fun literal =>
            ((eval literal inputs randomBits).toNat : ZMod p))).prod)
        ((monomial.map fun literal =>
          ((eval literal inputs randomBits).toNat : ZMod p))).prod

theorem polynomialEval_pow {p : Nat} (polynomial : BooleanPolynomial p)
    (exponent : Nat) (inputs randomBits : List Bool) :
    polynomialEval (polynomialPow polynomial exponent) inputs randomBits =
      polynomialEval polynomial inputs randomBits ^ exponent := by
  induction exponent with
  | zero => simp [polynomialPow, polynomialEval]
  | succ exponent ih =>
      rw [polynomialPow, polynomialEval_mul, ih, pow_succ']

theorem polynomialEval_neg {p : Nat} (hp : p.Prime)
    (polynomial : BooleanPolynomial p) (inputs randomBits : List Bool) :
    polynomialEval (polynomialNeg p polynomial) inputs randomBits =
      -polynomialEval polynomial inputs randomBits := by
  have h_coefficient : ((p - 1 : Nat) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le]
    simp
  have h_replicate : ∀ count : Nat,
      polynomialEval (List.replicate count polynomial).flatten
          inputs randomBits =
        count • polynomialEval polynomial inputs randomBits := by
    intro count
    induction count with
    | zero => simp [polynomialEval]
    | succ count ih =>
        rw [List.replicate_succ, List.flatten_cons,
          polynomialEval_append, ih, succ_nsmul]
        exact add_comm _ _
  rw [polynomialNeg, h_replicate, nsmul_eq_mul]
  rw [h_coefficient, neg_one_mul]

theorem polynomialEval_zeroIndicator {p : Nat} (hp : p.Prime)
    (polynomial : BooleanPolynomial p) (inputs randomBits : List Bool) :
    polynomialEval (zeroIndicatorPolynomial p polynomial) inputs randomBits =
      1 - polynomialEval polynomial inputs randomBits ^ (p - 1) := by
  rw [zeroIndicatorPolynomial, polynomialEval_append,
    polynomialEval_neg hp, polynomialEval_pow]
  simp only [polynomialEval, List.map_cons, List.map_nil, List.prod_nil,
    List.sum_cons, List.sum_nil, add_zero, sub_eq_add_neg]

mutual

/-- Correctness of the polynomial compilation on the AND/MOD fragment. -/
theorem compileValuePolynomial_eval {p : Nat} (hp : p.Prime)
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool)
    (h_formula : HasOnlyAndModGates formula) :
    polynomialEval (compileValuePolynomial formula) inputs randomBits =
      ((eval formula inputs randomBits).toNat : ZMod p) := by
  match formula with
  | .input idx negated =>
      simp [compileValuePolynomial, polynomialEval]
  | .constant value label =>
      cases value <;> simp [compileValuePolynomial, polynomialEval, eval]
  | .notGate child => simp [HasOnlyAndModGates] at h_formula
  | .orGate children => simp [HasOnlyAndModGates] at h_formula
  | .andGate children =>
      simp only [HasOnlyAndModGates] at h_formula
      rw [compileValuePolynomial,
        compileProductPolynomial_eval hp children inputs randomBits h_formula,
        eval_andGate_cast]
  | .modGate children =>
      simp only [HasOnlyAndModGates] at h_formula
      rw [compileValuePolynomial, polynomialEval_zeroIndicator hp,
        compileSumPolynomial_eval hp children inputs randomBits h_formula,
        eval_modGate_cast hp]

/-- The compiled sum is the sum of the embedded Boolean child values. -/
theorem compileSumPolynomial_eval {p : Nat} (hp : p.Prime)
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool)
    (h_formulas : ∀ formula ∈ formulas, HasOnlyAndModGates formula) :
    polynomialEval (compileSumPolynomial formulas) inputs randomBits =
      (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum := by
  match formulas with
  | [] => simp [compileSumPolynomial, polynomialEval]
  | formula :: formulas =>
      rw [compileSumPolynomial, polynomialEval_append,
        compileValuePolynomial_eval hp formula inputs randomBits
          (h_formulas formula (by simp)),
        compileSumPolynomial_eval hp formulas inputs randomBits (by
          intro child h_child
          exact h_formulas child (by simp [h_child]))]
      simp

/-- The compiled product is the product of the embedded Boolean child
values. -/
theorem compileProductPolynomial_eval {p : Nat} (hp : p.Prime)
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool)
    (h_formulas : ∀ formula ∈ formulas, HasOnlyAndModGates formula) :
    polynomialEval (compileProductPolynomial formulas) inputs randomBits =
      (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).prod := by
  match formulas with
  | [] => simp [compileProductPolynomial, polynomialEval]
  | formula :: formulas =>
      rw [compileProductPolynomial, polynomialEval_mul,
        compileValuePolynomial_eval hp formula inputs randomBits
          (h_formulas formula (by simp)),
        compileProductPolynomial_eval hp formulas inputs randomBits (by
          intro child h_child
          exact h_formulas child (by simp [h_child]))]
      simp

end


/-- Global AND/MOD normalization preserves evaluation for prime modulus. -/
theorem normalizeAndMod_eval {p : Nat} (hp : p.Prime)
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool)
    (h_formula : HasOnlyAndModGates formula) :
    eval (normalizeAndMod formula) inputs randomBits =
      eval formula inputs randomBits := by
  have h_compiled := compileValuePolynomial_eval hp formula inputs randomBits
    h_formula
  have h_cast :
      ((eval (normalizeAndMod formula) inputs randomBits).toNat : ZMod p) =
        ((eval formula inputs randomBits).toNat : ZMod p) := by
    rw [normalizeAndMod, eval_modGate_cast hp]
    simp only [List.map_map]
    change 1 -
      ((zeroIndicatorPolynomial p (compileValuePolynomial formula)).map
        fun monomial =>
          ((eval (.andGate monomial) inputs randomBits).toNat : ZMod p)).sum ^
        (p - 1) = _
    rw [show
        ((zeroIndicatorPolynomial p (compileValuePolynomial formula)).map
          fun monomial =>
            ((eval (.andGate monomial) inputs randomBits).toNat : ZMod p)).sum =
          polynomialEval
            (zeroIndicatorPolynomial p (compileValuePolynomial formula))
            inputs randomBits by
      simp only [polynomialEval]
      congr 1
      apply List.map_congr_left
      intro monomial h_monomial
      exact eval_andGate_cast monomial inputs randomBits]
    rw [polynomialEval_zeroIndicator hp, h_compiled]
    cases h_eval : eval formula inputs randomBits <;>
      simp [Nat.sub_ne_zero_of_lt hp.one_lt]
  cases h_left : eval (normalizeAndMod formula) inputs randomBits with
  | false =>
      cases h_right : eval formula inputs randomBits with
      | false => rfl
      | true =>
          simp only [h_left, h_right, Bool.toNat_false, Bool.toNat_true,
            Nat.cast_zero, Nat.cast_one] at h_cast
          exact False.elim
            (hp.ne_one (ZMod.one_eq_zero_iff.mp h_cast.symm))
  | true =>
      cases h_right : eval formula inputs randomBits with
      | false =>
          simp only [h_left, h_right, Bool.toNat_false, Bool.toNat_true,
            Nat.cast_zero, Nat.cast_one] at h_cast
          exact False.elim
            (hp.ne_one (ZMod.one_eq_zero_iff.mp h_cast))
      | true => rfl

/-- Global normalization preserves error probability. -/
theorem normalizeAndMod_errorProbability_eq {p : Nat} (hp : p.Prime)
    (formula : ProbabilisticACCFormula p) (randomBitCount : Nat)
    (inputs : List Bool) (expected : Bool)
    (h_formula : HasOnlyAndModGates formula) :
    errorProbability (normalizeAndMod formula) randomBitCount inputs expected =
      errorProbability formula randomBitCount inputs expected := by
  apply errorProbability_congr
  intro randomBits
  exact normalizeAndMod_eval hp formula inputs randomBits h_formula

end Circuits.ACC.ProbabilisticACCFormula
