import ACC.Formula.Probabilistic.AndModNormalization.Correctness

namespace Circuits.ACC.ProbabilisticACCFormula

/-! ## Syntax and resource bounds for AND/MOD normalization -/

/-- Polynomial multiplication preserves the invariant that every monomial
factor is an input literal. -/
theorem polynomialMul_literals {p : Nat}
    (left right : BooleanPolynomial p)
    (h_left : ∀ monomial ∈ left, ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal)
    (h_right : ∀ monomial ∈ right, ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal) :
    ∀ monomial ∈ polynomialMul left right, ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal := by
  intro monomial h_monomial literal h_literal
  simp only [polynomialMul, List.mem_flatMap, List.mem_map] at h_monomial
  obtain ⟨leftMonomial, h_leftMonomial, rightMonomial,
    h_rightMonomial, rfl⟩ := h_monomial
  rw [List.mem_append] at h_literal
  exact h_literal.elim
    (h_left leftMonomial h_leftMonomial literal)
    (h_right rightMonomial h_rightMonomial literal)

/-- Polynomial powers preserve the literal-factor invariant. -/
theorem polynomialPow_literals {p : Nat} (polynomial : BooleanPolynomial p)
    (h_polynomial : ∀ monomial ∈ polynomial, ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal) :
    ∀ exponent monomial, monomial ∈ polynomialPow polynomial exponent →
      ∀ literal ∈ monomial, IsProbabilisticModPAndLiteral literal := by
  intro exponent
  induction exponent with
  | zero => simp [polynomialPow]
  | succ exponent ih =>
      exact polynomialMul_literals polynomial
        (polynomialPow polynomial exponent) h_polynomial (ih)

/-- Coefficient negation preserves monomials and hence their literals. -/
theorem polynomialNeg_literals {p : Nat} (polynomial : BooleanPolynomial p)
    (h_polynomial : ∀ monomial ∈ polynomial, ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal) :
    ∀ monomial, monomial ∈ polynomialNeg p polynomial →
      ∀ literal ∈ monomial, IsProbabilisticModPAndLiteral literal := by
  intro monomial h_monomial literal h_literal
  simp only [polynomialNeg, List.mem_flatten] at h_monomial
  obtain ⟨copy, h_copy, h_monomial⟩ := h_monomial
  have h_copy_eq : copy = polynomial := by
    simpa using (List.eq_of_mem_replicate h_copy)
  subst copy
  exact h_polynomial monomial h_monomial literal h_literal

/-- The Fermat zero-indicator preserves the literal-factor invariant. -/
theorem zeroIndicatorPolynomial_literals {p : Nat}
    (polynomial : BooleanPolynomial p)
    (h_polynomial : ∀ monomial ∈ polynomial, ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal) :
    ∀ monomial,
      monomial ∈ zeroIndicatorPolynomial p polynomial →
      ∀ literal ∈ monomial, IsProbabilisticModPAndLiteral literal := by
  intro monomial h_monomial literal h_literal
  simp only [zeroIndicatorPolynomial, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at h_monomial
  rcases h_monomial with rfl | h_monomial
  · simp at h_literal
  · exact polynomialNeg_literals (polynomialPow polynomial (p - 1))
      (polynomialPow_literals polynomial h_polynomial (p - 1))
      monomial h_monomial literal h_literal

mutual

/-- Every factor in every compiled monomial is an input literal. -/
theorem compileValuePolynomial_literals {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    ∀ monomial ∈ compileValuePolynomial formula,
      ∀ literal ∈ monomial, IsProbabilisticModPAndLiteral literal := by
  match formula with
  | .input .. => simp [compileValuePolynomial,
      IsProbabilisticModPAndLiteral]
  | .constant value label =>
      cases value <;> simp [compileValuePolynomial]
  | .notGate child => simp [compileValuePolynomial]
  | .orGate children => simp [compileValuePolynomial]
  | .andGate children =>
      exact compileProductPolynomial_literals children
  | .modGate children =>
      exact zeroIndicatorPolynomial_literals
        (compileSumPolynomial children)
        (compileSumPolynomial_literals children)

/-- Literal-factor invariant for the sum compiler. -/
theorem compileSumPolynomial_literals {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    ∀ monomial ∈ compileSumPolynomial formulas,
      ∀ literal ∈ monomial, IsProbabilisticModPAndLiteral literal := by
  match formulas with
  | [] => simp [compileSumPolynomial]
  | formula :: formulas =>
      intro monomial h_monomial
      simp only [compileSumPolynomial, List.mem_append] at h_monomial
      rcases h_monomial with h_monomial | h_monomial
      · exact compileValuePolynomial_literals formula
          monomial h_monomial
      · exact compileSumPolynomial_literals formulas monomial h_monomial

/-- Literal-factor invariant for the product compiler. -/
theorem compileProductPolynomial_literals {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) :
    ∀ monomial ∈ compileProductPolynomial formulas,
      ∀ literal ∈ monomial, IsProbabilisticModPAndLiteral literal := by
  match formulas with
  | [] => simp [compileProductPolynomial]
  | formula :: formulas =>
      exact polynomialMul_literals (compileValuePolynomial formula)
        (compileProductPolynomial formulas)
        (compileValuePolynomial_literals formula)
        (compileProductPolynomial_literals formulas)

end

/-- A monomial consisting only of input literals has no internal gates. -/
theorem sum_circuitSize_eq_zero_of_literals {p : Nat}
    (monomial : List (ProbabilisticACCFormula p))
    (h_literals : ∀ literal ∈ monomial,
      IsProbabilisticModPAndLiteral literal) :
    (monomial.map circuitSize).sum = 0 := by
  induction monomial with
  | nil => simp
  | cons literal literals ih =>
      have h_input := h_literals literal (by simp)
      have h_tail : ∀ child ∈ literals,
          IsProbabilisticModPAndLiteral child := by
        intro child h_child
        exact h_literals child (by simp [h_child])
      cases literal <;> simp_all [IsProbabilisticModPAndLiteral, circuitSize]

/-- The global normalizer always has the required depth-three syntax. -/
theorem normalizeAndMod_isProbabilisticModPAndCircuit {p : Nat}
    (formula : ProbabilisticACCFormula p)
    (_h_formula : HasOnlyAndModGates formula) :
    IsProbabilisticModPAndCircuit (normalizeAndMod formula) := by
  simp only [normalizeAndMod, IsProbabilisticModPAndCircuit]
  intro child h_child
  simp only [List.mem_map] at h_child
  obtain ⟨monomial, h_monomial, rfl⟩ := h_child
  simp only [IsAndOfProbabilisticModPAndLiterals]
  exact zeroIndicatorPolynomial_literals (compileValuePolynomial formula)
    (compileValuePolynomial_literals formula) monomial h_monomial

/-- Exact gate count of the globally normalized formula. -/
theorem normalizeAndMod_circuitSize_eq {p : Nat}
    (formula : ProbabilisticACCFormula p) :
    circuitSize (normalizeAndMod formula) =
      2 + (p - 1) * compilationMonomialCount formula ^ (p - 1) := by
  have polynomial_gate_sizes :
      ∀ polynomial : BooleanPolynomial p,
        (∀ monomial ∈ polynomial, ∀ literal ∈ monomial,
          IsProbabilisticModPAndLiteral literal) →
        (polynomial.map
          (circuitSize ∘ fun monomial => .andGate monomial)).sum =
            polynomial.length := by
    intro polynomial h_literals
    induction polynomial with
    | nil => simp
    | cons monomial monomials ih =>
        have h_monomial : ∀ literal ∈ monomial,
            IsProbabilisticModPAndLiteral literal := by
          intro literal h_literal
          exact h_literals monomial (by simp) literal h_literal
        have h_monomials : ∀ monomial ∈ monomials,
            ∀ literal ∈ monomial,
              IsProbabilisticModPAndLiteral literal := by
          intro tailMonomial h_tailMonomial literal h_literal
          exact h_literals tailMonomial (by simp [h_tailMonomial]) literal h_literal
        have h_factor_sizes : (monomial.map circuitSize).sum = 0 := by
          exact sum_circuitSize_eq_zero_of_literals monomial h_monomial
        simp [circuitSize, h_factor_sizes, ih h_monomials, Nat.add_comm]
  simp only [normalizeAndMod, circuitSize, List.map_map]
  rw [polynomial_gate_sizes _
    (zeroIndicatorPolynomial_literals _
      (compileValuePolynomial_literals formula))]
  rw [zeroIndicatorPolynomial_length, compileValuePolynomial_length]
  omega

/-- Every AND gate in the normalized depth-three circuit has fan-in at most
the compiled polynomial degree. -/
theorem normalizeAndMod_isOfOrder {p : Nat}
    (formula : ProbabilisticACCFormula p)
    (_h_formula : HasOnlyAndModGates formula) :
    IsOfOrder (normalizeAndMod formula)
      ((p - 1) * compilationDegree formula) := by
  simp only [normalizeAndMod, IsOfOrder]
  intro child h_child
  simp only [List.mem_map] at h_child
  obtain ⟨monomial, h_monomial, rfl⟩ := h_child
  simp only [IsOfOrder]
  constructor
  · exact zeroIndicatorPolynomial_hasDegreeAtMost
      (compileValuePolynomial formula) (compilationDegree formula)
      (compileValuePolynomial_hasDegreeAtMost formula) monomial h_monomial
  · intro literal h_literal
    have h_input := zeroIndicatorPolynomial_literals
      (compileValuePolynomial formula)
      (compileValuePolynomial_literals formula) monomial h_monomial
        literal h_literal
    cases literal <;> simp_all [IsProbabilisticModPAndLiteral, IsOfOrder]

private theorem nat_le_two_pow_self (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
          calc
            n + 2 ≤ 2 * (n + 1) := by omega
            _ ≤ 2 * 2 ^ (n + 1) := by gcongr
            _ = 2 ^ (n + 2) := by rw [pow_succ]; ring

/-- A closed-form quasipolynomial-style size certificate for normalization.
The logarithm controls the polynomial base of the monomial expansion, while
`compilationRank_le` controls its exponent by order and depth. -/
theorem normalizeAndMod_circuitSize_le_two_pow {p : Nat} (hp : 2 ≤ p)
    (formula : ProbabilisticACCFormula p) (order : Nat)
    (h_formula : HasOnlyAndModGates formula) (h_order : IsOfOrder formula order) :
    circuitSize (normalizeAndMod formula) ≤
      2 ^ ((3 * p + 2) *
        (Nat.clog 2 (2 * p * formula.nodeCount) + 1) *
        (max order (3 * p)) ^ (formula.depth + 1)) := by
  let base := 2 * p * formula.nodeCount
  let rankBound := (max order (3 * p)) ^ (formula.depth + 1)
  let logarithm := Nat.clog 2 base
  have h_base : 0 < base := by
    dsimp [base]
    have := nodeCount_pos formula
    positivity
  have h_base_pow : base ≤ 2 ^ logarithm := by
    exact Nat.le_pow_clog (by omega) base
  have h_rank := compilationRank_le hp formula order h_formula h_order
  have h_count := compilationMonomialCount_le hp formula
  have h_count_two : compilationMonomialCount formula ≤
      2 ^ (logarithm * rankBound) := by
    calc
      compilationMonomialCount formula ≤ base ^ compilationRank formula := by
        simpa [base] using h_count
      _ ≤ base ^ rankBound := by gcongr
      _ ≤ (2 ^ logarithm) ^ rankBound := by gcongr
      _ = 2 ^ (logarithm * rankBound) := by rw [Nat.pow_mul]
  have h_rankBound : 1 ≤ rankBound := by
    have h_rankBase : 0 < max order (3 * p) := by omega
    exact Nat.one_le_pow _ _ h_rankBase
  have h_logarithm : 1 ≤ logarithm := by
    have h_four : 4 ≤ base := by
      dsimp [base]
      have := nodeCount_pos formula
      nlinarith
    have := Nat.clog_pos (b := 2) (n := base) (by omega) (by omega)
    omega
  let expansionExponent := logarithm * rankBound * (p - 1)
  have h_expansionPower : compilationMonomialCount formula ^ (p - 1) ≤
      2 ^ expansionExponent := by
    calc
      compilationMonomialCount formula ^ (p - 1) ≤
          (2 ^ (logarithm * rankBound)) ^ (p - 1) := by gcongr
      _ = 2 ^ expansionExponent := by
        rw [← Nat.pow_mul]
  have h_coefficient : p - 1 ≤ 2 ^ p := by
    exact (Nat.sub_le p 1).trans (nat_le_two_pow_self p)
  have h_inner : 1 + (p - 1) *
      compilationMonomialCount formula ^ (p - 1) ≤
      2 ^ (p + expansionExponent + 1) := by
    have h_term : (p - 1) *
        compilationMonomialCount formula ^ (p - 1) ≤
        2 ^ (p + expansionExponent) := by
      calc
        (p - 1) * compilationMonomialCount formula ^ (p - 1) ≤
            2 ^ p * 2 ^ expansionExponent :=
          Nat.mul_le_mul h_coefficient h_expansionPower
        _ = 2 ^ (p + expansionExponent) := by rw [pow_add]
    calc
      1 + (p - 1) * compilationMonomialCount formula ^ (p - 1) ≤
          2 ^ (p + expansionExponent) + 2 ^ (p + expansionExponent) := by
        exact Nat.add_le_add (Nat.one_le_pow _ _ (by omega)) h_term
      _ = 2 ^ (p + expansionExponent + 1) := by
        rw [pow_succ]
        ring
  have h_exponent : p + expansionExponent + 2 ≤
      (3 * p + 2) * (logarithm + 1) * rankBound := by
    have h_product : 1 ≤ logarithm * rankBound := by
      exact Nat.mul_le_mul h_logarithm h_rankBound
    calc
      p + expansionExponent + 2 ≤
          (p + 2) * (logarithm * rankBound) +
            p * (logarithm * rankBound) := by
        dsimp [expansionExponent]
        have h_constant : p + 2 ≤
            (p + 2) * (logarithm * rankBound) := by
          calc
            p + 2 = (p + 2) * 1 := by ring
            _ ≤ (p + 2) * (logarithm * rankBound) := by gcongr
        have h_powerCoefficient :
            logarithm * rankBound * (p - 1) ≤
              p * (logarithm * rankBound) := by
          ring_nf
          gcongr
          exact Nat.sub_le p 1
        omega
      _ = (2 * p + 2) * (logarithm * rankBound) := by ring
      _ ≤ (3 * p + 2) * (logarithm * rankBound) :=
        Nat.mul_le_mul_right (logarithm * rankBound) (by omega)
      _ ≤ (3 * p + 2) * (logarithm + 1) * rankBound := by
        ring_nf
        omega
  rw [normalizeAndMod_circuitSize_eq]
  calc
    2 + (p - 1) * compilationMonomialCount formula ^ (p - 1) =
        1 + (1 + (p - 1) *
          compilationMonomialCount formula ^ (p - 1)) := by omega
    _ ≤ 1 + 2 ^ (p + expansionExponent + 1) := by gcongr
    _ ≤ 2 ^ (p + expansionExponent + 1) +
        2 ^ (p + expansionExponent + 1) := by
      exact Nat.add_le_add_right (Nat.one_le_pow _ _ (by omega)) _
    _ = 2 ^ (p + expansionExponent + 2) := by
      rw [pow_succ]
      ring
    _ ≤ 2 ^ ((3 * p + 2) * (logarithm + 1) * rankBound) :=
      Nat.pow_le_pow_right (by omega) h_exponent
    _ = 2 ^ ((3 * p + 2) *
        (Nat.clog 2 (2 * p * formula.nodeCount) + 1) *
        (max order (3 * p)) ^ (formula.depth + 1)) := rfl


end Circuits.ACC.ProbabilisticACCFormula
