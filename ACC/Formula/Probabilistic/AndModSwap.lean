import Mathlib.FieldTheory.Finite.Basic
import ACC.Formula.Probabilistic.Basic

namespace Circuits.ACC.ProbabilisticACCFormula

/-! ## Swapping an AND of modulo gates

Let the direct children of an AND gate be modulo gates with input sums
`x₁, …, xₘ` in `ZMod p`.  When `p` is prime, Fermat's little theorem makes

```text
1 - xᵢ^(p - 1)
```

the indicator that the `i`th modulo gate accepts.  The AND therefore has the
same value as

```text
P = ∏ i, (1 - xᵢ^(p - 1)).
```

A modulo gate accepts when its input sum is zero, so the desired replacement
computes `1 - P`.  Its expansion contains no constant monomial.  Every power
`xᵢ^(p - 1)` is expanded into ordered `(p - 1)`-tuples of inputs of the
corresponding modulo gate, and products of such tuples become AND gates.
Negative coefficients are represented by `p - 1` copies of a monomial,
which is coefficient `-1` in `ZMod p`.

`swapAndModMonomials` constructs this expansion by the recurrence

```text
1 - (1 - X) * (1 - Q) = X + Q - X * Q.
```

The final formula is thus one modulo gate whose children are AND gates.  The
equivalence theorem requires `p` to be prime; the syntax construction itself
is defined for every natural modulus.
-/

/-- All ordered tuples of length `degree` drawn from `formulas`.

Repetitions are intentional: after evaluation, summing the products of these
tuples expands `(sum formulas) ^ degree`. -/
def powerTuples {α : Type} (formulas : List α) : Nat → List (List α)
  | 0 => [[]]
  | degree + 1 =>
      formulas.flatMap fun formula =>
        (powerTuples formulas degree).map (formula :: ·)

/-- Pairwise products of two lists of monomials.  A monomial is represented
by its list of formula factors, and multiplication concatenates factors. -/
def multiplyMonomials {α : Type} (left right : List (List α)) : List (List α) :=
  left.flatMap fun leftMonomial =>
    right.map fun rightMonomial => leftMonomial ++ rightMonomial

/-- Monomials in the expansion of
`1 - ∏ inputs, (1 - (sum inputs)^(p - 1))`.

Multiplicity records coefficients modulo `p`.  In the recursive cross-term,
`p - 1` copies encode multiplication by `-1`. -/
def swapAndModMonomials {α : Type} (p : Nat) :
    List (List α) → List (List α)
  | [] => []
  | formulas :: modInputs =>
      let head := powerTuples formulas (p - 1)
      let tail := swapAndModMonomials p modInputs
      head ++ tail ++
        (List.replicate (p - 1) (multiplyMonomials head tail)).flatten

/-- Replace
`andGate (modInputs.map modGate)` by an equivalent modulo gate over AND
monomials. -/
def swapAndOfMods {p : Nat}
    (modInputs : List (List (ProbabilisticACCFormula p))) :
    ProbabilisticACCFormula p :=
  .modGate ((swapAndModMonomials p modInputs).map .andGate)

/-- The local target shape produced by `swapAndOfMods`: one modulo gate whose
direct children are all AND gates. -/
def IsModOfAnds {p : Nat} : ProbabilisticACCFormula p → Prop
  | .modGate formulas =>
      ∀ formula ∈ formulas, ∃ children, formula = .andGate children
  | _ => False

/-- `swapAndOfMods` has a modulo output gate and only AND gates immediately
below it. -/
theorem swapAndOfMods_isModOfAnds {p : Nat}
    (modInputs : List (List (ProbabilisticACCFormula p))) :
    IsModOfAnds (swapAndOfMods modInputs) := by
  intro formula h_formula
  simp only [List.mem_map] at h_formula
  obtain ⟨monomial, _, rfl⟩ := h_formula
  exact ⟨monomial, rfl⟩

private def monomialValue {α R : Type} [CommSemiring R]
    (value : α → R) (monomial : List α) : R :=
  (monomial.map value).prod

private def monomialSum {α R : Type} [CommSemiring R]
    (value : α → R) (monomials : List (List α)) : R :=
  (monomials.map (monomialValue value)).sum

private theorem monomialSum_append {α R : Type} [CommSemiring R]
    (value : α → R) (left right : List (List α)) :
    monomialSum value (left ++ right) =
      monomialSum value left + monomialSum value right := by
  simp [monomialSum]

private theorem monomialSum_consFlatMap {α R : Type} [CommSemiring R]
    (value : α → R) (formulas : List α) (monomials : List (List α)) :
    monomialSum value
        (formulas.flatMap fun formula => monomials.map (formula :: ·)) =
      (formulas.map value).sum * monomialSum value monomials := by
  induction formulas with
  | nil => simp [monomialSum]
  | cons formula formulas ih =>
      rw [List.flatMap_cons, monomialSum_append, ih]
      simp only [List.map_cons, List.sum_cons, add_mul]
      congr 1
      simp only [monomialSum, List.map_map]
      change
        (monomials.map fun monomial =>
          monomialValue value (formula :: monomial)).sum =
        value formula * (monomials.map (monomialValue value)).sum
      simp only [monomialValue, List.map_cons, List.prod_cons]
      exact List.sum_map_mul_left monomials (monomialValue value) (value formula)

private theorem powerTuples_monomialSum {α R : Type} [CommSemiring R]
    (value : α → R) (formulas : List α) (degree : Nat) :
    monomialSum value (powerTuples formulas degree) =
      (formulas.map value).sum ^ degree := by
  induction degree with
  | zero => simp [powerTuples, monomialSum, monomialValue]
  | succ degree ih =>
      rw [powerTuples, monomialSum_consFlatMap, ih, pow_succ']

private theorem multiplyMonomials_monomialSum {α R : Type} [CommSemiring R]
    (value : α → R) (left right : List (List α)) :
    monomialSum value (multiplyMonomials left right) =
      monomialSum value left * monomialSum value right := by
  induction left with
  | nil => simp [multiplyMonomials, monomialSum]
  | cons monomial monomials ih =>
      rw [show multiplyMonomials (monomial :: monomials) right =
        right.map (monomial ++ ·) ++ multiplyMonomials monomials right by rfl]
      rw [monomialSum_append, ih]
      simp only [monomialSum, List.map_cons, List.sum_cons, add_mul]
      congr 1
      rw [List.map_map]
      change
        (right.map fun rightMonomial =>
          monomialValue value (monomial ++ rightMonomial)).sum =
        monomialValue value monomial *
          (right.map (monomialValue value)).sum
      simp only [monomialValue, List.map_append, List.prod_append]
      exact List.sum_map_mul_left right (monomialValue value)
        (List.map value monomial).prod

private theorem replicateFlatten_monomialSum {α R : Type} [CommSemiring R]
    (value : α → R) (count : Nat) (monomials : List (List α)) :
    monomialSum value (List.replicate count monomials).flatten =
      count • monomialSum value monomials := by
  induction count with
  | zero => simp [monomialSum]
  | succ count ih =>
      simp [monomialSum]

private theorem swapAndModMonomials_monomialSum {p : Nat}
    (hp : p.Prime) {α : Type} (value : α → ZMod p)
    (modInputs : List (List α)) :
    monomialSum value (swapAndModMonomials p modInputs) =
      1 - (modInputs.map fun formulas =>
        1 - (formulas.map value).sum ^ (p - 1)).prod := by
  have h_coefficient : ((p - 1 : Nat) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le]
    simp
  induction modInputs with
  | nil => simp [swapAndModMonomials, monomialSum]
  | cons formulas modInputs ih =>
      simp only [swapAndModMonomials, List.map_cons, List.prod_cons]
      rw [monomialSum_append, monomialSum_append]
      rw [powerTuples_monomialSum, ih,
        replicateFlatten_monomialSum, multiplyMonomials_monomialSum,
        powerTuples_monomialSum, ih]
      rw [nsmul_eq_mul, h_coefficient]
      ring

private theorem all_cast {p : Nat} (values : List Bool) :
    ((if values.all (· == true) then true else false).toNat : ZMod p) =
      (values.map fun value => (value.toNat : ZMod p)).prod := by
  induction values with
  | nil => simp
  | cons value values ih =>
      cases value with
      | false => simp
      | true => simpa using ih

/-- The value of an AND gate, embedded in `ZMod p`, is the product of the
embedded Boolean values of its children. -/
theorem eval_andGate_cast {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    ((eval (.andGate formulas) inputs randomBits).toNat : ZMod p) =
      (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).prod := by
  convert all_cast (p := p) (formulas.map fun formula =>
    eval formula inputs randomBits) using 1
  · simp only [eval]
  · rw [List.map_map]
    rfl

/-- Expanding a power into ordered tuples and turning every tuple into an AND
gate computes the corresponding power of the sum of child values. -/
theorem powerTuples_andGate_eval_sum {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (degree : Nat)
    (inputs randomBits : List Bool) :
    ((((powerTuples formulas degree).map .andGate).map fun formula =>
      ((eval formula inputs randomBits).toNat : ZMod p)).sum) =
      (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum ^ degree := by
  let value : ProbabilisticACCFormula p → ZMod p := fun formula =>
    ((eval formula inputs randomBits).toNat : ZMod p)
  calc
    ((((powerTuples formulas degree).map .andGate).map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum) =
        monomialSum value (powerTuples formulas degree) := by
      simp only [List.map_map, monomialSum, value]
      congr 1
      apply List.map_congr_left
      intro monomial h_monomial
      exact eval_andGate_cast monomial inputs randomBits
    _ = _ := powerTuples_monomialSum value formulas degree

private theorem eval_modGate_eq_true_iff_nat {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    eval (.modGate formulas) inputs randomBits = true ↔
      ((formulas.map fun formula => eval formula inputs randomBits).map
        Bool.toNat).sum % p = 0 := by
  simp [eval]

/-- A modulo gate is true exactly when the sum of its child values is zero in
`ZMod p`. -/
theorem eval_modGate_eq_true_iff {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    eval (.modGate formulas) inputs randomBits = true ↔
      (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum = 0 := by
  rw [eval_modGate_eq_true_iff_nat,
    ← Nat.dvd_iff_mod_eq_zero,
    ← ZMod.natCast_eq_zero_iff]
  have h_cast :
      (((formulas.map fun formula => eval formula inputs randomBits).map
        Bool.toNat).sum : ZMod p) =
        (formulas.map fun formula =>
          ((eval formula inputs randomBits).toNat : ZMod p)).sum := by
    rw [Nat.cast_list_sum, List.map_map, List.map_map]
    rfl
  rw [h_cast]

/-- For prime `p`, the embedded Boolean value of a modulo gate is its Fermat
zero-indicator `1 - x^(p - 1)`. -/
theorem eval_modGate_cast {p : Nat} (hp : p.Prime)
    (formulas : List (ProbabilisticACCFormula p))
    (inputs randomBits : List Bool) :
    ((eval (.modGate formulas) inputs randomBits).toNat : ZMod p) =
      1 - (formulas.map fun formula =>
        ((eval formula inputs randomBits).toNat : ZMod p)).sum ^ (p - 1) := by
  let total := (formulas.map fun formula =>
    ((eval formula inputs randomBits).toNat : ZMod p)).sum
  by_cases h_total : total = 0
  · have h_eval := (eval_modGate_eq_true_iff formulas inputs randomBits).2 h_total
    rw [h_eval]
    simp [total, h_total, Nat.sub_ne_zero_of_lt hp.one_lt]
  · have h_power : total ^ (p - 1) = 1 :=
      @ZMod.pow_card_sub_one_eq_one p ⟨hp⟩ total h_total
    have h_eval : eval (.modGate formulas) inputs randomBits = false := by
      cases h : eval (.modGate formulas) inputs randomBits with
      | false => rfl
      | true =>
          exact False.elim (h_total
            ((eval_modGate_eq_true_iff formulas inputs randomBits).1 h))
    rw [h_eval, h_power]
    simp

/-- Swapping an AND of modulo gates into a modulo gate over AND monomials
preserves evaluation for prime `p`.

The theorem is pointwise in both external inputs and random bits, so the
transformation does not change the randomized function computed by the
formula. -/
theorem swapAndOfMods_eval {p : Nat} (hp : p.Prime)
    (modInputs : List (List (ProbabilisticACCFormula p)))
    (inputs randomBits : List Bool) :
    eval (swapAndOfMods modInputs) inputs randomBits =
      eval (.andGate (modInputs.map .modGate)) inputs randomBits := by
  let value : ProbabilisticACCFormula p → ZMod p := fun formula =>
    ((eval formula inputs randomBits).toNat : ZMod p)
  let factors := modInputs.map fun formulas =>
    1 - (formulas.map value).sum ^ (p - 1)
  have h_source :
      ((eval (.andGate (modInputs.map .modGate)) inputs randomBits).toNat :
          ZMod p) = factors.prod := by
    rw [eval_andGate_cast]
    simp only [List.map_map, factors, value]
    congr 1
    apply List.map_congr_left
    intro formulas h_formulas
    exact eval_modGate_cast hp formulas inputs randomBits
  have h_sum :
      (((swapAndModMonomials p modInputs).map .andGate).map value).sum =
        1 - factors.prod := by
    calc
      (((swapAndModMonomials p modInputs).map .andGate).map value).sum =
          monomialSum value (swapAndModMonomials p modInputs) := by
            simp only [List.map_map, monomialSum, value]
            congr 1
            apply List.map_congr_left
            intro monomial h_monomial
            exact eval_andGate_cast monomial inputs randomBits
      _ = 1 - factors.prod := by
        simpa [factors] using
          swapAndModMonomials_monomialSum hp value modInputs
  cases h_original : eval (.andGate (modInputs.map .modGate)) inputs randomBits with
  | true =>
      have h_factors : factors.prod = 1 := by
        simpa [h_original] using h_source.symm
      have h_transformed : eval (swapAndOfMods modInputs) inputs randomBits = true := by
        apply (eval_modGate_eq_true_iff
          ((swapAndModMonomials p modInputs).map .andGate)
          inputs randomBits).2
        simpa [swapAndOfMods, value, h_factors] using h_sum
      simp [h_transformed]
  | false =>
      have h_factors : factors.prod = 0 := by
        simpa [h_original] using h_source.symm
      have h_nonzero :
          (((swapAndModMonomials p modInputs).map .andGate).map value).sum ≠ 0 := by
        rw [h_sum, h_factors]
        intro h_one
        have h_one' : (1 : ZMod p) = 0 := by simpa using h_one
        exact hp.ne_one (ZMod.one_eq_zero_iff.mp h_one')
      have h_transformed : eval (swapAndOfMods modInputs) inputs randomBits = false := by
        cases h_eval : eval (swapAndOfMods modInputs) inputs randomBits with
        | false => rfl
        | true =>
            exact False.elim (h_nonzero
              ((eval_modGate_eq_true_iff
                ((swapAndModMonomials p modInputs).map .andGate)
                inputs randomBits).1 (by simpa [swapAndOfMods] using h_eval)))
      simp [h_transformed]

/-- For prime `p`, the local AND/MOD swap preserves error probability. -/
theorem swapAndOfMods_errorProbability_eq {p : Nat} (hp : p.Prime)
    (modInputs : List (List (ProbabilisticACCFormula p)))
    (randomBitCount : Nat) (inputs : List Bool) (expected : Bool) :
    errorProbability (swapAndOfMods modInputs) randomBitCount inputs expected =
      errorProbability (.andGate (modInputs.map .modGate)) randomBitCount
        inputs expected := by
  apply errorProbability_congr
  intro randomBits
  exact swapAndOfMods_eval hp modInputs inputs randomBits

end Circuits.ACC.ProbabilisticACCFormula
