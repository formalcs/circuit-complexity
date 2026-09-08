import ACC.LowerBounds.FiniteFieldRootsOfUnity
import ACC.LowerBounds.BooleanDegree
import ACC.LowerBounds.MultilinearMonomialCount
import Mathlib.Analysis.Real.Sqrt

namespace Circuits.ACC

open scoped FinsetFamily

/-!
# Low-degree polynomial disagreement with modular counting

This file states the low-degree polynomial lower bound for the residue-class
functions `MOD_{r,i}`.  Boolean inputs are represented by functions
`Fin n → Bool`, and a family indexed by `Fin r` represents
`F₀, …, Fᵣ₋₁`.
-/

namespace PolynomialModLowerBound

/-- A multivariate polynomial is multilinear when every individual variable
has degree at most one. -/
def IsMultilinear {n : ℕ} {K : Type*} [CommSemiring K]
    (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ j, F.degreeOf j ≤ 1

/-- Evaluate a polynomial on a Boolean input, embedding `false` as `0` and
`true` as `1` in the coefficient field. -/
noncomputable def evalBool {n : ℕ} {K : Type*} [CommSemiring K]
    (F : MvPolynomial (Fin n) K) (x : Fin n → Bool) : K :=
  MvPolynomial.eval (fun j ↦ ((x j).toNat : K)) F

/-- The field-valued indicator of inputs whose Hamming weight is congruent to
`i` modulo `r`. -/
def modIndicator {n r : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin r) (x : Fin n → Bool) : K :=
  if (∑ j, (x j).toNat) % r = i then 1 else 0

/-- The Boolean inputs on which at least one polynomial in the family fails
to compute its corresponding residue-class indicator. -/
noncomputable def disagreementInputs {n r : ℕ} {K : Type*} [CommSemiring K]
    (F : Fin r → MvPolynomial (Fin n) K) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun x ↦
    ∃ i : Fin r, evalBool (F i) x ≠ modIndicator i x

/-- Let `p` be prime and let `r ≠ 1` be coprime to `p`.  Suppose the extension
field `GF(p^k)` contains a nontrivial `r`-th root of unity.  Then, for all
sufficiently large `n`, every family `F₀, …, Fᵣ₋₁` of multilinear
polynomials of degree at most `√n` disagrees with its corresponding
residue-class indicator on at least `2^n / 10` Boolean inputs. -/
theorem lowDegree_polynomials_disagree_with_mod
    (p r k : ℕ) (hp : p.Prime) (hr : r ≠ 1) (hcop : r.Coprime p)
    (_hk : 0 < k) (ω : @GaloisField p ⟨hp⟩ k)
    (hω_ne : ω ≠ 1) (hω_pow : ω ^ r = 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n > n₀ →
      ∀ F : Fin r → MvPolynomial (Fin n) (@GaloisField p ⟨hp⟩ k),
        (∀ i, IsMultilinear (F i) ∧
          ((F i).totalDegree : ℝ) ≤ Real.sqrt n) →
        2 ^ n / 10 ≤ (disagreementInputs F).card := by
  classical
  let K := @GaloisField p ⟨hp⟩ k
  have hr0 : r ≠ 0 := by
    intro hr_zero
    subst r
    simp only [Nat.coprime_zero_left] at hcop
    exact hp.ne_one hcop
  have hω_zero : ω ≠ 0 := by
    intro hω_zero
    subst ω
    simp [zero_pow hr0] at hω_pow
  refine ⟨9_000_000, ?_⟩
  intro n hn F hF
  have hn_large : 9_000_000 ≤ n := by omega
  let d : ℕ := Nat.floor (Real.sqrt n)
  let q : ℝ := (n : ℝ) / 2 - Real.sqrt n / 2
  let a : ℕ := Nat.ceil q - 1
  let P : (Fin n → Bool) → K :=
    ∑ i : Fin r, ω ^ (i : ℕ) • BooleanDegree.evalPolynomial (F i)
  have hdegree_each : ∀ i, (F i).totalDegree ≤ d := by
    intro i
    apply Nat.le_floor
    exact (hF i).2
  have hP_degree : P ∈ BooleanDegree.degreeSpace (K := K) (Fin n) d := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _
      (BooleanDegree.evalPolynomial_mem_degreeSpace (hdegree_each i))
  have hcharacter (x : Fin n → Bool) :
      BooleanDegree.twist ω (1 : (Fin n → Bool) → K) x =
        ω ^ (∑ j, (x j).toNat) := by
    simp only [BooleanDegree.twist, Pi.one_apply, mul_one]
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j _
    cases x j <;> simp
  have hpow_mod (m : ℕ) : ω ^ (m % r) = ω ^ m := by
    nth_rw 2 [← Nat.mod_add_div m r]
    rw [pow_add, pow_mul, hω_pow, one_pow, mul_one]
  have hP_agrees (x : Fin n → Bool) (hx : x ∉ disagreementInputs F) :
      P x = BooleanDegree.twist ω (1 : (Fin n → Bool) → K) x := by
    have hgood : ∀ i : Fin r, evalBool (F i) x = modIndicator i x := by
      intro i
      by_contra hi
      exact hx (by
        simp only [disagreementInputs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, hi⟩)
    let residue : Fin r := ⟨(∑ j, (x j).toNat) % r, Nat.mod_lt _ (Nat.pos_of_ne_zero hr0)⟩
    have hP_residue : P x = ω ^ (residue : ℕ) := by
      simp only [P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single residue]
      · rw [show BooleanDegree.evalPolynomial (F residue) x =
            evalBool (F residue) x by rfl, hgood]
        simp [modIndicator, residue]
      · intro i _ hi
        rw [show BooleanDegree.evalPolynomial (F i) x = evalBool (F i) x by rfl,
          hgood]
        have hne : (∑ j, (x j).toNat) % r ≠ (i : ℕ) := by
          intro heq
          apply hi
          exact Fin.ext heq.symm
        simp [modIndicator, hne]
      · simp
    rw [hP_residue, hcharacter, show (residue : ℕ) =
      (∑ j, (x j).toNat) % r by rfl, hpow_mod]
  have hq_nonneg : 0 ≤ q := by
    have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hsqrt_le : Real.sqrt n ≤ n := by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [Real.sqrt_nonneg n]
    dsimp [q]
    linarith
  have ha_lt : (a : ℝ) < q := by
    have hceil := Nat.ceil_lt_add_one hq_nonneg
    have hceil_pos : 0 < Nat.ceil q := by
      rw [Nat.ceil_pos]
      dsimp [q]
      have hnR : (9_000_000 : ℝ) ≤ n := by exact_mod_cast hn_large
      have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith [Real.sqrt_nonneg n]
    have hsub : Nat.ceil q - 1 + 1 = Nat.ceil q := by omega
    have hsub_real : ((Nat.ceil q - 1 : ℕ) : ℝ) + 1 = Nat.ceil q := by
      exact_mod_cast hsub
    dsimp [a]
    linarith
  have hd_le : (d : ℝ) ≤ Real.sqrt n := by
    exact Nat.floor_le (Real.sqrt_nonneg n)
  have hdegree_rank : a + (d + a) < n := by
    have hreal : (a : ℝ) + ((d : ℝ) + a) < n := by
      dsimp [q] at ha_lt
      nlinarith
    exact_mod_cast hreal
  have hrank := BooleanDegree.lowDegreeMonomials_card_le_error
    (K := K) ω hω_zero hω_ne d a P hP_degree
    (disagreementInputs F) hP_agrees (by simpa using hdegree_rank)
  let A : Finset (Finset (Fin n)) := MultilinearMonomialCount.lowDegreeMonomials n
  let B : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun s ↦ s.card ≤ a
  have hcompl_to_B : ∀ s ∈ Aᶜ, (sᶜ) ∈ B := by
    intro s hs
    have hs_high : (n : ℝ) / 2 + Real.sqrt n / 2 < (s.card : ℝ) := by
      simpa [A, MultilinearMonomialCount.lowDegreeMonomials] using hs
    have hcard_sum : s.card + sᶜ.card = n := by
      simpa only [Fintype.card_fin] using Finset.card_add_card_compl s
    have hscomp_lt : (sᶜ.card : ℝ) < q := by
      have hcast : (s.card : ℝ) + (sᶜ.card : ℝ) = n := by exact_mod_cast hcard_sum
      dsimp [q]
      linarith
    have hscomp_ceil : sᶜ.card < Nat.ceil q := by
      exact_mod_cast (lt_of_lt_of_le hscomp_lt (Nat.le_ceil q))
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [a]
    omega
  have hcompl_card : (Aᶜ).card ≤ B.card := by
    let e : (↑(Aᶜ)) ↪ (↑B) :=
      ⟨fun s ↦ ⟨s.1ᶜ, hcompl_to_B s.1 s.2⟩, by
        intro s t hst
        apply Subtype.ext
        simpa using congrArg (fun u : Finset (Fin n) ↦ uᶜ) (Subtype.ext_iff.mp hst)⟩
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective e e.injective
  have hB_rank : B.card ≤ (disagreementInputs F).card := by
    have hBcard : B.card = Fintype.card {s : Finset (Fin n) // s.card ≤ a} := by
      simp [B, Fintype.card_subtype]
    rw [hBcard]
    exact hrank
  have htotal : 2 ^ n ≤ A.card + (disagreementInputs F).card := by
    have hcard_compl := Finset.card_compl A
    have hcard_univ : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp
    rw [hcard_univ] at hcard_compl
    omega
  have hA_real := MultilinearMonomialCount.lowDegreeMonomials_card_le n hn_large
  have herror_ten : 2 ^ n ≤ 10 * (disagreementInputs F).card := by
    have htotal_real : (2 : ℝ) ^ n ≤
        (A.card : ℝ) + ((disagreementInputs F).card : ℝ) := by
      exact_mod_cast htotal
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
    have herror_real : (1 / 10 : ℝ) * (2 : ℝ) ^ n ≤
        ((disagreementInputs F).card : ℝ) := by
      change ((A.card : ℝ) ≤ (9 / 10 : ℝ) * (2 : ℝ) ^ n) at hA_real
      nlinarith
    exact_mod_cast (show (2 : ℝ) ^ n ≤
      10 * ((disagreementInputs F).card : ℝ) by nlinarith)
  exact Nat.div_le_of_le_mul herror_ten

end PolynomialModLowerBound

end Circuits.ACC
