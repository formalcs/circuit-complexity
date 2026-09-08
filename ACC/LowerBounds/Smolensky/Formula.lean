import ACC.LowerBounds.Smolensky.Restriction
import ACC.Formula.Semantics
import ACC.Functions.Mod

namespace Circuits.ACC

/-!
# Smolensky's theorem

The modulo convention is provided by `ACC.Functions.Mod` and agrees with
`ACCFormula.modGate`.
-/

/-- The quantitative form of Smolensky's argument used below.

For every sufficiently large `n`, a polynomial-size, constant-depth
`ACCFormula[p]` family disagrees with `MOD_r` on some input of length `n + r`.
The harmless shift by `r` is removed in
`smolensky_mod_eventually_disagrees`. -/
theorem smolensky_mod_eventually_disagrees_shifted
    (p r : ℕ) (hp : p.Prime) (hr : 1 < r) (hcop : r.Coprime p) :
    ∀ (sizeCoefficient sizeExponent depthBound : ℕ)
      (family : ACCFormula.ACCFormulaFamily p sizeCoefficient sizeExponent
        depthBound),
      ∃ n₀ : ℕ, ∀ n : ℕ, n > n₀ →
        ∃ x : Fin (n + r) → Bool,
          ACCFormula.eval (family ⟨n + r, by omega⟩).val (List.ofFn x) ≠
            modFunction r x := by
  classical
  intro sizeCoefficient sizeExponent depthBound family
  have hr_ne : r ≠ 1 := by omega
  obtain ⟨k, hk, ω, hω_ne, hω_pow⟩ :=
    exists_nontrivial_rootOfUnity_galoisField p r hp hr_ne hcop
  obtain ⟨lowerThreshold, hlower⟩ :=
    PolynomialModLowerBound.lowDegree_polynomials_disagree_with_mod
      p r k hp hr_ne hcop hk ω hω_ne hω_pow
  obtain ⟨polynomialFamily, degreeCoefficient, degreeExponent,
      hdegreeCoefficient, hpolynomial⟩ :=
    ModPAndCircuit.exists_average_case_multilinear_polynomial_family
      p sizeCoefficient sizeExponent depthBound hp family 1
  obtain ⟨degreeThreshold, hdegreeThreshold⟩ :=
    SmolenskyBridge.eventually_polylogarithmicBound_le_sqrt
      r degreeCoefficient degreeExponent
  refine ⟨max lowerThreshold degreeThreshold + 20 * r * 2 ^ r + 20, ?_⟩
  intro n hn
  by_contra hcomputeAll
  push Not at hcomputeAll
  have hn_lower : n > lowerThreshold := by
    omega
  have hn_degree : n > degreeThreshold := by
    omega
  have hnpos : 0 < n := by
    omega
  let N : PNat := ⟨n + r, by omega⟩
  let q : MultilinearPolynomial p (n + r) :=
    ⟨(polynomialFamily N).terms⟩
  have hqdegree : MultilinearPolynomial.DegreeAtMost q
      (polylogarithmicBound (n + r) degreeCoefficient degreeExponent) := by
    intro term hterm
    exact (hpolynomial N).1 term hterm
  let K := @GaloisField p ⟨hp⟩ k
  let F : Fin r → MvPolynomial (Fin n) K := fun i ↦
    SmolenskyBridge.restrictedPolynomial p n r (K := K) i q
  have hF : ∀ i, PolynomialModLowerBound.IsMultilinear (F i) ∧
      ((F i).totalDegree : ℝ) ≤ Real.sqrt n := by
    intro i
    constructor
    · exact SmolenskyBridge.restrictedPolynomial_multilinear
        p n r i q
    · have htd := SmolenskyBridge.restrictedPolynomial_totalDegree_le
        (K := K) p n r
        (polylogarithmicBound (n + r) degreeCoefficient degreeExponent)
        i q hqdegree
      have htdReal : ((F i).totalDegree : ℝ) ≤
          (polylogarithmicBound (n + r) degreeCoefficient degreeExponent : ℕ) := by
        dsimp [F]
        exact_mod_cast htd
      exact htdReal.trans (hdegreeThreshold n hn_degree)
  have hlowerBound : 2 ^ n / 10 ≤
      (PolynomialModLowerBound.disagreementInputs F).card :=
    hlower n hn_lower F hF
  let agreement : Finset (Fin N.val → Bool) :=
    Finset.univ.filter fun inputs ↦
      MultilinearPolynomial.eval (polynomialFamily N) inputs =
        ((ACCFormula.eval (family N).val (List.ofFn inputs)).toNat : ZMod p)
  let errors : Finset (Fin N.val → Bool) := agreementᶜ
  have agreement_spec (inputs : Fin N.val → Bool) :
      inputs ∈ agreement ↔
        MultilinearPolynomial.eval (polynomialFamily N) inputs =
          ((ACCFormula.eval (family N).val (List.ofFn inputs)).toNat : ZMod p) := by
    change inputs ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    simp
  have herrorsCard : errors.card =
      Fintype.card (Fin N.val → Bool) - agreement.card := by
    dsimp only [errors]
    exact Finset.card_compl agreement
  change Finset (Fin (n + r) → Bool) at agreement
  change Finset (Fin (n + r) → Bool) at errors
  have hagreementCount :
      ModPAndCircuit.multilinearPolynomialAgreementCount
          family polynomialFamily N = agreement.card := by
    rfl
  have havg := (hpolynomial N).2
  rw [hagreementCount] at havg
  have hagreement_le : agreement.card ≤ 2 ^ (n + r) := by
    calc
      agreement.card ≤ Fintype.card (Fin (n + r) → Bool) :=
        Finset.card_le_univ _
      _ = 2 ^ (n + r) := by simp
  have hpartition : agreement.card + errors.card = 2 ^ (n + r) := by
    have herrorsCard' : errors.card = 2 ^ (n + r) - agreement.card := by
      calc
        errors.card = Fintype.card (Fin N.val → Bool) - agreement.card :=
          herrorsCard
        _ = 2 ^ (n + r) - agreement.card := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
          rfl
    rw [herrorsCard']
    omega
  have hNq : (0 : ℚ) < ((n + r : ℕ) : ℚ) := by positivity
  have hagreementRat :
      ((2 ^ (n + r) : ℕ) : ℚ) -
          ((2 ^ (n + r) : ℕ) : ℚ) / (n + r) ≤
        (agreement.card : ℚ) := by
    convert havg using 1
    all_goals simp [N]
    ring
  have herrorRat : (errors.card : ℚ) ≤
      ((2 ^ (n + r) : ℕ) : ℚ) / (n + r) := by
    have hpartitionRat : (agreement.card : ℚ) + errors.card =
        (2 ^ (n + r) : ℕ) := by exact_mod_cast hpartition
    linarith
  have herror : errors.card * (n + r) ≤ 2 ^ (n + r) := by
    have hmulRat : (errors.card : ℚ) * ((n + r : ℕ) : ℚ) ≤
        ((2 ^ (n + r) : ℕ) : ℚ) :=
      (le_div_iff₀ hNq).mp (by simpa using herrorRat)
    exact_mod_cast hmulRat
  let residueErrors (i : Fin r) : Finset (Fin n → Bool) :=
    Finset.univ.filter fun x ↦
      PolynomialModLowerBound.evalBool (F i) x ≠
        PolynomialModLowerBound.modIndicator i x
  have hresidue_card (i : Fin r) :
      (residueErrors i).card ≤ errors.card := by
    apply Finset.card_le_card_of_injOn
      (SmolenskyBridge.residueExtension n r i)
    · intro x hx
      have hxerr : PolynomialModLowerBound.evalBool (F i) x ≠
          PolynomialModLowerBound.modIndicator i x := by
        simpa [residueErrors] using (Finset.mem_filter.mp hx).2
      have hext : SmolenskyBridge.residueExtension n r i x ∉ agreement := by
        intro hagree
        have hagreeEval :
            MultilinearPolynomial.eval (polynomialFamily N)
                (SmolenskyBridge.residueExtension n r i x) =
              ((ACCFormula.eval (family N).val
                (List.ofFn (SmolenskyBridge.residueExtension n r i x))).toNat :
                  ZMod p) := by
          exact (agreement_spec _).mp hagree
        apply hxerr
        dsimp [F]
        rw [SmolenskyBridge.restrictedPolynomial_eval]
        have hqeval : MultilinearPolynomial.eval q
              (SmolenskyBridge.residueExtension n r i x) =
            MultilinearPolynomial.eval (polynomialFamily N)
              (SmolenskyBridge.residueExtension n r i x) := by
          rfl
        rw [hqeval, hagreeEval]
        have hcompute :
            ACCFormula.eval (family N).val
                (List.ofFn (SmolenskyBridge.residueExtension n r i x)) =
              modFunction r (SmolenskyBridge.residueExtension n r i x) := by
          simpa [N] using hcomputeAll
            (SmolenskyBridge.residueExtension n r i x)
        rw [hcompute]
        unfold modFunction PolynomialModLowerBound.modIndicator
        rw [SmolenskyBridge.residueExtension_weight]
        have hiff := SmolenskyBridge.residueExtension_mod_iff r
          (by omega) i (∑ j, (x j).toNat)
        by_cases hmod : (∑ j, (x j).toNat) % r = i.val
        · have hextmod :
              ((∑ j, (x j).toNat) + (r - i.val)) % r = 0 := hiff.mpr hmod
          simp [hmod, hextmod]
        · have hextmod :
              ((∑ j, (x j).toNat) + (r - i.val)) % r ≠ 0 := by
            exact fun h ↦ hmod (hiff.mp h)
          simp [hmod, hextmod]
      change SmolenskyBridge.residueExtension n r i x ∈ agreementᶜ
      exact Finset.mem_compl.mpr hext
    · intro x hx y hy hxy
      funext j
      have hj := congrFun hxy (Fin.castAdd r j)
      simpa using hj
  have hdisagreement :
      PolynomialModLowerBound.disagreementInputs F =
        (Finset.univ : Finset (Fin r)).biUnion residueErrors := by
    ext x
    simp [PolynomialModLowerBound.disagreementInputs, residueErrors]
  have hdisagreement_card :
      (PolynomialModLowerBound.disagreementInputs F).card ≤
        r * errors.card := by
    rw [hdisagreement]
    refine Finset.card_biUnion_le.trans ?_
    calc
      ∑ i : Fin r, (residueErrors i).card ≤
          ∑ _i : Fin r, errors.card :=
        Finset.sum_le_sum fun i _ ↦ hresidue_card i
      _ = r * errors.card := by simp
  have hthreshold : 20 * r * 2 ^ r ≤ n + r := by
    omega
  have hscaled : (20 * r * errors.card) * 2 ^ r ≤
      (2 ^ n) * 2 ^ r := by
    calc
      (20 * r * errors.card) * 2 ^ r =
          errors.card * (20 * r * 2 ^ r) := by ring
      _ ≤ errors.card * (n + r) := Nat.mul_le_mul_left _ hthreshold
      _ ≤ 2 ^ (n + r) := herror
      _ = (2 ^ n) * 2 ^ r := by rw [pow_add]
  have htwenty_errors : 20 * r * errors.card ≤ 2 ^ n := by
    exact Nat.le_of_mul_le_mul_right hscaled (by positivity)
  have htwenty_disagreement :
      20 * (PolynomialModLowerBound.disagreementInputs F).card ≤ 2 ^ n := by
    calc
      20 * (PolynomialModLowerBound.disagreementInputs F).card ≤
          20 * (r * errors.card) := Nat.mul_le_mul_left _ hdisagreement_card
      _ = 20 * r * errors.card := by ring
      _ ≤ 2 ^ n := htwenty_errors
  have hpow_large : 20 ≤ 2 ^ n := by
    have hfive : 5 ≤ n := by
      omega
    calc
      20 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := by
        gcongr
        norm_num
  have hupper : (PolynomialModLowerBound.disagreementInputs F).card <
      2 ^ n / 10 := by
    let u := (PolynomialModLowerBound.disagreementInputs F).card
    have huplus : (u + 1) * 10 ≤ 2 ^ n := by
      by_cases hu : u = 0
      · rw [hu]
        norm_num
        exact (by omega : 10 ≤ 20).trans hpow_large
      · calc
          (u + 1) * 10 ≤ 20 * u := by omega
          _ ≤ 2 ^ n := by simpa [u] using htwenty_disagreement
    have : u + 1 ≤ 2 ^ n / 10 :=
      (Nat.le_div_iff_mul_le (by omega)).2 huplus
    omega
  exact (not_lt_of_ge hlowerBound) hupper

/-- **Smolensky's theorem, eventual-disagreement form.**

Let `p` be prime and let `r > 1` be coprime to `p`. Every polynomial-size,
constant-depth `ACCFormula[p]` family disagrees with `MOD_r` at every
sufficiently large input length. -/
theorem smolensky_mod_formula_eventually_disagrees
    (p r : ℕ) (hp : p.Prime) (hr : 1 < r) (hcop : r.Coprime p) :
    ∀ (sizeCoefficient sizeExponent depthBound : ℕ)
      (family : ACCFormula.ACCFormulaFamily p sizeCoefficient sizeExponent
        depthBound),
      ∃ n₀ : ℕ, ∀ N : PNat, N.val > n₀ →
        ¬ACCFormula.ComputesAtLength (family N).val N.val
          (modFunctionList r) := by
  intro sizeCoefficient sizeExponent depthBound family
  obtain ⟨n₀, hn₀⟩ :=
    smolensky_mod_eventually_disagrees_shifted p r hp hr hcop
      sizeCoefficient sizeExponent depthBound family
  refine ⟨n₀ + r, ?_⟩
  intro N hN
  let n := N.val - r
  have hn : n > n₀ := by
    dsimp [n]
    omega
  have hdecomp : n + r = N.val := by
    dsimp [n]
    omega
  obtain ⟨x, hx⟩ := hn₀ n hn
  have hN_eq : N = (⟨n + r, by omega⟩ : PNat) := by
    apply Subtype.ext
    exact hdecomp.symm
  rw [hN_eq]
  intro hcomputes
  exact hx (by
    simpa using hcomputes (List.ofFn x) (by simp))

#print axioms smolensky_mod_formula_eventually_disagrees

/-- **Smolensky's theorem.**

Let `p` be prime and let `r > 1` be coprime to `p`. Then `MOD_r` is not
computed by any polynomial-size, constant-depth `ACCFormula[p]` family. -/
theorem smolensky_mod_lower_bound
    (p r : ℕ) (hp : p.Prime) (hr : 1 < r) (hcop : r.Coprime p) :
    ∀ (sizeCoefficient sizeExponent depthBound : ℕ)
      (family : ACCFormula.ACCFormulaFamily p sizeCoefficient sizeExponent
        depthBound),
      ¬∀ (n : PNat) (x : Fin n.val → Bool),
        ACCFormula.eval (family n).val (List.ofFn x) = modFunction r x := by
  intro sizeCoefficient sizeExponent depthBound family hcompute
  obtain ⟨n₀, hdisagree⟩ :=
    smolensky_mod_eventually_disagrees_shifted p r hp hr hcop
      sizeCoefficient sizeExponent depthBound family
  obtain ⟨x, hx⟩ := hdisagree (n₀ + 1) (by omega)
  let N : PNat := ⟨n₀ + 1 + r, by omega⟩
  exact hx (by simpa [N] using hcompute N x)

#print axioms smolensky_mod_lower_bound

end Circuits.ACC
