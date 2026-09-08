import ACC.LowerBounds.PolynomialMod
import ACC.Simulation.PolynomialApproximation
import ACC.Asymptotics.Polylogarithmic

namespace Circuits.ACC

open ModPAndCircuit

namespace SmolenskyBridge


/-- Append an `r`-bit suffix containing exactly `r-i` ones. -/
def residueExtension (n r : ℕ) (i : Fin r) (x : Fin n → Bool) :
    Fin (n + r) → Bool :=
  Fin.append x (fun j ↦ decide (j.val < r - i.val))

@[simp] theorem residueExtension_left (n r : ℕ) (i : Fin r)
    (x : Fin n → Bool) (j : Fin n) :
    residueExtension n r i x (Fin.castAdd r j) = x j := by
  simp [residueExtension]

@[simp] theorem residueExtension_right (n r : ℕ) (i : Fin r)
    (x : Fin n → Bool) (j : Fin r) :
    residueExtension n r i x (Fin.natAdd n j) =
      decide (j.val < r - i.val) := by
  simp [residueExtension]

theorem residueExtension_weight (n r : ℕ) (i : Fin r)
    (x : Fin n → Bool) :
    ∑ j, (residueExtension n r i x j).toNat =
      (∑ j, (x j).toNat) + (r - i.val) := by
  rw [Fin.sum_univ_add]
  simp only [residueExtension_left, residueExtension_right]
  congr 1
  calc
    (∑ j : Fin r, (decide (j.val < r - i.val) : Bool).toNat) =
        ∑ j : Fin r, if j.val < r - i.val then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : j.val < r - i.val <;> simp [h]
    _ = ((Finset.univ : Finset (Fin r)).filter
          fun j ↦ j.val < r - i.val).card := Finset.sum_boole _ _
    _ = r - i.val := by
      rw [Fin.card_filter_val_lt]
      exact min_eq_right (Nat.sub_le r i.val)

theorem residueExtension_mod_iff (r : ℕ) (hr : 0 < r) (i : Fin r)
    (weight : ℕ) :
    (weight + (r - i.val)) % r = 0 ↔ weight % r = i.val := by
  let a := weight % r
  have ha : a < r := Nat.mod_lt _ hr
  have hi : i.val < r := i.isLt
  constructor
  · intro h
    have hmod : (a + (r - i.val)) % r = 0 := by
      simpa [a, Nat.add_mod] using h
    have hdvd : r ∣ a + (r - i.val) := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨c, hc⟩ := hdvd
    have hsum_pos : 0 < a + (r - i.val) := by
      by_cases hz : a = 0
      · subst a
        omega
      · omega
    have hcpos : 0 < c := by
      by_contra hc0
      have : c = 0 := Nat.eq_zero_of_not_pos hc0
      simp [this] at hc
      omega
    have hclt : c < 2 := by
      have hsumlt : a + (r - i.val) < 2 * r := by omega
      by_contra hc2
      have htwo : 2 ≤ c := by omega
      have hmul : 2 * r ≤ c * r := Nat.mul_le_mul_right r htwo
      rw [Nat.mul_comm c r, ← hc] at hmul
      omega
    have hc1 : c = 1 := by omega
    subst c
    omega
  · intro h
    change a = i.val at h
    have hsum : a + (r - i.val) = r := by omega
    calc
      (weight + (r - i.val)) % r =
          (a + (r - i.val)) % r := by simp [a, Nat.add_mod]
      _ = 0 := by rw [hsum, Nat.mod_self]

/-- The variables of a monomial which lie in the first `n` coordinates. -/
def headSupport (n r : ℕ) (s : Finset (Fin (n + r))) : Finset (Fin n) :=
  Finset.filterMap
    (fun j ↦ if h : j.val < n then some ⟨j.val, h⟩ else none) s (by
      intro a b z ha hb
      by_cases hA : a.val < n
      · simp [hA] at ha
        by_cases hB : b.val < n
        · simp [hB] at hb
          apply Fin.ext
          exact congrArg (fun w : Fin n ↦ w.val) (ha.trans hb.symm)
        · simp [hB] at hb
      · simp [hA] at ha)

@[simp] theorem mem_headSupport {n r : ℕ} {s : Finset (Fin (n + r))}
    {j : Fin n} : j ∈ headSupport n r s ↔ Fin.castAdd r j ∈ s := by
  classical
  simp only [headSupport, Finset.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hmap⟩
    split at hmap <;> simp_all
    subst j
    simpa using ha
  · intro hj
    refine ⟨Fin.castAdd r j, hj, ?_⟩
    simp

theorem card_headSupport_le {n r : ℕ} (s : Finset (Fin (n + r))) :
    (headSupport n r s).card ≤ s.card := by
  classical
  apply Finset.card_le_card_of_injOn (Fin.castAdd r)
  · intro j hj
    exact mem_headSupport.mp hj
  · intro a ha b hb hab
    apply Fin.ext
    exact congrArg (fun w : Fin (n + r) ↦ w.val) hab

theorem headSupport_insert_of_lt {n r : ℕ} {s : Finset (Fin (n + r))}
    {a : Fin (n + r)} (ha : a.val < n) :
    headSupport n r (insert a s) =
      insert ⟨a.val, ha⟩ (headSupport n r s) := by
  classical
  ext j
  simp only [mem_headSupport, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · left
      apply Fin.ext
      exact congrArg (fun z : Fin (n + r) ↦ z.val) h
    · exact Or.inr h
  · rintro (h | h)
    · left
      apply Fin.ext
      exact congrArg (fun z : Fin n ↦ z.val) h
    · exact Or.inr h

theorem headSupport_insert_of_ge {n r : ℕ} {s : Finset (Fin (n + r))}
    {a : Fin (n + r)} (ha : n ≤ a.val) :
    headSupport n r (insert a s) = headSupport n r s := by
  classical
  ext j
  simp only [mem_headSupport, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · have := congrArg (fun z : Fin (n + r) ↦ z.val) h
      simp at this
      omega
    · exact h
  · exact Or.inr

/-- The value contributed by suffix variables to a squarefree monomial. -/
def suffixValue (n r : ℕ) (i : Fin r) (s : Finset (Fin (n + r))) : ℕ :=
  ∏ j ∈ s, if n ≤ j.val then
    ((decide (j.val - n < r - i.val) : Bool).toNat)
  else 1

theorem residueExtension_apply (n r : ℕ) (i : Fin r)
    (x : Fin n → Bool) (j : Fin (n + r)) :
    residueExtension n r i x j =
      if h : j.val < n then x ⟨j.val, h⟩
      else decide (j.val - n < r - i.val) := by
  refine Fin.addCases (motive := fun j ↦
    residueExtension n r i x j =
      if h : j.val < n then x ⟨j.val, h⟩
      else decide (j.val - n < r - i.val)) ?_ ?_ j
  · intro a
    simp
  · intro b
    simp

theorem monomial_residueExtension
    (p n r : ℕ) (i : Fin r) (x : Fin n → Bool)
    (s : Finset (Fin (n + r))) :
    (∏ j ∈ s, ((residueExtension n r i x j).toNat : ZMod p)) =
      (suffixValue n r i s : ZMod p) *
        ∏ j ∈ headSupport n r s, ((x j).toNat : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [suffixValue, headSupport]
  | @insert a s ha ih =>
      by_cases hhead : a.val < n
      · have hnot : (⟨a.val, hhead⟩ : Fin n) ∉ headSupport n r s := by
          rw [mem_headSupport]
          intro hmem
          apply ha
          have heq : Fin.castAdd r (⟨a.val, hhead⟩ : Fin n) = a := by
            apply Fin.ext
            rfl
          simpa [heq] using hmem
        rw [Finset.prod_insert ha, headSupport_insert_of_lt hhead,
          Finset.prod_insert hnot, ih]
        simp [suffixValue, ha, hhead, Nat.not_le_of_lt hhead,
          residueExtension_apply, mul_assoc, mul_comm]
      · have hge : n ≤ a.val := Nat.le_of_not_gt hhead
        rw [Finset.prod_insert ha, headSupport_insert_of_ge hge, ih]
        simp only [suffixValue, Finset.prod_insert ha, hge, if_true]
        rw [residueExtension_apply, dif_neg hhead]
        push_cast
        ring

/-- Restrict an expanded polynomial over `ZMod p` to a residue-selecting
Boolean suffix and extend its coefficients to a field of characteristic
`p`. -/
noncomputable def restrictedPolynomial
    (p n r : ℕ) {K : Type*} [CommSemiring K] [Algebra (ZMod p) K]
    (i : Fin r) (q : MultilinearPolynomial p (n + r)) :
    MvPolynomial (Fin n) K :=
  (q.terms.map fun term ↦
    MvPolynomial.C (algebraMap (ZMod p) K
      (term.1 * (suffixValue n r i term.2 : ZMod p))) *
      ∏ j ∈ headSupport n r term.2, MvPolynomial.X j).sum

theorem restrictedPolynomial_eval
    (p n r : ℕ) {K : Type*} [CommSemiring K] [Algebra (ZMod p) K]
    (i : Fin r) (q : MultilinearPolynomial p (n + r))
    (x : Fin n → Bool) :
    PolynomialModLowerBound.evalBool
        (restrictedPolynomial p n r (K := K) i q) x =
      algebraMap (ZMod p) K
        (MultilinearPolynomial.eval q (residueExtension n r i x)) := by
  classical
  unfold restrictedPolynomial PolynomialModLowerBound.evalBool
    MultilinearPolynomial.eval
  induction q.terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons, map_add]
      rw [ih]
      simp only [MvPolynomial.eval_C, MvPolynomial.eval_prod, MvPolynomial.eval_X,
        map_mul]
      rw [monomial_residueExtension]
      simp only [map_mul, map_natCast, map_prod]
      ring

private theorem totalDegree_term_le_card
    {p n r : ℕ} {K : Type*} [Field K] [Algebra (ZMod p) K]
    (i : Fin r) (term : ZMod p × Finset (Fin (n + r))) :
    (MvPolynomial.C (algebraMap (ZMod p) K
        (term.1 * (suffixValue n r i term.2 : ZMod p))) *
        ∏ j ∈ headSupport n r term.2, MvPolynomial.X j).totalDegree ≤
      term.2.card := by
  calc
    _ ≤ (MvPolynomial.C (algebraMap (ZMod p) K
          (term.1 * (suffixValue n r i term.2 : ZMod p))) :
          MvPolynomial (Fin n) K).totalDegree +
        (∏ j ∈ headSupport n r term.2,
          (MvPolynomial.X j : MvPolynomial (Fin n) K)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + ∑ j ∈ headSupport n r term.2,
          (MvPolynomial.X j : MvPolynomial (Fin n) K).totalDegree := by
      rw [MvPolynomial.totalDegree_C]
      gcongr
      exact MvPolynomial.totalDegree_finsetProd _ _
    _ = (headSupport n r term.2).card := by simp
    _ ≤ term.2.card := card_headSupport_le _

private theorem degreeOf_squarefreeProduct
    {n : ℕ} {K : Type*} [Field K] (v : Fin n) (s : Finset (Fin n)) :
    MvPolynomial.degreeOf v
        (∏ j ∈ s, (MvPolynomial.X j : MvPolynomial (Fin n) K)) ≤
      if v ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine (MvPolynomial.degreeOf_mul_le v _ _).trans ?_
      by_cases hva : v = a
      · subst a
        have hvs : v ∉ s := ha
        have ih0 : MvPolynomial.degreeOf v
            (∏ j ∈ s, (MvPolynomial.X j : MvPolynomial (Fin n) K)) ≤ 0 := by
          simpa [hvs] using ih
        rw [MvPolynomial.degreeOf_X]
        simp only [ite_true]
        have hadd := add_le_add_right ih0 1
        simpa using hadd
      · by_cases hvs : v ∈ s
        · rw [MvPolynomial.degreeOf_X]
          simp only [hva, if_false, zero_add, Finset.mem_insert, hvs,
            or_true, if_true]
          simpa [hvs] using ih
        · rw [MvPolynomial.degreeOf_X]
          simp only [hva, if_false, zero_add, Finset.mem_insert, hvs,
            or_false]
          simpa [hvs] using ih

private theorem degreeOf_term_le_one
    {p n r : ℕ} {K : Type*} [Field K] [Algebra (ZMod p) K]
    (i : Fin r) (term : ZMod p × Finset (Fin (n + r))) (v : Fin n) :
    MvPolynomial.degreeOf v
        (MvPolynomial.C (algebraMap (ZMod p) K
          (term.1 * (suffixValue n r i term.2 : ZMod p))) *
          ∏ j ∈ headSupport n r term.2, MvPolynomial.X j) ≤ 1 := by
  refine (MvPolynomial.degreeOf_mul_le v _ _).trans ?_
  rw [MvPolynomial.degreeOf_C]
  simp only [zero_add]
  exact (degreeOf_squarefreeProduct v (headSupport n r term.2)).trans (by
    split <;> simp)

set_option maxHeartbeats 800000 in
-- Elaborating the dependent list induction below exceeds the default budget.
theorem restrictedPolynomial_totalDegree_le
    (p n r d : ℕ) {K : Type*} [Field K] [Algebra (ZMod p) K]
    (i : Fin r) (q : MultilinearPolynomial p (n + r))
    (hq : MultilinearPolynomial.DegreeAtMost q d) :
    (restrictedPolynomial p n r (K := K) i q).totalDegree ≤ d := by
  classical
  unfold restrictedPolynomial
  have aux : ∀ terms : List (ZMod p × Finset (Fin (n + r))),
      (∀ term ∈ terms, term.2.card ≤ d) →
      (List.map
        (fun (term : ZMod p × Finset (Fin (n + r))) ↦
          MvPolynomial.C (algebraMap (ZMod p) K
            (term.1 * (suffixValue n r i term.2 : ZMod p))) *
            ∏ j ∈ headSupport n r term.2, MvPolynomial.X j)
        terms).sum.totalDegree ≤ d := by
    intro terms hall
    induction terms with
    | nil => simp
    | cons term terms ih =>
        rw [List.map_cons, List.sum_cons]
        refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_term_le_card i term).trans
            (hall term (by simp))
        · apply ih
          intro t ht
          exact hall t (by simp [ht])
  exact aux q.terms hq

theorem restrictedPolynomial_multilinear
    (p n r : ℕ) {K : Type*} [Field K] [Algebra (ZMod p) K]
    (i : Fin r) (q : MultilinearPolynomial p (n + r)) :
    PolynomialModLowerBound.IsMultilinear
      (restrictedPolynomial p n r (K := K) i q) := by
  classical
  intro v
  unfold restrictedPolynomial
  induction q.terms with
  | nil => simp
  | cons term terms ih =>
      rw [List.map_cons, List.sum_cons]
      exact (MvPolynomial.degreeOf_add_le v _ _).trans
        (max_le (degreeOf_term_le_one i term v) ih)


end SmolenskyBridge

end Circuits.ACC
