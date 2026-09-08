import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Degree spaces of functions on the Boolean cube

This file develops the small piece of Reed--Muller linear algebra used in the
Smolensky polynomial lower bound.
-/

namespace Circuits.ACC.BooleanDegree

open Function

variable {K : Type*} [Field K]

/-- The squarefree monomial indexed by `s`, viewed as a function on the
Boolean cube. -/
def monomial {α : Type*} (s : Finset α) (x : α → Bool) : K :=
  ∏ i ∈ s, if x i then 1 else 0

/-- Functions representable on the Boolean cube by polynomials of degree at
most `d`. -/
def degreeSpace (α : Type*) [Fintype α] (d : ℕ) : Submodule K ((α → Bool) → K) :=
  Submodule.span K (Set.range fun s : {s : Finset α // s.card ≤ d} ↦ monomial s.1)

/-- Multiplication by the character `x ↦ ω ^ |x|`. -/
def twist {α : Type*} [Fintype α] (ω : K) (f : (α → Bool) → K) :
    (α → Bool) → K :=
  fun x ↦ (∏ i, if x i then ω else 1) * f x

@[simp] theorem monomial_empty {α : Type*} (x : α → Bool) :
    monomial (K := K) ∅ x = 1 := by
  simp [monomial]

theorem monomial_mem_degreeSpace {α : Type*} [Fintype α]
    {s : Finset α} {d : ℕ} (hs : s.card ≤ d) :
    monomial (K := K) s ∈ degreeSpace (K := K) α d := by
  apply Submodule.subset_span
  exact ⟨⟨s, hs⟩, rfl⟩

theorem degreeSpace_mono {α : Type*} [Fintype α] {a b : ℕ} (hab : a ≤ b) :
    degreeSpace (K := K) α a ≤ degreeSpace (K := K) α b := by
  apply Submodule.span_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨s.1, s.2.trans hab⟩, rfl⟩

private theorem monomial_eq_one_or_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → Bool) :
    monomial (K := K) s x = if ∀ i ∈ s, x i = true then 1 else 0 := by
  classical
  by_cases h : ∀ i ∈ s, x i = true
  · rw [if_pos h]
    simp only [monomial]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hxi⟩ := h
    simp only [monomial]
    apply Finset.prod_eq_zero hi
    cases hix : x i <;> simp_all

theorem monomial_mul {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    monomial (K := K) s * monomial t = monomial (s ∪ t) := by
  classical
  funext x
  simp only [Pi.mul_apply, monomial_eq_one_or_zero]
  by_cases hs : ∀ i ∈ s, x i = true
  · by_cases ht : ∀ i ∈ t, x i = true
    · rw [if_pos hs, if_pos ht, if_pos]
      · simp
      · intro i hi
        exact (Finset.mem_union.mp hi).elim (hs i) (ht i)
    · rw [if_pos hs, if_neg ht, mul_zero, if_neg]
      intro hst
      exact ht fun i hi ↦ hst i (Finset.mem_union_right s hi)
  · by_cases ht : ∀ i ∈ t, x i = true
    · rw [if_neg hs, if_pos ht, zero_mul, if_neg]
      intro hst
      exact hs fun i hi ↦ hst i (Finset.mem_union_left t hi)
    · rw [if_neg hs, if_neg ht, zero_mul, if_neg]
      intro hst
      exact hs fun i hi ↦ hst i (Finset.mem_union_left t hi)

/-- Degree spaces are closed under pointwise multiplication, with degrees
adding. -/
theorem mul_mem_degreeSpace {α : Type*} [Fintype α] {a b : ℕ}
    {f g : (α → Bool) → K}
    (hf : f ∈ degreeSpace (K := K) α a)
    (hg : g ∈ degreeSpace (K := K) α b) :
    f * g ∈ degreeSpace (K := K) α (a + b) := by
  classical
  change f ∈ Submodule.span K _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, rfl⟩ := hf
    change g ∈ Submodule.span K _ at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨t, rfl⟩ := hg
      rw [monomial_mul]
      apply monomial_mem_degreeSpace
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add s.2 t.2)
    | zero => simpa using Submodule.zero_mem (degreeSpace (K := K) α (a + b))
    | add g h _ _ hg hh =>
      simpa [mul_add] using Submodule.add_mem _ hg hh
    | smul c g _ hg =>
      have hc := Submodule.smul_mem (degreeSpace (K := K) α (a + b)) c hg
      convert hc using 1
      funext x
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
  | zero => simpa using Submodule.zero_mem (degreeSpace (K := K) α (a + b))
  | add f h _ _ hf hh =>
    simpa [add_mul] using Submodule.add_mem _ hf hh
  | smul c f _ hf =>
    have hc := Submodule.smul_mem (degreeSpace (K := K) α (a + b)) c hf
    convert hc using 1
    funext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Evaluate an `MvPolynomial` after embedding Boolean values into its
coefficient field. -/
noncomputable def evalPolynomial {α : Type*}
    (F : MvPolynomial α K) (x : α → Bool) : K :=
  MvPolynomial.eval (fun i ↦ ((x i).toNat : K)) F

private theorem eval_monomial_term {α : Type*} [DecidableEq α]
    (m : α →₀ ℕ) (x : α → Bool) :
    (∏ i ∈ m.support, (((x i).toNat : K) ^ m i)) =
      monomial (K := K) m.support x := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
  cases hxi : x i <;> simp [monomial, hxi, hmi]

theorem evalPolynomial_eq_sum {α : Type*} [DecidableEq α]
    (F : MvPolynomial α K) :
    evalPolynomial F = ∑ m ∈ F.support, F.coeff m • monomial m.support := by
  classical
  funext x
  simp only [evalPolynomial, MvPolynomial.eval_eq, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial_term]

private theorem support_card_le_sum {α : Type*} (m : α →₀ ℕ) :
    m.support.card ≤ m.sum fun _ e ↦ e := by
  classical
  calc
    m.support.card = ∑ i ∈ m.support, 1 := by simp
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ = m.sum fun _ e ↦ e := rfl

theorem evalPolynomial_mem_degreeSpace {α : Type*} [Fintype α]
    {F : MvPolynomial α K} {d : ℕ} (hF : F.totalDegree ≤ d) :
    evalPolynomial F ∈ degreeSpace (K := K) α d := by
  classical
  rw [evalPolynomial_eq_sum]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  apply monomial_mem_degreeSpace
  exact (support_card_le_sum m).trans
    ((MvPolynomial.le_totalDegree hm).trans hF)

/-- The Boolean assignment which is true exactly on `t`. -/
def assignmentOfSet {α : Type*} [DecidableEq α] (t : Finset α) : α → Bool :=
  fun i ↦ decide (i ∈ t)

@[simp] theorem monomial_assignmentOfSet {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    monomial (K := K) s (assignmentOfSet t) = if s ⊆ t then 1 else 0 := by
  classical
  rw [monomial_eq_one_or_zero]
  by_cases hst : s ⊆ t
  · rw [if_pos hst, if_pos]
    intro i hi
    simp [assignmentOfSet, hst hi]
  · rw [if_neg hst, if_neg]
    intro h
    exact hst fun i hi ↦ by
      have := h i hi
      simpa [assignmentOfSet] using this

/-- Squarefree monomials are linearly independent as functions on the
Boolean cube. -/
theorem monomial_linearIndependent {α : Type*} [Fintype α] :
    LinearIndependent K (fun s : Finset α ↦ monomial (K := K) s) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply Finset.strongInduction
  intro t ih
  have ht := congrFun hc (assignmentOfSet t)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    monomial_assignmentOfSet, mul_ite, mul_one, mul_zero] at ht
  have hsum : ∑ s ∈ t.powerset, c s = 0 := by
    rw [← Finset.sum_filter] at ht
    have hfilter :
        (Finset.univ.filter fun s : Finset α ↦ s ⊆ t) = t.powerset := by
      ext s
      simp
    simpa [hfilter] using ht
  have hproper : ∑ s ∈ t.powerset.erase t, c s = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hs_power : s ∈ t.powerset := (Finset.mem_erase.mp hs).2
    have hs_ne : s ≠ t := (Finset.mem_erase.mp hs).1
    have hsub := Finset.mem_powerset.mp hs_power
    exact ih s ⟨hsub, fun hts ↦ hs_ne (Finset.Subset.antisymm hsub hts)⟩
  have hsplit := Finset.sum_erase_add (s := t.powerset) (f := c)
    (Finset.mem_powerset.mpr (Finset.Subset.rfl : t ⊆ t))
  rw [hproper] at hsplit
  rw [← hsplit] at hsum
  simpa using hsum

/-- Restrict a function on an option cube to the face on which the new
coordinate is `b`. -/
def face (α : Type*) (b : Bool) :
    (((Option α → Bool) → K) →ₗ[K] ((α → Bool) → K)) where
  toFun f x := f (fun o ↦ o.elim b x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Difference of the `true` and `false` faces. -/
def faceDiff (α : Type*) :
    (((Option α → Bool) → K) →ₗ[K] ((α → Bool) → K)) :=
  face (K := K) α true - face (K := K) α false

@[simp] theorem face_apply {α : Type*} (b : Bool)
    (f : (Option α → Bool) → K) (x : α → Bool) :
    face (K := K) α b f x = f (fun o ↦ o.elim b x) := rfl

@[simp] theorem faceDiff_apply {α : Type*}
    (f : (Option α → Bool) → K) (x : α → Bool) :
    faceDiff (K := K) α f x =
      f (fun o ↦ o.elim true x) - f (fun o ↦ o.elim false x) := rfl

private theorem monomial_face_false {α : Type*} [DecidableEq α]
    (s : Finset (Option α)) (x : α → Bool) :
    face (K := K) α false (monomial s) x =
      if none ∈ s then 0 else monomial (s.eraseNone) x := by
  classical
  by_cases hs : none ∈ s
  · rw [if_pos hs]
    simp only [face_apply, monomial]
    exact Finset.prod_eq_zero hs (by simp)
  · rw [if_neg hs]
    simp only [face_apply, monomial]
    rw [Finset.prod_eraseNone]
    apply Finset.prod_congr rfl
    intro o ho
    cases o with
    | none => exact (hs ho).elim
    | some i => rfl

private theorem monomial_face_true {α : Type*} [DecidableEq α]
    (s : Finset (Option α)) (x : α → Bool) :
    face (K := K) α true (monomial s) x = monomial (s.eraseNone) x := by
  classical
  simp only [face_apply, monomial]
  rw [Finset.prod_eraseNone]
  apply Finset.prod_congr rfl
  intro o ho
  cases o <;> rfl

private theorem monomial_faceDiff {α : Type*} [DecidableEq α]
    (s : Finset (Option α)) :
    faceDiff (K := K) α (monomial s) =
      if none ∈ s then monomial (s.eraseNone) else 0 := by
  classical
  funext x
  change face (K := K) α true (monomial s) x -
    face (K := K) α false (monomial s) x = _
  rw [monomial_face_true, monomial_face_false]
  split <;> simp_all

theorem face_false_mem {α : Type*} [Fintype α] {d : ℕ}
    {f : (Option α → Bool) → K}
    (hf : f ∈ degreeSpace (K := K) (Option α) d) :
    face (K := K) α false f ∈ degreeSpace (K := K) α d := by
  change f ∈ Submodule.span K _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, rfl⟩ := hf
    classical
    rw [show face (K := K) α false (monomial s.1) =
      if none ∈ s.1 then 0 else monomial s.1.eraseNone by
        funext x
        by_cases hnone : none ∈ s.1
        · rw [if_pos hnone, Pi.zero_apply]
          simpa [hnone] using monomial_face_false (K := K) s.1 x
        · rw [if_neg hnone]
          simpa [hnone] using monomial_face_false (K := K) s.1 x]
    split
    · exact Submodule.zero_mem _
    · exact monomial_mem_degreeSpace
        ((Finset.card_eraseNone_le s.1).trans s.2)
  | zero => exact Submodule.zero_mem (degreeSpace (K := K) α d)
  | add f g _ _ hf hg =>
    simpa using Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    simpa using Submodule.smul_mem _ c hf

theorem faceDiff_mem {α : Type*} [Fintype α] {d : ℕ}
    {f : (Option α → Bool) → K}
    (hf : f ∈ degreeSpace (K := K) (Option α) d) :
    faceDiff (K := K) α f ∈ degreeSpace (K := K) α (d - 1) := by
  change f ∈ Submodule.span K _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, rfl⟩ := hf
    classical
    rw [monomial_faceDiff (K := K)]
    split
    · apply monomial_mem_degreeSpace
      have hcard := Finset.card_eraseNone_of_mem (s := s.1) (by assumption)
      omega
    · exact Submodule.zero_mem _
  | zero =>
    simpa using Submodule.zero_mem (degreeSpace (K := K) α (d - 1))
  | add f g _ _ hf hg =>
    simpa using Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    simpa using Submodule.smul_mem _ c hf

theorem faceDiff_eq_zero_of_mem_degreeSpace_zero {α : Type*} [Fintype α]
    {f : (Option α → Bool) → K}
    (hf : f ∈ degreeSpace (K := K) (Option α) 0) :
    faceDiff (K := K) α f = 0 := by
  change f ∈ Submodule.span K _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, rfl⟩ := hf
    classical
    rw [monomial_faceDiff (K := K)]
    have hs_empty : s.1 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp s.2)
    simp [hs_empty]
  | zero => simp
  | add f g _ _ hf hg => simp [hf, hg]
  | smul c f _ hf => simp [hf]

theorem face_true_eq_add_diff {α : Type*}
    (f : (Option α → Bool) → K) :
    face (K := K) α true f =
      face (K := K) α false f + faceDiff (K := K) α f := by
  ext x
  simp [faceDiff]

/-- Rename the coordinates of a Boolean-cube function. -/
def reindex {α β : Type*} (e : α ≃ β) :
    ((α → Bool) → K) ≃ₗ[K] ((β → Bool) → K) where
  toFun f x := f (x ∘ e)
  invFun f x := f (x ∘ e.symm)
  left_inv f := by
    funext x
    change f ((x ∘ e.symm) ∘ e) = f x
    congr 1
    funext i
    simp
  right_inv f := by
    funext x
    change f ((x ∘ e) ∘ e.symm) = f x
    congr 1
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem reindex_apply {α β : Type*} (e : α ≃ β)
    (f : (α → Bool) → K) (x : β → Bool) :
    reindex (K := K) e f x = f (x ∘ e) := rfl

theorem reindex_monomial {α β : Type*} [DecidableEq β]
    (e : α ≃ β) (s : Finset α) :
    reindex (K := K) e (monomial s) = monomial (s.map e.toEmbedding) := by
  classical
  funext x
  simp only [reindex_apply, monomial, Finset.prod_map]
  rfl

theorem reindex_mem_degreeSpace {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) {d : ℕ} {f : (α → Bool) → K}
    (hf : f ∈ degreeSpace (K := K) α d) :
    reindex (K := K) e f ∈ degreeSpace (K := K) β d := by
  classical
  change f ∈ Submodule.span K _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, rfl⟩ := hf
    rw [reindex_monomial]
    apply monomial_mem_degreeSpace
    simpa using s.2
  | zero =>
    simpa using Submodule.zero_mem (degreeSpace (K := K) β d)
  | add f g _ _ hf hg =>
    simpa using Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    simpa using Submodule.smul_mem _ c hf

theorem reindex_twist {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (ω : K) (f : (α → Bool) → K) :
    reindex (K := K) e (twist ω f) = twist ω (reindex (K := K) e f) := by
  classical
  funext x
  simp only [reindex_apply, twist]
  congr 1
  rw [← e.prod_comp]
  rfl

theorem face_false_twist {α : Type*} [Fintype α]
    (ω : K) (f : (Option α → Bool) → K) :
    face (K := K) α false (twist ω f) =
      twist ω (face (K := K) α false f) := by
  classical
  funext x
  simp only [face_apply, twist]
  simp only [univ_option, Finset.prod_insertNone, Option.elim_none,
    Option.elim_some, Bool.false_eq_true, if_false, one_mul]
  rfl

theorem faceDiff_twist {α : Type*} [Fintype α]
    (ω : K) (f : (Option α → Bool) → K) :
    faceDiff (K := K) α (twist ω f) =
      twist ω ((ω - 1) • face (K := K) α false f +
        ω • faceDiff (K := K) α f) := by
  classical
  funext x
  simp only [faceDiff_apply, twist, face_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [univ_option, Finset.prod_insertNone, Option.elim_none,
    Option.elim_some, Bool.false_eq_true, if_false, if_true,
    one_mul]
  let A : K := ∏ i, if x i then ω else 1
  let u : K := f (fun o ↦ o.elim true x)
  let v : K := f (fun o ↦ o.elim false x)
  change ω * A * u - A * v = A * ((ω - 1) * v + ω * (u - v))
  ring

theorem twist_eq_zero_iff {α : Type*} [Fintype α]
    {ω : K} (hω : ω ≠ 0) (f : (α → Bool) → K) :
    twist ω f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext x
    have hx := congrFun h x
    simp only [twist, Pi.zero_apply] at hx
    apply (mul_eq_zero.mp hx).resolve_left
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split <;> simp_all
  · rintro rfl
    funext x
    exact mul_zero _

/-- A nontrivial coordinatewise character carries the degree-`a` space
transversely to the degree-`b` space whenever `a + b` is smaller than the
number of variables.  This is the algebraic core of Smolensky's rank
argument. -/
theorem twist_transverse (ω : K) (hω_zero : ω ≠ 0) (hω_one : ω ≠ 1) :
    ∀ (α : Type*) [Fintype α] (a b : ℕ) (f : (α → Bool) → K),
      f ∈ degreeSpace (K := K) α a →
      twist ω f ∈ degreeSpace (K := K) α b →
      a + b < Fintype.card α → f = 0 := by
  classical
  refine Fintype.induction_empty_option
    (P := fun α ↦ ∀ (a b : ℕ) (f : (α → Bool) → K),
      f ∈ degreeSpace (K := K) α a →
      twist ω f ∈ degreeSpace (K := K) α b →
      a + b < Fintype.card α → f = 0) ?_ ?_ ?_
  · intro α β _ e ih a b f hf htf hab
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let f' : (α → Bool) → K := reindex (K := K) e.symm f
    have hf' : f' ∈ degreeSpace (K := K) α a :=
      reindex_mem_degreeSpace (K := K) e.symm hf
    have htf' : twist ω f' ∈ degreeSpace (K := K) α b := by
      rw [← reindex_twist (K := K) e.symm]
      exact reindex_mem_degreeSpace (K := K) e.symm htf
    have hab' : a + b < Fintype.card α := by
      simpa [Fintype.card_congr e] using hab
    have hf'_zero := ih a b f' hf' htf' hab'
    apply (reindex (K := K) e.symm).injective
    simpa [f'] using hf'_zero
  · intro a b f _ _ hab
    simp at hab
  · intro α _ ih a b f hf htf hab
    let u : (α → Bool) → K := face (K := K) α false f
    let v : (α → Bool) → K := faceDiff (K := K) α f
    let w : (α → Bool) → K := (ω - 1) • u + ω • v
    have hu : u ∈ degreeSpace (K := K) α a := face_false_mem hf
    have hv : v ∈ degreeSpace (K := K) α (a - 1) := faceDiff_mem hf
    have hv_a : v ∈ degreeSpace (K := K) α a :=
      degreeSpace_mono (K := K) (Nat.sub_le a 1) hv
    have hw : w ∈ degreeSpace (K := K) α a := by
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu)
        (Submodule.smul_mem _ _ hv_a)
    have htu : twist ω u ∈ degreeSpace (K := K) α b := by
      rw [← face_false_twist (K := K)]
      exact face_false_mem htf
    have htw : twist ω w ∈ degreeSpace (K := K) α (b - 1) := by
      rw [← faceDiff_twist (K := K)]
      exact faceDiff_mem htf
    have hw_zero : w = 0 := by
      by_cases hb : b = 0
      · subst b
        have hdiff : faceDiff (K := K) α (twist ω f) = 0 :=
          faceDiff_eq_zero_of_mem_degreeSpace_zero htf
        rw [faceDiff_twist (K := K)] at hdiff
        exact (twist_eq_zero_iff hω_zero w).mp hdiff
      · apply ih a (b - 1) w hw htw
        rw [Fintype.card_option] at hab
        omega
    have hu_pred : u ∈ degreeSpace (K := K) α (a - 1) := by
      by_cases ha : a = 0
      · subst a
        have hv_zero : v = 0 := faceDiff_eq_zero_of_mem_degreeSpace_zero hf
        have hscaled : (ω - 1) • u = 0 := by
          simpa [w, hv_zero] using hw_zero
        have hnonzero : ω - 1 ≠ 0 := sub_ne_zero.mpr hω_one
        have hu_zero : u = 0 := by
          exact (smul_eq_zero.mp hscaled).resolve_left hnonzero
        simpa [hu_zero]
      · have hscaled : (ω - 1) • u = -ω • v := by
          have := hw_zero
          simp only [w, Pi.add_def, Pi.smul_def] at this ⊢
          ext x
          have hx := congrFun this x
          simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hx ⊢
          simpa [neg_mul] using eq_neg_of_add_eq_zero_left hx
        have hscaled_mem : (ω - 1) • u ∈ degreeSpace (K := K) α (a - 1) := by
          rw [hscaled]
          exact Submodule.smul_mem _ _ hv
        have hinv := Submodule.smul_mem (degreeSpace (K := K) α (a - 1))
          (ω - 1)⁻¹ hscaled_mem
        have hnonzero : ω - 1 ≠ 0 := sub_ne_zero.mpr hω_one
        simpa [smul_smul, hnonzero] using hinv
    have hu_zero : u = 0 := by
      by_cases ha : a = 0
      · subst a
        have hv_zero : v = 0 := faceDiff_eq_zero_of_mem_degreeSpace_zero hf
        have hscaled : (ω - 1) • u = 0 := by
          simpa [w, hv_zero] using hw_zero
        exact (smul_eq_zero.mp hscaled).resolve_left (sub_ne_zero.mpr hω_one)
      · apply ih (a - 1) b u hu_pred htu
        rw [Fintype.card_option] at hab
        omega
    have hv_zero : v = 0 := by
      have hscaled : ω • v = 0 := by
        simpa [w, hu_zero] using hw_zero
      exact (smul_eq_zero.mp hscaled).resolve_left hω_zero
    funext x
    let y : α → Bool := fun i ↦ x (some i)
    cases hx : x none with
    | false =>
        have hxeq : x = fun o ↦ o.elim false y := by
          funext o
          cases o with
          | none => simpa using hx
          | some i => rfl
        rw [hxeq]
        exact congrFun hu_zero y
    | true =>
        have hxeq : x = fun o ↦ o.elim true y := by
          funext o
          cases o with
          | none => simpa using hx
          | some i => rfl
        rw [hxeq]
        change face (K := K) α true f y = 0
        rw [face_true_eq_add_diff (K := K) f]
        simp [u, v, hu_zero, hv_zero]

/-- The rank consequence of `twist_transverse`: if a degree-`d` function
agrees with the character off `E`, then `E` has at least as many points as
there are squarefree monomials of degree at most `a`, provided
`2a + d < |α|`. -/
theorem lowDegreeMonomials_card_le_error
    {α : Type*} [Fintype α] (ω : K) (hω_zero : ω ≠ 0) (hω_one : ω ≠ 1)
    (d a : ℕ) (p : (α → Bool) → K)
    (hp : p ∈ degreeSpace (K := K) α d)
    (E : Finset (α → Bool))
    (hagree : ∀ x ∉ E, p x = twist ω (1 : (α → Bool) → K) x)
    (hdegree : a + (d + a) < Fintype.card α) :
    Fintype.card {s : Finset α // s.card ≤ a} ≤ E.card := by
  classical
  let h : (α → Bool) → K := twist ω (1 : (α → Bool) → K) - p
  let vectors : {s : Finset α // s.card ≤ a} → (↑E → K) := fun s x ↦
    h x.1 * monomial (K := K) s.1 x.1
  have hvectors : LinearIndependent K vectors := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    let f : (α → Bool) → K :=
      ∑ s : {s : Finset α // s.card ≤ a}, c s • monomial (K := K) s.1
    have hf : f ∈ degreeSpace (K := K) α a := by
      apply Submodule.sum_mem
      intro s _
      exact Submodule.smul_mem _ _ (monomial_mem_degreeSpace s.2)
    have hhf : h * f = 0 := by
      funext x
      by_cases hx : x ∈ E
      · have hxsum := congrFun hsum ⟨x, hx⟩
        simp only [vectors, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at hxsum
        simp only [Pi.mul_apply, Pi.zero_apply]
        simp only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hxsum
      · have hp_char := hagree x hx
        simp only [Pi.mul_apply, Pi.zero_apply]
        change (twist ω (1 : (α → Bool) → K) x - p x) * f x = 0
        rw [hp_char]
        simp
    have htwist_mul : twist ω f = p * f := by
      funext x
      have hx := congrFun hhf x
      simp only [Pi.mul_apply, Pi.zero_apply, h, Pi.sub_apply] at hx
      have hchar : twist ω (1 : (α → Bool) → K) x * f x = twist ω f x := by
        simp [twist]
      change twist ω f x = p x * f x
      rw [← hchar]
      apply sub_eq_zero.mp
      simpa [sub_mul] using hx
    have hpf : p * f ∈ degreeSpace (K := K) α (d + a) :=
      mul_mem_degreeSpace hp hf
    have htf : twist ω f ∈ degreeSpace (K := K) α (d + a) := by
      rw [htwist_mul]
      exact hpf
    have hf_zero : f = 0 :=
      twist_transverse ω hω_zero hω_one α a (d + a) f hf htf hdegree
    have hmono : LinearIndependent K
        (fun s : {s : Finset α // s.card ≤ a} ↦ monomial (K := K) s.1) :=
      monomial_linearIndependent.comp Subtype.val Subtype.val_injective
    exact (Fintype.linearIndependent_iff.mp hmono c) (by simpa [f] using hf_zero)
  calc
    Fintype.card {s : Finset α // s.card ≤ a}
        ≤ Module.finrank K (↑E → K) := hvectors.fintype_card_le_finrank
    _ = E.card := by
      rw [Module.finrank_pi]
      simp

end Circuits.ACC.BooleanDegree
