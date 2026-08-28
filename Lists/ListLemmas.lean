import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card

namespace Lists.ListLemmas

/-- Monotonicity of `List.foldl max` in the initial accumulator. -/
theorem foldl_max_mono {l : List Nat} {a b : Nat} (hab : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    omega

/-- The initial accumulator is at most `List.foldl max`. -/
theorem init_le_foldl_max {l : List Nat} {init : Nat} :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    exact Nat.le_trans (Nat.le_max_left init hd) ih

/-- Any member of a list is at most `List.foldl max 0` over the list. -/
theorem mem_le_foldl_max {l : List Nat} {x : Nat} (hx : x ∈ l) :
    x ≤ l.foldl max 0 := by
  induction l with
  | nil => simp at hx
  | cons a tl ih =>
    simp only [List.foldl]
    rw [List.mem_cons] at hx
    cases hx with
    | inl h => subst h; exact Nat.le_trans (Nat.le_max_right 0 x) init_le_foldl_max
    | inr h => exact Nat.le_trans (ih h) (foldl_max_mono (Nat.zero_le _))

/-- If every member of a list is bounded by `b`, then its maximum is also
    bounded by `b`. -/
theorem foldl_max_le_of_forall {l : List Nat} {b : Nat}
    (h : ∀ x ∈ l, x ≤ b) : l.foldl max 0 ≤ b := by
  have hgen : ∀ (acc : Nat), acc ≤ b → l.foldl max acc ≤ b := by
    intro acc
    induction l generalizing acc with
    | nil => intro hacc; simpa using hacc
    | cons y ys ih =>
      intro hacc
      simp only [List.foldl_cons]
      apply ih
      · intro x hx
        exact h x (List.mem_cons_of_mem y hx)
      · exact max_le hacc (h y List.mem_cons_self)
  exact hgen 0 (Nat.zero_le b)

/-- A mapped `foldl max` stays below a common bound when its initial value and
    every mapped element do. -/
theorem foldl_max_map_le_of_forall {α : Type*} (l : List α) (f : α → Nat)
    (b init : Nat) (hinit : init ≤ b) (h : ∀ x ∈ l, f x ≤ b) :
    (l.map f).foldl max init ≤ b := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · exact max_le hinit (h x List.mem_cons_self)
    · intro y hy
      exact h y (List.mem_cons_of_mem _ hy)

/-- Two prefixes of the same list are comparable: one is a prefix of the other. -/
lemma prefix_or_prefix_of_prefix {α : Type}
    {l₁ l₂ l : List α} (h₁ : l₁ <+: l) (h₂ : l₂ <+: l) :
    l₁ <+: l₂ ∨ l₂ <+: l₁ := by
  obtain ⟨t₁, rfl⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  induction l₁ generalizing l₂ t₂ with
  | nil => left; exact List.nil_prefix
  | cons a rest₁ ih =>
    cases l₂ with
    | nil => right; exact List.nil_prefix
    | cons b rest₂ =>
      rw [List.cons_append, List.cons_append] at ht₂
      have hab := List.cons.inj ht₂
      rw [hab.1]
      have ih' := ih (t₂ := t₂) hab.2
      cases ih' with
      | inl h => left; exact List.cons_prefix_cons.mpr ⟨rfl, h⟩
      | inr h => right; exact List.cons_prefix_cons.mpr ⟨rfl, h⟩

/-- If a list of pairs has nodup first components, two members with the same
    first component must have the same second component. -/
lemma nodup_map_fst_snd_eq
    {α β : Type*} {l : List (α × β)} (hnd : (l.map Prod.fst).Nodup)
    {a : α} {b1 b2 : β} (h1 : (a, b1) ∈ l) (h2 : (a, b2) ∈ l) :
    b1 = b2 := by
  induction l with
  | nil => simp at h1
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with h1_eq | h1_rest <;>
    rcases List.mem_cons.mp h2 with h2_eq | h2_rest
    · -- Both equal to p: (a, b1) = p and (a, b2) = p
      exact (Prod.mk.inj (h2_eq.trans h1_eq.symm)).2.symm
    · -- h1 = p, h2 in rest: p.1 = a ∈ ps.map fst contradicts nodup
      exfalso
      have hpa : p.1 = a := (congr_arg Prod.fst h1_eq).symm
      exact hnd.1 (hpa ▸ List.mem_map.mpr ⟨(a, b2), h2_rest, rfl⟩)
    · exfalso
      have hpa : p.1 = a := (congr_arg Prod.fst h2_eq).symm
      exact hnd.1 (hpa ▸ List.mem_map.mpr ⟨(a, b1), h1_rest, rfl⟩)
    · exact ih hnd.2 h1_rest h2_rest

end Lists.ListLemmas
