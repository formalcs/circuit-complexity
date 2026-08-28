import Formulas.Basic

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

-- Helper: (List.foldr max 0) of a sublist is ≤ (List.foldr max 0) of the full list
theorem foldr_max_sublist {l1 l2 : List Nat} (h : l1.Sublist l2) : (List.foldr max 0) l1 ≤ (List.foldr max 0) l2 := by
  induction h with
  | slnil => simp [List.foldr_cons, List.foldr_nil]
  | cons a _ ih =>
    simp [List.foldr_cons, List.foldr_nil]
    omega
  | cons_cons a _ ih =>
    simp [List.foldr_cons, List.foldr_nil]
    omega

-- Helper: (List.foldr max 0) of a mapped list is ≤ uniform bound
theorem foldr_max_map_le {α : Type*} (f : α → Nat) (l : List α) (bound : Nat)
    (hb : ∀ x ∈ l, f x ≤ bound) : (List.foldr max 0) (l.map f) ≤ bound := by
  induction l with
  | nil => simp [List.foldr_cons, List.foldr_nil]
  | cons head tail ih =>
    simp only [List.foldr_cons, List.foldr_nil, List.map]
    apply max_le
    · exact hb head (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun x hx => hb x (List.mem_cons.mpr (Or.inr hx)))

-- Helper: x ∈ l → x ≤ (List.foldr max 0) l
theorem mem_le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ (List.foldr max 0) l := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp only [List.foldr_cons, List.foldr_nil]
    rcases List.mem_cons.mp h with rfl | ht
    · exact le_max_left x ((List.foldr max 0) tail)
    · exact le_trans (ih ht) (le_max_right head ((List.foldr max 0) tail))

-- Helper: x ∈ l → f x ≤ (List.foldr max 0) (l.map f)
theorem mem_le_foldr_max_map {α : Type*} {l : List α} {x : α} {f : α → Nat}
    (h : x ∈ l) : f x ≤ (List.foldr max 0) (l.map f) := by
  apply mem_le_foldr_max
  exact List.mem_map.mpr ⟨x, h, rfl⟩

end Circuits
