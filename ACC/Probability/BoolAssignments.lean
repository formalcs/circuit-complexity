import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Circuits.ACC

/-! ## Counting Boolean mask assignments

This module contains finite counting lemmas used by the probabilistic
OR-elimination gadget.  They are independent of formula syntax: a fixed
nonzero Boolean vector is masked by a uniformly chosen Boolean vector, and
we count masks whose selected coordinates sum to zero modulo `p`.
-/

namespace BoolAssignments

/-- Split a Boolean assignment on `Fin (left + right)` into its consecutive
left and right blocks, with inverse given by `Fin.append`. -/
def appendEquiv (left right : Nat) :
    ((Fin left → Bool) × (Fin right → Bool)) ≃
      (Fin (left + right) → Bool) where
  toFun assignments := Fin.append assignments.1 assignments.2
  invFun assignment :=
    (fun i => assignment (Fin.castAdd right i),
      fun i => assignment (Fin.natAdd left i))
  left_inv assignments := by
    apply Prod.ext <;> funext i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  right_inv assignment := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.append_left]
    · intro j
      simp [Fin.append_right]

/-- A fiberwise counting bound for consecutive Boolean-assignment blocks.
If every fixed left block admits at most `bound` right blocks satisfying
`property`, then at most `2^left * bound` complete assignments satisfy it. -/
theorem card_filter_append_le (left right bound : Nat)
    (property : (Fin (left + right) → Bool) → Prop)
    [DecidablePred property]
    (h_fiber : ∀ leftAssignment : Fin left → Bool,
      ((Finset.univ : Finset (Fin right → Bool)).filter fun rightAssignment =>
        property (Fin.append leftAssignment rightAssignment)).card ≤ bound) :
    ((Finset.univ : Finset (Fin (left + right) → Bool)).filter property).card ≤
      2 ^ left * bound := by
  classical
  let splitSubtype :
      {assignment : Fin (left + right) → Bool // property assignment} ≃
        {assignments : (Fin left → Bool) × (Fin right → Bool) //
          property (Fin.append assignments.1 assignments.2)} :=
    (appendEquiv left right).symm.subtypeEquiv (by
      intro assignment
      have h_eq := (appendEquiv left right).apply_symm_apply assignment
      change
        Fin.append (fun i => assignment (Fin.castAdd right i))
          (fun i => assignment (Fin.natAdd left i)) = assignment at h_eq
      change property assignment ↔
        property (Fin.append (fun i => assignment (Fin.castAdd right i))
          (fun i => assignment (Fin.natAdd left i)))
      rw [h_eq])
  let fiberSubtype :
      {assignments : (Fin left → Bool) × (Fin right → Bool) //
        property (Fin.append assignments.1 assignments.2)} ≃
        Σ leftAssignment : Fin left → Bool,
          {rightAssignment : Fin right → Bool //
            property (Fin.append leftAssignment rightAssignment)} :=
    Equiv.subtypeProdEquivSigmaSubtype fun leftAssignment rightAssignment =>
      property (Fin.append leftAssignment rightAssignment)
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (splitSubtype.trans fiberSubtype)]
  rw [Fintype.card_sigma]
  calc
    (∑ leftAssignment : Fin left → Bool,
        Fintype.card {rightAssignment : Fin right → Bool //
          property (Fin.append leftAssignment rightAssignment)}) ≤
        ∑ _leftAssignment : Fin left → Bool, bound := by
      apply Finset.sum_le_sum
      intro leftAssignment _
      rw [Fintype.card_subtype]
      exact h_fiber leftAssignment
    _ = 2 ^ left * bound := by simp

/-- Refined block-counting bound.  Only left assignments satisfying
`leftProperty` may have a nonempty fiber, and every such fiber has size at
most `bound`. -/
theorem card_filter_append_le_of_left (left right bound : Nat)
    (leftProperty : (Fin left → Bool) → Prop)
    (property : (Fin (left + right) → Bool) → Prop)
    [DecidablePred leftProperty] [DecidablePred property]
    (h_fiber : ∀ leftAssignment : Fin left → Bool,
      ((Finset.univ : Finset (Fin right → Bool)).filter fun rightAssignment =>
        property (Fin.append leftAssignment rightAssignment)).card ≤
          if leftProperty leftAssignment then bound else 0) :
    ((Finset.univ : Finset (Fin (left + right) → Bool)).filter property).card ≤
      ((Finset.univ : Finset (Fin left → Bool)).filter leftProperty).card *
        bound := by
  classical
  let splitSubtype :
      {assignment : Fin (left + right) → Bool // property assignment} ≃
        {assignments : (Fin left → Bool) × (Fin right → Bool) //
          property (Fin.append assignments.1 assignments.2)} :=
    (appendEquiv left right).symm.subtypeEquiv (by
      intro assignment
      have h_eq := (appendEquiv left right).apply_symm_apply assignment
      change
        Fin.append (fun i => assignment (Fin.castAdd right i))
          (fun i => assignment (Fin.natAdd left i)) = assignment at h_eq
      change property assignment ↔
        property (Fin.append (fun i => assignment (Fin.castAdd right i))
          (fun i => assignment (Fin.natAdd left i)))
      rw [h_eq])
  let fiberSubtype :
      {assignments : (Fin left → Bool) × (Fin right → Bool) //
        property (Fin.append assignments.1 assignments.2)} ≃
        Σ leftAssignment : Fin left → Bool,
          {rightAssignment : Fin right → Bool //
            property (Fin.append leftAssignment rightAssignment)} :=
    Equiv.subtypeProdEquivSigmaSubtype fun leftAssignment rightAssignment =>
      property (Fin.append leftAssignment rightAssignment)
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (splitSubtype.trans fiberSubtype)]
  rw [Fintype.card_sigma]
  calc
    (∑ leftAssignment : Fin left → Bool,
        Fintype.card {rightAssignment : Fin right → Bool //
          property (Fin.append leftAssignment rightAssignment)}) ≤
        ∑ leftAssignment : Fin left → Bool,
          if leftProperty leftAssignment then bound else 0 := by
      apply Finset.sum_le_sum
      intro leftAssignment _
      rw [Fintype.card_subtype]
      exact h_fiber leftAssignment
    _ = ((Finset.univ : Finset (Fin left → Bool)).filter leftProperty).card *
          bound := by
      rw [Finset.sum_ite]
      simp

/-- Count an event by separating an exceptional set of left blocks from a
uniformly bounded right-block event.  This is the finite union-bound form
used to compose errors of sequential randomized transformations. -/
theorem card_filter_append_le_with_left_exceptions
    (left right rightBound : Nat)
    (leftException : (Fin left → Bool) → Prop)
    (property : (Fin (left + right) → Bool) → Prop)
    [DecidablePred leftException] [DecidablePred property]
    (h_fiber : ∀ leftAssignment : Fin left → Bool,
      ¬leftException leftAssignment →
        ((Finset.univ : Finset (Fin right → Bool)).filter
          fun rightAssignment =>
            property (Fin.append leftAssignment rightAssignment)).card ≤
          rightBound) :
    ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
        property).card ≤
      ((Finset.univ : Finset (Fin left → Bool)).filter
          leftException).card * 2 ^ right + 2 ^ left * rightBound := by
  classical
  let residual : (Fin (left + right) → Bool) → Prop := fun assignment =>
    property assignment ∧
      ¬leftException (fun i => assignment (Fin.castAdd right i))
  have h_union :
      ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
          property).card ≤
        ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
            fun assignment =>
              leftException (fun i => assignment (Fin.castAdd right i))).card +
          ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
            residual).card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro assignment h_assignment
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_assignment
    by_cases h_left :
        leftException (fun i => assignment (Fin.castAdd right i))
    · exact Or.inl h_left
    · exact Or.inr ⟨h_assignment, h_left⟩
  have h_exception :
      ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
          fun assignment =>
            leftException (fun i => assignment (Fin.castAdd right i))).card ≤
        ((Finset.univ : Finset (Fin left → Bool)).filter
            leftException).card * 2 ^ right := by
    apply card_filter_append_le_of_left left right (2 ^ right)
      leftException _
    intro leftAssignment
    by_cases h_left : leftException leftAssignment
    · simp [h_left]
    · simp [h_left]
  have h_residual :
      ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
          residual).card ≤ 2 ^ left * rightBound := by
    apply card_filter_append_le left right rightBound residual
    intro leftAssignment
    by_cases h_left : leftException leftAssignment
    · have h_empty :
          (Finset.univ.filter fun rightAssignment : Fin right → Bool =>
            residual (Fin.append leftAssignment rightAssignment)) = ∅ := by
          ext rightAssignment
          simp [residual, h_left, Fin.append_left]
      rw [h_empty]
      simp
    · refine (Finset.card_le_card ?_).trans (h_fiber leftAssignment h_left)
      intro rightAssignment h_right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, residual]
        at h_right ⊢
      exact h_right.1
  exact le_trans h_union (Nat.add_le_add h_exception h_residual)

/-- Scaled form of sequential error composition.  Exceptional left blocks
permit every right block; on every nonexceptional left block the right fiber
is bounded after multiplication by `scale`. -/
theorem card_filter_append_mul_le_with_left_exceptions
    (left right scale rightNumerator : Nat)
    (leftException : (Fin left → Bool) → Prop)
    (property : (Fin (left + right) → Bool) → Prop)
    [DecidablePred leftException] [DecidablePred property]
    (h_fiber : ∀ leftAssignment : Fin left → Bool,
      ¬leftException leftAssignment →
        ((Finset.univ : Finset (Fin right → Bool)).filter
          fun rightAssignment =>
            property (Fin.append leftAssignment rightAssignment)).card *
              scale ≤ rightNumerator) :
    ((Finset.univ : Finset (Fin (left + right) → Bool)).filter
        property).card * scale ≤
      ((Finset.univ : Finset (Fin left → Bool)).filter
          leftException).card * 2 ^ right * scale +
        2 ^ left * rightNumerator := by
  classical
  let splitSubtype :
      {assignment : Fin (left + right) → Bool // property assignment} ≃
        Σ leftAssignment : Fin left → Bool,
          {rightAssignment : Fin right → Bool //
            property (Fin.append leftAssignment rightAssignment)} :=
    ((appendEquiv left right).symm.subtypeEquiv (by
      intro assignment
      have h_eq := (appendEquiv left right).apply_symm_apply assignment
      change
        Fin.append (fun i => assignment (Fin.castAdd right i))
          (fun i => assignment (Fin.natAdd left i)) = assignment at h_eq
      change property assignment ↔
        property (Fin.append (fun i => assignment (Fin.castAdd right i))
          (fun i => assignment (Fin.natAdd left i)))
      rw [h_eq])).trans
        (Equiv.subtypeProdEquivSigmaSubtype fun leftAssignment rightAssignment =>
          property (Fin.append leftAssignment rightAssignment))
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr splitSubtype, Fintype.card_sigma]
  rw [Finset.sum_mul]
  calc
    (∑ leftAssignment : Fin left → Bool,
        Fintype.card {rightAssignment : Fin right → Bool //
          property (Fin.append leftAssignment rightAssignment)} * scale) ≤
        ∑ leftAssignment : Fin left → Bool,
          if leftException leftAssignment then 2 ^ right * scale
          else rightNumerator := by
      apply Finset.sum_le_sum
      intro leftAssignment _
      by_cases h_left : leftException leftAssignment
      · simp only [h_left, if_true]
        rw [Fintype.card_subtype]
        exact Nat.mul_le_mul_right scale (by
          simpa [Fintype.card_fun] using
            Finset.card_le_univ
              (Finset.univ.filter fun rightAssignment : Fin right → Bool =>
                property (Fin.append leftAssignment rightAssignment)))
      · simp only [h_left, if_false]
        rw [Fintype.card_subtype]
        exact h_fiber leftAssignment h_left
    _ ≤
        ((Finset.univ : Finset (Fin left → Bool)).filter
            leftException).card * (2 ^ right * scale) +
          2 ^ left * rightNumerator := by
      calc
        (∑ leftAssignment : Fin left → Bool,
            if leftException leftAssignment then 2 ^ right * scale
            else rightNumerator) ≤
            ∑ leftAssignment : Fin left → Bool,
              ((if leftException leftAssignment then 2 ^ right * scale
              else 0) + rightNumerator) := by
            apply Finset.sum_le_sum
            intro leftAssignment _
            by_cases h_left : leftException leftAssignment <;> simp [h_left]
        _ = ((Finset.univ : Finset (Fin left → Bool)).filter
              leftException).card * (2 ^ right * scale) +
              2 ^ left * rightNumerator := by
            rw [Finset.sum_add_distrib, Finset.sum_ite]
            simp
    _ = _ := by ac_rfl

/-- Flip one coordinate of a Boolean assignment. -/
def toggle {m : Nat} (i : Fin m) (assignment : Fin m → Bool) : Fin m → Bool :=
  Function.update assignment i (!assignment i)

/-- Toggling the same coordinate twice returns the original assignment. -/
@[simp]
theorem toggle_toggle {m : Nat} (i : Fin m) (assignment : Fin m → Bool) :
    toggle i (toggle i assignment) = assignment := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [toggle]
  · simp [toggle, hji]

/-- Toggling a fixed coordinate is injective. -/
theorem toggle_injective {m : Nat} (i : Fin m) :
    Function.Injective (toggle i) := by
  intro left right h
  have h' := congrArg (toggle i) h
  simpa using h'

/-- Sum of the coordinates selected by `mask`, interpreted in `ZMod p`. -/
def maskedSum (p : Nat) {m : Nat} (values mask : Fin m → Bool) : ZMod p :=
  ∑ i, ((mask i && values i).toNat : ZMod p)

/-- List presentation of `maskedSum` for two finite vectors. -/
theorem maskedSum_eq_zipWith_ofFn {p m : Nat} (values mask : Fin m → Bool) :
    maskedSum p values mask =
      (((List.ofFn mask).zipWith (· && ·) (List.ofFn values)).map fun value =>
        (value.toNat : ZMod p)).sum := by
  unfold maskedSum
  rw [← List.sum_ofFn]
  congr 1
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact ih (fun i => values i.succ) (fun i => mask i.succ)

/-- List-valued corollary of `maskedSum_eq_zipWith_ofFn`. -/
theorem maskedSum_get_eq_zipWith {p : Nat} (values : List Bool)
    (mask : Fin values.length → Bool) :
    maskedSum p values.get mask =
      (((List.ofFn mask).zipWith (· && ·) values).map fun value =>
        (value.toNat : ZMod p)).sum := by
  simpa using maskedSum_eq_zipWith_ofFn (p := p) values.get mask

/-- Natural-number modular-test presentation of `maskedSum = 0`. -/
theorem zipWith_sum_mod_eq_zero_iff {p : Nat} (values : List Bool)
    (mask : Fin values.length → Bool) :
    (((List.ofFn mask).zipWith (· && ·) values).map Bool.toNat).sum % p = 0 ↔
      maskedSum p values.get mask = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
  rw [maskedSum_get_eq_zipWith]
  rw [Nat.cast_list_sum]
  simp only [List.map_map]
  rfl

/-- Finite-vector version of `zipWith_sum_mod_eq_zero_iff`. -/
theorem zipWith_ofFn_sum_mod_eq_zero_iff {p m : Nat}
    (values mask : Fin m → Bool) :
    (((List.ofFn mask).zipWith (· && ·) (List.ofFn values)).map
      Bool.toNat).sum % p = 0 ↔ maskedSum p values mask = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
  rw [maskedSum_eq_zipWith_ofFn]
  rw [Nat.cast_list_sum]
  simp only [List.map_map]
  rfl

/-- Flipping a coordinate whose fixed value is true changes `maskedSum` by
`1`; the sign is determined by the old mask bit. -/
theorem maskedSum_toggle {p m : Nat} (values mask : Fin m → Bool)
    (i : Fin m) (h_value : values i = true) :
    maskedSum p values (toggle i mask) =
      if mask i then maskedSum p values mask - 1
      else maskedSum p values mask + 1 := by
  unfold maskedSum
  rw [← Finset.univ.sum_erase_add _ (Finset.mem_univ i)]
  rw [← Finset.univ.sum_erase_add _ (Finset.mem_univ i)]
  have h_away :
      (∑ x ∈ Finset.univ.erase i,
          (((toggle i mask) x && values x).toNat : ZMod p)) =
        ∑ x ∈ Finset.univ.erase i,
          ((mask x && values x).toNat : ZMod p) := by
    apply Finset.sum_congr rfl
    intro j h_j
    have hji : j ≠ i := by
      exact (Finset.mem_erase.mp h_j).1
    simp [toggle, hji]
  rw [h_away]
  cases h_mask : mask i <;> simp [toggle, h_mask, h_value]

/-- If `p > 1`, toggling an active coordinate sends an accepting mask to a
non-accepting mask. -/
theorem maskedSum_toggle_ne_zero {p m : Nat} (hp : 1 < p)
    (values mask : Fin m → Bool) (i : Fin m) (h_value : values i = true)
    (h_zero : maskedSum p values mask = 0) :
    maskedSum p values (toggle i mask) ≠ 0 := by
  have : Nontrivial (ZMod p) :=
    ZMod.nontrivial_iff.mpr (Nat.ne_of_gt hp)
  rw [maskedSum_toggle values mask i h_value, h_zero]
  cases mask i <;> simp

/-- The finite set of masks whose selected coordinates sum to zero modulo
`p`. -/
def acceptingMasks (p : Nat) {m : Nat}
    (values : Fin m → Bool) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun mask => maskedSum p values mask = 0

/-- If a Boolean vector of length `n + 1` has a true coordinate, at most
`2^n` masks make its selected-coordinate sum zero modulo `p`.

The proof restricts an accepting mask away from a fixed true coordinate.
That restriction is injective on accepting masks: two distinct extensions
would differ only at the fixed coordinate, hence would be related by
`toggle`, but toggling an active coordinate cannot preserve acceptance. -/
theorem acceptingMasks_card_le_half {p n : Nat} (hp : 1 < p)
    (values : Fin (n + 1) → Bool) (i : Fin (n + 1))
    (h_value : values i = true) :
    (acceptingMasks p values).card ≤ 2 ^ n := by
  let restrict : (Fin (n + 1) → Bool) → (Fin n → Bool) := fun mask j =>
    mask (i.succAbove j)
  have h_card :
      (acceptingMasks p values).card ≤
        (Finset.univ : Finset (Fin n → Bool)).card := by
    apply Finset.card_le_card_of_injOn restrict
    · intro mask h_mask
      exact Finset.mem_univ _
    · intro left h_left right h_right h_restrict
      have h_left_zero : maskedSum p values left = 0 := by
        simpa [acceptingMasks] using h_left
      have h_right_zero : maskedSum p values right = 0 := by
        simpa [acceptingMasks] using h_right
      have h_at : left i = right i := by
        by_contra h_ne
        have h_right_toggle : right = toggle i left := by
          apply funext
          rw [Fin.forall_iff_succAbove i]
          constructor
          · simp only [toggle]
            cases h_left_i : left i <;> cases h_right_i : right i <;>
              simp_all
          · intro k
            have h_k := congrFun h_restrict k
            simpa [restrict, toggle, Fin.succAbove_ne] using h_k.symm
        have h_toggle_ne := maskedSum_toggle_ne_zero hp values left i h_value
          h_left_zero
        exact h_toggle_ne (by simpa [← h_right_toggle] using h_right_zero)
      apply funext
      rw [Fin.forall_iff_succAbove i]
      constructor
      · exact h_at
      · intro j
        exact congrFun h_restrict j
  simpa [Fintype.card_fun] using h_card

/-- Coordinate-free form of `acceptingMasks_card_le_half`: for every
nonzero Boolean vector, twice the number of accepting masks is at most the
total number `2^m` of masks. -/
theorem acceptingMasks_card_mul_two_le {p m : Nat} (hp : 1 < p)
    (values : Fin m → Bool) (h_nonzero : ∃ i, values i = true) :
    (acceptingMasks p values).card * 2 ≤ 2 ^ m := by
  obtain ⟨i, h_value⟩ := h_nonzero
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
      have h_half := acceptingMasks_card_le_half hp values i h_value
      calc
        (acceptingMasks p values).card * 2 ≤ 2 ^ n * 2 :=
          Nat.mul_le_mul_right 2 h_half
        _ = 2 ^ (n + 1) := by rw [pow_succ]

end BoolAssignments

end Circuits.ACC
