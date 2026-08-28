import Formulas.Eval
import Formulas.Properties
import Formulas.ConversionDepth
import Mathlib.Tactic.IntervalCases

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits
open UnboundedFanInFormula

/- The four probe inputs of length n (n ≥ 2): bits 0,1 set to b0,b1, rest zero. -/
def pt (n : Nat) (b0 b1 : Bool) : List Bool :=
  b0 :: b1 :: List.replicate (n - 2) false

theorem pt_length (n : Nat) (hn : 2 ≤ n) (b0 b1 : Bool) :
    (pt n b0 b1).length = n := by
  simp only [pt, List.length_cons, List.length_replicate]
  omega

/- eval helpers for the probe inputs. -/
theorem eval_input_zero (n : Nat) (b : Bool) (c0 c1 : Bool) :
    ufiFormulaEval (inputGate 0 b) (pt n c0 c1)
      = (match b with | true => not c0 | false => c0) := by
  cases b <;> simp [pt, ufiFormulaEval, not]

theorem eval_input_one (n : Nat) (b : Bool) (c0 c1 : Bool) :
    ufiFormulaEval (inputGate 1 b) (pt n c0 c1)
      = (match b with | true => not c1 | false => c1) := by
  cases b <;> simp [pt, ufiFormulaEval, not]

theorem eval_input_ge2 (n i : Nat) (hi : 2 ≤ i) (b : Bool) (c0 c1 : Bool) :
    ufiFormulaEval (inputGate i b) (pt n c0 c1)
      = if i < n then (match b with | true => true | false => false) else false := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  have hg : (pt n c0 c1)[(j + 2)]?
      = (List.replicate (n - 2) false)[j]? := rfl
  by_cases hin : j + 2 < n
  · have hj : j < n - 2 := by omega
    cases b <;> simp [ufiFormulaEval, hg, List.getElem?_replicate, hj, hin, not]
  · have hj : ¬j < n - 2 := by omega
    cases b <;> simp [ufiFormulaEval, hg, List.getElem?_replicate, hj, hin, not]

/- eval of andGate / orGate over the children list. -/
theorem eval_andGate_one_iff (gs : List UnboundedFanInFormula) (inp : List Bool) :
    ufiFormulaEval (andGate gs) inp = true ↔ ∀ g ∈ gs, ufiFormulaEval g inp = true := by
  induction gs with
  | nil => simp [ufiFormulaEval]
  | cons g0 rest ih =>
    simp only [ufiFormulaEval, List.mem_cons]
    cases hg0 : ufiFormulaEval g0 inp with
    | false =>
      constructor
      · intro h; simp at h
      · intro h; exact absurd (h g0 (Or.inl rfl)) (by rw [hg0]; simp)
    | true =>
      rw [ih]
      constructor
      · intro h g hg; rcases hg with rfl | hm
        · exact hg0
        · exact h g hm
      · intro h g hg; exact h g (Or.inr hg)

theorem eval_orGate_one_iff (gs : List UnboundedFanInFormula) (inp : List Bool) :
    ufiFormulaEval (orGate gs) inp = true ↔ ∃ g ∈ gs, ufiFormulaEval g inp = true := by
  induction gs with
  | nil => simp [ufiFormulaEval]
  | cons g0 rest ih =>
    simp only [ufiFormulaEval, List.mem_cons]
    cases hg0 : ufiFormulaEval g0 inp with
    | false =>
      rw [ih]
      constructor
      · intro h; obtain ⟨g, hg, hv⟩ := h; exact ⟨g, Or.inr hg, hv⟩
      · intro h; obtain ⟨g, hg, hv⟩ := h
        rcases hg with rfl | hm
        · exact absurd hv (by rw [hg0]; simp)
        · exact ⟨g, hm, hv⟩
    | true =>
      constructor
      · intro _; exact ⟨g0, Or.inl rfl, hg0⟩
      · intro _; rfl

theorem eval_not (g : UnboundedFanInFormula) (inp : List Bool) :
    ufiFormulaEval (notGate g) inp = not (ufiFormulaEval g inp) := by
  simp only [ufiFormulaEval]

/- Per-child invariants for depth-0 leaves (inputGate / constant). -/
theorem leaf_and_inv (n : Nat) (g : UnboundedFanInFormula)
    (h0 : ufiFormulaDepth g = 0)
    (h10 : ufiFormulaEval g (pt n true false) = true)
    (h01 : ufiFormulaEval g (pt n false true) = true) :
    ufiFormulaEval g (pt n false false) = true := by
  cases g with
  | inputGate i b =>
    rcases Nat.lt_or_ge i 2 with hlt | hge
    · interval_cases i
      · rw [eval_input_zero] at h10 h01 ⊢; cases b <;> simp [not] at *
      · rw [eval_input_one] at h10 h01 ⊢; cases b <;> simp [not] at *
    · rw [eval_input_ge2 n i hge] at h10 ⊢
      exact h10
  | constant c l => simp only [ufiFormulaEval] at h10 ⊢; exact h10
  | notGate h => simp [ufiFormulaDepth] at h0
  | andGate gs => simp only [ufiFormulaDepth] at h0; omega
  | orGate gs => simp only [ufiFormulaDepth] at h0; omega

theorem leaf_or (n : Nat) (g : UnboundedFanInFormula)
    (h0 : ufiFormulaDepth g = 0)
    (h10 : ufiFormulaEval g (pt n true false) = true) :
    ufiFormulaEval g (pt n false false) = true ∨ ufiFormulaEval g (pt n true true) = true := by
  cases g with
  | inputGate i b =>
    rcases Nat.lt_or_ge i 2 with hlt | hge
    · interval_cases i
      · rw [eval_input_zero] at h10
        right; rw [eval_input_zero]
        cases b with
        | true => simp [not] at h10
        | false => rfl
      · rw [eval_input_one] at h10
        left; rw [eval_input_one]
        cases b with
        | true => rfl
        | false => simp at h10
    · left; rw [eval_input_ge2 n i hge] at h10 ⊢
      exact h10
  | constant c l => left; simp only [ufiFormulaEval] at h10 ⊢; exact h10
  | notGate h => simp [ufiFormulaDepth] at h0
  | andGate gs => simp only [ufiFormulaDepth] at h0; omega
  | orGate gs => simp only [ufiFormulaDepth] at h0; omega

theorem notleaf_inv (n : Nat) (h : UnboundedFanInFormula)
    (hh0 : ufiFormulaDepth h = 0)
    (h10 : ufiFormulaEval (notGate h) (pt n true false) = true)
    (h01 : ufiFormulaEval (notGate h) (pt n false true) = true) :
    ufiFormulaEval (notGate h) (pt n false false) = true := by
  rw [eval_not] at h10 h01 ⊢
  cases h with
  | inputGate i b =>
    rcases Nat.lt_or_ge i 2 with hlt | hge
    · interval_cases i
      · rw [eval_input_zero] at h10 h01 ⊢; cases b <;> simp [not] at *
      · rw [eval_input_one] at h10 h01 ⊢; cases b <;> simp [not] at *
    · rw [eval_input_ge2 n i hge] at h10 ⊢
      exact h10
  | constant c l => simp only [ufiFormulaEval] at h10 ⊢; exact h10
  | notGate h2 => simp [ufiFormulaDepth] at hh0
  | andGate gs => simp only [ufiFormulaDepth] at hh0; omega
  | orGate gs => simp only [ufiFormulaDepth] at hh0; omega

/- The key invariant: a depth-≤1 formula cannot realise the XOR pattern on the
   two free coordinates. -/
theorem depth_one_xor_inv (n : Nat) (g : UnboundedFanInFormula)
    (hd : ufiFormulaDepth g ≤ 1)
    (h10 : ufiFormulaEval g (pt n true false) = true)
    (h01 : ufiFormulaEval g (pt n false true) = true) :
    ufiFormulaEval g (pt n false false) = true
      ∨ ufiFormulaEval g (pt n true true) = true := by
  cases g with
  | inputGate i b => exact Or.inl (leaf_and_inv n (inputGate i b) (by simp only [ufiFormulaDepth]) h10 h01)
  | constant c l => exact Or.inl (leaf_and_inv n (constant c l) (by simp only [ufiFormulaDepth]) h10 h01)
  | notGate h =>
    have hh0 : ufiFormulaDepth h = 0 := by
      simp only [ufiFormulaDepth] at hd; omega
    exact Or.inl (notleaf_inv n h hh0 h10 h01)
  | andGate gs =>
    have hchild : ∀ g0 ∈ gs, ufiFormulaDepth g0 = 0 := by
      intro g0 hg0
      have hle := mem_le_foldr_max_map (f := ufiFormulaDepth) hg0
      simp only [ufiFormulaDepth] at hd
      omega
    left
    rw [eval_andGate_one_iff] at h10 h01 ⊢
    intro g0 hg0
    exact leaf_and_inv n g0 (hchild g0 hg0) (h10 g0 hg0) (h01 g0 hg0)
  | orGate gs =>
    have hchild : ∀ g0 ∈ gs, ufiFormulaDepth g0 = 0 := by
      intro g0 hg0
      have hle := mem_le_foldr_max_map (f := ufiFormulaDepth) hg0
      simp only [ufiFormulaDepth] at hd
      omega
    rw [eval_orGate_one_iff] at h10
    obtain ⟨g0, hg0, hv⟩ := h10
    rcases leaf_or n g0 (hchild g0 hg0) hv with hl | hr
    · left; rw [eval_orGate_one_iff]; exact ⟨g0, hg0, hl⟩
    · right; rw [eval_orGate_one_iff]; exact ⟨g0, hg0, hr⟩

/- Parity (count of ones) of the probe inputs. -/
theorem countP_pt (n : Nat) (b0 b1 : Bool) :
    (pt n b0 b1).countP (· == true) = Bool.toNat b0 + Bool.toNat b1 := by
  have hrep : (List.replicate (n - 2) false).countP (· == true) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    rw [List.mem_replicate] at hx
    rw [hx.2]; decide
  cases b0 <;> cases b1 <;>
    simp only [pt, List.countP_cons, hrep, Bool.toNat] <;> decide

theorem bit_eq_one {x : Bool} (h : x ≠ false) : x = true := by
  cases x with
  | false => exact absurd rfl h
  | true => rfl

/- Main result: any depth-≤1 formula misclassifies parity on some length-n input
   (n ≥ 2). -/
theorem depth_one_misclassifies (n : Nat) (hn : 2 ≤ n) (g : UnboundedFanInFormula)
    (hd : ufiFormulaDepth g ≤ 1) :
    ∃ (inputs : List Bool), inputs.length = n ∧
      ((ufiFormulaEval g inputs == false ∧ Odd (inputs.countP (· == true)))
        ∨ (ufiFormulaEval g inputs == true ∧ ¬ Odd (inputs.countP (· == true)))) := by
  by_cases h10z : ufiFormulaEval g (pt n true false) = false
  · exact ⟨pt n true false, pt_length n hn _ _, Or.inl
      ⟨by rw [h10z]; rfl, by rw [countP_pt]; exact ⟨0, by decide⟩⟩⟩
  by_cases h01z : ufiFormulaEval g (pt n false true) = false
  · exact ⟨pt n false true, pt_length n hn _ _, Or.inl
      ⟨by rw [h01z]; rfl, by rw [countP_pt]; exact ⟨0, by decide⟩⟩⟩
  by_cases h00o : ufiFormulaEval g (pt n false false) = true
  · exact ⟨pt n false false, pt_length n hn _ _, Or.inr
      ⟨by rw [h00o]; rfl, by rw [countP_pt]; rintro ⟨m, hm⟩; simp [Bool.toNat] at hm⟩⟩
  by_cases h11o : ufiFormulaEval g (pt n true true) = true
  · exact ⟨pt n true true, pt_length n hn _ _, Or.inr
      ⟨by rw [h11o]; rfl, by rw [countP_pt]; rintro ⟨m, hm⟩; simp [Bool.toNat] at hm⟩⟩
  exfalso
  have v10 : ufiFormulaEval g (pt n true false) = true := bit_eq_one h10z
  have v01 : ufiFormulaEval g (pt n false true) = true := bit_eq_one h01z
  rcases depth_one_xor_inv n g hd v10 v01 with h | h
  · exact h00o h
  · exact h11o h

end Circuits
