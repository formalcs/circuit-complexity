import Formulas.CircuitFamilies
import Parity.ParityProperties

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits

open CnfDnf.Families

/-- XOR built from bounded-fan-in AND, OR, and NOT gates. -/
def xorBFI (left right : BoundedFanInFormula) : BoundedFanInFormula :=
  .orGate (.andGate left (.notGate right))
    (.andGate right (.notGate left))

theorem circuit_size_xorBFI (left right : BoundedFanInFormula) :
    bfiFormulaCircuitSize (xorBFI left right) =
      5 + 2 * bfiFormulaCircuitSize left +
        2 * bfiFormulaCircuitSize right := by
  simp [xorBFI, bfiFormulaCircuitSize]
  omega

theorem depth_xorBFI (left right : BoundedFanInFormula) :
    bfiFormulaDepth (xorBFI left right) =
      3 + max (bfiFormulaDepth left) (bfiFormulaDepth right) := by
  simp [xorBFI, bfiFormulaDepth]
  omega

/-- A balanced bounded-fan-in formula computing parity on the input interval
    `[start, start + length)`. -/
def parityCircuitRange : Nat → Nat → BoundedFanInFormula
  | _, 0 => .constant false 0
  | start, 1 => .inputGate start false
  | start, length + 2 =>
      let half := (length + 2) / 2
      xorBFI (parityCircuitRange start half)
        (parityCircuitRange (start + half) (length + 2 - half))

/-- A balanced bounded-fan-in formula computing parity on `n` inputs. -/
def parityCircuit (n : Nat) : BoundedFanInFormula :=
  parityCircuitRange 0 n

@[simp] theorem collect_xorBFI (left right : BoundedFanInFormula) :
    bfiCollectInputIndices (xorBFI left right) =
      (bfiCollectInputIndices left ++ bfiCollectInputIndices right) ++
        (bfiCollectInputIndices right ++ bfiCollectInputIndices left) := by
  simp [xorBFI, bfiCollectInputIndices, List.append_assoc]

theorem mem_collect_parityCircuitRange (start length index : Nat) :
    index ∈ bfiCollectInputIndices (parityCircuitRange start length) ↔
      start ≤ index ∧ index < start + length := by
  match length with
  | 0 =>
      simp [parityCircuitRange, bfiCollectInputIndices]
  | 1 =>
      simp [parityCircuitRange, bfiCollectInputIndices, List.mem_singleton]
      omega
  | length + 2 =>
      have h_sum :
          (length + 2) / 2 + ((length + 2) - (length + 2) / 2) =
            length + 2 :=
        Nat.add_sub_cancel' (Nat.div_le_self _ _)
      simp only [parityCircuitRange, collect_xorBFI, List.mem_append]
      have h_left :=
        mem_collect_parityCircuitRange start ((length + 2) / 2) index
      have h_right :=
        mem_collect_parityCircuitRange (start + (length + 2) / 2)
          ((length + 2) - (length + 2) / 2) index
      constructor
      · rintro ((h | h) | h | h)
        all_goals constructor
        · exact (h_left.mp h).1
        · have := (h_left.mp h).2
          omega
        · have := (h_right.mp h).1
          omega
        · have := (h_right.mp h).2
          omega
        · have := (h_right.mp h).1
          omega
        · have := (h_right.mp h).2
          omega
        · exact (h_left.mp h).1
        · have := (h_left.mp h).2
          omega
      · intro ⟨h_start, h_end⟩
        by_cases h_half : index < start + (length + 2) / 2
        · exact Or.inl (Or.inl (h_left.mpr ⟨h_start, h_half⟩))
        · have h_right_start : start + (length + 2) / 2 ≤ index := by
            omega
          have h_right_end :
              index < start + (length + 2) / 2 +
                ((length + 2) - (length + 2) / 2) := by
            omega
          exact Or.inl (Or.inr (h_right.mpr ⟨h_right_start, h_right_end⟩))
  termination_by length

theorem parityCircuit_input_indices_upper_bound (n : PNat) :
    bfiLargestInput (parityCircuit n) < n := by
  simp only [bfiLargestInput, parityCircuit]
  have h_bound :
      (bfiCollectInputIndices (parityCircuitRange 0 n.val)).foldr max 0 ≤
        n.val - 1 := by
    apply adder_foldr_max_le_of_all_le
    intro index h_index
    have h_mem :=
      (mem_collect_parityCircuitRange 0 n.val index).mp h_index
    omega
  exact lt_of_le_of_lt h_bound (Nat.sub_lt n.pos (by omega))

private lemma half_sum_sq_bound (m half remainder : Nat) (h_m : 2 ≤ m)
    (h_half : half = m / 2) (h_remainder : remainder = m - half) :
    10 * half ^ 2 + 10 * remainder ^ 2 + 7 ≤ 5 * m ^ 2 + 14 := by
  rcases Nat.even_or_odd m with ⟨k, h_k⟩ | ⟨k, h_k⟩
  · have h_half_value : half = k := by
      subst h_half
      subst h_k
      omega
    have h_remainder_value : remainder = k := by
      subst h_remainder
      subst h_half
      subst h_k
      omega
    nlinarith [sq_nonneg k]
  · have h_half_value : half = k := by
      subst h_half
      subst h_k
      omega
    have h_remainder_value : remainder = k + 1 := by
      subst h_remainder
      subst h_half
      subst h_k
      omega
    nlinarith [sq_nonneg k]

theorem circuit_size_parityCircuitRange_bound (start length : Nat)
    (h_length : 1 ≤ length) :
    bfiFormulaCircuitSize (parityCircuitRange start length) + 4 ≤
      5 * length ^ 2 := by
  match length, h_length with
  | 1, _ =>
      simp [parityCircuitRange, bfiFormulaCircuitSize]
  | length + 2, _ =>
      simp only [parityCircuitRange]
      rw [circuit_size_xorBFI]
      let half := (length + 2) / 2
      let remainder := (length + 2) - half
      have h_half_pos : 1 ≤ half := by omega
      have h_remainder_pos : 1 ≤ remainder := by omega
      have h_left :=
        circuit_size_parityCircuitRange_bound start half h_half_pos
      have h_right :=
        circuit_size_parityCircuitRange_bound (start + half) remainder
          h_remainder_pos
      have h_square :=
        half_sum_sq_bound (length + 2) half remainder (by omega) rfl rfl
      nlinarith
  termination_by length

theorem parityCircuit_output_has_quadratic_upper_bound (n : Nat)
    (h_n : 1 ≤ n) :
    bfiFormulaCircuitSize (parityCircuit n) ≤ 5 * n ^ 2 := by
  have h_bound := circuit_size_parityCircuitRange_bound 0 n h_n
  simp only [parityCircuit]
  omega

theorem depth_parityCircuitRange_bound (start length : Nat) :
    bfiFormulaDepth (parityCircuitRange start length) ≤
      3 * Nat.clog 2 length := by
  match length with
  | 0 =>
      simp [parityCircuitRange, bfiFormulaDepth]
  | 1 =>
      simp [parityCircuitRange, bfiFormulaDepth, Nat.clog]
  | length + 2 =>
      simp only [parityCircuitRange]
      rw [depth_xorBFI]
      let half := (length + 2) / 2
      let remainder := (length + 2) - half
      have h_left := depth_parityCircuitRange_bound start half
      have h_right :=
        depth_parityCircuitRange_bound (start + half) remainder
      let ceiling := (length + 2 + 2 - 1) / 2
      have h_clog :
          Nat.clog 2 (length + 2) = Nat.clog 2 ceiling + 1 :=
        Nat.clog_of_two_le (by omega) (by omega)
      have h_half_le : half ≤ ceiling := by omega
      have h_remainder_le : remainder ≤ ceiling := by omega
      have h_clog_half : Nat.clog 2 half ≤ Nat.clog 2 ceiling :=
        Nat.clog_monotone 2 h_half_le
      have h_clog_remainder : Nat.clog 2 remainder ≤ Nat.clog 2 ceiling :=
        Nat.clog_monotone 2 h_remainder_le
      calc
        3 + max (bfiFormulaDepth (parityCircuitRange start half))
              (bfiFormulaDepth
                (parityCircuitRange (start + half) remainder))
            ≤ 3 + max (3 * Nat.clog 2 half)
                (3 * Nat.clog 2 remainder) := by omega
        _ ≤ 3 + 3 * Nat.clog 2 ceiling := by omega
        _ = 3 * (Nat.clog 2 ceiling + 1) := by ring
        _ = 3 * Nat.clog 2 (length + 2) := by rw [h_clog]
  termination_by length

theorem parityCircuit_output_has_logarithmic_depth_upper_bound (n : Nat) :
    bfiFormulaDepth (parityCircuit n) ≤
      Nat.clog 2 (5 * n ^ 2) * 3 := by
  have h_bound := depth_parityCircuitRange_bound 0 n
  simp only [parityCircuit]
  calc
    bfiFormulaDepth (parityCircuitRange 0 n) ≤ 3 * Nat.clog 2 n := h_bound
    _ ≤ 3 * Nat.clog 2 (5 * n ^ 2) := by
      apply Nat.mul_le_mul_left
      apply Nat.clog_monotone
      cases n with
      | zero => simp
      | succ predecessor => nlinarith
    _ = Nat.clog 2 (5 * n ^ 2) * 3 := by ring

/-- The polynomial-size, logarithmic-depth family of balanced parity
    formulas. -/
def parityNC1FormulaFamily : NC1FormulaFamily 5 2 3 :=
  fun n =>
    ⟨parityCircuit n.val, by
      constructor
      · exact parityCircuit_input_indices_upper_bound n
      · constructor
        · exact parityCircuit_output_has_logarithmic_depth_upper_bound n
        · exact parityCircuit_output_has_quadratic_upper_bound n n.pos⟩

private theorem even_iff_not_odd {n : Nat} : Even n ↔ ¬Odd n :=
  ⟨fun h_even h_odd => (Nat.not_even_iff_odd.mpr h_odd) h_even,
    fun h_not_odd =>
      (Nat.even_or_odd n).elim id (fun h_odd => absurd h_odd h_not_odd)⟩

private theorem eval_input_eq_getD (index : Nat) (inputs : List Bool) :
    bfiFormulaEval (.inputGate index false) inputs =
      inputs.getD index false := by
  simp [bfiFormulaEval, List.getD]
  cases inputs[index]? <;> rfl

private theorem eval_xorBFI_eq_true (left right : BoundedFanInFormula)
    (inputs : List Bool) :
    bfiFormulaEval (xorBFI left right) inputs = true ↔
      bfiFormulaEval left inputs ≠ bfiFormulaEval right inputs := by
  unfold xorBFI
  cases h_left : bfiFormulaEval left inputs <;>
    cases h_right : bfiFormulaEval right inputs <;>
    simp [bfiFormulaEval, h_left, h_right]

private theorem countP_range'_cons_shift (head : Bool) (tail : List Bool)
    (start length : Nat) :
    (List.range' (start + 1) length).countP
        (fun i => (head :: tail).getD i false == true) =
      (List.range' start length).countP
        (fun i => tail.getD i false == true) := by
  induction length generalizing start with
  | zero => simp
  | succ length ih =>
      have h_left :
          List.range' (start + 1) (length + 1) =
            (start + 1) :: List.range' (start + 2) length := rfl
      have h_right :
          List.range' start (length + 1) =
            start :: List.range' (start + 1) length := rfl
      rw [h_left, h_right]
      simp only [List.countP_cons, List.getD_cons_succ]
      congr 1
      exact ih (start + 1)

private theorem countP_range'_getD_eq_countP (inputs : List Bool) :
    (List.range' 0 inputs.length).countP
        (fun i => inputs.getD i false == true) =
      inputs.countP (· == true) := by
  induction inputs with
  | nil => simp
  | cons head tail ih =>
      have h_range :
          List.range' 0 (tail.length + 1) =
            0 :: List.range' 1 tail.length := rfl
      rw [List.length_cons, h_range]
      simp only [List.countP_cons, List.getD_cons_zero]
      congr 1
      rw [countP_range'_cons_shift]
      exact ih

theorem eval_parityCircuitRange_eq_true_iff (start length : Nat)
    (inputs : List Bool) :
    bfiFormulaEval (parityCircuitRange start length) inputs = true ↔
      Odd ((List.range' start length).countP
        (fun i => inputs.getD i false == true)) := by
  match length with
  | 0 =>
      simp only [parityCircuitRange, bfiFormulaEval,
        show List.range' start 0 = [] from rfl, List.countP_nil]
      exact ⟨fun h => Bool.noConfusion h,
        fun ⟨multiplier, h_multiplier⟩ => by
          exfalso
          omega⟩
  | 1 =>
      simp only [parityCircuitRange]
      rw [eval_input_eq_getD]
      simp only [show List.range' start 1 = [start] from rfl,
        List.countP_cons, List.countP_nil]
      cases inputs.getD start false <;> simp [Nat.odd_iff]
  | length + 2 =>
      simp only [parityCircuitRange]
      rw [eval_xorBFI_eq_true]
      let half := (length + 2) / 2
      let remainder := (length + 2) - half
      have h_left := eval_parityCircuitRange_eq_true_iff start half inputs
      have h_right :=
        eval_parityCircuitRange_eq_true_iff (start + half) remainder inputs
      have h_range :
          List.range' start (length + 2) =
            List.range' start half ++
              List.range' (start + half) remainder := by
        have h_sum : half + remainder = length + 2 := by omega
        rw [← h_sum, ← List.range'_append]
        simp
      rw [h_range, List.countP_append, Nat.odd_add]
      simp only [even_iff_not_odd]
      rw [← h_left, ← h_right]
      cases bfiFormulaEval (parityCircuitRange start half) inputs <;>
        cases bfiFormulaEval
          (parityCircuitRange (start + half) remainder) inputs <;>
        simp
  termination_by length

/-- `parityCircuit n` computes parity on every list of exactly `n` bits. -/
theorem parityCircuit_is_correct (n : Nat) :
    BFIFormulaComputesParity n (parityCircuit n) := by
  intro inputs h_length
  apply Bool.eq_iff_iff.mpr
  rw [parityCircuit, eval_parityCircuitRange_eq_true_iff,
    ← h_length, countP_range'_getD_eq_countP,
    odd_countP_iff_parityBit]

end Circuits
