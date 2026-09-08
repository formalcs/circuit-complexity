import ACC.Formula.Probabilistic.OrElimination.Correctness

namespace Circuits.ACC.ACCFormula

open ProbabilisticACCFormula

/-! ## Resource bounds for OR-gate elimination -/

/-- Every ACC formula has at least one syntax-tree node. -/
theorem nodeCount_pos {p : Nat} (formula : ACCFormula p) :
    0 < formula.nodeCount := by
  cases formula <;> simp [ACCFormula.nodeCount]

/-- Removing one root from every formula in a list and then restoring the
number of roots recovers the total node count. -/
theorem sum_nodeCount_sub_one_add_length {p : Nat}
    (formulas : List (ACCFormula p)) :
    (formulas.map fun formula => formula.nodeCount - 1).sum + formulas.length =
      (formulas.map ACCFormula.nodeCount).sum := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h_pos := nodeCount_pos formula
      omega

/-- The number of formula roots in a list is at most its total syntax-tree
node count. -/
theorem length_le_sum_nodeCount {p : Nat} (formulas : List (ACCFormula p)) :
    formulas.length ≤ (formulas.map ACCFormula.nodeCount).sum := by
  induction formulas with
  | nil => simp
  | cons formula formulas ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h_pos := nodeCount_pos formula
      omega

private theorem max?_getD_cons (value : Nat) (values : List Nat) :
    (value :: values).max?.getD 0 = max value (values.max?.getD 0) := by
  cases values with
  | nil => simp
  | cons head tail => simp [List.max?_cons]

mutual

/-- A depth-sensitive syntax bound for OR elimination.  Each source gate
level costs at most a factor `3 * (repetitions + 1)`; in particular, constant
source depth turns the logarithmic repetition count into only a polynomial
syntax-size overhead. -/
theorem eliminateOrGatesAux_nodeCount_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) (nextRandom : Nat) :
    ProbabilisticACCFormula.nodeCount
        (eliminateOrGatesAux repetitions formula nextRandom).1 ≤
      (3 * (repetitions + 1)) ^ formula.depth * formula.nodeCount := by
  let scale := 3 * (repetitions + 1)
  have h_scale : 3 ≤ scale := by
    simp [scale]
  match formula with
  | .input idx negated => simp [eliminateOrGatesAux, ACCFormula.depth,
      ACCFormula.nodeCount, ProbabilisticACCFormula.nodeCount]
  | .constant value label => simp [eliminateOrGatesAux, ACCFormula.depth,
      ACCFormula.nodeCount, ProbabilisticACCFormula.nodeCount]
  | .notGate child =>
      rcases h_child : eliminateOrGatesAux repetitions child nextRandom with
        ⟨transformed, finalRandom⟩
      have h_bound : transformed.nodeCount ≤
          scale ^ child.depth * child.nodeCount := by
        simpa [scale, h_child] using
          eliminateOrGatesAux_nodeCount_le repetitions child nextRandom
      simp only [eliminateOrGatesAux, h_child,
        ProbabilisticACCFormula.nodeCount, ACCFormula.depth,
        ACCFormula.nodeCount, pow_succ]
      calc
        transformed.nodeCount + 1 ≤
            scale ^ child.depth * child.nodeCount + 1 :=
          Nat.add_le_add_right h_bound 1
        _ ≤ scale ^ child.depth * child.nodeCount +
              scale ^ child.depth :=
          Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
        _ = scale ^ child.depth * (child.nodeCount + 1) := by ring
        _ ≤ scale ^ child.depth * scale * (child.nodeCount + 1) := by
          have h_pow_scale : scale ^ child.depth ≤
              scale ^ child.depth * scale := by
            calc
              scale ^ child.depth = scale ^ child.depth * 1 := by omega
              _ ≤ scale ^ child.depth * scale := by gcongr; omega
          exact Nat.mul_le_mul_right (child.nodeCount + 1)
            h_pow_scale
        _ = (3 * (repetitions + 1)) ^ (child.depth + 1) *
              (child.nodeCount + 1) := by
          rw [pow_succ]
  | .andGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children nextRandom with
        ⟨transformed, finalRandom⟩
      have h_bound :
          (transformed.map ProbabilisticACCFormula.nodeCount).sum ≤
            scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum := by
        simpa [scale, h_children] using
          eliminateOrGatesListAux_nodeCount_le repetitions children nextRandom
      simp only [eliminateOrGatesAux, h_children,
        ProbabilisticACCFormula.nodeCount, ACCFormula.depth,
        ACCFormula.nodeCount]
      calc
        (transformed.map ProbabilisticACCFormula.nodeCount).sum + 1 ≤
            scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum + 1 :=
          Nat.add_le_add_right h_bound 1
        _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum +
              scale ^ (children.map ACCFormula.depth).max?.getD 0 :=
          Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
        _ = scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (1 + (children.map ACCFormula.nodeCount).sum) := by ring
        _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale *
              (1 + (children.map ACCFormula.nodeCount).sum) := by
          have h_pow_scale :
              scale ^ (children.map ACCFormula.depth).max?.getD 0 ≤
                scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale := by
            calc
              scale ^ (children.map ACCFormula.depth).max?.getD 0 =
                  scale ^ (children.map ACCFormula.depth).max?.getD 0 * 1 := by omega
              _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale := by
                gcongr
                omega
          exact Nat.mul_le_mul_right
            (1 + (children.map ACCFormula.nodeCount).sum)
            h_pow_scale
        _ = (3 * (repetitions + 1)) ^
              (1 + (children.map ACCFormula.depth).max?.getD 0) *
                (1 + (children.map ACCFormula.nodeCount).sum) := by
          rw [show 1 + (children.map ACCFormula.depth).max?.getD 0 =
            (children.map ACCFormula.depth).max?.getD 0 + 1 by omega, pow_succ]
  | .orGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children nextRandom with
        ⟨transformed, afterChildren⟩
      have h_bound :
          (transformed.map ProbabilisticACCFormula.nodeCount).sum ≤
            scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum := by
        simpa [scale, h_children] using
          eliminateOrGatesListAux_nodeCount_le repetitions children nextRandom
      have h_gadget := approximateOr_nodeCount_eq transformed repetitions afterChildren
      have h_length := length_le_sum_nodeCount children
      have h_transformed_length :=
        eliminateOrGatesListAux_length repetitions children nextRandom
      rw [h_children] at h_transformed_length
      simp only [eliminateOrGatesAux, h_children, ACCFormula.depth,
        ACCFormula.nodeCount]
      rw [h_gadget]
      have h_pow : 1 ≤
          scale ^ (children.map ACCFormula.depth).max?.getD 0 := by
        exact Nat.one_le_pow _ _ (by omega)
      have h_transformed_length_le : transformed.length ≤
          (children.map ACCFormula.nodeCount).sum := by
        rw [h_transformed_length]
        exact h_length
      have h_scale_eq : scale = 3 * (repetitions + 1) := rfl
      calc
        2 + repetitions *
            ((transformed.map ProbabilisticACCFormula.nodeCount).sum +
              2 * transformed.length + 1) ≤
          2 + repetitions *
            (scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                (children.map ACCFormula.nodeCount).sum +
              2 * transformed.length + 1) := by gcongr
        _ ≤ 2 + repetitions *
            (scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                (children.map ACCFormula.nodeCount).sum +
              2 * (children.map ACCFormula.nodeCount).sum + 1) := by gcongr
        _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale *
              (1 + (children.map ACCFormula.nodeCount).sum) := by
          let power := scale ^ (children.map ACCFormula.depth).max?.getD 0
          let size := (children.map ACCFormula.nodeCount).sum
          have h_two_size : 2 * size ≤ 2 * power * size := by
            calc
              2 * size = 2 * 1 * size := by ring
              _ ≤ 2 * power * size := by gcongr
          have h_inside : power * size + 2 * size + 1 ≤
              3 * power * (size + 1) := by
            calc
              power * size + 2 * size + 1 ≤
                  power * size + 2 * power * size + power := by omega
              _ ≤ 3 * power * (size + 1) := by
                ring_nf
                omega
          have h_two : 2 ≤ 3 * power * (size + 1) := by
            calc
              2 ≤ 3 := by omega
              _ = 3 * 1 * 1 := by omega
              _ ≤ 3 * power * (size + 1) := by (gcongr; omega)
          dsimp [power, size] at h_inside h_two ⊢
          rw [h_scale_eq]
          calc
            2 + repetitions *
                (scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                    (children.map ACCFormula.nodeCount).sum +
                  2 * (children.map ACCFormula.nodeCount).sum + 1) ≤
              2 + repetitions *
                (3 * scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                  ((children.map ACCFormula.nodeCount).sum + 1)) := by gcongr
            _ ≤ 3 * scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                  ((children.map ACCFormula.nodeCount).sum + 1) +
                repetitions *
                  (3 * scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                    ((children.map ACCFormula.nodeCount).sum + 1)) := by gcongr
            _ = scale ^ (children.map ACCFormula.depth).max?.getD 0 *
                (3 * (repetitions + 1)) *
                  (1 + (children.map ACCFormula.nodeCount).sum) := by ring
        _ = (3 * (repetitions + 1)) ^
              (1 + (children.map ACCFormula.depth).max?.getD 0) *
                (1 + (children.map ACCFormula.nodeCount).sum) := by
          rw [show 1 + (children.map ACCFormula.depth).max?.getD 0 =
            (children.map ACCFormula.depth).max?.getD 0 + 1 by omega, pow_succ]
  | .modGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children nextRandom with
        ⟨transformed, finalRandom⟩
      have h_bound :
          (transformed.map ProbabilisticACCFormula.nodeCount).sum ≤
            scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum := by
        simpa [scale, h_children] using
          eliminateOrGatesListAux_nodeCount_le repetitions children nextRandom
      simp only [eliminateOrGatesAux, h_children,
        ProbabilisticACCFormula.nodeCount, ACCFormula.depth,
        ACCFormula.nodeCount]
      calc
        (transformed.map ProbabilisticACCFormula.nodeCount).sum + 1 ≤
            scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum + 1 :=
          Nat.add_le_add_right h_bound 1
        _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (children.map ACCFormula.nodeCount).sum +
              scale ^ (children.map ACCFormula.depth).max?.getD 0 :=
          Nat.add_le_add_left (Nat.one_le_pow _ _ (by omega)) _
        _ = scale ^ (children.map ACCFormula.depth).max?.getD 0 *
              (1 + (children.map ACCFormula.nodeCount).sum) := by ring
        _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale *
              (1 + (children.map ACCFormula.nodeCount).sum) := by
          have h_pow_scale :
              scale ^ (children.map ACCFormula.depth).max?.getD 0 ≤
                scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale := by
            calc
              scale ^ (children.map ACCFormula.depth).max?.getD 0 =
                  scale ^ (children.map ACCFormula.depth).max?.getD 0 * 1 := by omega
              _ ≤ scale ^ (children.map ACCFormula.depth).max?.getD 0 * scale := by
                gcongr
                omega
          exact Nat.mul_le_mul_right
            (1 + (children.map ACCFormula.nodeCount).sum)
            h_pow_scale
        _ = (3 * (repetitions + 1)) ^
              (1 + (children.map ACCFormula.depth).max?.getD 0) *
                (1 + (children.map ACCFormula.nodeCount).sum) := by
          rw [show 1 + (children.map ACCFormula.depth).max?.getD 0 =
            (children.map ACCFormula.depth).max?.getD 0 + 1 by omega, pow_succ]

/-- List form of the depth-sensitive OR-elimination syntax bound. -/
theorem eliminateOrGatesListAux_nodeCount_le {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) (nextRandom : Nat) :
    (((eliminateOrGatesListAux repetitions formulas nextRandom).1.map
        ProbabilisticACCFormula.nodeCount).sum) ≤
      (3 * (repetitions + 1)) ^
          (formulas.map ACCFormula.depth).max?.getD 0 *
        (formulas.map ACCFormula.nodeCount).sum := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux]
  | formula :: formulas =>
      rcases h_formula : eliminateOrGatesAux repetitions formula nextRandom with
        ⟨transformed, afterFormula⟩
      rcases h_formulas : eliminateOrGatesListAux repetitions formulas afterFormula with
        ⟨transformedFormulas, finalRandom⟩
      have h_head := eliminateOrGatesAux_nodeCount_le repetitions formula nextRandom
      rw [h_formula] at h_head
      have h_tail := eliminateOrGatesListAux_nodeCount_le repetitions formulas afterFormula
      rw [h_formulas] at h_tail
      simp only [eliminateOrGatesListAux, h_formula, h_formulas, List.map_cons,
        List.sum_cons, max?_getD_cons]
      have h_head_pow :
          (3 * (repetitions + 1)) ^ formula.depth ≤
            (3 * (repetitions + 1)) ^
              max formula.depth ((formulas.map ACCFormula.depth).max?.getD 0) := by
        exact Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
      have h_tail_pow :
          (3 * (repetitions + 1)) ^
              (formulas.map ACCFormula.depth).max?.getD 0 ≤
            (3 * (repetitions + 1)) ^
              max formula.depth ((formulas.map ACCFormula.depth).max?.getD 0) := by
        exact Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      calc
        transformed.nodeCount +
            (transformedFormulas.map ProbabilisticACCFormula.nodeCount).sum ≤
          (3 * (repetitions + 1)) ^ formula.depth * formula.nodeCount +
            (3 * (repetitions + 1)) ^
              (formulas.map ACCFormula.depth).max?.getD 0 *
                (formulas.map ACCFormula.nodeCount).sum :=
          Nat.add_le_add h_head h_tail
        _ ≤ (3 * (repetitions + 1)) ^
              max formula.depth ((formulas.map ACCFormula.depth).max?.getD 0) *
                formula.nodeCount +
            (3 * (repetitions + 1)) ^
              max formula.depth ((formulas.map ACCFormula.depth).max?.getD 0) *
                (formulas.map ACCFormula.nodeCount).sum := by gcongr
        _ = _ := by
          rw [← Nat.mul_add]

end

/-- Public depth-sensitive syntax-size bound. -/
theorem eliminateOrGates_nodeCount_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) :
    ProbabilisticACCFormula.nodeCount
        (eliminateOrGates repetitions formula) ≤
      (3 * (repetitions + 1)) ^ formula.depth * formula.nodeCount := by
  simpa [eliminateOrGates] using
    eliminateOrGatesAux_nodeCount_le repetitions formula 0

mutual

/-- OR elimination increases depth by at most a factor of four. -/
theorem eliminateOrGatesAux_depth_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) (nextRandom : Nat) :
    ProbabilisticACCFormula.depth
        (eliminateOrGatesAux repetitions formula nextRandom).1 ≤
      4 * formula.depth := by
  match formula with
  | .input idx negated => simp [eliminateOrGatesAux, ACCFormula.depth,
      ProbabilisticACCFormula.depth]
  | .constant value label => simp [eliminateOrGatesAux, ACCFormula.depth,
      ProbabilisticACCFormula.depth]
  | .notGate child =>
      rcases h_child : eliminateOrGatesAux repetitions child nextRandom with
        ⟨transformed, finalRandom⟩
      have h_bound : transformed.depth ≤ 4 * child.depth := by
        simpa [h_child] using
          eliminateOrGatesAux_depth_le repetitions child nextRandom
      simp only [eliminateOrGatesAux, h_child, ProbabilisticACCFormula.depth,
        ACCFormula.depth]
      omega
  | .andGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children nextRandom with
        ⟨transformed, finalRandom⟩
      have h_bound :
          (transformed.map ProbabilisticACCFormula.depth).max?.getD 0 ≤
            4 * (children.map ACCFormula.depth).max?.getD 0 := by
        simpa [h_children] using
          eliminateOrGatesListAux_depth_le repetitions children nextRandom
      simp only [eliminateOrGatesAux, h_children,
        ProbabilisticACCFormula.depth, ACCFormula.depth]
      omega
  | .orGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children nextRandom with
        ⟨transformed, afterChildren⟩
      have h_bound :
          (transformed.map ProbabilisticACCFormula.depth).max?.getD 0 ≤
            4 * (children.map ACCFormula.depth).max?.getD 0 := by
        simpa [h_children] using
          eliminateOrGatesListAux_depth_le repetitions children nextRandom
      have h_gadget := approximateOr_depth_le transformed repetitions afterChildren
      simp only [eliminateOrGatesAux, h_children, ACCFormula.depth]
      exact h_gadget.trans (by omega)
  | .modGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children nextRandom with
        ⟨transformed, finalRandom⟩
      have h_bound :
          (transformed.map ProbabilisticACCFormula.depth).max?.getD 0 ≤
            4 * (children.map ACCFormula.depth).max?.getD 0 := by
        simpa [h_children] using
          eliminateOrGatesListAux_depth_le repetitions children nextRandom
      simp only [eliminateOrGatesAux, h_children,
        ProbabilisticACCFormula.depth, ACCFormula.depth]
      omega

/-- List form of the depth bound for OR elimination. -/
theorem eliminateOrGatesListAux_depth_le {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) (nextRandom : Nat) :
    (((eliminateOrGatesListAux repetitions formulas nextRandom).1.map
      ProbabilisticACCFormula.depth).max?.getD 0) ≤
      4 * (formulas.map ACCFormula.depth).max?.getD 0 := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux]
  | formula :: formulas =>
      rcases h_formula : eliminateOrGatesAux repetitions formula nextRandom with
        ⟨transformed, afterFormula⟩
      rcases h_formulas : eliminateOrGatesListAux repetitions formulas afterFormula with
        ⟨transformedFormulas, finalRandom⟩
      have h_head := eliminateOrGatesAux_depth_le repetitions formula nextRandom
      rw [h_formula] at h_head
      have h_tail := eliminateOrGatesListAux_depth_le repetitions formulas afterFormula
      rw [h_formulas] at h_tail
      simp only [eliminateOrGatesListAux, h_formula, h_formulas, List.map_cons]
      rw [max?_getD_cons, max?_getD_cons]
      exact max_le (h_head.trans (Nat.mul_le_mul_left 4 (Nat.le_max_left _ _)))
        (h_tail.trans (Nat.mul_le_mul_left 4 (Nat.le_max_right _ _)))

end

/-- Public constant-factor depth bound for OR elimination. -/
theorem eliminateOrGates_depth_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) :
    ProbabilisticACCFormula.depth (eliminateOrGates repetitions formula) ≤
      4 * formula.depth := by
  simpa [eliminateOrGates] using
    eliminateOrGatesAux_depth_le repetitions formula 0

mutual

/-- OR elimination allocates at most `repetitions` bits per non-root syntax
node. -/
theorem orEliminationRandomBitCountAux_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) :
    orEliminationRandomBitCountAux repetitions formula ≤
      repetitions * (formula.nodeCount - 1) := by
  match formula with
  | .input idx negated => simp [orEliminationRandomBitCountAux,
      ACCFormula.nodeCount]
  | .constant value label => simp [orEliminationRandomBitCountAux,
      ACCFormula.nodeCount]
  | .notGate child =>
      exact (orEliminationRandomBitCountAux_le repetitions child).trans (by
        simp only [ACCFormula.nodeCount]
        gcongr
        omega)
  | .andGate children =>
      exact (orEliminationRandomBitCountListAux_le repetitions children).trans
        (by
          simp only [ACCFormula.nodeCount]
          gcongr
          rw [← sum_nodeCount_sub_one_add_length children]
          omega)
  | .orGate children =>
      have h_children :=
        orEliminationRandomBitCountListAux_le repetitions children
      simp only [orEliminationRandomBitCountAux, ACCFormula.nodeCount]
      calc
        orEliminationRandomBitCountListAux repetitions children +
            repetitions * children.length ≤
          repetitions *
              (children.map fun child => child.nodeCount - 1).sum +
            repetitions * children.length :=
          Nat.add_le_add_right h_children _
        _ = repetitions * (children.map ACCFormula.nodeCount).sum := by
          rw [← Nat.mul_add,
            sum_nodeCount_sub_one_add_length children]
        _ = repetitions *
            (1 + (children.map ACCFormula.nodeCount).sum - 1) := by
          congr 1
          omega
  | .modGate children =>
      exact (orEliminationRandomBitCountListAux_le repetitions children).trans
        (by
          simp only [ACCFormula.nodeCount]
          gcongr
          rw [← sum_nodeCount_sub_one_add_length children]
          omega)

/-- List form of the random-bit allocation bound. -/
theorem orEliminationRandomBitCountListAux_le {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) :
    orEliminationRandomBitCountListAux repetitions formulas ≤
      repetitions *
        (formulas.map fun formula => formula.nodeCount - 1).sum := by
  match formulas with
  | [] => simp [orEliminationRandomBitCountListAux]
  | formula :: formulas =>
      simp only [orEliminationRandomBitCountListAux, List.map_cons,
        List.sum_cons]
      calc
        _ ≤ repetitions * (formula.nodeCount - 1) +
              repetitions *
                (formulas.map fun child => child.nodeCount - 1).sum :=
          Nat.add_le_add
            (orEliminationRandomBitCountAux_le repetitions formula)
            (orEliminationRandomBitCountListAux_le repetitions formulas)
        _ = _ := by rw [Nat.mul_add]

end

/-- Public random-bit count bound. -/
theorem eliminateOrGatesRandomBitCount_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) :
    eliminateOrGatesRandomBitCount repetitions formula ≤
      repetitions * formula.nodeCount := by
  exact (orEliminationRandomBitCountAux_le repetitions formula).trans
    (Nat.mul_le_mul_left repetitions (Nat.sub_le _ _))

end Circuits.ACC.ACCFormula
