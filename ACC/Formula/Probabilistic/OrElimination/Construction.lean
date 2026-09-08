import ACC.Formula.Probabilistic.OrElimination.ApproximateOr

namespace Circuits.ACC.ACCFormula

open ProbabilisticACCFormula

/-! ## Recursive OR-gate elimination -/

mutual
/-- Replace every OR gate by `approximateOr`, recursively transforming its
    children first and threading fresh random-input indices through the whole
    syntax tree.

    This auxiliary operation is total: pre-existing AND and NOT gates are
    copied. The public structural guarantees therefore assume
    `HasOnlyOrAndModGates`, which rules those constructors out in the source. -/
def eliminateOrGatesAux {p : Nat} (repetitions : Nat) :
    ACCFormula p → Nat → ProbabilisticACCFormula p × Nat
  | .input idx negated, nextRandom =>
      (.input (.external idx) negated, nextRandom)
  | .constant value label, nextRandom =>
      (.constant value label, nextRandom)
  | .notGate formula, nextRandom =>
      let (transformed, finalRandom) :=
        eliminateOrGatesAux repetitions formula nextRandom
      (.notGate transformed, finalRandom)
  | .andGate formulas, nextRandom =>
      let (transformed, finalRandom) :=
        eliminateOrGatesListAux repetitions formulas nextRandom
      (.andGate transformed, finalRandom)
  | .orGate formulas, nextRandom =>
      let (transformed, afterChildren) :=
        eliminateOrGatesListAux repetitions formulas nextRandom
      approximateOr transformed repetitions afterChildren
  | .modGate formulas, nextRandom =>
      let (transformed, finalRandom) :=
        eliminateOrGatesListAux repetitions formulas nextRandom
      (.modGate transformed, finalRandom)

/-- Apply `eliminateOrGatesAux` to a list from left to right. Random indices
    consumed by one child are skipped before transforming the next, ensuring
    disjoint randomness for distinct formula occurrences. -/
def eliminateOrGatesListAux {p : Nat} (repetitions : Nat) :
    List (ACCFormula p) → Nat →
      List (ProbabilisticACCFormula p) × Nat
  | [], nextRandom => ([], nextRandom)
  | formula :: formulas, nextRandom =>
      let (transformed, afterFormula) :=
        eliminateOrGatesAux repetitions formula nextRandom
      let (transformedFormulas, finalRandom) :=
        eliminateOrGatesListAux repetitions formulas afterFormula
      (transformed :: transformedFormulas, finalRandom)
end

mutual

/-- Number of random bits allocated while eliminating OR gates in a formula.
This syntax-directed count is independent of the starting allocator index. -/
def orEliminationRandomBitCountAux {p : Nat} (repetitions : Nat) :
    ACCFormula p → Nat
  | .input _ _ => 0
  | .constant _ _ => 0
  | .notGate formula => orEliminationRandomBitCountAux repetitions formula
  | .andGate formulas =>
      orEliminationRandomBitCountListAux repetitions formulas
  | .orGate formulas =>
      orEliminationRandomBitCountListAux repetitions formulas +
        repetitions * formulas.length
  | .modGate formulas =>
      orEliminationRandomBitCountListAux repetitions formulas

/-- Sum of the OR-elimination random-bit counts of a formula list. -/
def orEliminationRandomBitCountListAux {p : Nat} (repetitions : Nat) :
    List (ACCFormula p) → Nat
  | [] => 0
  | formula :: formulas =>
      orEliminationRandomBitCountAux repetitions formula +
        orEliminationRandomBitCountListAux repetitions formulas

end

mutual

/-- OR elimination preserves the number and order of formulas in a child
list. -/
theorem eliminateOrGatesListAux_length {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) (nextRandom : Nat) :
    (eliminateOrGatesListAux repetitions formulas nextRandom).1.length =
      formulas.length := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux]
  | formula :: formulas =>
      rcases h_formula : eliminateOrGatesAux repetitions formula nextRandom with
        ⟨transformed, afterFormula⟩
      rcases h_tail : eliminateOrGatesListAux repetitions formulas afterFormula
        with ⟨transformedTail, finalRandom⟩
      have ih := eliminateOrGatesListAux_length repetitions formulas afterFormula
      rw [h_tail] at ih
      simp [eliminateOrGatesListAux, h_formula, h_tail, ih]

/-- Exact allocator result for recursive OR elimination. -/
theorem eliminateOrGatesAux_finalRandom {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) (nextRandom : Nat) :
    (eliminateOrGatesAux repetitions formula nextRandom).2 =
      nextRandom + orEliminationRandomBitCountAux repetitions formula := by
  match formula with
  | .input idx negated => simp [eliminateOrGatesAux,
      orEliminationRandomBitCountAux]
  | .constant value label => simp [eliminateOrGatesAux,
      orEliminationRandomBitCountAux]
  | .notGate child =>
      rcases h_child : eliminateOrGatesAux repetitions child nextRandom with
        ⟨transformed, finalRandom⟩
      have ih := eliminateOrGatesAux_finalRandom repetitions child nextRandom
      rw [h_child] at ih
      simpa [eliminateOrGatesAux, orEliminationRandomBitCountAux, h_child]
        using ih
  | .andGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
        nextRandom with ⟨transformed, finalRandom⟩
      have ih := eliminateOrGatesListAux_finalRandom repetitions children
        nextRandom
      rw [h_children] at ih
      simpa [eliminateOrGatesAux, orEliminationRandomBitCountAux, h_children]
        using ih
  | .orGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
        nextRandom with ⟨transformed, afterChildren⟩
      have h_after := eliminateOrGatesListAux_finalRandom repetitions children
        nextRandom
      rw [h_children] at h_after
      change afterChildren = nextRandom +
        orEliminationRandomBitCountListAux repetitions children at h_after
      have h_length := eliminateOrGatesListAux_length repetitions children
        nextRandom
      rw [h_children] at h_length
      change transformed.length = children.length at h_length
      simp only [eliminateOrGatesAux, h_children]
      rw [approximateOr_finalRandom, h_length, h_after,
        orEliminationRandomBitCountAux]
      omega
  | .modGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
        nextRandom with ⟨transformed, finalRandom⟩
      have ih := eliminateOrGatesListAux_finalRandom repetitions children
        nextRandom
      rw [h_children] at ih
      simpa [eliminateOrGatesAux, orEliminationRandomBitCountAux, h_children]
        using ih

/-- Exact allocator result for the list traversal. -/
theorem eliminateOrGatesListAux_finalRandom {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) (nextRandom : Nat) :
    (eliminateOrGatesListAux repetitions formulas nextRandom).2 =
      nextRandom +
        orEliminationRandomBitCountListAux repetitions formulas := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux, orEliminationRandomBitCountListAux]
  | formula :: formulas =>
      rcases h_formula : eliminateOrGatesAux repetitions formula nextRandom with
        ⟨transformed, afterFormula⟩
      rcases h_tail : eliminateOrGatesListAux repetitions formulas afterFormula
        with ⟨transformedTail, finalRandom⟩
      have h_after := eliminateOrGatesAux_finalRandom repetitions formula
        nextRandom
      rw [h_formula] at h_after
      have h_final := eliminateOrGatesListAux_finalRandom repetitions formulas
        afterFormula
      rw [h_tail] at h_final
      simp only [eliminateOrGatesListAux, h_formula, h_tail,
        orEliminationRandomBitCountListAux]
      omega

end

mutual

/-- Recursive OR elimination never moves the random-input allocator
backwards. -/
theorem eliminateOrGatesAux_nextRandom_le {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) (nextRandom : Nat) :
    nextRandom ≤ (eliminateOrGatesAux repetitions formula nextRandom).2 := by
  match formula with
  | .input idx negated => simp [eliminateOrGatesAux]
  | .constant value label => simp [eliminateOrGatesAux]
  | .notGate child =>
      rcases h_child : eliminateOrGatesAux repetitions child nextRandom with
        ⟨transformed, finalRandom⟩
      have h_final := eliminateOrGatesAux_nextRandom_le repetitions child
        nextRandom
      rw [h_child] at h_final
      simpa [eliminateOrGatesAux, h_child] using h_final
  | .andGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, finalRandom⟩
      have h_final := eliminateOrGatesListAux_nextRandom_le repetitions
        children nextRandom
      rw [h_children] at h_final
      simpa [eliminateOrGatesAux, h_children] using h_final
  | .orGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, afterChildren⟩
      rcases h_approximate : approximateOr transformed repetitions
          afterChildren with ⟨output, finalRandom⟩
      have h_after := eliminateOrGatesListAux_nextRandom_le repetitions
        children nextRandom
      rw [h_children] at h_after
      have h_final := approximateOr_finalRandom transformed repetitions
        afterChildren
      rw [h_approximate] at h_final
      change finalRandom =
        afterChildren + repetitions * transformed.length at h_final
      have h_after_le_final : afterChildren ≤ finalRandom := by omega
      simp only [eliminateOrGatesAux, h_children, h_approximate]
      exact h_after.trans h_after_le_final
  | .modGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, finalRandom⟩
      have h_final := eliminateOrGatesListAux_nextRandom_le repetitions
        children nextRandom
      rw [h_children] at h_final
      simpa [eliminateOrGatesAux, h_children] using h_final

/-- The list traversal used by OR elimination never moves the random-input
allocator backwards. -/
theorem eliminateOrGatesListAux_nextRandom_le {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) (nextRandom : Nat) :
    nextRandom ≤
      (eliminateOrGatesListAux repetitions formulas nextRandom).2 := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux]
  | formula :: formulas =>
      rcases h_formula : eliminateOrGatesAux repetitions formula nextRandom
        with ⟨transformed, afterFormula⟩
      rcases h_formulas : eliminateOrGatesListAux repetitions formulas
          afterFormula with ⟨transformedFormulas, finalRandom⟩
      have h_after := eliminateOrGatesAux_nextRandom_le repetitions formula
        nextRandom
      rw [h_formula] at h_after
      have h_final := eliminateOrGatesListAux_nextRandom_le repetitions
        formulas afterFormula
      rw [h_formulas] at h_final
      simp only [eliminateOrGatesListAux, h_formula, h_formulas]
      exact h_after.trans h_final

end

mutual

/-- The output of recursive OR elimination uses precisely the interval that
starts at the supplied allocator index and ends at the returned index. -/
theorem eliminateOrGatesAux_usesRandomInputsIn {p : Nat}
    (repetitions : Nat) (formula : ACCFormula p) (nextRandom : Nat) :
    (eliminateOrGatesAux repetitions formula nextRandom).1.UsesRandomInputsIn
      nextRandom (eliminateOrGatesAux repetitions formula nextRandom).2 := by
  match formula with
  | .input idx negated =>
      simp [eliminateOrGatesAux,
        ProbabilisticACCFormula.UsesRandomInputsIn]
  | .constant value label =>
      simp [eliminateOrGatesAux,
        ProbabilisticACCFormula.UsesRandomInputsIn]
  | .notGate child =>
      rcases h_child : eliminateOrGatesAux repetitions child nextRandom with
        ⟨transformed, finalRandom⟩
      have h_support := eliminateOrGatesAux_usesRandomInputsIn repetitions
        child nextRandom
      rw [h_child] at h_support
      simpa [eliminateOrGatesAux, h_child,
        ProbabilisticACCFormula.UsesRandomInputsIn] using h_support
  | .andGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, finalRandom⟩
      have h_support := eliminateOrGatesListAux_usesRandomInputsIn repetitions
        children nextRandom
      rw [h_children] at h_support
      simpa [eliminateOrGatesAux, h_children,
        ProbabilisticACCFormula.UsesRandomInputsIn] using h_support
  | .orGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, afterChildren⟩
      have h_children_support :=
        eliminateOrGatesListAux_usesRandomInputsIn repetitions children
          nextRandom
      rw [h_children] at h_children_support
      have h_after := eliminateOrGatesListAux_nextRandom_le repetitions
        children nextRandom
      rw [h_children] at h_after
      simpa only [eliminateOrGatesAux, h_children] using
        approximateOr_usesRandomInputsIn transformed repetitions nextRandom
          afterChildren h_after h_children_support
  | .modGate children =>
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, finalRandom⟩
      have h_support := eliminateOrGatesListAux_usesRandomInputsIn repetitions
        children nextRandom
      rw [h_children] at h_support
      simpa [eliminateOrGatesAux, h_children,
        ProbabilisticACCFormula.UsesRandomInputsIn] using h_support

/-- List form of `eliminateOrGatesAux_usesRandomInputsIn`. -/
theorem eliminateOrGatesListAux_usesRandomInputsIn {p : Nat}
    (repetitions : Nat) (formulas : List (ACCFormula p))
    (nextRandom : Nat) :
    ∀ formula ∈ (eliminateOrGatesListAux repetitions formulas nextRandom).1,
      formula.UsesRandomInputsIn nextRandom
        (eliminateOrGatesListAux repetitions formulas nextRandom).2 := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux]
  | formula :: formulas =>
      rcases h_formula : eliminateOrGatesAux repetitions formula nextRandom
        with ⟨transformed, afterFormula⟩
      rcases h_formulas : eliminateOrGatesListAux repetitions formulas
          afterFormula with ⟨transformedFormulas, finalRandom⟩
      have h_head := eliminateOrGatesAux_usesRandomInputsIn repetitions
        formula nextRandom
      rw [h_formula] at h_head
      have h_after := eliminateOrGatesAux_nextRandom_le repetitions formula
        nextRandom
      rw [h_formula] at h_after
      have h_tail := eliminateOrGatesListAux_usesRandomInputsIn repetitions
        formulas afterFormula
      rw [h_formulas] at h_tail
      have h_final := eliminateOrGatesListAux_nextRandom_le repetitions
        formulas afterFormula
      rw [h_formulas] at h_final
      have h_head_wide :=
        ProbabilisticACCFormula.usesRandomInputsIn_mono transformed
          nextRandom afterFormula nextRandom finalRandom h_head (by omega)
          h_final
      have h_tail_wide : ∀ child ∈ transformedFormulas,
          child.UsesRandomInputsIn nextRandom finalRandom :=
        ProbabilisticACCFormula.usesRandomInputsInList_mono
          transformedFormulas afterFormula finalRandom nextRandom finalRandom
          h_tail h_after (by omega)
      intro output h_output
      simp only [eliminateOrGatesListAux, h_formula, h_formulas,
        List.mem_cons] at h_output
      simp only [eliminateOrGatesListAux, h_formula, h_formulas]
      rcases h_output with rfl | h_output
      · exact h_head_wide
      · exact h_tail_wide output h_output

end

/-- Eliminate every OR gate using `repetitions` independent modulo tests per
    gate, starting random-input allocation at index zero.

    Use `eliminateOrGatesRandomBitCount` to obtain the length of the random-bit
    list required to evaluate the result. -/
def eliminateOrGates {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) : ProbabilisticACCFormula p :=
  (eliminateOrGatesAux repetitions formula 0).1

/-- Number of random inputs allocated by `eliminateOrGates`. All random indices
    occurring in the transformed formula are strictly below this value. -/
def eliminateOrGatesRandomBitCount {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) : Nat :=
  orEliminationRandomBitCountAux repetitions formula

/-- All random leaves in the public OR-elimination output have indices below
`eliminateOrGatesRandomBitCount`. -/
theorem eliminateOrGates_usesRandomInputsIn {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) :
    (eliminateOrGates repetitions formula).UsesRandomInputsIn 0
      (eliminateOrGatesRandomBitCount repetitions formula) := by
  have h_support := eliminateOrGatesAux_usesRandomInputsIn repetitions
    formula 0
  have h_final := eliminateOrGatesAux_finalRandom repetitions formula 0
  rw [h_final] at h_support
  simpa [eliminateOrGates, eliminateOrGatesRandomBitCount] using h_support

/-- Random bits at indices beyond the allocator result cannot affect the
evaluation of an OR-elimination output. -/
theorem eliminateOrGates_eval_eq_of_randomBits_eq_below {p : Nat}
    (repetitions : Nat) (formula : ACCFormula p) (inputs : List Bool)
    (leftRandomBits rightRandomBits : List Bool)
    (h_agree : ∀ idx,
      idx < eliminateOrGatesRandomBitCount repetitions formula →
        leftRandomBits[idx]?.getD false =
          rightRandomBits[idx]?.getD false) :
    ProbabilisticACCFormula.eval (eliminateOrGates repetitions formula)
        inputs leftRandomBits =
      ProbabilisticACCFormula.eval (eliminateOrGates repetitions formula)
        inputs rightRandomBits := by
  apply ProbabilisticACCFormula.eval_eq_of_randomBits_eq_on
    (lower := 0)
    (upper := eliminateOrGatesRandomBitCount repetitions formula)
  · exact eliminateOrGates_usesRandomInputsIn repetitions formula
  · intro idx _ h_idx
    exact h_agree idx h_idx

/-- The syntax-directed random-bit count agrees with the allocator-based
public count. -/
theorem eliminateOrGatesRandomBitCount_eq {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) :
    eliminateOrGatesRandomBitCount repetitions formula =
      orEliminationRandomBitCountAux repetitions formula := by
  rfl

end Circuits.ACC.ACCFormula
