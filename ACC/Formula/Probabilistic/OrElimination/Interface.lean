import ACC.Formula.Probabilistic.OrElimination.Bounds

namespace Circuits.ACC.ACCFormula

open ProbabilisticACCFormula

/-! ## Public amplified OR-elimination interface -/

/-- Repetition count sufficient to make the union bound over all OR
occurrences at most `n⁻ᵏ`.

`nodeCount` is a convenient upper bound on the number of OR occurrences, and
ceiling logarithm ensures
`nodeCount * n^k ≤ 2^orEliminationRepetitions`. -/
def orEliminationRepetitions {p : Nat} (formula : ACCFormula p)
    (n k : Nat) : Nat :=
  Nat.clog 2 (formula.nodeCount * n ^ k)

/-- The amplified Chapter 3 transformation.

    For a formula `C`, input length `n`, and desired exponent `k`, this is
    `eliminateOrGates r C` with
    `r = ⌈log₂(C.nodeCount ⋅ n^k)⌉`. Its global union-bound budget is at
    most `n⁻ᵏ`. -/
def probabilisticOrElimination {p : Nat} (formula : ACCFormula p)
    (n k : Nat) : ProbabilisticACCFormula p :=
  eliminateOrGates (orEliminationRepetitions formula n k) formula

/-- Random-bit count paired with `probabilisticOrElimination`. -/
def probabilisticOrEliminationRandomBitCount {p : Nat}
    (formula : ACCFormula p) (n k : Nat) : Nat :=
  eliminateOrGatesRandomBitCount
    (orEliminationRepetitions formula n k) formula

/-- The two syntactic invariants established by probabilistic OR elimination:
    only AND and modulo gates remain, and all AND fan-ins are bounded by the
    larger of the binary masking fan-in and the amplification fan-in. -/
def IsOrEliminationOutput {p : Nat} (repetitions : Nat)
    (formula : ProbabilisticACCFormula p) : Prop :=
  formula.HasOnlyAndModGates ∧ formula.IsOfOrder (max 2 repetitions)

/-- Masking formulas that already satisfy the output invariants preserves
    those invariants. Each new root is a binary AND with one random leaf. -/
theorem randomMasks_isOrEliminationOutput {p : Nat} (repetitions : Nat)
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat)
    (h_formulas : ∀ formula ∈ formulas,
      IsOrEliminationOutput repetitions formula) :
    ∀ formula ∈ (randomMasks formulas nextRandom).1,
      IsOrEliminationOutput repetitions formula := by
  induction formulas generalizing nextRandom with
  | nil => simp [randomMasks]
  | cons formula formulas ih =>
      rcases h_masks : randomMasks formulas (nextRandom + 1) with
        ⟨masked, finalRandom⟩
      have h_formula := h_formulas formula (by simp)
      have h_tail : ∀ child ∈ formulas,
          IsOrEliminationOutput repetitions child := by
        intro child h_child
        exact h_formulas child (by simp [h_child])
      have h_masked := ih (nextRandom := nextRandom + 1) h_tail
      rw [h_masks] at h_masked
      intro transformed h_transformed
      simp only [randomMasks, h_masks, List.mem_cons] at h_transformed
      rcases h_transformed with h_head | h_tail
      · subst transformed
        constructor
        · simpa [ProbabilisticACCFormula.HasOnlyAndModGates,
            IsOrEliminationOutput] using h_formula.1
        · simp only [ProbabilisticACCFormula.IsOfOrder, List.length_cons,
            List.length_nil, zero_add]
          constructor
          · exact Nat.le_max_left 2 repetitions
          · intro child h_child
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h_child
            rcases h_child with rfl | rfl
            · simp [ProbabilisticACCFormula.IsOfOrder]
            · exact h_formula.2
      · exact h_masked transformed h_tail

/-- A modulo gate over valid random masks remains in the target fragment and
    obeys the same order bound. -/
theorem randomModTest_isOrEliminationOutput {p : Nat} (repetitions : Nat)
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat)
    (h_formulas : ∀ formula ∈ formulas,
      IsOrEliminationOutput repetitions formula) :
    IsOrEliminationOutput repetitions (randomModTest formulas nextRandom).1 := by
  rcases h_masks : randomMasks formulas nextRandom with ⟨masked, finalRandom⟩
  have h_masked := randomMasks_isOrEliminationOutput repetitions formulas
    nextRandom h_formulas
  rw [h_masks] at h_masked
  constructor
  · simp only [randomModTest, h_masks,
      ProbabilisticACCFormula.HasOnlyAndModGates]
    intro formula h_formula
    exact (h_masked formula h_formula).1
  · simp only [randomModTest, h_masks, ProbabilisticACCFormula.IsOfOrder]
    intro formula h_formula
    exact (h_masked formula h_formula).2

/-- `randomModTests` constructs exactly the requested number of tests. -/
theorem randomModTests_length {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) :
    (randomModTests formulas repetitions nextRandom).1.length = repetitions := by
  induction repetitions generalizing nextRandom with
  | zero => simp [randomModTests]
  | succ repetitions ih =>
      rcases h_test : randomModTest formulas nextRandom with ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas repetitions afterTest with
        ⟨tests, finalRandom⟩
      have h_length := ih afterTest
      rw [h_tests] at h_length
      simp [randomModTests, h_test, h_tests, h_length]

/-- Every test in an independently generated test list satisfies the target
    gate-fragment and order invariants. -/
theorem randomModTests_isOrEliminationOutput {p : Nat} (repetitions : Nat)
    (formulas : List (ProbabilisticACCFormula p)) (count nextRandom : Nat)
    (h_formulas : ∀ formula ∈ formulas,
      IsOrEliminationOutput repetitions formula) :
    ∀ formula ∈ (randomModTests formulas count nextRandom).1,
      IsOrEliminationOutput repetitions formula := by
  induction count generalizing nextRandom with
  | zero => simp [randomModTests]
  | succ count ih =>
      rcases h_test : randomModTest formulas nextRandom with ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas count afterTest with
        ⟨tests, finalRandom⟩
      have h_tail := ih (nextRandom := afterTest)
      rw [h_tests] at h_tail
      have h_head := randomModTest_isOrEliminationOutput repetitions formulas
        nextRandom h_formulas
      rw [h_test] at h_head
      intro formula h_formula
      simp only [randomModTests, h_test, h_tests, List.mem_cons] at h_formula
      rcases h_formula with rfl | h_formula
      · exact h_head
      · exact h_tail formula h_formula

/-- The complete amplified OR gadget contains only AND and modulo gates and
    has order at most `max 2 repetitions`. -/
theorem approximateOr_isOrEliminationOutput {p : Nat} (repetitions : Nat)
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat)
    (h_formulas : ∀ formula ∈ formulas,
      IsOrEliminationOutput repetitions formula) :
    IsOrEliminationOutput repetitions
      (approximateOr formulas repetitions nextRandom).1 := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  have h_test_outputs := randomModTests_isOrEliminationOutput repetitions
    formulas repetitions nextRandom h_formulas
  rw [h_tests] at h_test_outputs
  have h_length := randomModTests_length formulas repetitions nextRandom
  rw [h_tests] at h_length
  constructor
  · simp only [approximateOr, h_tests,
      ProbabilisticACCFormula.HasOnlyAndModGates, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq]
    intro formula h_formula
    exact (h_test_outputs formula h_formula).1
  · simp only [approximateOr, h_tests, ProbabilisticACCFormula.IsOfOrder,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    constructor
    · rw [h_length]
      exact Nat.le_max_right 2 repetitions
    · intro formula h_formula
      exact (h_test_outputs formula h_formula).2

mutual
/-- Under the source-fragment hypothesis, recursive OR elimination produces a
    valid target formula for every starting random-input index. -/
theorem eliminateOrGatesAux_isOrEliminationOutput {p : Nat}
    (repetitions : Nat) (formula : ACCFormula p) (nextRandom : Nat)
    (h_formula : HasOnlyOrAndModGates formula) :
    IsOrEliminationOutput repetitions
      (eliminateOrGatesAux repetitions formula nextRandom).1 := by
  match formula with
  | .input idx negated =>
      simp [eliminateOrGatesAux, IsOrEliminationOutput,
        ProbabilisticACCFormula.HasOnlyAndModGates,
        ProbabilisticACCFormula.IsOfOrder]
  | .constant value label =>
      simp [eliminateOrGatesAux, IsOrEliminationOutput,
        ProbabilisticACCFormula.HasOnlyAndModGates,
        ProbabilisticACCFormula.IsOfOrder]
  | .notGate child =>
      simp [HasOnlyOrAndModGates, HasNoNotGates] at h_formula
  | .andGate children =>
      simp [HasOnlyOrAndModGates, HasNoAndGates] at h_formula
  | .orGate children =>
      simp only [HasOnlyOrAndModGates, HasNoAndGates, HasNoNotGates]
        at h_formula
      have h_children : ∀ child ∈ children,
          HasOnlyOrAndModGates child := by
        intro child h_child
        exact ⟨h_formula.1 child h_child, h_formula.2 child h_child⟩
      rcases h_transformed : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, afterChildren⟩
      have h_outputs := eliminateOrGatesListAux_isOrEliminationOutput
        repetitions children nextRandom h_children
      rw [h_transformed] at h_outputs
      simp only [eliminateOrGatesAux, h_transformed]
      exact approximateOr_isOrEliminationOutput repetitions transformed
        afterChildren h_outputs
  | .modGate children =>
      simp only [HasOnlyOrAndModGates, HasNoAndGates, HasNoNotGates]
        at h_formula
      have h_children : ∀ child ∈ children,
          HasOnlyOrAndModGates child := by
        intro child h_child
        exact ⟨h_formula.1 child h_child, h_formula.2 child h_child⟩
      rcases h_transformed : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, finalRandom⟩
      have h_outputs := eliminateOrGatesListAux_isOrEliminationOutput
        repetitions children nextRandom h_children
      rw [h_transformed] at h_outputs
      constructor
      · simp only [eliminateOrGatesAux, h_transformed,
          ProbabilisticACCFormula.HasOnlyAndModGates]
        intro child h_child
        exact (h_outputs child h_child).1
      · simp only [eliminateOrGatesAux, h_transformed,
          ProbabilisticACCFormula.IsOfOrder]
        intro child h_child
        exact (h_outputs child h_child).2

/-- Pointwise form of `eliminateOrGatesAux_isOrEliminationOutput` for the
    state-threaded transformation of a child list. -/
theorem eliminateOrGatesListAux_isOrEliminationOutput {p : Nat}
    (repetitions : Nat) (formulas : List (ACCFormula p)) (nextRandom : Nat)
    (h_formulas : ∀ formula ∈ formulas, HasOnlyOrAndModGates formula) :
    ∀ formula ∈ (eliminateOrGatesListAux repetitions formulas nextRandom).1,
      IsOrEliminationOutput repetitions formula := by
  match formulas with
  | [] => simp [eliminateOrGatesListAux]
  | formula :: formulas =>
      have h_formula := h_formulas formula (by simp)
      have h_tail : ∀ child ∈ formulas, HasOnlyOrAndModGates child := by
        intro child h_child
        exact h_formulas child (by simp [h_child])
      rcases h_transformed : eliminateOrGatesAux repetitions formula nextRandom with
        ⟨transformed, afterFormula⟩
      rcases h_transformed_tail : eliminateOrGatesListAux repetitions formulas
          afterFormula with ⟨transformedFormulas, finalRandom⟩
      have h_head_output := eliminateOrGatesAux_isOrEliminationOutput
        repetitions formula nextRandom h_formula
      rw [h_transformed] at h_head_output
      have h_tail_outputs := eliminateOrGatesListAux_isOrEliminationOutput
        repetitions formulas afterFormula h_tail
      rw [h_transformed_tail] at h_tail_outputs
      intro output h_output
      simp only [eliminateOrGatesListAux, h_transformed, h_transformed_tail,
        List.mem_cons] at h_output
      rcases h_output with rfl | h_output
      · exact h_head_output
      · exact h_tail_outputs output h_output
end

/-- Probabilistic OR elimination removes all OR and NOT gates and bounds every
    AND fan-in by `max 2 repetitions`. -/
theorem eliminateOrGates_isOrEliminationOutput {p : Nat}
    (repetitions : Nat) (formula : ACCFormula p)
    (h_formula : HasOnlyOrAndModGates formula) :
    IsOrEliminationOutput repetitions (eliminateOrGates repetitions formula) := by
  exact eliminateOrGatesAux_isOrEliminationOutput repetitions formula 0 h_formula

/-- Every internal node produced by probabilistic OR elimination is an AND or
    modulo gate. -/
theorem eliminateOrGates_hasOnlyAndModGates {p : Nat}
    (repetitions : Nat) (formula : ACCFormula p)
    (h_formula : HasOnlyOrAndModGates formula) :
    (eliminateOrGates repetitions formula).HasOnlyAndModGates :=
  (eliminateOrGates_isOrEliminationOutput repetitions formula h_formula).1

/-- Every AND introduced by probabilistic OR elimination has fan-in at most
    `max 2 repetitions`. -/
theorem eliminateOrGates_isOfOrder {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) (h_formula : HasOnlyOrAndModGates formula) :
    (eliminateOrGates repetitions formula).IsOfOrder (max 2 repetitions) :=
  (eliminateOrGates_isOrEliminationOutput repetitions formula h_formula).2

/-- The amplified transformation has the explicit order bound determined by
    its repetition count. -/
theorem probabilisticOrElimination_isOfOrder {p : Nat} (formula : ACCFormula p)
    (n k : Nat) (h_formula : HasOnlyOrAndModGates formula) :
    (probabilisticOrElimination formula n k).IsOfOrder
      (max 2 (orEliminationRepetitions formula n k)) :=
  eliminateOrGates_isOfOrder _ formula h_formula

/-- The amplified transformation contains only AND and modulo gates. -/
theorem probabilisticOrElimination_hasOnlyAndModGates {p : Nat}
    (formula : ACCFormula p) (n k : Nat)
    (h_formula : HasOnlyOrAndModGates formula) :
    (probabilisticOrElimination formula n k).HasOnlyAndModGates :=
  eliminateOrGates_hasOnlyAndModGates _ formula h_formula

/-- The repetition count is large enough for a union bound assigning error
    `2⁻ʳ` to each of at most `nodeCount` OR gates. -/
theorem nodeCount_mul_pow_le_two_pow_orEliminationRepetitions {p : Nat}
    (formula : ACCFormula p) (n k : Nat) :
    formula.nodeCount * n ^ k ≤
      2 ^ orEliminationRepetitions formula n k := by
  exact Nat.le_pow_clog (by omega) _

/-- For a formula family with `nodeCount ≤ nᵃ`, the number of repetitions is
    at most `(a + k) ⋅ ⌈log₂ n⌉`. This is the explicit `O(log n)` bound
    for fixed `a` and `k`. -/
theorem orEliminationRepetitions_le {p : Nat} (formula : ACCFormula p)
    (n a k : Nat) (h_size : formula.nodeCount ≤ n ^ a) :
    orEliminationRepetitions formula n k ≤
      (a + k) * Nat.clog 2 n := by
  apply Nat.clog_le_of_le_pow
  calc
    formula.nodeCount * n ^ k ≤ n ^ a * n ^ k :=
      Nat.mul_le_mul_right (n ^ k) h_size
    _ = n ^ (a + k) := (Nat.pow_add n a k).symm
    _ ≤ (2 ^ Nat.clog 2 n) ^ (a + k) := by
      gcongr
      exact Nat.le_pow_clog (by omega) n
    _ = 2 ^ (Nat.clog 2 n * (a + k)) := by rw [Nat.pow_mul]
    _ = 2 ^ ((a + k) * Nat.clog 2 n) := by rw [Nat.mul_comm]

/-- Coefficient-aware repetition bound using `clog 2 (n+1)`, so it also
holds at the positive input length `n = 1`. -/
theorem orEliminationRepetitions_le_of_nodeCount_le {p : Nat}
    (formula : ACCFormula p) (n coefficient exponent k : Nat)
    (hn : 0 < n)
    (_h_coefficient : 0 < coefficient)
    (h_size : formula.nodeCount ≤ coefficient * n ^ exponent) :
    orEliminationRepetitions formula n k ≤
      (Nat.clog 2 coefficient + exponent + k) * Nat.clog 2 (n + 1) := by
  apply Nat.clog_le_of_le_pow
  have h_n : n ≤ 2 ^ Nat.clog 2 (n + 1) :=
    (Nat.le_add_right n 1).trans (Nat.le_pow_clog (by omega) (n + 1))
  calc
    formula.nodeCount * n ^ k ≤
        coefficient * n ^ exponent * n ^ k :=
      Nat.mul_le_mul_right (n ^ k) h_size
    _ = coefficient * n ^ (exponent + k) := by rw [Nat.pow_add]; ring
    _ ≤ 2 ^ Nat.clog 2 coefficient *
        (2 ^ Nat.clog 2 (n + 1)) ^ (exponent + k) := by
      gcongr
      exact Nat.le_pow_clog (by omega) coefficient
    _ = 2 ^ (Nat.clog 2 coefficient +
        Nat.clog 2 (n + 1) * (exponent + k)) := by
      rw [← Nat.pow_mul, ← pow_add]
    _ ≤ 2 ^ ((Nat.clog 2 coefficient + exponent + k) *
        Nat.clog 2 (n + 1)) := by
      have h_log : 1 ≤ Nat.clog 2 (n + 1) := by
        have := Nat.clog_pos (b := 2) (n := n + 1) (by omega) (by omega)
        omega
      have h_constant : Nat.clog 2 coefficient ≤
          Nat.clog 2 coefficient * Nat.clog 2 (n + 1) := by
        calc
          Nat.clog 2 coefficient = Nat.clog 2 coefficient * 1 := by omega
          _ ≤ Nat.clog 2 coefficient * Nat.clog 2 (n + 1) := by gcongr
      apply Nat.pow_le_pow_right (by omega)
      calc
          Nat.clog 2 coefficient +
              Nat.clog 2 (n + 1) * (exponent + k) ≤
            Nat.clog 2 coefficient * Nat.clog 2 (n + 1) +
              Nat.clog 2 (n + 1) * (exponent + k) := by gcongr
          _ = (Nat.clog 2 coefficient + exponent + k) *
              Nat.clog 2 (n + 1) := by ring

/-- The union-bound error budget selected by `orEliminationRepetitions` is at
    most `n⁻ᵏ`. -/
theorem orElimination_unionBound_le_inv_pow {p : Nat} (formula : ACCFormula p)
    (n k : Nat) (hn : 0 < n) :
    (formula.nodeCount : ℚ) /
        2 ^ orEliminationRepetitions formula n k ≤
      1 / (n : ℚ) ^ k := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  simpa using
    nodeCount_mul_pow_le_two_pow_orEliminationRepetitions formula n k

/-- The amplified entry point achieves the requested inverse-polynomial
error bound. -/
theorem probabilisticOrElimination_errorProbability_le {p : Nat}
    (hp : 1 < p) (formula : ACCFormula p) (n k : Nat) (inputs : List Bool)
    (hn : 0 < n) (h_formula : HasOnlyOrAndModGates formula) :
    ProbabilisticACCFormula.errorProbability
        (probabilisticOrElimination formula n k)
        (probabilisticOrEliminationRandomBitCount formula n k) inputs
        (ACCFormula.eval formula inputs) ≤
      1 / (n : ℚ) ^ k := by
  exact (eliminateOrGates_errorProbability_le hp
    (orEliminationRepetitions formula n k) formula inputs h_formula).trans
      (orElimination_unionBound_le_inv_pow formula n k hn)


end Circuits.ACC.ACCFormula
