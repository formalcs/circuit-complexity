import Mathlib.Data.Nat.Log
import ACC.Formula.Transform.AndNotElimination
import ACC.Formula.Probabilistic.Properties
import ACC.Probability.BoolAssignments

namespace Circuits.ACC.ACCFormula

open ProbabilisticACCFormula

/-! ## Randomized approximation of a single OR gate -/

def randomMasks {p : Nat} :
    List (ProbabilisticACCFormula p) → Nat →
      List (ProbabilisticACCFormula p) × Nat
  | [], nextRandom => ([], nextRandom)
  | formula :: formulas, nextRandom =>
      let (masked, finalRandom) := randomMasks formulas (nextRandom + 1)
      (.andGate [.input (.random nextRandom) false, formula] :: masked,
        finalRandom)

/-- Read a consecutive block from a random-bit list, using `false` for
missing positions just as `ProbabilisticACCFormula.eval` does. -/
def randomBitBlock : Nat → Nat → List Bool → List Bool
  | 0, _, _ => []
  | count + 1, nextRandom, randomBits =>
      randomBits[nextRandom]?.getD false ::
        randomBitBlock count (nextRandom + 1) randomBits

/-- Reading immediately after a prefix recovers a complete block exactly. -/
theorem randomBitBlock_append (count : Nat) (initialBits block : List Bool)
    (h_length : block.length = count) :
    randomBitBlock count initialBits.length (initialBits ++ block) = block := by
  induction count generalizing initialBits block with
  | zero =>
      have h_nil := List.length_eq_zero_iff.mp h_length
      subst block
      simp [randomBitBlock]
  | succ count ih =>
      cases block with
      | nil => simp at h_length
      | cons bit block =>
          have h_tail_length : block.length = count := by
            simp only [List.length_cons] at h_length
            omega
          simp only [randomBitBlock]
          have h_head :
              (initialBits ++ bit :: block)[initialBits.length]?.getD false = bit := by
            simp
          rw [h_head]
          have h_tail := ih (initialBits ++ [bit]) block h_tail_length
          simpa [List.append_assoc] using h_tail

/-- `List.ofFn` turns appended finite assignments into concatenated bit
lists. -/
theorem ofFn_append {left right : Nat} (leftAssignment : Fin left → Bool)
    (rightAssignment : Fin right → Bool) :
    List.ofFn (Fin.append leftAssignment rightAssignment) =
      List.ofFn leftAssignment ++ List.ofFn rightAssignment :=
  List.ofFn_fin_append leftAssignment rightAssignment

/-- Casting a finite index before applying `List.ofFn` preserves the list. -/
@[simp]
theorem ofFn_fin_cast {m n : Nat} (h : m = n) (assignment : Fin n → Bool) :
    List.ofFn (fun i : Fin m => assignment (Fin.cast h i)) =
      List.ofFn assignment := by
  subst n
  rfl

/-- Evaluation of the binary AND gate used for masking is Boolean
conjunction of the mask bit and the child value. -/
theorem eval_maskAnd {p : Nat} (randomIndex : Nat)
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool) :
    ProbabilisticACCFormula.eval
        (.andGate [.input (.random randomIndex) false, formula])
        inputs randomBits =
      (randomBits[randomIndex]?.getD false &&
        ProbabilisticACCFormula.eval formula inputs randomBits) := by
  cases h_random : randomBits[randomIndex]?.getD false <;>
    cases h_formula : ProbabilisticACCFormula.eval formula inputs randomBits <;>
    simp [ProbabilisticACCFormula.eval, h_random, h_formula]

/-- An AND gate evaluates to true when every child evaluates to true. -/
theorem eval_andGate_true_of_children_true {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (inputs randomBits : List Bool)
    (h_true : ∀ formula ∈ formulas,
      ProbabilisticACCFormula.eval formula inputs randomBits = true) :
    ProbabilisticACCFormula.eval (.andGate formulas) inputs randomBits = true := by
  simpa [ProbabilisticACCFormula.eval] using h_true

/-- The evaluated output list of `randomMasks` is the pointwise conjunction
of the freshly read mask block and the child-value list. -/
theorem randomMasks_eval {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat)
    (inputs randomBits : List Bool) :
    (randomMasks formulas nextRandom).1.map
        (fun formula =>
          ProbabilisticACCFormula.eval formula inputs randomBits) =
      List.zipWith (· && ·)
        (randomBitBlock formulas.length nextRandom randomBits)
        (formulas.map fun formula =>
          ProbabilisticACCFormula.eval formula inputs randomBits) := by
  induction formulas generalizing nextRandom with
  | nil => simp [randomMasks, randomBitBlock]
  | cons formula formulas ih =>
      rcases h_masks : randomMasks formulas (nextRandom + 1) with
        ⟨masked, finalRandom⟩
      have h_tail := ih (nextRandom + 1)
      rw [h_masks] at h_tail
      simp only [randomMasks, h_masks, List.map_cons, List.length_cons,
        randomBitBlock, List.zipWith_cons_cons]
      rw [eval_maskAnd, h_tail]

/-- One randomized NOR test for `formulas`.

    The children are first masked by independent random bits and then placed
    below one modulo gate. The test is always true if every child is false and,
    for `p > 1`, is true with probability at most `1/2` if some child is true.
    This probability statement presumes that the indices allocated from
    `nextRandom` are fresh for the child formulas, as guaranteed by
    `eliminateOrGatesAux`. -/
def randomModTest {p : Nat} (formulas : List (ProbabilisticACCFormula p))
    (nextRandom : Nat) : ProbabilisticACCFormula p × Nat :=
  let (masked, finalRandom) := randomMasks formulas nextRandom
  (.modGate masked, finalRandom)

/-- A randomized modulo test accepts exactly when the sum of its pointwise
masked child values is zero modulo `p`. -/
theorem randomModTest_eval_eq_true_iff {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat)
    (inputs randomBits : List Bool) :
    ProbabilisticACCFormula.eval (randomModTest formulas nextRandom).1
        inputs randomBits = true ↔
      ((List.zipWith (· && ·)
          (randomBitBlock formulas.length nextRandom randomBits)
          (formulas.map fun formula =>
            ProbabilisticACCFormula.eval formula inputs randomBits)).map
        Bool.toNat).sum % p = 0 := by
  rcases h_masks : randomMasks formulas nextRandom with
    ⟨masked, finalRandom⟩
  have h_eval := randomMasks_eval formulas nextRandom inputs randomBits
  rw [h_masks] at h_eval
  simp only [randomModTest, h_masks, ProbabilisticACCFormula.eval]
  rw [h_eval]
  simp

/-- A randomized modulo test always accepts when every child is false. -/
theorem randomModTest_eval_true_of_children_false {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat)
    (inputs randomBits : List Bool)
    (h_false : ∀ formula ∈ formulas,
      ProbabilisticACCFormula.eval formula inputs randomBits = false) :
    ProbabilisticACCFormula.eval (randomModTest formulas nextRandom).1
      inputs randomBits = true := by
  rw [randomModTest_eval_eq_true_iff]
  induction formulas generalizing nextRandom with
  | nil => simp [randomBitBlock]
  | cons formula formulas ih =>
      have h_formula := h_false formula (by simp)
      have h_tail : ∀ child ∈ formulas,
          ProbabilisticACCFormula.eval child inputs randomBits = false := by
        intro child h_child
        exact h_false child (by simp [h_child])
      simp only [List.length_cons, randomBitBlock, List.map_cons,
        List.zipWith_cons_cons, List.map_cons, List.sum_cons, h_formula,
        Bool.and_false, Bool.toNat_false, zero_add]
      exact ih (nextRandom + 1) h_tail

/-- Formulas supported before `nextRandom` have fixed values while a fresh
assignment block is appended after that index. -/
theorem evalList_append_fresh_eq {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (lower nextRandom : Nat)
    (inputs initialBits freshBits : List Bool)
    (h_initial_length : initialBits.length = nextRandom)
    (h_support : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom) :
    formulas.map (fun formula =>
        ProbabilisticACCFormula.eval formula inputs
          (initialBits ++ freshBits)) =
      formulas.map (fun formula =>
        ProbabilisticACCFormula.eval formula inputs initialBits) := by
  apply ProbabilisticACCFormula.evalList_eq_of_randomBits_eq_on
    formulas lower nextRandom inputs (initialBits ++ freshBits) initialBits
    h_support
  intro idx _ h_idx
  have h_idx_length : idx < initialBits.length := by omega
  rw [List.getElem?_append_left h_idx_length]

/-- Single-formula version of `evalList_append_fresh_eq`. -/
theorem eval_append_fresh_eq {p : Nat}
    (formula : ProbabilisticACCFormula p) (lower nextRandom : Nat)
    (inputs initialBits freshBits : List Bool)
    (h_initial_length : initialBits.length = nextRandom)
    (h_support : formula.UsesRandomInputsIn lower nextRandom) :
    ProbabilisticACCFormula.eval formula inputs (initialBits ++ freshBits) =
      ProbabilisticACCFormula.eval formula inputs initialBits := by
  apply ProbabilisticACCFormula.eval_eq_of_randomBits_eq_on formula lower
    nextRandom inputs (initialBits ++ freshBits) initialBits h_support
  intro idx _ h_idx
  have h_idx_length : idx < initialBits.length := by omega
  rw [List.getElem?_append_left h_idx_length]

/-- One fresh randomized modulo test accepts on at most half of its mask
assignments whenever at least one child is true. -/
theorem randomModTest_accepting_card_mul_two_le {p : Nat} (hp : 1 < p)
    (formulas : List (ProbabilisticACCFormula p))
    (lower nextRandom : Nat) (inputs initialBits : List Bool)
    (h_initial_length : initialBits.length = nextRandom)
    (h_support : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom)
    (h_nonzero : ∃ i : Fin formulas.length,
      ProbabilisticACCFormula.eval (formulas.get i) inputs initialBits = true) :
    ((Finset.univ : Finset (Fin formulas.length → Bool)).filter fun mask =>
      ProbabilisticACCFormula.eval (randomModTest formulas nextRandom).1 inputs
        (initialBits ++ List.ofFn mask) = true).card * 2 ≤
      2 ^ formulas.length := by
  let values : Fin formulas.length → Bool := fun i =>
    ProbabilisticACCFormula.eval (formulas.get i) inputs initialBits
  have h_event :
      ((Finset.univ : Finset (Fin formulas.length → Bool)).filter fun mask =>
        ProbabilisticACCFormula.eval (randomModTest formulas nextRandom).1 inputs
          (initialBits ++ List.ofFn mask) = true) =
        BoolAssignments.acceptingMasks p values := by
    ext mask
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      BoolAssignments.acceptingMasks]
    rw [randomModTest_eval_eq_true_iff]
    have h_block := randomBitBlock_append formulas.length initialBits
      (List.ofFn mask) (by simp)
    rw [h_initial_length] at h_block
    rw [h_block]
    have h_children := evalList_append_fresh_eq formulas lower nextRandom inputs
      initialBits (List.ofFn mask) h_initial_length h_support
    rw [h_children]
    have h_values :
        formulas.map (fun formula =>
          ProbabilisticACCFormula.eval formula inputs initialBits) =
          List.ofFn values := by
      simpa [values] using
        (List.ofFn_getElem_eq_map formulas fun formula =>
          ProbabilisticACCFormula.eval formula inputs initialBits).symm
    rw [h_values]
    exact BoolAssignments.zipWith_ofFn_sum_mod_eq_zero_iff values mask
  rw [h_event]
  apply BoolAssignments.acceptingMasks_card_mul_two_le hp
  simpa [values] using h_nonzero

/-- Construct `count` independent randomized modulo tests for the same
    disjunction. Fresh-index threading gives each copy its own random bits. -/
def randomModTests {p : Nat} (formulas : List (ProbabilisticACCFormula p)) :
    Nat → Nat → List (ProbabilisticACCFormula p) × Nat
  | 0, nextRandom => ([], nextRandom)
  | repetitions + 1, nextRandom =>
      let (test, afterTest) := randomModTest formulas nextRandom
      let (tests, finalRandom) := randomModTests formulas repetitions afterTest
      (test :: tests, finalRandom)

/-- Recursive presentation of the number of bits in consecutive mask blocks.
Its recursion matches `randomModTests` definitionally. -/
def randomTestBitCount (fanIn : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => fanIn + randomTestBitCount fanIn count

/-- Closed form for `randomTestBitCount`. -/
theorem randomTestBitCount_eq (fanIn count : Nat) :
    randomTestBitCount fanIn count = count * fanIn := by
  induction count with
  | zero => simp [randomTestBitCount]
  | succ count ih =>
      simp [randomTestBitCount, ih, Nat.succ_mul, Nat.add_comm]

/-- An AND gate is true exactly when all its children are true. -/
theorem eval_andGate_eq_true_iff {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (inputs randomBits : List Bool) :
    ProbabilisticACCFormula.eval (.andGate formulas) inputs randomBits = true ↔
      ∀ formula ∈ formulas,
        ProbabilisticACCFormula.eval formula inputs randomBits = true := by
  simp [ProbabilisticACCFormula.eval]

/-- If all children are false, every independently generated modulo test
accepts. -/
theorem randomModTests_eval_true_of_children_false {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (count nextRandom : Nat)
    (inputs randomBits : List Bool)
    (h_false : ∀ formula ∈ formulas,
      ProbabilisticACCFormula.eval formula inputs randomBits = false) :
    ∀ test ∈ (randomModTests formulas count nextRandom).1,
      ProbabilisticACCFormula.eval test inputs randomBits = true := by
  induction count generalizing nextRandom with
  | zero => simp [randomModTests]
  | succ count ih =>
      rcases h_test : randomModTest formulas nextRandom with
        ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas count afterTest with
        ⟨tests, finalRandom⟩
      have h_head := randomModTest_eval_true_of_children_false formulas
        nextRandom inputs randomBits h_false
      rw [h_test] at h_head
      have h_tail := ih afterTest
      rw [h_tests] at h_tail
      intro output h_output
      simp only [randomModTests, h_test, h_tests, List.mem_cons] at h_output
      rcases h_output with rfl | h_output
      · exact h_head
      · exact h_tail output h_output

/-- Approximate an OR gate by negating a conjunction of independent random
    modulo tests.

    If `tests = [D₁, …, Dᵣ]`, the returned formula is
    `modGate [andGate tests]`. For `p > 1`, the outer unary modulo gate negates
    the conjunction. The result has one-sided error at most `2⁻ʳ`; its only
    newly introduced AND gates have fan-in `2` or `repetitions`. The error
    statement requires the allocated random indices to be fresh for the child
    formulas. -/
def approximateOr {p : Nat} (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) : ProbabilisticACCFormula p × Nat :=
  let (tests, finalRandom) := randomModTests formulas repetitions nextRandom
  (.modGate [.andGate tests], finalRandom)

/-- Exact syntax-tree size of the freshly masked children. -/
theorem randomMasks_nodeCount_sum_eq {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat) :
    (((randomMasks formulas nextRandom).1.map
      ProbabilisticACCFormula.nodeCount).sum) =
      (formulas.map ProbabilisticACCFormula.nodeCount).sum +
        2 * formulas.length := by
  induction formulas generalizing nextRandom with
  | nil => simp [randomMasks]
  | cons formula formulas ih =>
      rcases h_masks : randomMasks formulas (nextRandom + 1) with
        ⟨masked, finalRandom⟩
      have h_tail := ih (nextRandom + 1)
      rw [h_masks] at h_tail
      simp [randomMasks, h_masks, ProbabilisticACCFormula.nodeCount,
        h_tail]
      omega

/-- Exact syntax-tree size of one randomized modulo test. -/
theorem randomModTest_nodeCount_eq {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat) :
    ProbabilisticACCFormula.nodeCount
        (randomModTest formulas nextRandom).1 =
      (formulas.map ProbabilisticACCFormula.nodeCount).sum +
        2 * formulas.length + 1 := by
  rcases h_masks : randomMasks formulas nextRandom with
    ⟨masked, finalRandom⟩
  have h_size := randomMasks_nodeCount_sum_eq formulas nextRandom
  rw [h_masks] at h_size
  simp [randomModTest, h_masks, ProbabilisticACCFormula.nodeCount, h_size]

/-- Exact total size of the independent test list. -/
theorem randomModTests_nodeCount_sum_eq {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) :
    (((randomModTests formulas repetitions nextRandom).1.map
      ProbabilisticACCFormula.nodeCount).sum) =
      repetitions *
        ((formulas.map ProbabilisticACCFormula.nodeCount).sum +
          2 * formulas.length + 1) := by
  induction repetitions generalizing nextRandom with
  | zero => simp [randomModTests]
  | succ repetitions ih =>
      rcases h_test : randomModTest formulas nextRandom with
        ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas repetitions afterTest with
        ⟨tests, finalRandom⟩
      have h_head := randomModTest_nodeCount_eq formulas nextRandom
      rw [h_test] at h_head
      have h_tail := ih afterTest
      rw [h_tests] at h_tail
      simp [randomModTests, h_test, h_tests, h_head, h_tail, Nat.succ_mul]
      omega

/-- Exact syntax-tree size of an amplified OR gadget. -/
theorem approximateOr_nodeCount_eq {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) :
    ProbabilisticACCFormula.nodeCount
        (approximateOr formulas repetitions nextRandom).1 =
      2 + repetitions *
        ((formulas.map ProbabilisticACCFormula.nodeCount).sum +
          2 * formulas.length + 1) := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  have h_size := randomModTests_nodeCount_sum_eq formulas repetitions nextRandom
  rw [h_tests] at h_size
  simp [approximateOr, h_tests, ProbabilisticACCFormula.nodeCount, h_size,
    Nat.add_comm]
  omega

private theorem max?_getD_map_le_of_forall {α : Type} (values : List α)
    (measure : α → Nat) (bound : Nat)
    (h_values : ∀ value ∈ values, measure value ≤ bound) :
    (values.map measure).max?.getD 0 ≤ bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons]
      rw [show (measure value :: values.map measure).max?.getD 0 =
        max (measure value) ((values.map measure).max?.getD 0) by
          cases values <;> simp [List.max?_cons]]
      exact max_le (h_values value (by simp))
        (ih (by
          intro child h_child
          exact h_values child (by simp [h_child])))

/-- Every mask adds exactly one level above its associated child, so the
whole masked list is at most one level deeper than the original child list. -/
theorem randomMasks_depth_max_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat) :
    (((randomMasks formulas nextRandom).1.map
      ProbabilisticACCFormula.depth).max?.getD 0) ≤
      1 + (formulas.map ProbabilisticACCFormula.depth).max?.getD 0 := by
  apply max?_getD_map_le_of_forall
  intro output h_output
  induction formulas generalizing nextRandom with
  | nil => simp [randomMasks] at h_output
  | cons formula formulas ih =>
      rcases h_masks : randomMasks formulas (nextRandom + 1) with
        ⟨masked, finalRandom⟩
      simp only [randomMasks, h_masks, List.mem_cons] at h_output
      have h_max :
          (formula.depth :: formulas.map ProbabilisticACCFormula.depth).max?.getD 0 =
            max formula.depth
              ((formulas.map ProbabilisticACCFormula.depth).max?.getD 0) := by
        cases formulas <;> simp [List.max?_cons]
      rcases h_output with rfl | h_output
      · have h_mask_depth :
            ProbabilisticACCFormula.depth
                (.andGate [.input (.random nextRandom) false, formula]) =
              formula.depth + 1 := by
            simp [ProbabilisticACCFormula.depth]
            omega
        rw [h_mask_depth]
        simp only [List.map_cons]
        rw [h_max]
        omega
      · have h_tail := ih (nextRandom + 1) (by simpa [h_masks] using h_output)
        simp only [List.map_cons]
        rw [h_max]
        omega

/-- One randomized modulo test adds at most two levels. -/
theorem randomModTest_depth_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat) :
    ProbabilisticACCFormula.depth (randomModTest formulas nextRandom).1 ≤
      2 + (formulas.map ProbabilisticACCFormula.depth).max?.getD 0 := by
  rcases h_masks : randomMasks formulas nextRandom with
    ⟨masked, finalRandom⟩
  have h_depth : (masked.map ProbabilisticACCFormula.depth).max?.getD 0 ≤
      1 + (formulas.map ProbabilisticACCFormula.depth).max?.getD 0 := by
    simpa [h_masks] using randomMasks_depth_max_le formulas nextRandom
  simp [randomModTest, h_masks, ProbabilisticACCFormula.depth]
  omega

/-- Every independently repeated test has the same two-level depth bound. -/
theorem randomModTests_depth_max_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) :
    (((randomModTests formulas repetitions nextRandom).1.map
      ProbabilisticACCFormula.depth).max?.getD 0) ≤
      2 + (formulas.map ProbabilisticACCFormula.depth).max?.getD 0 := by
  apply max?_getD_map_le_of_forall
  intro test h_test
  induction repetitions generalizing nextRandom with
  | zero => simp [randomModTests] at h_test
  | succ repetitions ih =>
      rcases h_head : randomModTest formulas nextRandom with
        ⟨head, afterHead⟩
      rcases h_tail : randomModTests formulas repetitions afterHead with
        ⟨tail, finalRandom⟩
      simp only [randomModTests, h_head, h_tail, List.mem_cons] at h_test
      rcases h_test with rfl | h_test
      · simpa [h_head] using randomModTest_depth_le formulas nextRandom
      · exact ih afterHead (by simpa [h_tail] using h_test)

/-- The complete amplified OR gadget adds at most four levels above the
maximum transformed-child depth. -/
theorem approximateOr_depth_le {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) :
    ProbabilisticACCFormula.depth
        (approximateOr formulas repetitions nextRandom).1 ≤
      4 + (formulas.map ProbabilisticACCFormula.depth).max?.getD 0 := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  have h_depth : (tests.map ProbabilisticACCFormula.depth).max?.getD 0 ≤
      2 + (formulas.map ProbabilisticACCFormula.depth).max?.getD 0 := by
    simpa [h_tests] using
      randomModTests_depth_max_le formulas repetitions nextRandom
  simp [approximateOr, h_tests, ProbabilisticACCFormula.depth]
  omega

/-- For `p > 1`, the amplified gadget is always false when every child is
false.  Thus OR elimination has one-sided local error. -/
theorem approximateOr_eval_false_of_children_false {p : Nat} (hp : 1 < p)
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) (inputs randomBits : List Bool)
    (h_false : ∀ formula ∈ formulas,
      ProbabilisticACCFormula.eval formula inputs randomBits = false) :
    ProbabilisticACCFormula.eval
        (approximateOr formulas repetitions nextRandom).1 inputs randomBits =
      false := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  have h_tests_true := randomModTests_eval_true_of_children_false formulas
    repetitions nextRandom inputs randomBits h_false
  rw [h_tests] at h_tests_true
  have h_and : ProbabilisticACCFormula.eval (.andGate tests) inputs
      randomBits = true :=
    eval_andGate_true_of_children_true tests inputs randomBits h_tests_true
  simp [approximateOr, h_tests, ProbabilisticACCFormula.eval, h_and,
    Nat.mod_eq_of_lt hp]

/-- `randomMasks` allocates exactly one fresh random bit per formula. -/
theorem randomMasks_finalRandom {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat) :
    (randomMasks formulas nextRandom).2 = nextRandom + formulas.length := by
  induction formulas generalizing nextRandom with
  | nil => simp [randomMasks]
  | cons formula formulas ih =>
      rcases h_masks : randomMasks formulas (nextRandom + 1) with
        ⟨masked, finalRandom⟩
      have h_final := ih (nextRandom + 1)
      rw [h_masks] at h_final
      simp only [randomMasks, h_masks, List.length_cons]
      omega

/-- One randomized modulo test allocates one bit per child formula. -/
theorem randomModTest_finalRandom {p : Nat}
    (formulas : List (ProbabilisticACCFormula p)) (nextRandom : Nat) :
    (randomModTest formulas nextRandom).2 =
      nextRandom + formulas.length := by
  rcases h_masks : randomMasks formulas nextRandom with
    ⟨masked, finalRandom⟩
  have h_final := randomMasks_finalRandom formulas nextRandom
  rw [h_masks] at h_final
  simpa [randomModTest, h_masks] using h_final

/-- A list of tests allocates `count * formulas.length` fresh random bits. -/
theorem randomModTests_finalRandom {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (count nextRandom : Nat) :
    (randomModTests formulas count nextRandom).2 =
      nextRandom + count * formulas.length := by
  induction count generalizing nextRandom with
  | zero => simp [randomModTests]
  | succ count ih =>
      rcases h_test : randomModTest formulas nextRandom with
        ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas count afterTest with
        ⟨tests, finalRandom⟩
      have h_afterTest := randomModTest_finalRandom formulas nextRandom
      rw [h_test] at h_afterTest
      have h_final := ih afterTest
      rw [h_tests] at h_final
      change afterTest = nextRandom + formulas.length at h_afterTest
      change finalRandom = afterTest + count * formulas.length at h_final
      simp only [randomModTests, h_test, h_tests]
      rw [h_final, h_afterTest]
      simp only [Nat.succ_mul]
      omega

/-- The complete OR gadget has the same allocator result as its test list. -/
theorem approximateOr_finalRandom {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) :
    (approximateOr formulas repetitions nextRandom).2 =
      nextRandom + repetitions * formulas.length := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  have h_final := randomModTests_finalRandom formulas repetitions nextRandom
  rw [h_tests] at h_final
  simpa [approximateOr, h_tests] using h_final

/-- Every mask produced by `randomMasks` is supported by the old child
interval together with the newly allocated mask bits. -/
theorem randomMasks_usesRandomInputsIn {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (lower nextRandom : Nat) (h_lower : lower ≤ nextRandom)
    (h_formulas : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom) :
    ∀ formula ∈ (randomMasks formulas nextRandom).1,
      formula.UsesRandomInputsIn lower
        (randomMasks formulas nextRandom).2 := by
  induction formulas generalizing nextRandom with
  | nil => simp [randomMasks]
  | cons formula formulas ih =>
      have h_formula := h_formulas formula (by simp)
      have h_tail : ∀ child ∈ formulas,
          child.UsesRandomInputsIn lower nextRandom := by
        intro child h_child
        exact h_formulas child (by simp [h_child])
      have h_tail_wide : ∀ child ∈ formulas,
          child.UsesRandomInputsIn lower (nextRandom + 1) :=
        ProbabilisticACCFormula.usesRandomInputsInList_mono formulas
          lower nextRandom lower (nextRandom + 1) h_tail
          (by omega) (by omega)
      rcases h_masks : randomMasks formulas (nextRandom + 1) with
        ⟨masked, finalRandom⟩
      have h_masked := ih (nextRandom := nextRandom + 1)
        (by omega) h_tail_wide
      rw [h_masks] at h_masked
      have h_final := randomMasks_finalRandom formulas (nextRandom + 1)
      rw [h_masks] at h_final
      change finalRandom = nextRandom + 1 + formulas.length at h_final
      have h_next_le_final : nextRandom ≤ finalRandom := by omega
      have h_next_lt_final : nextRandom < finalRandom := by omega
      have h_formula_wide :=
        ProbabilisticACCFormula.usesRandomInputsIn_mono formula
          lower nextRandom lower finalRandom h_formula (by omega)
          h_next_le_final
      have h_head :
          (ProbabilisticACCFormula.andGate
            [.input (.random nextRandom) false, formula]).UsesRandomInputsIn
              lower finalRandom := by
        simp only [ProbabilisticACCFormula.UsesRandomInputsIn]
        intro child h_child
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h_child
        rcases h_child with rfl | rfl
        · simpa [ProbabilisticACCFormula.UsesRandomInputsIn] using
            (show lower ≤ nextRandom ∧ nextRandom < finalRandom from
              ⟨h_lower, h_next_lt_final⟩)
        · exact h_formula_wide
      intro output h_output
      simp only [randomMasks, h_masks, List.mem_cons] at h_output
      simp only [randomMasks, h_masks]
      rcases h_output with rfl | h_output
      · exact h_head
      · exact h_masked output h_output

/-- A randomized modulo test is supported by the child interval and its
freshly allocated mask block. -/
theorem randomModTest_usesRandomInputsIn {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (lower nextRandom : Nat) (h_lower : lower ≤ nextRandom)
    (h_formulas : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom) :
    (randomModTest formulas nextRandom).1.UsesRandomInputsIn lower
      (randomModTest formulas nextRandom).2 := by
  rcases h_masks : randomMasks formulas nextRandom with
    ⟨masked, finalRandom⟩
  have h_masked := randomMasks_usesRandomInputsIn formulas lower nextRandom
    h_lower h_formulas
  rw [h_masks] at h_masked
  simp only [randomModTest, h_masks,
    ProbabilisticACCFormula.UsesRandomInputsIn]
  exact h_masked

/-- Every test in `randomModTests` is supported by the child interval and
the complete fresh interval allocated for the test list. -/
theorem randomModTests_usesRandomInputsIn {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (count lower nextRandom : Nat) (h_lower : lower ≤ nextRandom)
    (h_formulas : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom) :
    ∀ formula ∈ (randomModTests formulas count nextRandom).1,
      formula.UsesRandomInputsIn lower
        (randomModTests formulas count nextRandom).2 := by
  induction count generalizing nextRandom with
  | zero => simp [randomModTests]
  | succ count ih =>
      rcases h_test : randomModTest formulas nextRandom with
        ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas count afterTest with
        ⟨tests, finalRandom⟩
      have h_after := randomModTest_finalRandom formulas nextRandom
      rw [h_test] at h_after
      change afterTest = nextRandom + formulas.length at h_after
      have h_next_le_after : nextRandom ≤ afterTest := by omega
      have h_test_support := randomModTest_usesRandomInputsIn formulas lower
        nextRandom h_lower h_formulas
      rw [h_test] at h_test_support
      have h_formulas_wide : ∀ formula ∈ formulas,
          formula.UsesRandomInputsIn lower afterTest :=
        ProbabilisticACCFormula.usesRandomInputsInList_mono formulas
          lower nextRandom lower afterTest h_formulas (by omega)
          h_next_le_after
      have h_tests_support := ih (nextRandom := afterTest)
        (h_lower.trans h_next_le_after) h_formulas_wide
      rw [h_tests] at h_tests_support
      have h_final := randomModTests_finalRandom formulas count afterTest
      rw [h_tests] at h_final
      change finalRandom = afterTest + count * formulas.length at h_final
      have h_after_le_final : afterTest ≤ finalRandom := by omega
      have h_test_support_wide :=
        ProbabilisticACCFormula.usesRandomInputsIn_mono test lower afterTest
          lower finalRandom h_test_support (by omega) h_after_le_final
      intro output h_output
      simp only [randomModTests, h_test, h_tests, List.mem_cons] at h_output
      simp only [randomModTests, h_test, h_tests]
      rcases h_output with rfl | h_output
      · exact h_test_support_wide
      · exact h_tests_support output h_output

/-- The amplified OR gadget is supported by the child interval and exactly
the fresh interval returned by its allocator. -/
theorem approximateOr_usesRandomInputsIn {p : Nat}
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions lower nextRandom : Nat) (h_lower : lower ≤ nextRandom)
    (h_formulas : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom) :
    (approximateOr formulas repetitions nextRandom).1.UsesRandomInputsIn lower
      (approximateOr formulas repetitions nextRandom).2 := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  have h_test_support := randomModTests_usesRandomInputsIn formulas
    repetitions lower nextRandom h_lower h_formulas
  rw [h_tests] at h_test_support
  simp only [approximateOr, h_tests,
    ProbabilisticACCFormula.UsesRandomInputsIn,
    List.mem_cons, List.not_mem_nil, or_false]
  intro formula h_formula
  subst formula
  simp only [ProbabilisticACCFormula.UsesRandomInputsIn]
  exact h_test_support

/-- With a nonzero child-value vector, all `count` independent tests accept
on at most `2^(count * (fanIn - 1))` assignments to their fresh mask bits. -/
theorem randomModTests_all_true_card_le {p : Nat} (hp : 1 < p)
    (formulas : List (ProbabilisticACCFormula p)) (count lower nextRandom : Nat)
    (inputs initialBits : List Bool)
    (h_initial_length : initialBits.length = nextRandom)
    (h_lower : lower ≤ nextRandom)
    (h_support : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom)
    (h_nonzero : ∃ i : Fin formulas.length,
      ProbabilisticACCFormula.eval (formulas.get i) inputs initialBits = true) :
    ((Finset.univ : Finset
        (Fin (randomTestBitCount formulas.length count) → Bool)).filter
      fun freshAssignment =>
        ∀ test ∈ (randomModTests formulas count nextRandom).1,
          ProbabilisticACCFormula.eval test inputs
            (initialBits ++ List.ofFn freshAssignment) = true).card ≤
      2 ^ (count * (formulas.length - 1)) := by
  induction count generalizing nextRandom initialBits with
  | zero =>
      let only : Fin 0 → Bool := fun i => Fin.elim0 i
      have h_univ : (Finset.univ : Finset (Fin 0 → Bool)) = {only} := by
        ext assignment
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        funext i
        exact Fin.elim0 i
      simp only [randomTestBitCount, randomModTests, zero_mul, pow_zero]
      change (Finset.univ : Finset (Fin 0 → Bool)).card ≤ 1
      rw [h_univ]
      simp
  | succ count ih =>
      rcases h_test : randomModTest formulas nextRandom with
        ⟨test, afterTest⟩
      rcases h_tests : randomModTests formulas count afterTest with
        ⟨tests, finalRandom⟩
      have h_after := randomModTest_finalRandom formulas nextRandom
      rw [h_test] at h_after
      change afterTest = nextRandom + formulas.length at h_after
      have h_next_le_after : nextRandom ≤ afterTest := by omega
      have h_formulas_after : ∀ formula ∈ formulas,
          formula.UsesRandomInputsIn lower afterTest :=
        ProbabilisticACCFormula.usesRandomInputsInList_mono formulas
          lower nextRandom lower afterTest h_support (by omega)
          h_next_le_after
      have h_test_support := randomModTest_usesRandomInputsIn formulas lower
        nextRandom h_lower h_support
      rw [h_test] at h_test_support
      let leftProperty : (Fin formulas.length → Bool) → Prop := fun mask =>
        ProbabilisticACCFormula.eval test inputs
          (initialBits ++ List.ofFn mask) = true
      let property :
          (Fin (formulas.length +
            randomTestBitCount formulas.length count) → Bool) → Prop :=
        fun freshAssignment =>
          ∀ output ∈ test :: tests,
            ProbabilisticACCFormula.eval output inputs
              (initialBits ++ List.ofFn freshAssignment) = true
      have h_split := BoolAssignments.card_filter_append_le_of_left
        formulas.length (randomTestBitCount formulas.length count)
        (2 ^ (count * (formulas.length - 1))) leftProperty property (by
          intro mask
          let afterMask := initialBits ++ List.ofFn mask
          have h_afterMask_length : afterMask.length = afterTest := by
            simp [afterMask, h_initial_length]
            omega
          have h_nonzero_after : ∃ i : Fin formulas.length,
              ProbabilisticACCFormula.eval (formulas.get i) inputs
                afterMask = true := by
            obtain ⟨i, h_i⟩ := h_nonzero
            refine ⟨i, ?_⟩
            have h_fixed := eval_append_fresh_eq (formulas.get i) lower
              nextRandom inputs initialBits (List.ofFn mask) h_initial_length
              (h_support (formulas.get i) (List.get_mem formulas i))
            simpa [afterMask] using h_fixed.trans h_i
          have h_tail_bound := ih afterTest afterMask h_afterMask_length
            (h_lower.trans h_next_le_after) h_formulas_after h_nonzero_after
          rw [h_tests] at h_tail_bound
          by_cases h_head : leftProperty mask
          · simp only [h_head, if_true]
            apply Nat.le_trans (Finset.card_le_card ?_) h_tail_bound
            intro tailAssignment h_tailAssignment
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              at h_tailAssignment ⊢
            intro output h_output
            have h_all := h_tailAssignment output (by simp [h_output])
            simpa [property, afterMask, ofFn_append, List.append_assoc] using h_all
          · simp only [h_head, if_false, Nat.le_zero]
            rw [Finset.card_filter_eq_zero_iff]
            intro tailAssignment _ h_tailAssignment
            have h_head_full := h_tailAssignment test (by simp)
            have h_fixed := eval_append_fresh_eq test lower afterTest inputs
              afterMask (List.ofFn tailAssignment) h_afterMask_length
              h_test_support
            have h_head_full' :
                ProbabilisticACCFormula.eval test inputs
                  (afterMask ++ List.ofFn tailAssignment) = true := by
              simpa [afterMask, ofFn_append, List.append_assoc] using h_head_full
            apply h_head
            simpa [leftProperty] using h_fixed.symm.trans h_head_full')
      have h_first := randomModTest_accepting_card_mul_two_le hp formulas
        lower nextRandom inputs initialBits h_initial_length h_support h_nonzero
      rw [h_test] at h_first
      have h_length_pos : 0 < formulas.length := by
        obtain ⟨i, _⟩ := h_nonzero
        exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      have h_pow_split :
          2 ^ formulas.length = 2 ^ (formulas.length - 1) * 2 := by
        conv_lhs => rw [show formulas.length = formulas.length - 1 + 1 by omega]
        rw [pow_succ]
      have h_first_half :
          ((Finset.univ : Finset (Fin formulas.length → Bool)).filter
            leftProperty).card ≤ 2 ^ (formulas.length - 1) := by
        rw [h_pow_split] at h_first
        simpa [leftProperty] using Nat.le_of_mul_le_mul_right h_first
      have h_product :
          ((Finset.univ : Finset (Fin formulas.length → Bool)).filter
              leftProperty).card *
              2 ^ (count * (formulas.length - 1)) ≤
            2 ^ (formulas.length - 1) *
              2 ^ (count * (formulas.length - 1)) :=
        Nat.mul_le_mul_right _ h_first_half
      have h_bound := h_split.trans h_product
      have h_exponent :
          (count + 1) * (formulas.length - 1) =
            (formulas.length - 1) + count * (formulas.length - 1) := by
        simp only [Nat.add_mul, one_mul, Nat.add_comm]
      simp only [randomTestBitCount, randomModTests, h_test, h_tests]
      change
        ((Finset.univ : Finset
            (Fin (formulas.length +
              randomTestBitCount formulas.length count) → Bool)).filter
          property).card ≤ 2 ^ ((count + 1) * (formulas.length - 1))
      rw [h_exponent, pow_add]
      exact h_bound

/-- A unary modulo gate is Boolean negation when the modulus exceeds one. -/
theorem eval_modGate_singleton {p : Nat} (hp : 1 < p)
    (formula : ProbabilisticACCFormula p) (inputs randomBits : List Bool) :
    ProbabilisticACCFormula.eval (.modGate [formula]) inputs randomBits =
      !(ProbabilisticACCFormula.eval formula inputs randomBits) := by
  cases h_eval : ProbabilisticACCFormula.eval formula inputs randomBits <;>
    simp [ProbabilisticACCFormula.eval, h_eval, Nat.mod_eq_of_lt hp]

/-- The amplified OR gadget is false exactly when all of its random modulo
tests accept. -/
theorem approximateOr_eval_false_iff {p : Nat} (hp : 1 < p)
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions nextRandom : Nat) (inputs randomBits : List Bool) :
    ProbabilisticACCFormula.eval
        (approximateOr formulas repetitions nextRandom).1 inputs randomBits =
        false ↔
      ∀ test ∈ (randomModTests formulas repetitions nextRandom).1,
        ProbabilisticACCFormula.eval test inputs randomBits = true := by
  rcases h_tests : randomModTests formulas repetitions nextRandom with
    ⟨tests, finalRandom⟩
  simp only [approximateOr, h_tests]
  rw [eval_modGate_singleton hp]
  rw [← eval_andGate_eq_true_iff tests inputs randomBits]
  cases ProbabilisticACCFormula.eval (.andGate tests) inputs randomBits <;>
    decide

/-- If at least one child is true, the amplified OR gadget is false on at
most a `2⁻ʳ` fraction of its fresh mask assignments. -/
theorem approximateOr_false_card_le {p : Nat} (hp : 1 < p)
    (formulas : List (ProbabilisticACCFormula p))
    (repetitions lower nextRandom : Nat) (inputs initialBits : List Bool)
    (h_initial_length : initialBits.length = nextRandom)
    (h_lower : lower ≤ nextRandom)
    (h_support : ∀ formula ∈ formulas,
      formula.UsesRandomInputsIn lower nextRandom)
    (h_nonzero : ∃ i : Fin formulas.length,
      ProbabilisticACCFormula.eval (formulas.get i) inputs initialBits = true) :
    ((Finset.univ : Finset
        (Fin (randomTestBitCount formulas.length repetitions) → Bool)).filter
      fun freshAssignment =>
        ProbabilisticACCFormula.eval
          (approximateOr formulas repetitions nextRandom).1 inputs
            (initialBits ++ List.ofFn freshAssignment) = false).card ≤
      2 ^ (repetitions * (formulas.length - 1)) := by
  have h_bound := randomModTests_all_true_card_le hp formulas repetitions
    lower nextRandom inputs initialBits h_initial_length h_lower h_support
    h_nonzero
  have h_sets :
      (Finset.univ.filter fun freshAssignment :
          Fin (randomTestBitCount formulas.length repetitions) → Bool =>
        ProbabilisticACCFormula.eval
          (approximateOr formulas repetitions nextRandom).1 inputs
            (initialBits ++ List.ofFn freshAssignment) = false) =
      (Finset.univ.filter fun freshAssignment =>
        ∀ test ∈ (randomModTests formulas repetitions nextRandom).1,
          ProbabilisticACCFormula.eval test inputs
            (initialBits ++ List.ofFn freshAssignment) = true) := by
    ext freshAssignment
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact approximateOr_eval_false_iff hp formulas repetitions nextRandom
      inputs (initialBits ++ List.ofFn freshAssignment)
  rw [h_sets]
  exact h_bound


end Circuits.ACC.ACCFormula
