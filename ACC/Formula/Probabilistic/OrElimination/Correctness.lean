import ACC.Formula.Probabilistic.OrElimination.Construction

namespace Circuits.ACC.ACCFormula

open ProbabilisticACCFormula

/-! ## Correctness and error bounds for OR-gate elimination -/

/-- An OR gate is true exactly when at least one child is true. -/
theorem eval_orGate_eq_true_iff {p : Nat} (formulas : List (ACCFormula p))
    (inputs : List Bool) :
    ACCFormula.eval (.orGate formulas) inputs = true ↔
      ∃ formula ∈ formulas, ACCFormula.eval formula inputs = true := by
  simp [ACCFormula.eval, List.any_eq_true]

/-- Assignments to the fresh block on which state-threaded OR elimination
disagrees with its source formula. -/
def eliminateOrGatesAuxErrorAssignments {p : Nat} (repetitions : Nat)
    (formula : ACCFormula p) (nextRandom : Nat) (inputs initialBits : List Bool) :
    Finset (Fin (orEliminationRandomBitCountAux repetitions formula) → Bool) :=
  Finset.univ.filter fun freshAssignment =>
    ProbabilisticACCFormula.eval
        (eliminateOrGatesAux repetitions formula nextRandom).1 inputs
          (initialBits ++ List.ofFn freshAssignment) ≠
      ACCFormula.eval formula inputs

/-- Assignments on which the transformed and source child-value lists
disagree. -/
def eliminateOrGatesListAuxErrorAssignments {p : Nat} (repetitions : Nat)
    (formulas : List (ACCFormula p)) (nextRandom : Nat)
    (inputs initialBits : List Bool) :
    Finset
      (Fin (orEliminationRandomBitCountListAux repetitions formulas) → Bool) :=
  Finset.univ.filter fun freshAssignment =>
    (eliminateOrGatesListAux repetitions formulas nextRandom).1.map
        (fun formula => ProbabilisticACCFormula.eval formula inputs
          (initialBits ++ List.ofFn freshAssignment)) ≠
      formulas.map (fun formula => ACCFormula.eval formula inputs)

mutual

/-- Global finite union bound for state-threaded OR elimination.  Multiplying
the error count by `2^repetitions` avoids truncated natural division and says
directly that the error probability is at most
`formula.nodeCount / 2^repetitions`. -/
theorem eliminateOrGatesAux_error_card_mul_pow_le {p : Nat} (hp : 1 < p)
    (repetitions : Nat) (formula : ACCFormula p) (nextRandom : Nat)
    (inputs initialBits : List Bool) (h_initial_length : initialBits.length = nextRandom)
    (h_formula : HasOnlyOrAndModGates formula) :
    (eliminateOrGatesAuxErrorAssignments repetitions formula nextRandom inputs
        initialBits).card * 2 ^ repetitions ≤
      formula.nodeCount *
        2 ^ orEliminationRandomBitCountAux repetitions formula := by
  classical
  match formula with
  | .input idx negated =>
      simp only [eliminateOrGatesAuxErrorAssignments,
        orEliminationRandomBitCountAux, eliminateOrGatesAux,
        ACCFormula.eval, ACCFormula.nodeCount,
        ProbabilisticACCFormula.eval, pow_zero, Nat.mul_one]
      simp only [ne_eq, eq_self, not_true_eq_false, Finset.filter_false,
        Finset.card_empty, zero_mul, Nat.zero_le]
  | .constant value label =>
      simp only [eliminateOrGatesAuxErrorAssignments,
        orEliminationRandomBitCountAux, eliminateOrGatesAux,
        ACCFormula.eval, ACCFormula.nodeCount,
        ProbabilisticACCFormula.eval, pow_zero, Nat.mul_one]
      simp only [ne_eq, eq_self, not_true_eq_false, Finset.filter_false,
        Finset.card_empty, zero_mul, Nat.zero_le]
  | .notGate child =>
      simp [HasOnlyOrAndModGates, HasNoNotGates] at h_formula
  | .andGate children => simp [HasOnlyOrAndModGates, HasNoAndGates] at h_formula
  | .orGate children =>
      simp only [HasOnlyOrAndModGates, HasNoAndGates, HasNoNotGates]
        at h_formula
      let childBits := orEliminationRandomBitCountListAux repetitions children
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, afterChildren⟩
      let maskBits := repetitions * children.length
      have h_after := eliminateOrGatesListAux_finalRandom repetitions children
        nextRandom
      rw [h_children] at h_after
      change afterChildren = nextRandom + childBits at h_after
      have h_length := eliminateOrGatesListAux_length repetitions children
        nextRandom
      rw [h_children] at h_length
      change transformed.length = children.length at h_length
      have h_children_support :=
        eliminateOrGatesListAux_usesRandomInputsIn repetitions children
          nextRandom
      rw [h_children] at h_children_support
      have h_children_bound :=
        eliminateOrGatesListAux_error_card_mul_pow_le hp repetitions children
          nextRandom inputs initialBits h_initial_length (by
            intro child h_child
            exact ⟨h_formula.1 child h_child, h_formula.2 child h_child⟩)
      let childError : (Fin childBits → Bool) → Prop := fun assignment =>
        transformed.map (fun child => ProbabilisticACCFormula.eval child inputs
          (initialBits ++ List.ofFn assignment)) ≠
        children.map (fun child => ACCFormula.eval child inputs)
      let property : (Fin (childBits + maskBits) → Bool) → Prop :=
        fun assignment =>
          ProbabilisticACCFormula.eval
              (approximateOr transformed repetitions afterChildren).1 inputs
                (initialBits ++ List.ofFn assignment) ≠
            ACCFormula.eval (.orGate children) inputs
      have h_composed :=
        BoolAssignments.card_filter_append_mul_le_with_left_exceptions
          childBits maskBits (2 ^ repetitions) (2 ^ maskBits)
          childError property (by
            intro childAssignment h_child_correct
            let afterChildBits := initialBits ++ List.ofFn childAssignment
            have h_afterChildBits_length : afterChildBits.length = afterChildren := by
              simp [afterChildBits, h_initial_length, h_after, childBits]
            have h_values :
                transformed.map (fun child =>
                  ProbabilisticACCFormula.eval child inputs afterChildBits) =
                  children.map (fun child => ACCFormula.eval child inputs) := by
              simpa [childError, afterChildBits] using
                not_ne_iff.mp h_child_correct
            by_cases h_source : ACCFormula.eval (.orGate children) inputs = false
            · have h_transformed_false : ∀ child ∈ transformed,
                ProbabilisticACCFormula.eval child inputs afterChildBits = false := by
                intro child h_child
                by_contra h_true
                have h_child_true :
                    ProbabilisticACCFormula.eval child inputs afterChildBits = true := by
                  cases h_eval :
                      ProbabilisticACCFormula.eval child inputs afterChildBits
                  · exact False.elim (h_true h_eval)
                  · rfl
                have h_source_any :
                    ∃ sourceChild ∈ children,
                      ACCFormula.eval sourceChild inputs = true := by
                  have h_mem : true ∈ transformed.map (fun output =>
                      ProbabilisticACCFormula.eval output inputs afterChildBits) := by
                    exact List.mem_map.mpr ⟨child, h_child, h_child_true⟩
                  rw [h_values] at h_mem
                  simpa using h_mem
                have h_gate_true :=
                  (eval_orGate_eq_true_iff children inputs).2 h_source_any
                exact Bool.noConfusion (h_source.symm.trans h_gate_true)
              have h_zero :
                  ((Finset.univ : Finset (Fin maskBits → Bool)).filter
                    fun maskAssignment =>
                      property (Fin.append childAssignment maskAssignment)).card =
                    0 := by
                rw [Finset.card_filter_eq_zero_iff]
                intro maskAssignment _ h_error
                have h_exact := approximateOr_eval_false_of_children_false hp
                  transformed repetitions afterChildren inputs
                    (afterChildBits ++ List.ofFn maskAssignment) (by
                      intro child h_child
                      have h_fixed := eval_append_fresh_eq child nextRandom
                        afterChildren inputs afterChildBits
                          (List.ofFn maskAssignment) h_afterChildBits_length
                          (h_children_support child h_child)
                      exact h_fixed.trans
                        (h_transformed_false child h_child))
                apply h_error
                simpa [property, afterChildBits, ofFn_append,
                  List.append_assoc, h_source] using h_exact
              rw [h_zero]
              simp
            · have h_source_true := Bool.eq_true_of_not_eq_false h_source
              have h_nonzero : ∃ i : Fin transformed.length,
                    ProbabilisticACCFormula.eval (transformed.get i) inputs
                      afterChildBits = true := by
                  have h_source_any :=
                    (eval_orGate_eq_true_iff children inputs).1 h_source_true
                  obtain ⟨sourceChild, h_sourceChild, h_sourceTrue⟩ := h_source_any
                  have h_mem : true ∈ children.map (fun child =>
                      ACCFormula.eval child inputs) :=
                    List.mem_map.mpr
                      ⟨sourceChild, h_sourceChild, h_sourceTrue⟩
                  rw [← h_values] at h_mem
                  obtain ⟨child, h_child, h_child_true⟩ := List.mem_map.mp h_mem
                  obtain ⟨i, h_i⟩ := List.get_of_mem h_child
                  refine ⟨i, ?_⟩
                  rw [h_i]
                  exact h_child_true
              have h_local := approximateOr_false_card_le hp transformed
                repetitions nextRandom afterChildren inputs afterChildBits
                h_afterChildBits_length (by omega) h_children_support h_nonzero
              rw [randomTestBitCount_eq] at h_local
              have h_maskLength :
                  repetitions * transformed.length = maskBits := by
                simp [maskBits, h_length]
              let castMask : (Fin maskBits → Bool) →
                  (Fin (repetitions * transformed.length) → Bool) :=
                fun assignment i => assignment (Fin.cast h_maskLength i)
              have h_card_transformed :
                  ((Finset.univ : Finset (Fin maskBits → Bool)).filter
                    fun maskAssignment =>
                      property (Fin.append childAssignment maskAssignment)).card ≤
                    2 ^ (repetitions * (transformed.length - 1)) := by
                apply (Finset.card_le_card_of_injOn castMask ?_ ?_).trans h_local
                · intro maskAssignment h_error
                  simp only [property] at h_error ⊢
                  have h_error_false :
                      ProbabilisticACCFormula.eval
                        (approximateOr transformed repetitions afterChildren).1
                          inputs (afterChildBits ++ List.ofFn maskAssignment) =
                            false := by
                    cases h_eval : ProbabilisticACCFormula.eval
                        (approximateOr transformed repetitions afterChildren).1
                          inputs (afterChildBits ++ List.ofFn maskAssignment) <;>
                      simp_all [afterChildBits, List.append_assoc]
                  simpa [castMask, afterChildBits, h_maskLength] using
                    h_error_false
                · intro left _ right _ h_equal
                  funext i
                  have h_at := congrFun h_equal (Fin.cast h_maskLength.symm i)
                  simpa [castMask] using h_at
              have h_card :
                  ((Finset.univ : Finset (Fin maskBits → Bool)).filter
                    fun maskAssignment =>
                      property (Fin.append childAssignment maskAssignment)).card ≤
                    2 ^ (repetitions * (children.length - 1)) := by
                simpa [h_length] using h_card_transformed
              have h_length_pos : 0 < children.length := by
                obtain ⟨i, _⟩ := h_nonzero
                rw [← h_length]
                exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
              calc
                _ ≤ 2 ^ (repetitions * (children.length - 1)) *
                      2 ^ repetitions := Nat.mul_le_mul_right _ h_card
                _ = 2 ^ maskBits := by
                  rw [← pow_add]
                  congr 1
                  simp only [maskBits]
                  have h_decompose :
                      children.length = children.length - 1 + 1 := by
                    omega
                  conv_rhs => rw [h_decompose]
                  simp [Nat.mul_add])
      have h_child_set :
          (Finset.univ.filter childError).card =
            (eliminateOrGatesListAuxErrorAssignments repetitions children
              nextRandom inputs initialBits).card := by
        simp [childError, eliminateOrGatesListAuxErrorAssignments, h_children,
          childBits]
      rw [h_child_set] at h_composed
      have h_child_term :
          (eliminateOrGatesListAuxErrorAssignments repetitions children
              nextRandom inputs initialBits).card * 2 ^ maskBits *
                2 ^ repetitions ≤
            ((children.map ACCFormula.nodeCount).sum * 2 ^ childBits) *
              2 ^ maskBits := by
        calc
          _ = ((eliminateOrGatesListAuxErrorAssignments repetitions children
                nextRandom inputs initialBits).card * 2 ^ repetitions) *
                2 ^ maskBits := by ac_rfl
          _ ≤ ((children.map ACCFormula.nodeCount).sum * 2 ^ childBits) *
                2 ^ maskBits := Nat.mul_le_mul_right _ h_children_bound
      have h_bound := h_composed.trans
        (Nat.add_le_add h_child_term (le_refl _))
      simp only [eliminateOrGatesAuxErrorAssignments, eliminateOrGatesAux,
        h_children, orEliminationRandomBitCountAux]
      change
        (Finset.univ.filter property).card * 2 ^ repetitions ≤
          ACCFormula.nodeCount (.orGate children) *
            2 ^ (childBits + maskBits)
      rw [ACCFormula.nodeCount, pow_add]
      exact h_bound.trans_eq (by ring)
  | .modGate children =>
      simp only [HasOnlyOrAndModGates, HasNoAndGates, HasNoNotGates]
        at h_formula
      rcases h_children : eliminateOrGatesListAux repetitions children
          nextRandom with ⟨transformed, finalRandom⟩
      have h_list := eliminateOrGatesListAux_error_card_mul_pow_le hp
        repetitions children nextRandom inputs initialBits h_initial_length
        (by
          intro child h_child
          exact ⟨h_formula.1 child h_child, h_formula.2 child h_child⟩)
      let formulaErrors : Finset
          (Fin (orEliminationRandomBitCountListAux repetitions children) → Bool) :=
        Finset.univ.filter fun assignment =>
          ProbabilisticACCFormula.eval (.modGate transformed) inputs
              (initialBits ++ List.ofFn assignment) ≠
            ACCFormula.eval (.modGate children) inputs
      let listErrors : Finset
          (Fin (orEliminationRandomBitCountListAux repetitions children) → Bool) :=
        Finset.univ.filter fun assignment =>
          transformed.map (fun child => ProbabilisticACCFormula.eval child
              inputs (initialBits ++ List.ofFn assignment)) ≠
            children.map (fun child => ACCFormula.eval child inputs)
      have h_formula_card :
          (eliminateOrGatesAuxErrorAssignments repetitions (.modGate children)
              nextRandom inputs initialBits).card = formulaErrors.card := by
        simp [eliminateOrGatesAuxErrorAssignments, formulaErrors,
          orEliminationRandomBitCountAux, eliminateOrGatesAux, h_children]
        rfl
      have h_list_card :
          (eliminateOrGatesListAuxErrorAssignments repetitions children
              nextRandom inputs initialBits).card = listErrors.card := by
        simp [eliminateOrGatesListAuxErrorAssignments, listErrors, h_children]
      have h_subset : formulaErrors ⊆ listErrors := by
        intro assignment h_assignment
        simp only [formulaErrors, listErrors, Finset.mem_filter,
          Finset.mem_univ, true_and]
          at h_assignment ⊢
        intro h_values
        apply h_assignment
        simp [ProbabilisticACCFormula.eval, ACCFormula.eval, h_values]
      have h_card :
          (eliminateOrGatesAuxErrorAssignments repetitions (.modGate children)
              nextRandom inputs initialBits).card ≤
            (eliminateOrGatesListAuxErrorAssignments repetitions children
              nextRandom inputs initialBits).card := by
        rw [h_formula_card, h_list_card]
        exact Finset.card_le_card h_subset
      calc
        _ ≤ (eliminateOrGatesListAuxErrorAssignments repetitions children
              nextRandom inputs initialBits).card * 2 ^ repetitions :=
          Nat.mul_le_mul_right _ h_card
        _ ≤ (children.map ACCFormula.nodeCount).sum *
              2 ^ orEliminationRandomBitCountListAux repetitions children := h_list
        _ ≤ ACCFormula.nodeCount (.modGate children) *
              2 ^ orEliminationRandomBitCountAux repetitions
                (.modGate children) := by
          simp only [ACCFormula.nodeCount, orEliminationRandomBitCountAux]
          exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- List-valued global union bound used in the gate cases. -/
theorem eliminateOrGatesListAux_error_card_mul_pow_le {p : Nat} (hp : 1 < p)
    (repetitions : Nat) (formulas : List (ACCFormula p)) (nextRandom : Nat)
    (inputs initialBits : List Bool) (h_initial_length : initialBits.length = nextRandom)
    (h_formulas : ∀ formula ∈ formulas, HasOnlyOrAndModGates formula) :
    (eliminateOrGatesListAuxErrorAssignments repetitions formulas nextRandom
        inputs initialBits).card * 2 ^ repetitions ≤
      (formulas.map ACCFormula.nodeCount).sum *
        2 ^ orEliminationRandomBitCountListAux repetitions formulas := by
  classical
  match formulas with
  | [] =>
      change ((Finset.univ : Finset (Fin 0 → Bool)).filter
        (fun _ => False)).card * 2 ^ repetitions ≤ 0
      simp
  | formula :: formulas =>
      let headBits := orEliminationRandomBitCountAux repetitions formula
      let tailBits := orEliminationRandomBitCountListAux repetitions formulas
      rcases h_head : eliminateOrGatesAux repetitions formula nextRandom with
        ⟨transformed, afterFormula⟩
      rcases h_tail : eliminateOrGatesListAux repetitions formulas afterFormula with
        ⟨transformedTail, finalRandom⟩
      have h_after := eliminateOrGatesAux_finalRandom repetitions formula
        nextRandom
      rw [h_head] at h_after
      change afterFormula = nextRandom + headBits at h_after
      have h_head_support := eliminateOrGatesAux_usesRandomInputsIn repetitions
        formula nextRandom
      rw [h_head] at h_head_support
      have h_head_bound := eliminateOrGatesAux_error_card_mul_pow_le hp
        repetitions formula nextRandom inputs initialBits h_initial_length
        (h_formulas formula (by simp))
      let headError : (Fin headBits → Bool) → Prop := fun assignment =>
        ProbabilisticACCFormula.eval transformed inputs
            (initialBits ++ List.ofFn assignment) ≠
          ACCFormula.eval formula inputs
      let property : (Fin (headBits + tailBits) → Bool) → Prop :=
        fun assignment =>
          (transformed :: transformedTail).map (fun output =>
            ProbabilisticACCFormula.eval output inputs
              (initialBits ++ List.ofFn assignment)) ≠
            (formula :: formulas).map (fun source => ACCFormula.eval source inputs)
      have h_composed :=
        BoolAssignments.card_filter_append_mul_le_with_left_exceptions
          headBits tailBits (2 ^ repetitions)
          ((formulas.map ACCFormula.nodeCount).sum * 2 ^ tailBits)
          headError property (by
            intro headAssignment h_head_correct
            let afterHeadBits := initialBits ++ List.ofFn headAssignment
            have h_afterHeadBits_length : afterHeadBits.length = afterFormula := by
              simp [afterHeadBits, h_initial_length, h_after, headBits]
            have h_tail_bound :=
              eliminateOrGatesListAux_error_card_mul_pow_le hp repetitions
                formulas afterFormula inputs afterHeadBits
                h_afterHeadBits_length (by
                  intro child h_child
                  exact h_formulas child (by simp [h_child]))
            simp only [eliminateOrGatesListAuxErrorAssignments, h_tail]
              at h_tail_bound
            apply (Nat.mul_le_mul_right (2 ^ repetitions)
              (Finset.card_le_card ?_)).trans h_tail_bound
            intro tailAssignment h_error
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, property]
              at h_error ⊢
            have h_fixed := eval_append_fresh_eq transformed nextRandom
              afterFormula inputs afterHeadBits (List.ofFn tailAssignment)
              h_afterHeadBits_length h_head_support
            have h_head_eq :
                ProbabilisticACCFormula.eval transformed inputs
                    (afterHeadBits ++ List.ofFn tailAssignment) =
                  ACCFormula.eval formula inputs := by
              exact h_fixed.trans (not_ne_iff.mp h_head_correct)
            have h_head_eq' :
                ProbabilisticACCFormula.eval transformed inputs
                    (initialBits ++ List.ofFn
                      (Fin.append headAssignment tailAssignment)) =
                  ACCFormula.eval formula inputs := by
              simpa [afterHeadBits, ofFn_append, List.append_assoc] using
                h_head_eq
            intro h_tail_eq
            apply h_error
            simp only [List.map_cons, List.cons.injEq]
            constructor
            · exact h_head_eq'
            · simpa [afterHeadBits, ofFn_append, List.append_assoc] using
                h_tail_eq)
      have h_head_set :
          (Finset.univ.filter headError).card =
            (eliminateOrGatesAuxErrorAssignments repetitions formula nextRandom
              inputs initialBits).card := by
        simp [headError, eliminateOrGatesAuxErrorAssignments, h_head, headBits]
      rw [h_head_set] at h_composed
      have h_head_term :
          (eliminateOrGatesAuxErrorAssignments repetitions formula nextRandom
              inputs initialBits).card * 2 ^ tailBits * 2 ^ repetitions ≤
            (formula.nodeCount * 2 ^ headBits) * 2 ^ tailBits := by
        calc
          _ = ((eliminateOrGatesAuxErrorAssignments repetitions formula
                nextRandom inputs initialBits).card * 2 ^ repetitions) *
              2 ^ tailBits := by ac_rfl
          _ ≤ (formula.nodeCount * 2 ^ headBits) * 2 ^ tailBits :=
            Nat.mul_le_mul_right _ h_head_bound
      have h_bound := h_composed.trans
        (Nat.add_le_add h_head_term (le_refl _))
      simp only [eliminateOrGatesListAuxErrorAssignments,
        eliminateOrGatesListAux, h_head, h_tail,
        orEliminationRandomBitCountListAux, List.map_cons, List.sum_cons]
      change
        (Finset.univ.filter property).card * 2 ^ repetitions ≤
          (formula.nodeCount + (formulas.map ACCFormula.nodeCount).sum) *
            2 ^ (headBits + tailBits)
      rw [pow_add]
      exact h_bound.trans_eq (by ring)

end

/-- Public error-count form of the recursive union bound. -/
theorem eliminateOrGates_errorCount_mul_pow_le {p : Nat} (hp : 1 < p)
    (repetitions : Nat) (formula : ACCFormula p) (inputs : List Bool)
    (h_formula : HasOnlyOrAndModGates formula) :
    ProbabilisticACCFormula.errorCount (eliminateOrGates repetitions formula)
        (eliminateOrGatesRandomBitCount repetitions formula) inputs
        (ACCFormula.eval formula inputs) * 2 ^ repetitions ≤
      formula.nodeCount *
        2 ^ eliminateOrGatesRandomBitCount repetitions formula := by
  have h_bound := eliminateOrGatesAux_error_card_mul_pow_le hp repetitions
    formula 0 inputs [] (by simp) h_formula
  change
    (eliminateOrGatesAuxErrorAssignments repetitions formula 0 inputs []).card *
        2 ^ repetitions ≤
      formula.nodeCount *
        2 ^ orEliminationRandomBitCountAux repetitions formula
  exact h_bound

/-- OR elimination has global error probability at most
`nodeCount / 2^repetitions`. -/
theorem eliminateOrGates_errorProbability_le {p : Nat} (hp : 1 < p)
    (repetitions : Nat) (formula : ACCFormula p) (inputs : List Bool)
    (h_formula : HasOnlyOrAndModGates formula) :
    ProbabilisticACCFormula.errorProbability
        (eliminateOrGates repetitions formula)
        (eliminateOrGatesRandomBitCount repetitions formula) inputs
        (ACCFormula.eval formula inputs) ≤
      (formula.nodeCount : ℚ) / 2 ^ repetitions := by
  unfold ProbabilisticACCFormula.errorProbability
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  exact eliminateOrGates_errorCount_mul_pow_le hp repetitions formula inputs
    h_formula

end Circuits.ACC.ACCFormula
