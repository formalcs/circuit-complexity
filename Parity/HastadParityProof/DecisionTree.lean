/-
  Decision-tree and depth-one/depth-two collapse infrastructure.

  This module is part of the Håstad parity lower-bound proof.
-/

import Parity.HastadParityProof.SwitchingRound
import Formulas.CnfDnf.Dual

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open Circuits.CnfDnf.Families
open Circuits.CnfDnf.Restrictions
open UnboundedFanInFormula

set_option linter.style.longLine false

/-! ### Iterated switching over formula depth

    Phrased *post*-parameter-choice: given that all the analytic
    inequalities `pᵢ < 1` for the union bound have already been met,
    produce a deterministic restriction and a narrow DNF on the live
    coordinates that agrees with the original formula on every input
    compatible with the restriction.

    The threshold hypotheses package the analytic preconditions supplied by
    the parameter lemmas. The proof executes the inductive depth reduction
    (depth `d` → `d−1` → … → `1`), at each step using
    `exists_switching_lemma_pigeonhole_list` to fix one layer at once and a
    canonical decision-tree representation to fold the result into the next
    layer up.

    #### Decomposition

    `exists_iterated_switching_depth_collapse` is the analytic heart of the
    iterated restriction argument.  We decompose it into three sub-lemmas:

    * **Base:** `exists_depth_one_collapse` turns a depth-at-most-one AC0
      formula under the switching threshold into a narrow DNF (modulo
      possibly fixing one input to make `dnfWidth < live.length`).
    * **Step:** `exists_switching_depth_reduction` shows that a depth-`(d+1)`
      AC0 formula on `n ≥ 2` inputs is equivalent to a depth-≤-`d` AC0
      formula on `live.length ≥ 2` live inputs after fixing the
      remaining inputs to `deadBits`.  This is where one round of
      the switching lemma is invoked, folding the bottom layer's
      width-bounded DNF into the layer above.
    * **Composition:** `exists_composed_collapse` combines an outer
      restriction `(live₁, dead₁)` with an inner restriction
      `(live₂, dead₂)` on the live coordinates into a single
      restriction on the original `n` inputs.

    The wiring is then a straightforward induction on `d`
    using `Nat.le_induction` starting at `d = 1`. -/

/-! ### Helper eval lemmas for andGate/orGate -/

/-- An `andGate` evaluates to `false` if any one of its gates evaluates to `false`. -/
lemma andGate_eval_zero_of_mem_zero
    (gates : List UnboundedFanInFormula) (inputs : List Bool)
    (g₀ : UnboundedFanInFormula) (hg₀_mem : g₀ ∈ gates)
    (hg₀_eval : ufiFormulaEval g₀ inputs = false) :
    ufiFormulaEval (UnboundedFanInFormula.andGate gates) inputs = false := by
  induction gates with
  | nil => exact absurd hg₀_mem List.not_mem_nil
  | cons g rest ih =>
    rcases List.mem_cons.mp hg₀_mem with rfl | hg₀_in_rest
    · simp only [ufiFormulaEval, hg₀_eval]
    · simp only [ufiFormulaEval]
      cases h_g : ufiFormulaEval g inputs with
      | false => rfl
      | true => exact ih hg₀_in_rest

/-- An `orGate` evaluates to `true` if any one of its gates evaluates to `true`. -/
lemma orGate_eval_one_of_mem_one
    (gates : List UnboundedFanInFormula) (inputs : List Bool)
    (g₀ : UnboundedFanInFormula) (hg₀_mem : g₀ ∈ gates)
    (hg₀_eval : ufiFormulaEval g₀ inputs = true) :
    ufiFormulaEval (UnboundedFanInFormula.orGate gates) inputs = true := by
  induction gates with
  | nil => exact absurd hg₀_mem List.not_mem_nil
  | cons g rest ih =>
    rcases List.mem_cons.mp hg₀_mem with rfl | hg₀_in_rest
    · simp only [ufiFormulaEval, hg₀_eval]
    · simp only [ufiFormulaEval]
      cases h_g : ufiFormulaEval g inputs with
      | true => rfl
      | false => exact ih hg₀_in_rest

/-- An `andGate` evaluates to `true` if every gate evaluates to `true`. -/
lemma andGate_eval_one_of_all_one
    (gates : List UnboundedFanInFormula) (inputs : List Bool)
    (h : ∀ g ∈ gates, ufiFormulaEval g inputs = true) :
    ufiFormulaEval (UnboundedFanInFormula.andGate gates) inputs = true := by
  induction gates with
  | nil => simp only [ufiFormulaEval]
  | cons g rest ih =>
    simp only [ufiFormulaEval]
    rw [h g List.mem_cons_self]
    exact ih (fun g' hg' => h g' (List.mem_cons.mpr (Or.inr hg')))

/-- An `orGate` evaluates to `false` if every gate evaluates to `false`. -/
lemma orGate_eval_zero_of_all_zero
    (gates : List UnboundedFanInFormula) (inputs : List Bool)
    (h : ∀ g ∈ gates, ufiFormulaEval g inputs = false) :
    ufiFormulaEval (UnboundedFanInFormula.orGate gates) inputs = false := by
  induction gates with
  | nil => simp only [ufiFormulaEval]
  | cons g rest ih =>
    simp only [ufiFormulaEval]
    rw [h g List.mem_cons_self]
    exact ih (fun g' hg' => h g' (List.mem_cons.mpr (Or.inr hg')))

/-- The singleton OR-of-AND-of-`g` wrapper evaluates exactly as `g`. -/
lemma eval_or_and_singleton_base (g : UnboundedFanInFormula) (xs : List Bool) :
    ufiFormulaEval
        (UnboundedFanInFormula.orGate [UnboundedFanInFormula.andGate [g]]) xs
      = ufiFormulaEval g xs := by
  simp only [ufiFormulaEval]
  cases ufiFormulaEval g xs <;> rfl

/-- Value of `assembleInput` at any in-range index. -/
lemma assembleInput_get_at
    (n : Nat) (live : List Nat) (liveBits deadBits : List Bool)
    (i : Nat) (hi : i < n) :
    (assembleInput n live liveBits deadBits)[i]? =
      some (assembleInputFn live liveBits deadBits i) := by
  rw [assembleInput_eq_map]
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-- A depth-at-most-one AC0 formula satisfying the switching threshold
    collapses to a narrow DNF on some `≥ 2`-element live set.  The threshold
    and `2 ≤ t` imply the `3 ≤ n` bound used in the construction.

    The proof is a complete case analysis on the root constructor:

    * An `inputGate i b` is reindexed to input `0` on the two-element live
      list `[i, other]`, producing a one-literal DNF of width one.
    * A `constant` is represented by one of the canonical width-zero DNFs:
      `orGate []` for false and `orGate [andGate []]` for true.
    * A `notGate` contradicts strict alternating leveling, which permits
      negation only through the polarity bit stored in `inputGate`.
    * At an `andGate` or `orGate`, the depth bound forces every child to be
      an input or constant.  If a child already forces the root's value, the
      target is the corresponding constant DNF.  Otherwise, an input child is
      removed from the live set and assigned a value that forces the root; if
      no such child exists, the child classification and global input bound
      show that every child has the opposite constant value.  Removing one
      input leaves `n - 1 ≥ 2` live inputs.

    Thus the only nonconstant target is the one-literal DNF used for an input
    root; every AND/OR branch has width zero.  This stronger construction
    immediately supplies `w < live.length`. -/
lemma exists_depth_one_collapse
      {c k n : Nat}
      (formula : LeveledUFIFormulaOfSizePolyNAndDepthD n c k 1)
      (t : Nat)
      (ht : 2 ≤ t)
      (h_thresh : 20 * t * (t + 1) ≤ n) :
  ∃ (live : List Nat)
    (_h_live_lt : ∀ v ∈ live, v < n)
    (_h_live_nodup : live.Nodup)
    (_h_live_big : 2 ≤ live.length)
    (deadBits : List Bool)
    (w : Nat) (_hw : w < live.length)
    (g : UnboundedFanInDNF live.length),
    dnfWidth g.val ≤ w ∧
    ∀ (liveBits : List Bool), liveBits.length = live.length →
      ufiFormulaEval formula.val
          (assembleInput n live liveBits deadBits) =
      ufiFormulaEval g.val liveBits := by
  -- Since `t ≥ 2`, the left side of the threshold is already positive and
  -- much larger than three.  This is the sole arithmetic fact about the
  -- switching parameters needed by the structural base case.
  have h_three_le_n : 3 ≤ n := by nlinarith
  -- Unpack the formula subtype.  Of its fields, this proof uses the input
  -- bound, the depth bound, and strict leveling; size and positivity play no
  -- role at depth one.
  obtain ⟨formula, h_ib, h_depth, _h_size, _h_pos, h_strict_f⟩ := formula
  -- Recover the plain strict-leveling discipline from the fused field.
  have h_strict := Circuits.Leveling.isProperlyLeveled_imp_strict _ _ h_strict_f
  -- The "constant false" DNF and "constant one" DNF that we'll use as targets.
  -- Both have width 0 < live.length whenever live.length ≥ 2.
  -- Reusable construction: for any m ≥ 1, `orGate []` is a width-0 DNF on m inputs
  -- evaluating to `false`, and `orGate [andGate []]` is a width-0 DNF evaluating to `true`.
  -- Each `refine` below provides, in order: the live indices and their three
  -- invariants, the fixed bits, the width bound, a typed DNF, its width proof,
  -- and finally semantic agreement for every assignment to the live inputs.
  cases formula with
  | inputGate i b =>
    -- The formula computes one literal.  Its index is in range by `h_ib`.
    -- Choose any different in-range index as padding so the live list has
    -- length two, and place `i` first so it is reindexed to `0`.
    have hi : i < n := by
      simpa [ufiLargestInput, ufiCollectInputIndices, List.foldr_cons, List.foldr_nil,
        Nat.max_zero] using h_ib
    obtain ⟨other, hother_lt, hother_ne⟩ : ∃ o, o < n ∧ i ≠ o := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨[i, other], ?_, ?_, ?_, List.replicate (n - 2) false,
            1, ?_,
            ⟨UnboundedFanInFormula.orGate
                [UnboundedFanInFormula.andGate
                  [UnboundedFanInFormula.inputGate 0 b]], ?_, ?_⟩, ?_, ?_⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hi
      · exact hother_lt
    · simp [hother_ne]
    · simp only [List.length_cons, List.length_nil]; omega
    · simp only [List.length_cons, List.length_nil]; omega
    · have hlm : ufiLargestInput (UnboundedFanInFormula.orGate
          [UnboundedFanInFormula.andGate
            [UnboundedFanInFormula.inputGate 0 b]]) = 0 := by
        simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_cons, List.foldr_nil]
      rw [hlm]
      simp only [List.length_cons, List.length_nil]; omega
    · simp [isDNF, isAndOfInputsOnly, isInput]
    · simp only [dnfWidth, List.map_cons, List.map_nil, List.foldl_cons,
        List.foldl_nil, List.length_cons, List.length_nil]
      omega
    · intro lb hlb
      -- `assembleInput` reads the value for original variable `i` from live
      -- position zero (`h_a`), exactly where the target literal reads it (`h_b`).
      have h_live_lt_io : ∀ v ∈ [i, other], v < n := by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hi
        · exact hother_lt
      have hfind : [i, other].findIdx? (· = i) = some 0 := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨Nat.zero_lt_succ 1, by simp, ?_⟩
        intro j hj
        omega
      have h_a :
          (assembleInput n [i, other] lb
              (List.replicate (n - 2) false))[i]? =
            some (lb.getD 0 false) := by
        rw [assembleInput_get_at n [i, other] lb
          (List.replicate (n - 2) false) i hi]
        unfold assembleInputFn
        rw [hfind]
      have h_b : lb[0]? = some (lb.getD 0 false) := by
        cases lb with
        | nil => simp at hlb
        | cons a t => rfl
      rw [eval_or_and_singleton_base]
      unfold ufiFormulaEval
      rw [h_a, h_b]
  | constant b lbl =>
    -- Constants do not depend on the restriction.  Keep variables `0` and
    -- `1` live solely to meet the two-live-variable invariant, fix all other
    -- positions arbitrarily, and use the matching canonical constant DNF.
    cases b with
    | true =>
      refine ⟨[0, 1], ?_, ?_, ?_, List.replicate (n - 2) false, 0, ?_,
              ⟨UnboundedFanInFormula.orGate
                  [UnboundedFanInFormula.andGate []], ?_, ?_⟩, ?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega
      · decide
      · decide
      · decide
      · have hlm : ufiLargestInput (UnboundedFanInFormula.orGate
            [UnboundedFanInFormula.andGate []]) = 0 := by
          simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil]
        rw [hlm]; decide
      · decide
      · decide
      · intro lb hlb; simp [ufiFormulaEval]
    | false =>
      refine ⟨[0, 1], ?_, ?_, ?_, List.replicate (n - 2) false, 0, ?_,
              ⟨UnboundedFanInFormula.orGate [], ?_, ?_⟩, ?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega
      · decide
      · decide
      · decide
      · have hlm : ufiLargestInput (UnboundedFanInFormula.orGate []) = 0 := by
          simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil]
        rw [hlm]; decide
      · decide
      · decide
      · intro lb hlb; simp [ufiFormulaEval]
  | notGate sub =>
    -- Strictly leveled UFI formulas contain no explicit `notGate`; literal
    -- negation is represented by the Boolean polarity on `inputGate` instead.
    exact absurd h_strict (by simp [IsAlternatingAndLeveledAt])
  | andGate gates =>
    -- Since `depth (andGate gates) ≤ 1`, the maximum child depth is zero.
    -- The next two facts turn that numerical observation into a syntactic
    -- classification of every child as an `inputGate` or `constant`.
    have h_child_depth : ∀ g ∈ gates, ufiFormulaDepth g = 0 := by
      intro g hg
      have h_le : ufiFormulaDepth g ≤ 0 := by
        have h₁ : ufiFormulaDepth g ≤
            (List.foldr max 0) (gates.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        have h₂ : 1 + (List.foldr max 0) (gates.map ufiFormulaDepth) ≤ 1 := by
          have := h_depth
          simp [ufiFormulaDepth] at this
          omega
        omega
      omega
    -- Classify each child as either inputGate or constant.
    have h_child_simple : ∀ g ∈ gates,
        (∃ i b, g = UnboundedFanInFormula.inputGate i b) ∨
        (∃ b lbl, g = UnboundedFanInFormula.constant b lbl) := by
      intro g hg
      have hd := h_child_depth g hg
      cases g with
      | inputGate i b => exact Or.inl ⟨i, b, rfl⟩
      | constant b lbl => exact Or.inr ⟨b, lbl, rfl⟩
      | notGate _ => simp [ufiFormulaDepth] at hd
      | andGate _ => simp [ufiFormulaDepth] at hd
      | orGate _ => simp [ufiFormulaDepth] at hd
    -- Decide whether some gate evaluates to `false` regardless of the
    -- assembled input (a "default-false" gate): either `constant false _`
    -- or an `inputGate i false` with `n ≤ i`.
    by_cases h_dz : ∃ g₀ ∈ gates,
        (∃ lbl, g₀ = UnboundedFanInFormula.constant false lbl) ∨
        (∃ i, g₀ = UnboundedFanInFormula.inputGate i false ∧ n ≤ i)
    · -- Default-false gate present: andGate evaluates to false on any assembly.
      -- Keep all variables live (so `assembleInput` is just a reindexing with
      -- no fixed positions) and represent the result by constant false.
      obtain ⟨g₀, hg₀_mem, hg₀_kind⟩ := h_dz
      refine ⟨List.range n, ?_, ?_, ?_, [], 0, ?_,
              ⟨UnboundedFanInFormula.orGate [], ?_, ?_⟩, ?_, ?_⟩
      · intro v hv; rw [List.mem_range] at hv; exact hv
      · exact List.nodup_range
      · rw [List.length_range]; omega
      · rw [List.length_range]; omega
      · simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil,
              List.length_range]; omega
      · decide
      · simp [dnfWidth]
      · intro liveBits h_lb_len
        have h_assembled_len :
            (assembleInput n (List.range n) liveBits []).length = n := by
          simp [assembleInput]
        have h_g₀_zero :
            ufiFormulaEval g₀
                (assembleInput n (List.range n) liveBits []) = false := by
          rcases hg₀_kind with ⟨lbl, rfl⟩ | ⟨i, rfl, hi⟩
          · simp [ufiFormulaEval]
          · simp only [ufiFormulaEval]
            have h_none :
                (assembleInput n (List.range n) liveBits [])[i]? = none := by
              rw [List.getElem?_eq_none_iff]; rw [h_assembled_len]; exact hi
            rw [h_none]
        rw [andGate_eval_zero_of_mem_zero gates _ g₀ hg₀_mem h_g₀_zero]
        change false = ufiFormulaEval (UnboundedFanInFormula.orGate []) liveBits
        simp [ufiFormulaEval]
    · -- No default-false gate. Every gate is one of:
      --   * `constant one _` (default-one), or
      --   * `inputGate i true` with `n ≤ i` (default-one), or
      --   * `inputGate i b` with `i < n` (settable).
      -- Look for a settable input.
      by_cases h_set : ∃ i b, i < n ∧ UnboundedFanInFormula.inputGate i b ∈ gates
      · -- Pick a settable input `i₀, b₀`. Set its assembled value so the
        -- literal evaluates to false, killing the andGate.
        obtain ⟨i₀, b₀, hi₀, hg₀_mem⟩ := h_set
        let killValue : Bool := if b₀ then true else false
        -- All indices except `i₀` remain live.  Hence the single entry in
        -- `deadBits` is precisely the value installed at `i₀`.
        let live : List Nat := (List.range n).filter (· ≠ i₀)
        have h_live_lt : ∀ v ∈ live, v < n := by
          intro v hv
          rw [List.mem_filter, List.mem_range] at hv
          exact hv.1
        have h_live_nodup : live.Nodup :=
          List.nodup_range.filter _
        have h_live_len : live.length = n - 1 := by
          have h_to_finset : live.toFinset = (Finset.range n).erase i₀ := by
            ext x
            simp [live, List.mem_range,
                  Finset.mem_erase, Finset.mem_range]
            tauto
          have h₁ : (live.toFinset : Finset Nat).card = live.length :=
            List.toFinset_card_of_nodup h_live_nodup
          rw [← h₁, h_to_finset,
              Finset.card_erase_of_mem (Finset.mem_range.mpr hi₀),
              Finset.card_range]
        have h_live_big : 2 ≤ live.length := by rw [h_live_len]; omega
        refine ⟨live, h_live_lt, h_live_nodup, h_live_big, [killValue], 0, ?_,
                ⟨UnboundedFanInFormula.orGate [], ?_, ?_⟩, ?_, ?_⟩
        · rw [h_live_len]; omega
        · simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil,
                h_live_len]; omega
        · decide
        · simp [dnfWidth]
        · intro liveBits h_lb_len
          -- The assembled value at `i₀` equals `killValue`.
          have h_not_in : i₀ ∉ live := by
            intro hmem; rw [List.mem_filter] at hmem
            simp at hmem
          have h_at_i₀ :
              (assembleInput n live liveBits [killValue])[i₀]? =
                some killValue := by
            rw [assembleInput_get_at n live liveBits [killValue] i₀ hi₀]
            unfold assembleInputFn
            have h_find_idx : live.findIdx? (· = i₀) = none :=
              findIdx?_eq_none_of_notMem live i₀ h_not_in
            rw [h_find_idx]
            -- Every smaller index remains live, so no dead position precedes
            -- `i₀`; its index in the dead-bit list is therefore zero.
            have h_filter_empty :
                ((List.range i₀).filter (fun k => !live.contains k)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro k hk
              rw [List.mem_range] at hk
              have hk_ne : k ≠ i₀ := Nat.ne_of_lt hk
              have hk_in_live : k ∈ live := by
                rw [List.mem_filter, List.mem_range]
                refine ⟨lt_trans hk hi₀, ?_⟩
                simp [hk_ne]
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
              rw [Bool.eq_false_iff]
              intro hcontra
              exact hcontra (List.elem_eq_true_of_mem hk_in_live)
            rw [h_filter_empty]
            simp [List.getD]
          -- The literal `inputGate i₀ b₀` evaluates to false on the assembled input.
          have h_lit_zero :
              ufiFormulaEval (UnboundedFanInFormula.inputGate i₀ b₀)
                (assembleInput n live liveBits [killValue]) = false := by
            unfold ufiFormulaEval
            rw [h_at_i₀]
            cases b₀ <;> simp [killValue, Bool.not]
          rw [andGate_eval_zero_of_mem_zero gates _ _ hg₀_mem h_lit_zero]
          change false = ufiFormulaEval (UnboundedFanInFormula.orGate []) liveBits
          simp [ufiFormulaEval]
      · -- No settable input either.  A child can only be `constant true _`:
        -- a false constant was excluded by `h_dz`, while any input is either
        -- settable or contradicts the formula-wide input bound `h_ib`.
        -- Establish this childwise, combine with AND semantics, and keep the
        -- full range live because no actual restriction is needed.
        have h_all_one_default : ∀ g ∈ gates, ∀ assembled : List Bool,
            assembled.length = n → ufiFormulaEval g assembled = true := by
          intro g hg assembled h_alen
          rcases h_child_simple g hg with ⟨i, b, rfl⟩ | ⟨b, lbl, rfl⟩
          · -- inputGate i b: not settable means ¬ i < n, i.e. n ≤ i.
            have h_n_le : n ≤ i := by
              by_contra h
              exact h_set ⟨i, b, Nat.lt_of_not_le h, hg⟩
            -- Not default-false means b ≠ false.
            have h_b_true : b = true := by
              by_contra h_bf
              have h_b_false : b = false := by cases b <;> simp_all
              subst h_b_false
              exact h_dz ⟨_, hg, Or.inr ⟨i, rfl, h_n_le⟩⟩
            simp only [ufiFormulaEval, h_b_true]
            have h_none : assembled[i]? = none := by
              rw [List.getElem?_eq_none_iff, h_alen]; exact h_n_le
            have hi_lt : i < n := by
              have hi := ufiLargestInput_andGate_child_le n gates h_ib
                (.inputGate i b) hg
              simpa [ufiLargestInput, ufiCollectInputIndices,
                List.foldr_cons, List.foldr_nil] using hi
            omega
          · -- constant b lbl: not default-false means b = one.
            have h_b_one : b = true := by
              cases b
              · exact absurd ⟨_, hg, Or.inl ⟨lbl, rfl⟩⟩ h_dz
              · rfl
            simp [ufiFormulaEval, h_b_one]
        refine ⟨List.range n, ?_, ?_, ?_, [], 0, ?_,
                ⟨UnboundedFanInFormula.orGate [UnboundedFanInFormula.andGate []],
                  ?_, ?_⟩, ?_, ?_⟩
        · intro v hv; rw [List.mem_range] at hv; exact hv
        · exact List.nodup_range
        · rw [List.length_range]; omega
        · rw [List.length_range]; omega
        · simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil,
                List.length_range]; omega
        · decide
        · simp [dnfWidth]
        · intro liveBits h_lb_len
          have h_alen :
              (assembleInput n (List.range n) liveBits []).length = n := by
            simp [assembleInput]
          have h_lhs_one :
              ufiFormulaEval (UnboundedFanInFormula.andGate gates)
                  (assembleInput n (List.range n) liveBits []) = true :=
            andGate_eval_one_of_all_one _ _
              (fun g hg => h_all_one_default g hg _ h_alen)
          rw [h_lhs_one]
          change true = ufiFormulaEval
              (UnboundedFanInFormula.orGate
                [UnboundedFanInFormula.andGate []]) liveBits
          simp [ufiFormulaEval]
  | orGate gates =>
    -- This is the Boolean dual of the `andGate` proof.  Child depth is again
    -- zero, so every child is an input or constant.
    have h_child_depth : ∀ g ∈ gates, ufiFormulaDepth g = 0 := by
      intro g hg
      have h_le : ufiFormulaDepth g ≤ 0 := by
        have h₁ : ufiFormulaDepth g ≤
            (List.foldr max 0) (gates.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        have h₂ : 1 + (List.foldr max 0) (gates.map ufiFormulaDepth) ≤ 1 := by
          have := h_depth
          simp [ufiFormulaDepth] at this
          omega
        omega
      omega
    have h_child_simple : ∀ g ∈ gates,
        (∃ i b, g = UnboundedFanInFormula.inputGate i b) ∨
        (∃ b lbl, g = UnboundedFanInFormula.constant b lbl) := by
      intro g hg
      have hd := h_child_depth g hg
      cases g with
      | inputGate i b => exact Or.inl ⟨i, b, rfl⟩
      | constant b lbl => exact Or.inr ⟨b, lbl, rfl⟩
      | notGate _ => simp [ufiFormulaDepth] at hd
      | andGate _ => simp [ufiFormulaDepth] at hd
      | orGate _ => simp [ufiFormulaDepth] at hd
    -- First detect a child that can force the OR to true.  A `constant true _`
    -- does so directly.  The syntactic alternative `inputGate i true` with
    -- `n ≤ i` is included to make the subsequent classification exhaustive,
    -- but `h_ib` rules it out inside the proof.  Thus this branch yields the
    -- constant-true DNF.
    by_cases h_do : ∃ g₀ ∈ gates,
        (∃ lbl, g₀ = UnboundedFanInFormula.constant true lbl) ∨
        (∃ i, g₀ = UnboundedFanInFormula.inputGate i true ∧ n ≤ i)
    · obtain ⟨g₀, hg₀_mem, hg₀_kind⟩ := h_do
      refine ⟨List.range n, ?_, ?_, ?_, [], 0, ?_,
              ⟨UnboundedFanInFormula.orGate [UnboundedFanInFormula.andGate []],
                ?_, ?_⟩, ?_, ?_⟩
      · intro v hv; rw [List.mem_range] at hv; exact hv
      · exact List.nodup_range
      · rw [List.length_range]; omega
      · rw [List.length_range]; omega
      · simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil,
              List.length_range]; omega
      · decide
      · simp [dnfWidth]
      · intro liveBits h_lb_len
        have h_assembled_len :
            (assembleInput n (List.range n) liveBits []).length = n := by
          simp [assembleInput]
        have h_g₀_one :
            ufiFormulaEval g₀
                (assembleInput n (List.range n) liveBits []) = true := by
          rcases hg₀_kind with ⟨lbl, rfl⟩ | ⟨i, rfl, hi⟩
          · simp [ufiFormulaEval]
          · unfold ufiFormulaEval
            have hi_lt : i < n := by
              have hib := ufiLargestInput_orGate_child_le n gates h_ib
                (.inputGate i true) hg₀_mem
              simpa [ufiLargestInput, ufiCollectInputIndices,
                List.foldr_cons, List.foldr_nil] using hib
            omega
        rw [orGate_eval_one_of_mem_one gates _ g₀ hg₀_mem h_g₀_one]
        change true = ufiFormulaEval
            (UnboundedFanInFormula.orGate
              [UnboundedFanInFormula.andGate []]) liveBits
        simp [ufiFormulaEval]
    · by_cases h_set : ∃ i b, i < n ∧ UnboundedFanInFormula.inputGate i b ∈ gates
      · -- Settable input: lift to one.
        obtain ⟨i₀, b₀, hi₀, hg₀_mem⟩ := h_set
        let liftValue : Bool := if b₀ then false else true
        -- Remove `i₀` from the live range and store its satisfying value as
        -- the sole dead bit.  The remaining live list has length `n - 1`.
        let live : List Nat := (List.range n).filter (· ≠ i₀)
        have h_live_lt : ∀ v ∈ live, v < n := by
          intro v hv
          rw [List.mem_filter, List.mem_range] at hv
          exact hv.1
        have h_live_nodup : live.Nodup :=
          List.nodup_range.filter _
        have h_live_len : live.length = n - 1 := by
          have h_to_finset : live.toFinset = (Finset.range n).erase i₀ := by
            ext x
            simp [live, List.mem_range,
                  Finset.mem_erase, Finset.mem_range]
            tauto
          have h₁ : (live.toFinset : Finset Nat).card = live.length :=
            List.toFinset_card_of_nodup h_live_nodup
          rw [← h₁, h_to_finset,
              Finset.card_erase_of_mem (Finset.mem_range.mpr hi₀),
              Finset.card_range]
        have h_live_big : 2 ≤ live.length := by rw [h_live_len]; omega
        refine ⟨live, h_live_lt, h_live_nodup, h_live_big, [liftValue], 0, ?_,
                ⟨UnboundedFanInFormula.orGate [UnboundedFanInFormula.andGate []],
                  ?_, ?_⟩, ?_, ?_⟩
        · rw [h_live_len]; omega
        · simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil,
                h_live_len]; omega
        · decide
        · simp [dnfWidth]
        · intro liveBits h_lb_len
          have h_not_in : i₀ ∉ live := by
            intro hmem; rw [List.mem_filter] at hmem
            simp at hmem
          have h_at_i₀ :
              (assembleInput n live liveBits [liftValue])[i₀]? =
                some liftValue := by
            rw [assembleInput_get_at n live liveBits [liftValue] i₀ hi₀]
            unfold assembleInputFn
            have h_find_idx : live.findIdx? (· = i₀) = none :=
              findIdx?_eq_none_of_notMem live i₀ h_not_in
            rw [h_find_idx]
            have h_filter_empty :
                ((List.range i₀).filter (fun k => !live.contains k)) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro k hk
              rw [List.mem_range] at hk
              have hk_ne : k ≠ i₀ := Nat.ne_of_lt hk
              have hk_in_live : k ∈ live := by
                rw [List.mem_filter, List.mem_range]
                refine ⟨lt_trans hk hi₀, ?_⟩
                simp [hk_ne]
              simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
              rw [Bool.eq_false_iff]
              intro hcontra
              exact hcontra (List.elem_eq_true_of_mem hk_in_live)
            rw [h_filter_empty]
            simp [List.getD]
          have h_lit_one :
              ufiFormulaEval (UnboundedFanInFormula.inputGate i₀ b₀)
                (assembleInput n live liveBits [liftValue]) = true := by
            unfold ufiFormulaEval
            rw [h_at_i₀]
            cases b₀ <;> simp [liftValue, Bool.not]
          rw [orGate_eval_one_of_mem_one gates _ _ hg₀_mem h_lit_one]
          change true = ufiFormulaEval
              (UnboundedFanInFormula.orGate
                [UnboundedFanInFormula.andGate []]) liveBits
          simp [ufiFormulaEval]
      · -- No default-one, no settable: every gate evaluates to false. orGate = false.
        -- Prove the claim childwise, combine it using OR semantics, and use
        -- the canonical constant-false DNF on the full live range.
        have h_all_zero_default : ∀ g ∈ gates, ∀ assembled : List Bool,
            assembled.length = n → ufiFormulaEval g assembled = false := by
          intro g hg assembled h_alen
          rcases h_child_simple g hg with ⟨i, b, rfl⟩ | ⟨b, lbl, rfl⟩
          · have h_n_le : n ≤ i := by
              by_contra h
              exact h_set ⟨i, b, Nat.lt_of_not_le h, hg⟩
            have h_b_false : b = false := by
              by_contra h_bt
              have h_b_true : b = true := by cases b <;> simp_all
              subst h_b_true
              exact h_do ⟨_, hg, Or.inr ⟨i, rfl, h_n_le⟩⟩
            simp only [ufiFormulaEval, h_b_false]
            have h_none : assembled[i]? = none := by
              rw [List.getElem?_eq_none_iff, h_alen]; exact h_n_le
            rw [h_none]
          · have h_b_zero : b = false := by
              cases b
              · rfl
              · exact absurd ⟨_, hg, Or.inl ⟨lbl, rfl⟩⟩ h_do
            simp [ufiFormulaEval, h_b_zero]
        refine ⟨List.range n, ?_, ?_, ?_, [], 0, ?_,
                ⟨UnboundedFanInFormula.orGate [], ?_, ?_⟩, ?_, ?_⟩
        · intro v hv; rw [List.mem_range] at hv; exact hv
        · exact List.nodup_range
        · rw [List.length_range]; omega
        · rw [List.length_range]; omega
        · simp [ufiLargestInput, ufiCollectInputIndices, List.foldr_nil,
                List.length_range]; omega
        · decide
        · simp [dnfWidth]
        · intro liveBits h_lb_len
          have h_alen :
              (assembleInput n (List.range n) liveBits []).length = n := by
            simp [assembleInput]
          have h_lhs_zero :
              ufiFormulaEval (UnboundedFanInFormula.orGate gates)
                  (assembleInput n (List.range n) liveBits []) = false :=
            orGate_eval_zero_of_all_zero _ _
              (fun g hg => h_all_zero_default g hg _ h_alen)
          rw [h_lhs_zero]
          change false = ufiFormulaEval (UnboundedFanInFormula.orGate []) liveBits
          simp [ufiFormulaEval]

/-! ### Sub-lemmas for `exists_switching_depth_reduction` -/

/-- Convert the `AssignedRandomRestriction` produced by
    `exists_switching_lemma_pigeonhole_list` into the `(live, deadBits)` shape consumed by
    `assembleInput`, with `live = ρ.liveVars.val.sort (≤)` and
    `deadBits` listing the values assigned to non-live positions
    of `[0, n)` in increasing order. -/
lemma exists_assembled_restriction
    {n : Nat} {σ : OpenUnitIntervalQ}
    (ρ : AssignedRandomRestriction σ n) :
    ∃ (live : List Nat)
      (_h_live_lt : ∀ v ∈ live, v < n)
      (_h_live_nodup : live.Nodup)
      (deadBits : List Bool)
      (_h_card : deadBits.length + live.length = n)
      (_h_live_eq : (live : Multiset Nat) =
          ρ.starAssignment.val.val.val),
      -- Faithfulness: the assembled input agrees with the restriction
      -- map on every position.
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b := by
  set liveSet : Finset Nat := ρ.starAssignment.val.val with hlive_set
  set deadBits : List Bool := ρ.varAssignments with hdead_bits
  let live : List Nat := liveSet.toList
  have hlive_sub : liveSet ⊆ Finset.range n :=
    ρ.starAssignment.val.property
  have h_card_sum : liveSet.card + deadBits.length = n :=
    ρ.non_starred_vars_fully_assigned
  have h_live_len : live.length = liveSet.card := Finset.length_toList _
  have h_live_nodup : live.Nodup := Finset.nodup_toList _
  have h_live_lt : ∀ v ∈ live, v < n := by
    intro v hv
    have hv_set : v ∈ liveSet := Finset.mem_toList.mp hv
    exact Finset.mem_range.mp (hlive_sub hv_set)
  have h_card : deadBits.length + live.length = n := by
    rw [h_live_len]; omega
  have h_live_eq : (live : Multiset Nat) =
      ρ.starAssignment.val.val.val := by
    change (liveSet.toList : Multiset Nat) = liveSet.val
    exact Finset.coe_toList _
  refine ⟨live, h_live_lt, h_live_nodup, deadBits, h_card, h_live_eq, ?_⟩
  intro liveBits h_lb_len i b h_map
  -- Unpack `h_map : mkAssignment liveSet deadBits i = some b`.
  unfold mkAssignment at h_map
  by_cases hi_live : i ∈ liveSet
  · rw [if_pos hi_live] at h_map; exact absurd h_map (by simp)
  rw [if_neg hi_live] at h_map
  -- `h_map : deadBits[((Finset.range i \ liveSet).card)]? = some b`
  -- Step 1: derive `i < n` from `getElem? = some b` and the dead-length bound.
  have hi_lt : i < n := by
    by_contra hi_ge
    push Not at hi_ge
    have h_sub : Finset.range n \ liveSet ⊆ Finset.range i \ liveSet :=
      Finset.sdiff_subset_sdiff (Finset.range_mono hi_ge) Finset.Subset.rfl
    have h_card_le :
        (Finset.range n \ liveSet).card ≤ (Finset.range i \ liveSet).card :=
      Finset.card_le_card h_sub
    have h_rn_eq : (Finset.range n \ liveSet).card = n - liveSet.card := by
      rw [Finset.card_sdiff_of_subset hlive_sub, Finset.card_range]
    have h_dead_eq : deadBits.length = n - liveSet.card := by omega
    have h_idx_ge : deadBits.length ≤ (Finset.range i \ liveSet).card := by
      rw [h_dead_eq, ← h_rn_eq]; exact h_card_le
    rw [List.getElem?_eq_none h_idx_ge] at h_map
    cases h_map
  -- Step 2: compute the assembled value at `i`.
  have h_i_not_in_live : i ∉ live := by
    intro h; exact hi_live (Finset.mem_toList.mp h)
  rw [assembleInput_get_at n live liveBits deadBits i hi_lt]
  unfold assembleInputFn
  rw [findIdx?_eq_none_of_notMem live i h_i_not_in_live]
  simp only []
  -- Step 3: rewrite the filter-length as the sdiff-card.
  have h_idx_eq :
      ((List.range i).filter (fun k => !live.contains k)).length =
        (Finset.range i \ liveSet).card := by
    have h_l_nodup :
        ((List.range i).filter (fun k => !live.contains k)).Nodup :=
      List.nodup_range.filter _
    rw [← List.toFinset_card_of_nodup h_l_nodup]
    congr 1
    ext x
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range,
               Finset.mem_sdiff, Finset.mem_range,
               Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨?_, ?_⟩
    · rintro ⟨hx_lt, hx_nc⟩
      refine ⟨hx_lt, ?_⟩
      intro hx_set
      have hx_live : x ∈ live := Finset.mem_toList.mpr hx_set
      have h_elem : live.contains x = true :=
        List.elem_eq_true_of_mem hx_live
      rw [h_elem] at hx_nc
      exact Bool.noConfusion hx_nc
    · rintro ⟨hx_lt, hx_nset⟩
      refine ⟨hx_lt, ?_⟩
      have h_not_in : x ∉ live := by
        intro h; exact hx_nset (Finset.mem_toList.mp h)
      rw [Bool.eq_false_iff]
      intro h_elem
      exact h_not_in (List.mem_of_elem_eq_true h_elem)
  rw [h_idx_eq]
  -- Step 4: convert `getElem? = some b` to `getD = b`.
  congr 1
  change deadBits[(Finset.range i \ liveSet).card]?.getD false = b
  simp [h_map]

/-- **DT-to-DNF clause widths are bounded by depth + path length.**

    Pure structural fact about `decisionTreeToDNFClauses`: every
    clause it produces has length at most `path.length +
    decisionTreeDepth tree`.  Specialised to `path = []` this gives
    `dnfWidth (decisionTreeToDNF tree) ≤ decisionTreeDepth
    tree`, which is the form consumed by
    `exists_narrow_dnf_from_good_restriction_dnf`. -/
lemma decisionTreeToDNFClauses_clause_length_le
    (tree : DecisionTrees.DecisionTree) (path : List UnboundedFanInFormula) :
    ∀ c ∈ DecisionTrees.decisionTreeToDNFClauses tree path,
      ∀ literals,
        c = UnboundedFanInFormula.andGate literals →
          literals.length ≤ path.length + DecisionTrees.decisionTreeDepth tree := by
  induction tree generalizing path with
  | dtLeaf b =>
    intro c hc literals hlit
    cases b with
    | false =>
      -- clauses are `[]`, vacuous.
      simp only [DecisionTrees.decisionTreeToDNFClauses,
        List.not_mem_nil] at hc
    | true =>
      -- clauses are `[andGate path]`, so `c = andGate path` and literals = path.
      simp only [DecisionTrees.decisionTreeToDNFClauses,
        List.mem_singleton] at hc
      subst hc
      cases hlit
      simp only [DecisionTrees.decisionTreeDepth, Nat.add_zero, le_refl]
  | dtNode i left right ih_l ih_r =>
    intro c hc literals hlit
    -- clauses = (left with path++[inputGate i true]) ++ (right with path++[inputGate i false])
    simp only [DecisionTrees.decisionTreeToDNFClauses, List.mem_append] at hc
    rcases hc with h_l | h_r
    · have := ih_l (path ++ [UnboundedFanInFormula.inputGate i true]) c h_l literals hlit
      simp [DecisionTrees.decisionTreeDepth] at this ⊢
      omega
    · have := ih_r (path ++ [UnboundedFanInFormula.inputGate i false]) c h_r literals hlit
      simp [DecisionTrees.decisionTreeDepth] at this ⊢
      omega

/-- **DT-to-DNF width is bounded by DT depth.**

    Specialisation of `decisionTreeToDNFClauses_clause_length_le`
    to `path = []`: `dnfWidth (decisionTreeToDNF tree) ≤
    decisionTreeDepth tree`. -/
lemma decisionTreeToDNF_dnfWidth_le_decisionTreeDepth (tree : DecisionTrees.DecisionTree) :
    dnfWidth (DecisionTrees.decisionTreeToDNF tree) ≤
      DecisionTrees.decisionTreeDepth tree := by
  -- `dnfWidth (orGate clauses)` reduces to a `foldl max 0` over per-clause widths.
  change ((DecisionTrees.decisionTreeToDNFClauses tree []).map
      (fun gate => match gate with
        | UnboundedFanInFormula.andGate literals => literals.length
        | _ => 0)).foldl max 0 ≤ DecisionTrees.decisionTreeDepth tree
  apply Lists.ListLemmas.foldl_max_map_le_of_forall _ _ _ 0 (Nat.zero_le _)
  intro gate hgate_mem
  cases gate with
  | andGate literals =>
    have h := decisionTreeToDNFClauses_clause_length_le tree []
      (UnboundedFanInFormula.andGate literals) hgate_mem literals rfl
    simpa using h
  | inputGate _ _ => exact Nat.zero_le _
  | constant _ _ => exact Nat.zero_le _
  | notGate _ => exact Nat.zero_le _
  | orGate _ => exact Nat.zero_le _

/-- Re-key a UFI formula by remapping each `inputGate i b` to `inputGate (φ i) b`.
    Constants are unchanged; gates are remapped recursively. -/
def ufiRekey (φ : Nat → Nat) :
    UnboundedFanInFormula → UnboundedFanInFormula
  | UnboundedFanInFormula.inputGate i b => UnboundedFanInFormula.inputGate (φ i) b
  | UnboundedFanInFormula.constant b lbl => UnboundedFanInFormula.constant b lbl
  | UnboundedFanInFormula.notGate sub => UnboundedFanInFormula.notGate (ufiRekey φ sub)
  | UnboundedFanInFormula.andGate gates =>
      UnboundedFanInFormula.andGate (gates.map (ufiRekey φ))
  | UnboundedFanInFormula.orGate gates =>
      UnboundedFanInFormula.orGate (gates.map (ufiRekey φ))

/-- **Re-keying preserves eval under index agreement.**

    If for every input index `i` appearing in `formula`, the input at
    `i` in `xs` equals the input at `φ i` in `ys` (or both are absent),
    then `formula` and `ufiRekey φ formula` evaluate to the same bit. -/
theorem ufiRekey_eval_eq (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) → (xs ys : List Bool) →
      (∀ i ∈ ufiCollectInputIndices formula,
          xs[i]? = ys[(φ i)]?) →
      ufiFormulaEval formula xs = ufiFormulaEval (ufiRekey φ formula) ys
  | UnboundedFanInFormula.inputGate i b, xs, ys, h_agree => by
      have hi : i ∈ ufiCollectInputIndices (UnboundedFanInFormula.inputGate i b) := by
        simp [ufiCollectInputIndices]
      have heq := h_agree i hi
      unfold ufiRekey ufiFormulaEval
      rw [heq]
  | UnboundedFanInFormula.constant b lbl, xs, ys, _ => by
      unfold ufiRekey ufiFormulaEval
      rfl
  | UnboundedFanInFormula.notGate sub, xs, ys, h_agree => by
      have h_sub : ∀ i ∈ ufiCollectInputIndices sub,
          xs[i]? = ys[(φ i)]? := by
        intro i hi
        apply h_agree
        simp [ufiCollectInputIndices, hi]
      have ih := ufiRekey_eval_eq φ sub xs ys h_sub
      simp only [ufiRekey, ufiFormulaEval, ih]
  | UnboundedFanInFormula.andGate gates, xs, ys, h_agree => by
      simp only [ufiRekey]
      rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all]
      have hmap : (gates.map fun c => ufiFormulaEval c xs) =
                  ((gates.map (ufiRekey φ)).map fun c => ufiFormulaEval c ys) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro g hg
        have h_sub : ∀ i ∈ ufiCollectInputIndices g,
            xs[i]? = ys[(φ i)]? := by
          intro i hi
          apply h_agree
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨g, hg, hi⟩
        exact ufiRekey_eval_eq φ g xs ys h_sub
      rw [hmap]
  | UnboundedFanInFormula.orGate gates, xs, ys, h_agree => by
      simp only [ufiRekey]
      rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any]
      have hmap : (gates.map fun c => ufiFormulaEval c xs) =
                  ((gates.map (ufiRekey φ)).map fun c => ufiFormulaEval c ys) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro g hg
        have h_sub : ∀ i ∈ ufiCollectInputIndices g,
            xs[i]? = ys[(φ i)]? := by
          intro i hi
          apply h_agree
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨g, hg, hi⟩
        exact ufiRekey_eval_eq φ g xs ys h_sub
      rw [hmap]

/-- **Re-keying preserves the `isDNF` shape.** -/
lemma isDNF_ufiRekey (φ : Nat → Nat) (formula : UnboundedFanInFormula)
    (h : isDNF formula = true) :
    isDNF (ufiRekey φ formula) = true := by
  -- `isDNF` requires `orGate gates` whose every entry is `andGate _` of inputs only.
  match formula with
  | UnboundedFanInFormula.inputGate _ _ => simp [isDNF] at h
  | UnboundedFanInFormula.constant _ _ => simp [isDNF] at h
  | UnboundedFanInFormula.notGate _ => simp [isDNF] at h
  | UnboundedFanInFormula.andGate _ => simp [isDNF] at h
  | UnboundedFanInFormula.orGate gates =>
    simp only [isDNF, ufiRekey, List.all_eq_true, List.mem_map] at h ⊢
    rintro y ⟨g, hg, rfl⟩
    have hg_clause : isAndOfInputsOnly g = true := h g hg
    -- `g` must be `andGate lits` with each `lit` an `inputGate ...`.
    match g, hg_clause with
    | UnboundedFanInFormula.andGate lits, hcl =>
      simp only [isAndOfInputsOnly, List.all_eq_true] at hcl
      simp only [ufiRekey, isAndOfInputsOnly, List.all_eq_true, List.mem_map]
      rintro z ⟨lit, hlit_mem, rfl⟩
      have hlit := hcl lit hlit_mem
      -- `lit` is `inputGate _ _`.
      cases lit with
      | inputGate _ _ => simp [ufiRekey, isInput]
      | constant _ _ => simp [isInput] at hlit
      | notGate _ => simp [isInput] at hlit
      | andGate _ => simp [isInput] at hlit
      | orGate _ => simp [isInput] at hlit

/-- **Re-keying preserves clause widths exactly.** -/
lemma ufiRekey_dnfWidth (φ : Nat → Nat) (formula : UnboundedFanInFormula) :
    dnfWidth (ufiRekey φ formula) = dnfWidth formula := by
  cases formula with
  | inputGate _ _ => simp [ufiRekey, dnfWidth]
  | constant _ _ => simp [ufiRekey, dnfWidth]
  | notGate _ => simp [ufiRekey, dnfWidth]
  | andGate _ => simp [ufiRekey, dnfWidth]
  | orGate gates =>
    -- After `cases`, the rekey reduces and `dnfWidth` unfolds.
    simp only [ufiRekey]
    change List.foldl max 0
        (List.map
          (fun gate => match gate with
            | UnboundedFanInFormula.andGate literals => literals.length
            | _ => 0)
          (gates.map (ufiRekey φ))) =
       List.foldl max 0
        (List.map
          (fun gate => match gate with
            | UnboundedFanInFormula.andGate literals => literals.length
            | _ => 0)
          gates)
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro g _
    cases g with
    | inputGate _ _ => simp [ufiRekey]
    | constant _ _ => simp [ufiRekey]
    | notGate _ => simp [ufiRekey]
    | andGate lits => simp [ufiRekey]
    | orGate _ => simp [ufiRekey]

/-- **Re-keying preserves the circuit size** (it only relabels `inputGate`
    leaves, never adding or removing gates). -/
theorem ufiRekey_ufiFormulaCircuitSize (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) →
      ufiFormulaCircuitSize (ufiRekey φ formula) = ufiFormulaCircuitSize formula
  | UnboundedFanInFormula.inputGate _ _ => by simp [ufiRekey, ufiFormulaCircuitSize]
  | UnboundedFanInFormula.constant _ _ => by simp [ufiRekey, ufiFormulaCircuitSize]
  | UnboundedFanInFormula.notGate sub => by
      simp only [ufiRekey, ufiFormulaCircuitSize]
      rw [ufiRekey_ufiFormulaCircuitSize φ sub]
  | UnboundedFanInFormula.andGate gates => by
      simp only [ufiRekey, ufiFormulaCircuitSize, List.map_map]
      have hmap : List.map (ufiFormulaCircuitSize ∘ ufiRekey φ) gates
          = List.map ufiFormulaCircuitSize gates :=
        List.map_congr_left (fun g _ => ufiRekey_ufiFormulaCircuitSize φ g)
      rw [hmap]
  | UnboundedFanInFormula.orGate gates => by
      simp only [ufiRekey, ufiFormulaCircuitSize, List.map_map]
      have hmap : List.map (ufiFormulaCircuitSize ∘ ufiRekey φ) gates
          = List.map ufiFormulaCircuitSize gates :=
        List.map_congr_left (fun g _ => ufiRekey_ufiFormulaCircuitSize φ g)
      rw [hmap]

/-- **Re-keyed `ufiCollectInputIndices` is the φ-image of the original.**

    Stated as a recursive theorem to handle the nested-inductive
    structure of `UnboundedFanInFormula`. -/
theorem ufiRekey_collect (φ : Nat → Nat) :
    (formula : UnboundedFanInFormula) →
      ufiCollectInputIndices (ufiRekey φ formula) =
        (ufiCollectInputIndices formula).map φ
  | UnboundedFanInFormula.inputGate i _ => by
      simp [ufiRekey, ufiCollectInputIndices]
  | UnboundedFanInFormula.constant _ _ => by
      simp [ufiRekey, ufiCollectInputIndices]
  | UnboundedFanInFormula.notGate sub => by
      simp only [ufiRekey, ufiCollectInputIndices]
      exact ufiRekey_collect φ sub
  | UnboundedFanInFormula.andGate gates => by
      simp only [ufiRekey, ufiCollectInputIndices, List.flatMap_map,
                 List.map_flatMap]
      apply List.flatMap_congr
      intro g hg
      exact ufiRekey_collect φ g
  | UnboundedFanInFormula.orGate gates => by
      simp only [ufiRekey, ufiCollectInputIndices, List.flatMap_map,
                 List.map_flatMap]
      apply List.flatMap_congr
      intro g hg
      exact ufiRekey_collect φ g

/-- **Re-keyed largest input is bounded by the bound on `φ`.** -/
lemma ufiRekey_ufiLargestInput_lt
    (φ : Nat → Nat) (formula : UnboundedFanInFormula) (m : Nat)
    (hbound : ∀ i ∈ ufiCollectInputIndices formula, φ i < m)
    (hpos : 0 < m) :
    ufiLargestInput (ufiRekey φ formula) < m := by
  unfold ufiLargestInput
  rw [ufiRekey_collect]
  -- Now bound `(List.foldr max 0) ((collect formula).map φ) < m`.
  set indices := ufiCollectInputIndices formula with h_indices
  by_cases hempty : indices = []
  · rw [hempty]; simp only [List.map_nil, List.foldr_nil]; exact hpos
  · -- `(List.foldr max 0) (indices.map φ) ≤ m - 1 < m`.
    have h_le : (List.foldr max 0) (indices.map φ) ≤ m - 1 := by
      apply adder_foldr_max_map_le
      intro i hi
      have := hbound i hi
      omega
    omega

/-- **Assembled input at a live index equals the live-bits entry at the
    corresponding rank.** -/
lemma assembleInput_at_live
    (n : Nat) (live : List Nat) (liveBits deadBits : List Bool)
    (h_lb_len : liveBits.length = live.length)
    (h_lt : ∀ v ∈ live, v < n)
    (i : Nat) (hi_live : i ∈ live)
    (j : Nat) (hj : live.findIdx? (· = i) = some j) :
    (assembleInput n live liveBits deadBits)[i]? =
      liveBits[j]? := by
  -- `i < n` since `live ⊆ [0,n)`.
  have hi_lt : i < n := h_lt i hi_live
  rw [assembleInput_get_at n live liveBits deadBits i hi_lt]
  unfold assembleInputFn
  rw [hj]
  -- Goal: `some (liveBits.getD j false) = liveBits j`. `j` is in range since `findIdx? = some` gives `j < live.length`.
  have hj_lt : j < live.length := by
    rw [List.findIdx?_eq_some_iff_getElem] at hj
    obtain ⟨h_lt', _, _⟩ := hj
    exact h_lt'
  rw [List.getElem?_eq_getElem (by rw [h_lb_len]; exact hj_lt)]
  have hjlt' : j < liveBits.length := by rw [h_lb_len]; exact hj_lt
  -- Goal: `some (liveBits.getD j false) = some liveBits[j]`.
  change some (liveBits.getD j false) = some liveBits[j]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt']
  rfl

/-- **Re-keying preserves the `isCNF` shape.** -/
lemma isCNF_ufiRekey (φ : Nat → Nat) (formula : UnboundedFanInFormula)
    (h : isCNF formula = true) :
    isCNF (ufiRekey φ formula) = true := by
  match formula with
  | UnboundedFanInFormula.inputGate _ _ => simp [isCNF] at h
  | UnboundedFanInFormula.constant _ _ => simp [isCNF] at h
  | UnboundedFanInFormula.notGate _ => simp [isCNF] at h
  | UnboundedFanInFormula.orGate _ => simp [isCNF] at h
  | UnboundedFanInFormula.andGate gates =>
    simp only [isCNF, ufiRekey, List.all_eq_true, List.mem_map] at h ⊢
    rintro y ⟨g, hg, rfl⟩
    have hg_clause : isOrOfInputsOnly g = true := h g hg
    match g, hg_clause with
    | UnboundedFanInFormula.orGate lits, hcl =>
      simp only [isOrOfInputsOnly, List.all_eq_true] at hcl
      simp only [ufiRekey, isOrOfInputsOnly, List.all_eq_true, List.mem_map]
      rintro z ⟨lit, hlit_mem, rfl⟩
      have hlit := hcl lit hlit_mem
      cases lit with
      | inputGate _ _ => simp [ufiRekey, isInput]
      | constant _ _ => simp [isInput] at hlit
      | notGate _ => simp [isInput] at hlit
      | andGate _ => simp [isInput] at hlit
      | orGate _ => simp [isInput] at hlit

/-- **Re-keying preserves CNF clause widths exactly.** -/
lemma ufiRekey_cnfWidth (φ : Nat → Nat) (formula : UnboundedFanInFormula) :
    cnfWidth (ufiRekey φ formula) = cnfWidth formula := by
  cases formula with
  | inputGate _ _ => simp [ufiRekey, cnfWidth]
  | constant _ _ => simp [ufiRekey, cnfWidth]
  | notGate _ => simp [ufiRekey, cnfWidth]
  | orGate _ => simp [ufiRekey, cnfWidth]
  | andGate gates =>
    simp only [ufiRekey]
    change List.foldl max 0
        (List.map
          (fun gate => match gate with
            | UnboundedFanInFormula.orGate literals => literals.length
            | _ => 0)
          (gates.map (ufiRekey φ))) =
       List.foldl max 0
        (List.map
          (fun gate => match gate with
            | UnboundedFanInFormula.orGate literals => literals.length
            | _ => 0)
          gates)
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro g _
    cases g with
    | inputGate _ _ => simp [ufiRekey]
    | constant _ _ => simp [ufiRekey]
    | notGate _ => simp [ufiRekey]
    | orGate lits => simp [ufiRekey]
    | andGate _ => simp [ufiRekey]

/-- **Re-keying a Nat-indexed DNF to the live namespace.**

    Given a `UnboundedFanInDNF n`-shaped formula whose every variable
    index appears in `live`, produce an `UnboundedFanInDNF live.length`
    obtained by replacing each variable index `i` with its rank
    `live.findIdx? (· = i)` (with the `Nodup` hypothesis ensuring
    uniqueness).  Width and eval agreement on assembled inputs are
    preserved.

    The proof factors through five reusable sub-lemmas:
      * `ufiRekey_eval_eq` — eval is preserved under index agreement.
      * `isDNF_ufiRekey` — DNF shape is preserved.
      * `ufiRekey_dnfWidth` — clause widths are preserved.
      * `ufiRekey_ufiLargestInput_lt` — largest input bound transports.
      * `assembleInput_at_live` — bridge: assembled value at a live
        index equals the live-bits entry at its rank.
-/
lemma exists_dnf_rekey_to_live
    {n : Nat} (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_pos : 0 < live.length)
    (g₀ : UnboundedFanInDNF n) (w : Nat)
    (hw_width : dnfWidth g₀.val ≤ w)
    (hvars : ∀ i ∈ ufiCollectInputIndices g₀.val, i ∈ live)
    (deadBits : List Bool) :
    ∃ (g : UnboundedFanInDNF live.length),
      dnfWidth g.val ≤ w ∧
      ufiFormulaCircuitSize g.val ≤ ufiFormulaCircuitSize g₀.val ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval g₀.val
            (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  -- Define the rank function and rekeyed formula.
  set φ : Nat → Nat := fun i => (live.findIdx? (· = i)).getD 0 with hφ_def
  set rekeyed : UnboundedFanInFormula := ufiRekey φ g₀.val with h_rekeyed
  -- Helper: for any `i ∈ live`, extract the canonical rank witness.
  have h_rank_witness : ∀ i ∈ live, ∃ j, live.findIdx? (· = i) = some j ∧
      j < live.length := by
    intro i hi_live
    rcases List.mem_iff_get.mp hi_live with ⟨⟨j, hjlt⟩, hj_eq⟩
    have hj_get : live[j] = i := by simpa using hj_eq
    refine ⟨j, ?_, hjlt⟩
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hjlt, by simpa using hj_get, ?_⟩
    intro k hkj
    simp only [decide_eq_true_eq]
    intro hk_eq
    have hk_lt_len : k < live.length := lt_trans hkj hjlt
    have heq_get : live[k] = live[j] := by rw [hk_eq, hj_get]
    have hk_ne_j : k ≠ j := Nat.ne_of_lt hkj
    exact hk_ne_j (List.Nodup.getElem_inj_iff h_live_nodup |>.mp heq_get)
  -- For every `i ∈ live`, `φ i < live.length`.
  have hφ_lt_of_mem : ∀ i ∈ live, φ i < live.length := by
    intro i hi_live
    obtain ⟨j, hj_eq, hjlt⟩ := h_rank_witness i hi_live
    change (live.findIdx? (· = i)).getD 0 < live.length
    rw [hj_eq]; exact hjlt
  -- Discharge invariants via sub-lemmas.
  have h_lo : ufiLargestInput rekeyed < live.length :=
    ufiRekey_ufiLargestInput_lt φ g₀.val live.length
      (fun i hi => hφ_lt_of_mem i (hvars i hi)) h_live_pos
  have h_dnf : isDNF rekeyed = true :=
    isDNF_ufiRekey φ g₀.val g₀.property.2
  let g : UnboundedFanInDNF live.length := ⟨rekeyed, h_lo, h_dnf⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · -- Width preservation.
    change dnfWidth rekeyed ≤ w
    rw [ufiRekey_dnfWidth]; exact hw_width
  · -- Circuit-size preservation.
    change ufiFormulaCircuitSize rekeyed ≤ ufiFormulaCircuitSize g₀.val
    rw [h_rekeyed, ufiRekey_ufiFormulaCircuitSize]
  · -- Eval agreement.
    intro liveBits h_lb_len
    apply ufiRekey_eval_eq φ g₀.val
    intro i hi
    have hi_live : i ∈ live := hvars i hi
    obtain ⟨j, hj_eq, _hjlt⟩ := h_rank_witness i hi_live
    have hφ_eq : φ i = j := by
      change (live.findIdx? (· = i)).getD 0 = j
      rw [hj_eq]; rfl
    rw [hφ_eq]
    exact assembleInput_at_live n live liveBits deadBits h_lb_len
      h_live_lt i hi_live j hj_eq

/-- **CNF dual of `exists_dnf_rekey_to_live`.**  Re-key a Nat-indexed CNF whose
    variables all lie in `live` to the compact `live.length` namespace,
    preserving `cnfWidth` and eval (under the assemble map). -/
lemma exists_cnf_rekey_to_live
    {n : Nat} (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_pos : 0 < live.length)
    (g₀ : UnboundedFanInCNF n) (w : Nat)
    (hw_width : cnfWidth g₀.val ≤ w)
    (hvars : ∀ i ∈ ufiCollectInputIndices g₀.val, i ∈ live)
    (deadBits : List Bool) :
    ∃ (g : UnboundedFanInCNF live.length),
      cnfWidth g.val ≤ w ∧
      ufiFormulaCircuitSize g.val ≤ ufiFormulaCircuitSize g₀.val ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval g₀.val
            (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  set φ : Nat → Nat := fun i => (live.findIdx? (· = i)).getD 0 with hφ_def
  set rekeyed : UnboundedFanInFormula := ufiRekey φ g₀.val with h_rekeyed
  have h_rank_witness : ∀ i ∈ live, ∃ j, live.findIdx? (· = i) = some j ∧
      j < live.length := by
    intro i hi_live
    rcases List.mem_iff_get.mp hi_live with ⟨⟨j, hjlt⟩, hj_eq⟩
    have hj_get : live[j] = i := by simpa using hj_eq
    refine ⟨j, ?_, hjlt⟩
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hjlt, by simpa using hj_get, ?_⟩
    intro k hkj
    simp only [decide_eq_true_eq]
    intro hk_eq
    have hk_lt_len : k < live.length := lt_trans hkj hjlt
    have heq_get : live[k] = live[j] := by rw [hk_eq, hj_get]
    have hk_ne_j : k ≠ j := Nat.ne_of_lt hkj
    exact hk_ne_j (List.Nodup.getElem_inj_iff h_live_nodup |>.mp heq_get)
  have hφ_lt_of_mem : ∀ i ∈ live, φ i < live.length := by
    intro i hi_live
    obtain ⟨j, hj_eq, hjlt⟩ := h_rank_witness i hi_live
    change (live.findIdx? (· = i)).getD 0 < live.length
    rw [hj_eq]; exact hjlt
  have h_lo : ufiLargestInput rekeyed < live.length :=
    ufiRekey_ufiLargestInput_lt φ g₀.val live.length
      (fun i hi => hφ_lt_of_mem i (hvars i hi)) h_live_pos
  have h_cnf : isCNF rekeyed = true :=
    isCNF_ufiRekey φ g₀.val g₀.property.2
  let g : UnboundedFanInCNF live.length := ⟨rekeyed, h_lo, h_cnf⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · change cnfWidth rekeyed ≤ w
    rw [ufiRekey_cnfWidth]; exact hw_width
  · change ufiFormulaCircuitSize rekeyed ≤ ufiFormulaCircuitSize g₀.val
    rw [h_rekeyed, ufiRekey_ufiFormulaCircuitSize]
  · intro liveBits h_lb_len
    apply ufiRekey_eval_eq φ g₀.val
    intro i hi
    have hi_live : i ∈ live := hvars i hi
    obtain ⟨j, hj_eq, _hjlt⟩ := h_rank_witness i hi_live
    have hφ_eq : φ i = j := by
      change (live.findIdx? (· = i)).getD 0 = j
      rw [hj_eq]; rfl
    rw [hφ_eq]
    exact assembleInput_at_live n live liveBits deadBits h_lb_len
      h_live_lt i hi_live j hj_eq

/-- **Helper: every clause produced by `decisionTreeToDNFClauses` is
    an `andGate` of `inputGate` literals only**, provided the path passed
    in already consists of `inputGate` literals. -/
lemma decisionTreeToDNFClauses_all_and_of_inputs :
    (tree : DecisionTrees.DecisionTree) → (path : List UnboundedFanInFormula) →
      (∀ p ∈ path, isInput p = true) →
      ∀ c ∈ DecisionTrees.decisionTreeToDNFClauses tree path,
        isAndOfInputsOnly c = true
  | DecisionTrees.DecisionTree.dtLeaf false, _, _ => by
      intro c hc
      simp [DecisionTrees.decisionTreeToDNFClauses] at hc
  | DecisionTrees.DecisionTree.dtLeaf true, path, h_path => by
      intro c hc
      simp only [DecisionTrees.decisionTreeToDNFClauses, List.mem_singleton] at hc
      subst hc
      simp only [isAndOfInputsOnly, List.all_eq_true]
      exact h_path
  | DecisionTrees.DecisionTree.dtNode i left right, path, h_path => by
      intro c hc
      simp only [DecisionTrees.decisionTreeToDNFClauses, List.mem_append] at hc
      have h_path_left : ∀ p ∈ path ++ [UnboundedFanInFormula.inputGate i true],
          isInput p = true := by
        intro p hp
        rcases List.mem_append.mp hp with h₁ | h₂
        · exact h_path p h₁
        · simp only [List.mem_singleton] at h₂
          subst h₂; rfl
      have h_path_right : ∀ p ∈ path ++ [UnboundedFanInFormula.inputGate i false],
          isInput p = true := by
        intro p hp
        rcases List.mem_append.mp hp with h₁ | h₂
        · exact h_path p h₁
        · simp only [List.mem_singleton] at h₂
          subst h₂; rfl
      rcases hc with hl | hr
      · exact decisionTreeToDNFClauses_all_and_of_inputs left _ h_path_left c hl
      · exact decisionTreeToDNFClauses_all_and_of_inputs right _ h_path_right c hr

/-- **`decisionTreeToDNF` always produces a DNF.** -/
lemma isDNF_decisionTreeToDNF (tree : DecisionTrees.DecisionTree) :
    isDNF (DecisionTrees.decisionTreeToDNF tree) = true := by
  unfold DecisionTrees.decisionTreeToDNF
  change ((DecisionTrees.decisionTreeToDNFClauses tree []).all
        isAndOfInputsOnly) = true
  rw [List.all_eq_true]
  intro c hc
  exact decisionTreeToDNFClauses_all_and_of_inputs tree [] (by intro p hp; cases hp) c hc

/-- **Helper for `canonicalDecisionTree_eval_eq`**: literal eval is preserved
    by `simpleRestrictLiteral` under a consistent assignment. -/
lemma simpleRestrictLiteral_eval_eq_aux
    (asgn : Nat → Option Bool) (xs : List Bool)
    (h_consistent : ∀ i b, asgn i = some b → xs[i]? = some b)
    (lit : UnboundedFanInFormula) :
    ufiFormulaEval (simpleRestrictLiteral asgn lit) xs =
      ufiFormulaEval lit xs := by
  match lit with
  | .inputGate i neg =>
    cases h : asgn i with
    | none =>
      have hsrl : simpleRestrictLiteral asgn (.inputGate i neg) = .inputGate i neg := by
        simp [simpleRestrictLiteral, h]
      rw [hsrl]
    | some b =>
      have hxs : xs[i]? = some b := h_consistent i b h
      have hsrl : simpleRestrictLiteral asgn (.inputGate i neg) =
          .constant (if neg = true then Bool.not b else b) 0 := by
        simp [simpleRestrictLiteral, h]
      rw [hsrl]
      have hlhs :
          ufiFormulaEval
              (.constant (if neg = true then Bool.not b else b) 0) xs
            = (if neg = true then Bool.not b else b) := by
        unfold ufiFormulaEval; rfl
      rw [hlhs]
      have hrhs :
          ufiFormulaEval (.inputGate i neg) xs =
            (if neg = true then Bool.not b else b) := by
        unfold ufiFormulaEval
        rw [hxs]
        cases neg <;> rfl
      rw [hrhs]
  | .constant _ _ => rfl
  | .notGate _ => rfl
  | .andGate _ => rfl
  | .orGate _ => rfl

/-- **Helper for `canonicalDecisionTree_eval_eq`**: an `andGate` of mapped
    literals evaluates the same as the original under a consistent assignment. -/
lemma simpleRestrictLiteral_andGate_literals_eval_eq_aux
    (asgn : Nat → Option Bool) (xs : List Bool)
    (h_consistent : ∀ i b, asgn i = some b → xs[i]? = some b)
    (lits : List UnboundedFanInFormula) :
    ufiFormulaEval
        (.andGate (lits.map (simpleRestrictLiteral asgn))) xs =
      ufiFormulaEval (.andGate lits) xs := by
  rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all]
  have h_eq :
      (lits.map (simpleRestrictLiteral asgn)).map
          (fun c => ufiFormulaEval c xs) =
        lits.map (fun c => ufiFormulaEval c xs) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro lit _
    exact simpleRestrictLiteral_eval_eq_aux asgn xs h_consistent lit
  rw [h_eq]

/-- **Helper for `canonicalDecisionTree_eval_eq`**: filtering out `constant`
    literals preserves the `.all (· == .one)` predicate when no
    `constant false` is present. -/
lemma andGate_filter_constants_all_eq_aux
    (xs : List Bool) (lits : List UnboundedFanInFormula)
    (h_no_zero : ∀ l ∈ lits, ∀ lbl, l ≠ .constant false lbl) :
    ((lits.filter
        (fun l => match l with | .constant _ _ => false | _ => true)).map
        (fun c => ufiFormulaEval c xs)).all (· == true) =
    (lits.map (fun c => ufiFormulaEval c xs)).all (· == true) := by
  induction lits with
  | nil => rfl
  | cons l rest ih =>
    have h_no_zero_rest : ∀ ll ∈ rest, ∀ lbl, ll ≠ .constant false lbl :=
      fun ll hll lbl => h_no_zero ll (List.mem_cons_of_mem _ hll) lbl
    cases l with
    | constant b lbl =>
      have hb : b = true := by
        cases b with
        | false =>
          exact absurd rfl
            (h_no_zero (.constant false lbl) List.mem_cons_self lbl)
        | true => rfl
      subst hb
      have hfilt :
          List.filter
            (fun l => match l with | .constant _ _ => false | _ => true)
            (.constant true lbl :: rest) =
          List.filter
            (fun l => match l with | .constant _ _ => false | _ => true) rest :=
        rfl
      rw [hfilt, ih h_no_zero_rest]
      simp only [List.map_cons, List.all_cons, ufiFormulaEval, beq_self_eq_true,
        Bool.true_and]
    | inputGate i neg =>
      have hfilt :
          List.filter
            (fun l => match l with | .constant _ _ => false | _ => true)
            (.inputGate i neg :: rest) =
          .inputGate i neg :: List.filter
            (fun l => match l with | .constant _ _ => false | _ => true) rest :=
        rfl
      rw [hfilt, List.map_cons, List.all_cons, List.map_cons, List.all_cons,
        ih h_no_zero_rest]
    | notGate g =>
      have hfilt :
          List.filter
            (fun l => match l with | .constant _ _ => false | _ => true)
            (.notGate g :: rest) =
          .notGate g :: List.filter
            (fun l => match l with | .constant _ _ => false | _ => true) rest :=
        rfl
      rw [hfilt, List.map_cons, List.all_cons, List.map_cons, List.all_cons,
        ih h_no_zero_rest]
    | andGate g =>
      have hfilt :
          List.filter
            (fun l => match l with | .constant _ _ => false | _ => true)
            (.andGate g :: rest) =
          .andGate g :: List.filter
            (fun l => match l with | .constant _ _ => false | _ => true) rest :=
        rfl
      rw [hfilt, List.map_cons, List.all_cons, List.map_cons, List.all_cons,
        ih h_no_zero_rest]
    | orGate g =>
      have hfilt :
          List.filter
            (fun l => match l with | .constant _ _ => false | _ => true)
            (.orGate g :: rest) =
          .orGate g :: List.filter
            (fun l => match l with | .constant _ _ => false | _ => true) rest :=
        rfl
      rw [hfilt, List.map_cons, List.all_cons, List.map_cons, List.all_cons,
        ih h_no_zero_rest]

/-- **Helper for `canonicalDecisionTree_eval_eq`**: filtering out `constant`
    literals preserves `andGate` eval when no `constant false` is present. -/
lemma andGate_filter_constants_eval_eq_aux
    (xs : List Bool) (lits : List UnboundedFanInFormula)
    (h_no_zero : ∀ l ∈ lits, ∀ lbl, l ≠ .constant false lbl) :
    ufiFormulaEval
        (.andGate (lits.filter
          (fun l => match l with | .constant _ _ => false | _ => true))) xs =
      ufiFormulaEval (.andGate lits) xs := by
  rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all,
    andGate_filter_constants_all_eq_aux xs lits h_no_zero]

/-- **Helper for `canonicalDecisionTree_eval_eq`**: a killed term
    (one that `simpleRestrictTerm` returns `none` for) evaluates to `.false`
    on consistent inputs. -/
lemma simpleRestrictTerm_andGate_killed_eval_zero_aux
    (asgn : Nat → Option Bool) (xs : List Bool)
    (h_consistent : ∀ i b, asgn i = some b → xs[i]? = some b)
    (lits : List UnboundedFanInFormula)
    (h_killed : simpleRestrictTerm asgn (.andGate lits) = none) :
    ufiFormulaEval (.andGate lits) xs = false := by
  simp only [simpleRestrictTerm] at h_killed
  split_ifs at h_killed with hany
  rw [List.any_eq_true] at hany
  obtain ⟨lApp, hl_app_mem, hl_app_match⟩ := hany
  rw [List.mem_map] at hl_app_mem
  obtain ⟨lOrig, hl_orig_mem, hl_app_eq⟩ := hl_app_mem
  -- lApp must be `.constant false (some lbl)` from `hl_app_match`.
  have h_l_app_form : ∃ lbl, lApp = .constant false lbl := by
    cases lApp with
    | constant b lbl =>
      cases b with
      | false => exact ⟨lbl, rfl⟩
      | true => simp at hl_app_match
    | inputGate _ _ => simp at hl_app_match
    | notGate _ => simp at hl_app_match
    | andGate _ => simp at hl_app_match
    | orGate _ => simp at hl_app_match
  obtain ⟨lbl_app, h_l_app_eq⟩ := h_l_app_form
  rw [h_l_app_eq] at hl_app_eq
  -- Show lOrig evaluates to `.false` on `xs`.
  have h_orig_zero : ufiFormulaEval lOrig xs = false := by
    cases lOrig with
    | inputGate i neg =>
      simp only [simpleRestrictLiteral] at hl_app_eq
      cases h_asgn : asgn i with
      | none =>
        rw [h_asgn] at hl_app_eq
        cases hl_app_eq
      | some b =>
        rw [h_asgn] at hl_app_eq
        injection hl_app_eq with h_bit _
        have hxs : xs[i]? = some b := h_consistent i b h_asgn
        have hev :
            ufiFormulaEval (.inputGate i neg) xs
              = (if neg = true then Bool.not b else b) := by
          unfold ufiFormulaEval
          rw [hxs]
          cases neg <;> rfl
        rw [hev]
        exact h_bit
    | constant b lbl' =>
      simp only [simpleRestrictLiteral] at hl_app_eq
      injection hl_app_eq with h_bit _
      have hev : ufiFormulaEval (.constant b lbl') xs = b := by
        unfold ufiFormulaEval; rfl
      rw [hev]
      exact h_bit
    | notGate _ =>
      simp only [simpleRestrictLiteral] at hl_app_eq
      cases hl_app_eq
    | andGate _ =>
      simp only [simpleRestrictLiteral] at hl_app_eq
      cases hl_app_eq
    | orGate _ =>
      simp only [simpleRestrictLiteral] at hl_app_eq
      cases hl_app_eq
  -- andGate has at least one `.false` element ⇒ andGate eval = `.false`.
  rw [ufi_eval_andGate_eq_all]
  have hne :
      ((lits.map (fun c => ufiFormulaEval c xs)).all (· == true)) = false := by
    rw [List.all_eq_false]
    refine ⟨ufiFormulaEval lOrig xs, ?_, ?_⟩
    · rw [List.mem_map]; exact ⟨lOrig, hl_orig_mem, rfl⟩
    · rw [h_orig_zero]; decide
  rw [hne]
  rfl

/-- **Helper for `canonicalDecisionTree_eval_eq`**: a surviving term has its
    eval preserved on consistent inputs. -/
lemma simpleRestrictTerm_andGate_some_eval_eq_aux
    (asgn : Nat → Option Bool) (xs : List Bool)
    (h_consistent : ∀ i b, asgn i = some b → xs[i]? = some b)
    (lits : List UnboundedFanInFormula) (t' : UnboundedFanInFormula)
    (h_some : simpleRestrictTerm asgn (.andGate lits) = some t') :
    ufiFormulaEval t' xs = ufiFormulaEval (.andGate lits) xs := by
  simp only [simpleRestrictTerm] at h_some
  split at h_some
  · exact absurd h_some (by intro h; cases h)
  rename_i hany_false
  simp only [Option.some.injEq] at h_some
  subst h_some
  have h_no_zero :
      ∀ l ∈ lits.map (simpleRestrictLiteral asgn),
        ∀ lbl, l ≠ .constant false lbl := by
    intro l hl lbl heq
    apply hany_false
    rw [List.any_eq_true]
    refine ⟨l, hl, ?_⟩
    rw [heq]
  have h_filter :=
    andGate_filter_constants_eval_eq_aux xs
      (lits.map (simpleRestrictLiteral asgn)) h_no_zero
  have h_mapped :=
    simpleRestrictLiteral_andGate_literals_eval_eq_aux asgn xs h_consistent lits
  exact h_filter.trans h_mapped

/-- **Helper for `canonicalDecisionTree_eval_eq`**: the `.any`-equivalence
    after `filterMap (simpleRestrictTerm asgn)` on `terms` (under consistency,
    when each term is `isAndOfInputsOnly`). -/
lemma orGate_filterMap_simpleRestrictTerm_any_eq_aux
    (asgn : Nat → Option Bool) (xs : List Bool)
    (h_consistent : ∀ i b, asgn i = some b → xs[i]? = some b)
    (terms : List UnboundedFanInFormula)
    (h_aoi : ∀ t ∈ terms, isAndOfInputsOnly t = true) :
    ((terms.filterMap (simpleRestrictTerm asgn)).map
        (fun c => ufiFormulaEval c xs)).any (· == true) =
    (terms.map (fun c => ufiFormulaEval c xs)).any (· == true) := by
  induction terms with
  | nil => rfl
  | cons t rest ih =>
    have h_aoi_rest : ∀ tt ∈ rest, isAndOfInputsOnly tt = true :=
      fun tt htt => h_aoi tt (List.mem_cons_of_mem _ htt)
    have h_t_aoi : isAndOfInputsOnly t = true := h_aoi t List.mem_cons_self
    cases t with
    | andGate lits =>
      simp only [List.filterMap_cons]
      cases hsrt : simpleRestrictTerm asgn (.andGate lits) with
      | none =>
        have h_t_zero :=
          simpleRestrictTerm_andGate_killed_eval_zero_aux
            asgn xs h_consistent lits hsrt
        have hzn : ((false == true : Bool)) = false := by decide
        simp only [List.map_cons, List.any_cons, h_t_zero, hzn, Bool.false_or]
        exact ih h_aoi_rest
      | some t' =>
        have h_t_eq :=
          simpleRestrictTerm_andGate_some_eval_eq_aux
            asgn xs h_consistent lits t' hsrt
        simp only [List.map_cons, List.any_cons, h_t_eq, ih h_aoi_rest]
    | inputGate _ _ => simp [isAndOfInputsOnly] at h_t_aoi
    | constant _ _ => simp [isAndOfInputsOnly] at h_t_aoi
    | notGate _ => simp [isAndOfInputsOnly] at h_t_aoi
    | orGate _ => simp [isAndOfInputsOnly] at h_t_aoi

/-- **Helper for `canonicalDecisionTree_eval_eq`**: `simpleRestrictDNF`
    preserves eval on consistent inputs (for orGate of and-of-inputs-only). -/
lemma simpleRestrictDNF_eval_eq_aux
    (asgn : Nat → Option Bool) (xs : List Bool)
    (h_consistent : ∀ i b, asgn i = some b → xs[i]? = some b)
    (terms : List UnboundedFanInFormula)
    (h_aoi : ∀ t ∈ terms, isAndOfInputsOnly t = true) :
    ufiFormulaEval (.orGate (terms.filterMap (simpleRestrictTerm asgn))) xs =
      ufiFormulaEval (.orGate terms) xs := by
  rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any,
    orGate_filterMap_simpleRestrictTerm_any_eq_aux
      asgn xs h_consistent terms h_aoi]

/-- **Canonical-DT eval agreement under a `ρ`-faithful assembly.**

    For any input `xs : List Bool` of length `n` that agrees with the
    restriction map `randomRestrictionToMap n σ ρ` on every
    `ρ`-assigned coordinate, the canonical full-query DT of `f.val`
    under that map evaluates the same as `f.val` on `xs`.

    This is the eval-agreement bridge used by
    `exists_narrow_dnf_from_good_restriction_dnf` to swap `f` for its
    canonical-DT representation before the DT-to-DNF conversion. -/
lemma canonicalDecisionTree_eval_eq
    {n : Nat} {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
    (xs : List Bool) (hxs_len : xs.length = n)
    (hxs_consistent : ∀ i b,
        mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
        xs[i]? = some b) :
    DecisionTrees.evalDecisionTree
        (canonicalDecisionTree f.val
          (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)) xs =
      ufiFormulaEval f.val xs := by
  set assignment : Nat → Option Bool :=
    restrictionAsFunction
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)
    with hasgn_fn_def
  have hdnf : isDNF f.val = true := f.property.2.1
  have hlarge : ufiLargestInput f.val < n := f.property.1
  -- Decompose `f.val` to `orGate terms`.
  rcases hfeq : f.val with _ | _ | _ | _ | terms
  all_goals (try (rw [hfeq] at hdnf; simp only [isDNF, List.all_eq_true,
    Bool.false_eq_true] at hdnf))
  -- Only the `orGate terms` case survives.
  -- `hdnf` is now: ∀ x ∈ terms, isAndOfInputsOnly x = true
  -- Consistency lifts from `randomRestrictionToMap` to `assignment`.
  have h_consistent : ∀ i b, assignment i = some b → xs[i]? = some b := by
    intro i b hi
    -- From `assignment i = some b`, find the corresponding entry in
    -- `mkAssignmentList`.
    simp only [hasgn_fn_def, restrictionAsFunction] at hi
    cases hf :
        (mkAssignmentList ρ.starAssignment.val.val
          ρ.varAssignments n).find? (fun p => p.1 == i) with
    | none => rw [hf] at hi; exact absurd hi (by simp)
    | some pair =>
      rw [hf] at hi
      have hp₁ : pair.1 = i := by
        have := List.find?_some hf
        simp only [beq_iff_eq] at this; exact this
      have hpair_eq : pair = (i, b) := by
        obtain ⟨pa, pb⟩ := pair
        simp only at hp₁; subst hp₁
        simp only [Option.some.injEq] at hi; subst hi
        rfl
      rw [hpair_eq] at hf
      have h_in_list : (i, b) ∈
          mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n :=
        List.mem_of_find?_eq_some hf
      -- From `(i, b) ∈ mkAssignmentList ...`, deduce `i < n`.
      unfold mkAssignmentList at h_in_list
      rw [List.mem_filterMap] at h_in_list
      obtain ⟨v, hv_mem, hv_eq⟩ := h_in_list
      have hv_lt : v < n := List.mem_range.mp hv_mem
      have hi_eq_v : i = v := by
        by_cases hv_live : v ∈ ρ.starAssignment.val.val
        · rw [if_pos hv_live] at hv_eq; cases hv_eq
        · rw [if_neg hv_live] at hv_eq
          cases hl : ρ.varAssignments[
              ((Finset.range v \ ρ.starAssignment.val.val).card)]? with
          | none =>
            simp [hl] at hv_eq
          | some bb =>
            have hv_eq' : some (v, bb) = some (i, b) := by
              simpa [hl] using hv_eq
            have hv_pair : (v, bb) = (i, b) := Option.some.inj hv_eq'
            exact (Prod.mk.inj hv_pair).1.symm
      have hi_lt : i < n := hi_eq_v ▸ hv_lt
      -- Now apply `cr_none_mkAssignmentList_eq` to bridge to `randomRestrictionToMap`.
      have h_cr_eq :=
        cr_none_mkAssignmentList_eq
          ρ.starAssignment.val.val ρ.varAssignments n i hi_lt
      have h_rrm :
          mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b := by
        rw [← h_cr_eq]
        simp only [restrictionAsFunction]
        have hf' :
            (mkAssignmentList ρ.starAssignment.val.val
              ρ.varAssignments n).find? (fun p => p.1 == i) =
                some (i, b) := by
          simpa [mkAssignmentList] using hf
        rw [hf']
      exact hxs_consistent i b h_rrm
  -- The restricted DNF and its clauses.
  set restricted := simpleRestrictDNF assignment (.orGate terms) with hrestricted
  have h_restricted_eq :
      restricted = .orGate (terms.filterMap (simpleRestrictTerm assignment)) := by
    rw [hrestricted]; rfl
  set clauses := dnfClauses restricted with hclauses
  -- Step 1: ClausesVarsInBounds — every clause variable is < xs.length.
  have h_bounds : ClausesVarsInBounds clauses xs := by
    intro c hc litpair hlit
    obtain ⟨li, lb⟩ := litpair
    -- Replicate the argument from `mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree`:
    -- `lit.1 ≤ ufiLargestInput f.val < n = xs.length`.
    rw [hclauses, hrestricted] at hc
    simp only [simpleRestrictDNF, dnfClauses, List.mem_map] at hc
    obtain ⟨t', ht'_mem, ht'_eq⟩ := hc
    rw [List.mem_filterMap] at ht'_mem
    obtain ⟨t, ht_orig, ht_some⟩ := ht'_mem
    have ht_aoi : isAndOfInputsOnly t = true := hdnf t ht_orig
    match t, ht_aoi, ht_some with
    | .andGate lits, _, ht_some =>
    simp only [simpleRestrictTerm] at ht_some
    split at ht_some
    · cases ht_some
    rename_i hnot_killed
    simp only [Option.some.injEq] at ht_some
    subst ht_some
    rw [← ht'_eq] at hlit
    simp only [List.mem_filterMap] at hlit
    obtain ⟨l, hl_mem_filt, hl_match⟩ := hlit
    match l, hl_match with
    | .inputGate vv neg, hl_match =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hl_match
    obtain ⟨rfl, _⟩ := hl_match
    rw [List.mem_filter, List.mem_map] at hl_mem_filt
    obtain ⟨⟨orig, horig_in, horig_eq⟩, _⟩ := hl_mem_filt
    match orig, horig_eq with
    | .inputGate ii bb, horig_eq =>
    simp only [simpleRestrictLiteral] at horig_eq
    cases hai : assignment ii with
    | some bbb =>
      rw [hai] at horig_eq; cases horig_eq
    | none =>
      rw [hai] at horig_eq
      simp only [UnboundedFanInFormula.inputGate.injEq] at horig_eq
      obtain ⟨rfl, _⟩ := horig_eq
      have hv_le : ii ≤ ufiLargestInput f.val := by
        apply mem_le_foldr_max
        rw [hfeq]
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        refine ⟨.andGate lits, ht_orig, ?_⟩
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨.inputGate ii bb, horig_in, by simp [ufiCollectInputIndices]⟩
      have : ii < n := Nat.lt_of_le_of_lt hv_le hlarge
      rw [hxs_len]; exact this
  -- Step 2: bridge DT eval ↔ evalClauses ↔ ufiFormulaEval restricted
  --         ↔ ufiFormulaEval (.orGate terms).
  have h_dt_iff_clauses :
      (DecisionTrees.evalDecisionTree
        (canonicalDecisionTree (.orGate terms)
          (mkAssignmentList ρ.starAssignment.val.val
            ρ.varAssignments n)) xs = true) ↔
      (DecisionTrees.evalClauses xs clauses = true) := by
    constructor
    · intro h
      have := canonicalDecisionTree_sound
        (.orGate terms)
          (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) xs h
      change DecisionTrees.evalClauses xs clauses = true
      rw [hclauses, hrestricted, hasgn_fn_def]; exact this
    · intro h
      apply canonicalDecisionTree_complete
        (.orGate terms)
          (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) xs
      · rw [← hasgn_fn_def, ← hrestricted, ← hclauses]; exact h_bounds
      · rw [← hasgn_fn_def, ← hrestricted, ← hclauses]; exact h
  -- Step 3: evalClauses xs clauses = ufiFormulaEval restricted xs.
  have h_clauses_eq_restricted :
      DecisionTrees.evalClauses xs clauses = ufiFormulaEval restricted xs := by
    rw [hclauses, h_restricted_eq]
    rw [dnfClauses_eq_extractAndLiterals]
    apply DecisionTrees.evalClauses_eq_dnf
    rw [List.all_eq_true]
    intro t' ht'_mem
    rw [List.mem_filterMap] at ht'_mem
    obtain ⟨t, ht_orig, ht_some⟩ := ht'_mem
    have ht_aoi : isAndOfInputsOnly t = true := hdnf t ht_orig
    match t, ht_aoi, ht_some with
    | .andGate lits, h_lits_aoi, ht_some =>
    simp only [simpleRestrictTerm] at ht_some
    split at ht_some
    · cases ht_some
    simp only [Option.some.injEq] at ht_some
    subst ht_some
    -- t' = .andGate (filtered applied); show isAndOfInputsOnly.
    simp only [isAndOfInputsOnly, List.all_eq_true]
    intro lit hlit
    rw [List.mem_filter, List.mem_map] at hlit
    obtain ⟨⟨orig, horig_mem, horig_eq⟩, hlit_pred⟩ := hlit
    -- orig must be inputGate (since lits.all isInput).
    simp only [isAndOfInputsOnly, List.all_eq_true] at h_lits_aoi
    have h_orig_input : isInput orig = true := h_lits_aoi orig horig_mem
    cases orig with
    | inputGate ii bb =>
      simp only [simpleRestrictLiteral] at horig_eq
      cases hai : assignment ii with
      | some _ =>
        rw [hai] at horig_eq
        subst horig_eq
        simp at hlit_pred
      | none =>
        rw [hai] at horig_eq
        subst horig_eq
        rfl
    | constant _ _ => simp [isInput] at h_orig_input
    | notGate _ => simp [isInput] at h_orig_input
    | andGate _ => simp [isInput] at h_orig_input
    | orGate _ => simp [isInput] at h_orig_input
  -- Step 4: ufiFormulaEval restricted xs = ufiFormulaEval (.orGate terms) xs.
  have h_restricted_eq_orig :
      ufiFormulaEval restricted xs = ufiFormulaEval (.orGate terms) xs := by
    rw [h_restricted_eq]
    exact simpleRestrictDNF_eval_eq_aux assignment xs h_consistent terms hdnf
  -- Step 5: combine — DT eval and ufi eval are both Bool-valued, equal.
  set decisionTreeValue := DecisionTrees.evalDecisionTree
    (canonicalDecisionTree (.orGate terms)
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)) xs with h_dt
  set formulaValue := ufiFormulaEval (.orGate terms) xs with h_ufi
  have h_iff : decisionTreeValue = true ↔ formulaValue = true := by
    rw [h_dt, h_ufi]
    rw [h_dt_iff_clauses, h_clauses_eq_restricted, h_restricted_eq_orig]
  cases h_dt_val : decisionTreeValue with
  | false =>
    cases h_ufi_val : formulaValue with
    | false => rfl
    | true =>
      have := h_iff.mpr h_ufi_val
      rw [h_dt_val] at this; exact absurd this (by simp)
  | true =>
    cases h_ufi_val : formulaValue with
    | false =>
      have := h_iff.mp h_dt_val
      rw [h_ufi_val] at this; exact absurd this (by simp)
    | true => rfl

/-- **Canonical-DT branching variables of a good restriction lie in
    `live`.**

    For a "good" `ρ`, every variable index that the canonical
    full-query DT branches on is among the live coordinates.  This
    is the structural invariant of `simpleRestrictDNF` plus the
    grafting-DT construction: every variable that was assigned by
    `ρ` is folded into the clause-restriction step and never
    appears as a DT branching variable. -/
lemma mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree
    {n : Nat} {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
    (live : List Nat)
    (_h_live_eq : (live : Multiset Nat) =
        ρ.starAssignment.val.val.val) :
    ∀ i ∈ DecisionTrees.dtCollectInputIndices
        (canonicalDecisionTree f.val
          (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)),
      i ∈ live := by
  intro i hi
  -- Abbreviations: the canonical DT is built from `clauses = dnfClauses restricted`
  -- where `restricted = simpleRestrictDNF assignment f.val` and
  -- `assignment = restrictionAsFunction assignmentList`,
  -- `assignmentList = mkAssignmentList liveFinset bits n`.
  set assignment : Nat → Option Bool :=
    restrictionAsFunction
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n)
    with hasgn_fn_def
  set clauses : List (List (Nat × Bool)) :=
    dnfClauses (simpleRestrictDNF assignment f.val) with hclauses_def
  -- Reduce `canonicalDecisionTree` via its `let`-bindings.
  have hi' : i ∈ DecisionTrees.dtCollectInputIndices
      (canonicalDecisionTreeAuxPreciseFull clauses.length clauses) := by
    simpa [canonicalDecisionTree,
           hasgn_fn_def, hclauses_def] using hi
  -- Step 1: structural lemma — branching vars come from clauses.
  obtain ⟨c, hc_mem, hi_in_c⟩ :=
    canonicalDecisionTreeAuxPreciseFull_vars_in clauses.length clauses i hi'
  rw [List.mem_map] at hi_in_c
  obtain ⟨⟨v, b⟩, hvb_mem, rfl⟩ := hi_in_c
  -- Step 2: extract `assignment v = none` AND `v ≤ ufiLargestInput f.val`
  -- by drilling into the structure of `simpleRestrictDNF` and `dnfClauses`.
  have hdnf_bool : isDNF f.val = true := f.property.2.1
  have h_large : ufiLargestInput f.val < n := f.property.1
  have h_extract : assignment v = none ∧ v ≤ ufiLargestInput f.val := by
    -- `f.val` is an `orGate` since `isDNF`.
    rcases hfeq : f.val with _ | _ | _ | _ | terms
    all_goals (try (simp only [hfeq, isDNF, List.all_eq_true,
      Bool.false_eq_true] at hdnf_bool))
    -- Only the `orGate terms` case survives.
    -- Now unfold `simpleRestrictDNF` and `dnfClauses` on it.
    rw [hclauses_def] at hc_mem
    simp only [hfeq, simpleRestrictDNF, dnfClauses, List.mem_map] at hc_mem
    obtain ⟨t', ht'_mem, ht'_eq⟩ := hc_mem
    rw [List.mem_filterMap] at ht'_mem
    obtain ⟨t, ht_orig, ht_some⟩ := ht'_mem
    -- `t` must be `andGate` since `isDNF` says all terms are and-of-inputs-only.
    have ht_aoi : isAndOfInputsOnly t = true := hdnf_bool _ ht_orig
    match t, ht_aoi, ht_some with
    | .andGate lits, _, ht_some =>
    -- `t = andGate lits`. Unfold `simpleRestrictTerm`.
    simp only [simpleRestrictTerm] at ht_some
    split at ht_some
    · cases ht_some
    rename_i hnot_killed
    simp only [Option.some.injEq] at ht_some
    subst ht_some
    -- `t' = andGate (filtered restricted lits)`. Substitute back into clause definition.
    rw [← ht'_eq] at hvb_mem
    simp only [List.mem_filterMap] at hvb_mem
    obtain ⟨lit, hlit_mem_filt, hlit_match⟩ := hvb_mem
    -- `lit` must be `inputGate` because the surrounding match returned `some (v, b)`.
    match lit, hlit_match with
    | .inputGate vv neg, hlit_match =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hlit_match
    obtain ⟨rfl, rfl⟩ := hlit_match
    -- `inputGate v b ∈ (lits.map (simpleRestrictLiteral assignment)).filter _`.
    rw [List.mem_filter, List.mem_map] at hlit_mem_filt
    obtain ⟨⟨orig, horig_in, horig_eq⟩, _⟩ := hlit_mem_filt
    -- Case on `orig`: `inputGate ii bb` is the only one that can map to `inputGate v b`.
    match orig, horig_eq with
    | .inputGate ii bb, horig_eq =>
    -- `simpleRestrictLiteral assignment (inputGate ii bb) = inputGate v b`.
    simp only [simpleRestrictLiteral] at horig_eq
    cases hai : assignment ii with
    | some bbb =>
      rw [hai] at horig_eq
      cases horig_eq
    | none =>
      rw [hai] at horig_eq
      simp only [UnboundedFanInFormula.inputGate.injEq] at horig_eq
      obtain ⟨rfl, rfl⟩ := horig_eq
      refine ⟨hai, ?_⟩
      -- `v ≤ ufiLargestInput (orGate terms)`.
      apply mem_le_foldr_max
      simp only [ufiCollectInputIndices, List.mem_flatMap]
      refine ⟨.andGate lits, ht_orig, ?_⟩
      simp only [ufiCollectInputIndices, List.mem_flatMap]
      exact ⟨.inputGate ii bb, horig_in, by simp [ufiCollectInputIndices]⟩
  obtain ⟨h_asgn_none, h_v_le⟩ := h_extract
  have hv_lt : v < n := Nat.lt_of_le_of_lt h_v_le h_large
  -- Step 3: bridge `assignment v = none` → `mkAssignment ... v = none`.
  have h_mk_none :
      mkAssignment ρ.starAssignment.val.val ρ.varAssignments v = none := by
    have heq := cr_none_mkAssignmentList_eq
      ρ.starAssignment.val.val ρ.varAssignments n v hv_lt
    -- `assignment v = combineRestrictions ... (mkAssignmentList ...) v`.
    have hunfold : assignment v = restrictionAsFunction
        (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) v := by
      simp [hasgn_fn_def]
    rw [hunfold, heq] at h_asgn_none
    exact h_asgn_none
  -- Step 4: derive Finset membership in `liveVars`.
  have h_in_finset : v ∈ ρ.starAssignment.val.val :=
    mkAssignment_none_imp_mem
      ρ.starAssignment.val.val ρ.varAssignments n
      ρ.starAssignment.val.property
      ρ.non_starred_vars_fully_assigned
      v hv_lt h_mk_none
  -- Step 5: convert Finset → Multiset → List.
  have h_in_mset : v ∈ ρ.starAssignment.val.val.val :=
    Finset.mem_def.mp h_in_finset
  rw [← _h_live_eq] at h_in_mset
  exact Multiset.mem_coe.mp h_in_mset

/- **Circuit-size bounds for the DT → DNF conversion.**  Needed to
   discharge the polynomial-size field of the switching step: a
   depth-`≤ t` decision tree yields a DNF of circuit size
   `≤ 1 + 2^(t+1)·(t+1)`. -/

/- A decision tree has `< 2^(depth+1)` nodes (binary-tree leaf bound). -/
lemma decisionTreeNodeCount_succ_le_pow (t : DecisionTrees.DecisionTree) :
    DecisionTrees.decisionTreeNodeCount t + 1
      ≤ 2 ^ (DecisionTrees.decisionTreeDepth t + 1) := by
  induction t with
  | dtLeaf b =>
      simp [DecisionTrees.decisionTreeNodeCount, DecisionTrees.decisionTreeDepth]
  | dtNode i l r ihl ihr =>
      set m := max (DecisionTrees.decisionTreeDepth l)
        (DecisionTrees.decisionTreeDepth r) with hm
      have hl : 2 ^ (DecisionTrees.decisionTreeDepth l + 1) ≤ 2 ^ (m + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hr : 2 ^ (DecisionTrees.decisionTreeDepth r + 1) ≤ 2 ^ (m + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpow : 2 ^ (1 + m + 1) = 2 ^ (m + 1) + 2 ^ (m + 1) := by
        rw [show 1 + m + 1 = (m + 1) + 1 by omega, pow_succ]; ring
      simp only [DecisionTrees.decisionTreeNodeCount, DecisionTrees.decisionTreeDepth,
        ← hm]
      omega

/- Sum of circuit sizes of the DNF clauses produced from `tree` along
   `path`, bounded by `circuit_size(tree)·(|path| + depth + 1)`. -/
lemma decisionTreeToDNFClauses_node_sum_le
    (tree : DecisionTrees.DecisionTree) (path : List UnboundedFanInFormula) :
    ((DecisionTrees.decisionTreeToDNFClauses tree path).map ufiFormulaCircuitSize).sum
      ≤ DecisionTrees.decisionTreeNodeCount tree
          * ((path.map ufiFormulaCircuitSize).sum
              + DecisionTrees.decisionTreeDepth tree + 1) := by
  induction tree generalizing path with
  | dtLeaf b =>
      cases b with
      | false =>
          simp [DecisionTrees.decisionTreeToDNFClauses,
            DecisionTrees.decisionTreeNodeCount, DecisionTrees.decisionTreeDepth]
      | true =>
          simp only [DecisionTrees.decisionTreeToDNFClauses,
            DecisionTrees.decisionTreeNodeCount, DecisionTrees.decisionTreeDepth,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            ufiFormulaCircuitSize]
          omega
  | dtNode i l r ihl ihr =>
      have hpl := ihl (path ++ [UnboundedFanInFormula.inputGate i true])
      have hpr := ihr (path ++ [UnboundedFanInFormula.inputGate i false])
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, ufiFormulaCircuitSize] at hpl hpr
      set pathSize := (path.map ufiFormulaCircuitSize).sum with h_path_size
      set ncl := DecisionTrees.decisionTreeNodeCount l with hncl
      set ncr := DecisionTrees.decisionTreeNodeCount r with hncr
      set dl := DecisionTrees.decisionTreeDepth l with hdl
      set dr := DecisionTrees.decisionTreeDepth r with hdr
      set depth := max dl dr with h_depth
      -- Lift each child bound to the common factor `(pathSize + depth + 2)`.
      have h₁ : ((DecisionTrees.decisionTreeToDNFClauses l
            (path ++ [UnboundedFanInFormula.inputGate i true])).map ufiFormulaCircuitSize).sum
          ≤ ncl * (pathSize + depth + 2) :=
        le_trans hpl (Nat.mul_le_mul_left _ (by omega))
      have h₂ : ((DecisionTrees.decisionTreeToDNFClauses r
            (path ++ [UnboundedFanInFormula.inputGate i false])).map ufiFormulaCircuitSize).sum
          ≤ ncr * (pathSize + depth + 2) :=
        le_trans hpr (Nat.mul_le_mul_left _ (by omega))
      simp only [DecisionTrees.decisionTreeToDNFClauses,
        DecisionTrees.decisionTreeNodeCount, DecisionTrees.decisionTreeDepth,
        List.map_append, List.sum_append, ← hncl, ← hncr, ← hdl, ← hdr, ← h_depth]
      calc ((DecisionTrees.decisionTreeToDNFClauses l
                (path ++ [UnboundedFanInFormula.inputGate i true])).map
                ufiFormulaCircuitSize).sum
            + ((DecisionTrees.decisionTreeToDNFClauses r
                (path ++ [UnboundedFanInFormula.inputGate i false])).map
                ufiFormulaCircuitSize).sum
          ≤ ncl * (pathSize + depth + 2) + ncr * (pathSize + depth + 2) := Nat.add_le_add h₁ h₂
        _ = (ncl + ncr) * (pathSize + depth + 2) := by ring
        _ ≤ (1 + ncl + ncr) * (pathSize + (1 + depth) + 1) := by
              apply Nat.mul_le_mul <;> omega

/- The DNF of a decision tree has circuit size `≤ 1 + circuit_size·(depth+1)`. -/
lemma decisionTreeToDNF_ufiFormulaCircuitSize_le (tree : DecisionTrees.DecisionTree) :
    ufiFormulaCircuitSize (DecisionTrees.decisionTreeToDNF tree)
      ≤ 1 + DecisionTrees.decisionTreeNodeCount tree
          * (DecisionTrees.decisionTreeDepth tree + 1) := by
  have h := decisionTreeToDNFClauses_node_sum_le tree []
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at h
  simp only [DecisionTrees.decisionTreeToDNF, ufiFormulaCircuitSize]
  omega

lemma properDNFCanonicalDecisionTree_eq_canonicalDecisionTree
    {n : Nat} {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n) :
    properDNFCanonicalDecisionTree f ρ =
      canonicalDecisionTree f.val
        (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) := by
  unfold properDNFCanonicalDecisionTree canonicalDecisionTree restrictDNF
  cases f.val <;> rfl

/-- **Analytic core of `exists_depth_two_dnf_collapse`**.

    Given a "good" restriction `ρ` for a `UnboundedFanInProperDNF n` —
    i.e. one whose canonical full-query decision tree has depth at
    most `decisionTreeDepthBound` (equivalently,
    `¬ isBadRestriction decisionTreeDepthBound n σ f ρ`) —
    together with the `(live, deadBits)` partition produced by
    `exists_assembled_restriction` and the live-count bounds, produce
    a width-`decisionTreeDepthBound` DNF on the live coordinates that agrees with the
    original DNF on every assembled input.

    The proof factors through five reusable sub-lemmas:

      * `decisionTreeToDNF_dnfWidth_le_decisionTreeDepth` — pure DT fact: the
        canonical DT's clause widths are bounded by its depth.
      * `mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree` — the
        canonical DT only branches on live coordinates (dead ones are
        already fixed by `ρ`).
      * `canonicalDecisionTree_eval_eq` — the canonical DT and `f`
        agree on all `ρ`-consistent inputs.
      * `exists_dnf_rekey_to_live` — re-key the resulting Nat-indexed DNF
        into the compact `live.length` namespace.
      * Standard `decisionTreeToDNF` eval correctness.

    The CNF dual `exists_depth_two_cnf_collapse` reuses this same lemma after a
    De Morgan transformation. -/
lemma exists_narrow_dnf_from_good_restriction_dnf
    {n : Nat} (decisionTreeDepthBound : Nat) {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
    (hρ : ¬ isBadRestriction decisionTreeDepthBound n σ f ρ)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_dt_lt : decisionTreeDepthBound < live.length) :
    ∃ (g : UnboundedFanInDNF live.length),
      dnfWidth g.val ≤ decisionTreeDepthBound ∧
      ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval f.val
            (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  -- Step 1: extract the DT depth bound from `¬ isBadRestriction`.
  set tree :=
    canonicalDecisionTree f.val
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) with htree
  have h_depth_le : DecisionTrees.decisionTreeDepth tree ≤ decisionTreeDepthBound := by
    unfold isBadRestriction at hρ
    rw [properDNFCanonicalDecisionTree_eq_canonicalDecisionTree, ← htree] at hρ
    -- `hρ : ¬ (decisionTreeDepth tree > decisionTreeDepthBound) = true`
    have : ¬ (decisionTreeDepthBound < DecisionTrees.decisionTreeDepth tree) := by
      intro hlt
      apply hρ
      simpa [decide_eq_true_eq] using hlt
    omega
  -- Step 2: width bound for the Nat-indexed DT-to-DNF.
  set rawFormula₀ : UnboundedFanInFormula := DecisionTrees.decisionTreeToDNF tree
    with hg₀_raw
  have h_width_g₀ : dnfWidth rawFormula₀ ≤ decisionTreeDepthBound := by
    have h₁ := decisionTreeToDNF_dnfWidth_le_decisionTreeDepth tree
    -- `h₁ : dnfWidth (decisionTreeToDNF tree) ≤ decisionTreeDepth tree`
    -- and `rawFormula₀ = decisionTreeToDNF tree` definitionally.
    change dnfWidth (DecisionTrees.decisionTreeToDNF tree) ≤ decisionTreeDepthBound
    omega
  -- Step 3: branching variables of `tree` are all in `live`.
  have h_branch_in_live :=
    mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree f ρ live h_live_eq
  -- Step 4: package `rawFormula₀` as a `UnboundedFanInDNF n` so we can
  -- invoke `exists_dnf_rekey_to_live`.
  -- This requires `ufiLargestInput rawFormula₀ < n` and `isDNF rawFormula₀ = true`.
  have h_g₀_vars_subset :
      ∀ i ∈ ufiCollectInputIndices rawFormula₀, i ∈ live := by
    intro i hi
    have h_dt : i ∈ DecisionTrees.dtCollectInputIndices tree := by
      exact DecisionTrees.dnf_inputs_sub_dt_inputs tree i hi
    exact h_branch_in_live i h_dt
  have h_g₀_inputs_lt : ufiLargestInput rawFormula₀ < n := by
    unfold ufiLargestInput
    apply Nat.lt_of_le_of_lt
      (adder_foldr_max_le_of_all_le
        (l := ufiCollectInputIndices rawFormula₀) (k := n - 1) ?_)
    · omega
    · intro i hi
      have hi_live := h_g₀_vars_subset i hi
      have hi_lt : i < n := h_live_lt i hi_live
      omega
  have h_g₀_is_dnf : isDNF rawFormula₀ = true :=
    isDNF_decisionTreeToDNF tree
  let g₀ : UnboundedFanInDNF n := ⟨rawFormula₀, h_g₀_inputs_lt, h_g₀_is_dnf⟩
  have h_g₀_vars_in_live :
      ∀ i ∈ ufiCollectInputIndices g₀.val, i ∈ live := h_g₀_vars_subset
  have h_live_pos : 0 < live.length := by omega
  -- Step 5: re-key to the compact namespace.
  obtain ⟨g, hg_width, hg_size, hg_eval₀⟩ :=
    exists_dnf_rekey_to_live live h_live_lt h_live_nodup h_live_pos g₀ decisionTreeDepthBound
      h_width_g₀ h_g₀_vars_in_live deadBits
  -- Circuit-size bound: rekey preserves circuit size, and `rawFormula₀` is a
  -- DT-to-DNF whose circuit size is bounded by the depth via Phase-1 lemmas.
  have h_size_g₀ :
      ufiFormulaCircuitSize rawFormula₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
    rw [hg₀_raw]
    have h₁ := decisionTreeToDNF_ufiFormulaCircuitSize_le tree
    have h₂ := decisionTreeNodeCount_succ_le_pow tree
    have hpow : (2 : Nat) ^ (DecisionTrees.decisionTreeDepth tree + 1)
        ≤ 2 ^ (decisionTreeDepthBound + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc ufiFormulaCircuitSize (DecisionTrees.decisionTreeToDNF tree)
        ≤ 1 + DecisionTrees.decisionTreeNodeCount tree
            * (DecisionTrees.decisionTreeDepth tree + 1) := h₁
      _ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul <;> omega
  have h_size_g : ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) :=
    le_trans hg_size h_size_g₀
  refine ⟨g, hg_width, h_size_g, ?_⟩
  intro liveBits h_lb_len
  -- Step 6: eval agreement.
  --   f on assembled  =[canonicalDecisionTree_eval_eq]=  tree on assembled
  --                  =[decisionTreeToDNF eval]=         g₀ on assembled
  --                  =[hg_eval₀]=                          g on liveBits
  set xs := assembleInput n live liveBits deadBits with hxs
  have hxs_len : xs.length = n :=
    length_assembleInput n live liveBits deadBits
  have hxs_consistent :
      ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
        xs[i]? = some b := h_assemble liveBits h_lb_len
  have h_dt_eq :
      DecisionTrees.evalDecisionTree tree xs =
        ufiFormulaEval f.val xs :=
    canonicalDecisionTree_eval_eq f ρ xs hxs_len hxs_consistent
  have h_dnf_eq :
      ufiFormulaEval rawFormula₀ xs =
        DecisionTrees.evalDecisionTree tree xs := by
    have h_range : ∀ i ∈ DecisionTrees.dtCollectInputIndices tree,
        i < xs.length := by
      intro i hi
      have hi_live := h_branch_in_live i hi
      have hi_lt : i < n := h_live_lt i hi_live
      rw [hxs_len]; exact hi_lt
    have := DecisionTrees.decisionTreeToDNF_eval_equiv tree xs h_range
    -- `this : evalDecisionTree tree xs = ufiFormulaEval (decisionTreeToDNF tree) xs`
    exact this.symm
  have h_g_eq :
      ufiFormulaEval g₀.val xs = ufiFormulaEval g.val liveBits :=
    hg_eval₀ liveBits h_lb_len
  change ufiFormulaEval f.val xs = ufiFormulaEval g.val liveBits
  rw [← h_dt_eq, ← h_dnf_eq]
  change ufiFormulaEval g₀.val xs = ufiFormulaEval g.val liveBits
  exact h_g_eq

/-- **Single-DNF switching collapse, OR-rooted depth-2 case.**
    A `UnboundedFanInProperDNF n` of *bottom fan-in* (width) `≤ w`
    admits a single deterministic restriction `(live, deadBits)`
    such that the restricted formula equals a width-`w' < live.length`
    DNF on `live.length` live coordinates, **provided `20·(w+1) < n`**.

    The threshold `20·(w+1) < n` is satisfiable exactly when the DNF
    width `w` is small relative to `n` (e.g. `w` constant, `n` large) —
    which is the regime in which the switching lemma is useful.  This
    is the honest hypothesis: a *single* restriction collapses a
    width-`w` DNF onto `Θ(n/w)` live variables, so we need `n/w` large
    to retain at least 2 live variables (one more than the canonical
    DT depth `decisionTreeDepthBound = 1`).

    Note this width `w` is the BOTTOM FAN-IN, NOT the circuit-size bound
    `c·n^k`.  Feeding the loose circuit-size bound here would force
    `20·(c·n^k+1) < n`, which is unsatisfiable for `k ≥ 1`; that
    reflects the genuine fact that a single restriction cannot collapse
    a polynomially-wide DNF.  In the iterated framework the relevant
    width at the depth-2 base case is the constant decision-tree depth
    delivered by the previous switching round.

    Strategy: pick exactly two live variables, i.e. `σ := 2/n`, and
    DT depth bound `decisionTreeDepthBound := 1`; the analytic bound
    `(10·σ·w)^1 = 20w/n < 1` from the exact single-DNF switching
    lemma forces existence of a `ρ`
    with canonical-DT depth `≤ decisionTreeDepthBound`; convert `ρ` to (live, deadBits)
    via `exists_assembled_restriction`; then convert the canonical DT
    into a width-`decisionTreeDepthBound` DNF on the live coordinates via
    `exists_narrow_dnf_from_good_restriction_dnf`.  The live-count bound
    `decisionTreeDepthBound < live.length` follows from `live.length = ⌈σ·n⌉ = 2`.

    The constant `20` is therefore the product `10 · 2`, not a separate
    switching-lemma constant.  The factor `10` comes from the exact switching
    estimate `(10·σ·w)^d`; the factor `2` comes from retaining the smallest
    integer number of variables strictly greater than the target tree depth
    `1`.  Substituting `σ = 2/n` gives `10·σ·w = 20w/n`.  The stated
    hypothesis uses `w + 1` rather than `w`: `20(w+1) < n` uniformly implies
    `20w/n < 1`, including when `w = 0`, and also makes `n` large enough for
    `σ = 2/n` to lie in the required range `0 < σ ≤ 1/5`. -/
lemma exists_depth_two_dnf_collapse
    (w : Nat) {n : Nat}
    (f : UnboundedFanInProperDNF n)
    (hwidth : dnfWidth f.val ≤ w)
    (h_thresh : 20 * (w + 1) < n) :
    ∃ (live : List Nat)
      (_h_live_lt : ∀ v ∈ live, v < n)
      (_h_live_nodup : live.Nodup)
      (_h_live_big : 2 ≤ live.length)
      (deadBits : List Bool)
      (w' : Nat) (_hw : w' < live.length)
      (g : UnboundedFanInDNF live.length),
      dnfWidth g.val ≤ w' ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval f.val
            (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  -- Step 1: construct exact σ := 2/n ≤ 1/5 directly, with the
  --         canonical DT depth bound decisionTreeDepthBound := 1.
  have hn_pos_nat : 0 < n := by omega
  have hnq_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos_nat
  set σv : ℚ := 2 / (n : ℚ) with hσv_def
  have hσv_pos : 0 < σv := by rw [hσv_def]; positivity
  have hσv_lt_one : σv < 1 := by
    rw [hσv_def, div_lt_one hnq_pos]
    have h_twenty_lt_n : (20 : Nat) < n := by
      have h20le : 20 ≤ 20 * (w + 1) := by nlinarith
      omega
    exact_mod_cast (by omega : 2 < n)
  have hσv_le_fifth : σv ≤ 1 / 5 := by
    rw [hσv_def]
    rw [div_le_iff₀ hnq_pos]
    have h_twenty_lt_n : (20 : Nat) < n := by
      have h20le : 20 ≤ 20 * (w + 1) := by nlinarith
      omega
    have h10q : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (by omega : 10 ≤ n)
    nlinarith
  set σ : OpenUnitIntervalQ := ⟨σv, hσv_pos, hσv_lt_one⟩ with hσ_def
  set decisionTreeDepthBound : Nat := 1 with hd_dt_def
  have hσn : σ.val * (n : ℚ) = 2 := by
    change σv * (n : ℚ) = 2
    rw [hσv_def]
    field_simp [ne_of_gt hnq_pos]
  have hs_exact : (Nat.ceil (σ.val * (n : ℚ)) : ℚ) = σ.val * (n : ℚ) := by
    rw [hσn]
    norm_num
  have h_ten_sigma_w : 10 * σ.val * ((w : Nat) : ℚ) = (20 * (w : ℚ)) / (n : ℚ) := by
    change 10 * σv * ((w : Nat) : ℚ) = (20 * (w : ℚ)) / (n : ℚ)
    rw [hσv_def]
    ring
  have h_base_lt_one : (20 * (w : ℚ)) / (n : ℚ) < 1 := by
    rw [div_lt_one hnq_pos]
    have hcast : (20 : ℚ) * ((w : ℚ) + 1) < (n : ℚ) := by
      have hth : (20 * (w + 1) : Nat) < n := h_thresh
      have : ((20 * (w + 1) : Nat) : ℚ) < ((n : Nat) : ℚ) := by exact_mod_cast hth
      push_cast at this ⊢
      linarith
    nlinarith
  have h_bound' : (10 * σ.val * ((w : Nat) : ℚ)) ^ decisionTreeDepthBound < 1 := by
    rw [h_ten_sigma_w, hd_dt_def]
    simpa using h_base_lt_one
  -- Step 2: apply switching-lemma pigeonhole at width `w`.
  obtain ⟨ρ, hρ_not_bad⟩ :=
    exists_switching_lemma_pigeonhole_exact w decisionTreeDepthBound f hwidth σ hσv_le_fifth hs_exact h_bound'
  -- Step 3: convert ρ into the (live, deadBits) shape.
  obtain ⟨live, h_live_lt, h_live_nodup, deadBits, h_card, h_live_eq, h_assemble⟩ :=
    exists_assembled_restriction ρ
  -- Step 4: live-count bounds.  `live.length = ⌈σ·n⌉ = 2`.
  have h_live_card : live.length = Nat.ceil (σ.val * (n : ℚ)) := by
    have h₁ : live.length = ρ.starAssignment.val.val.card := by
      have hcard := congrArg Multiset.card h_live_eq
      simp only [Multiset.coe_card] at hcard
      exact hcard
    rw [h₁, ρ.starAssignment.property]
  have h_live_big : 2 ≤ live.length := by
    rw [h_live_card, hσn]
    norm_num
  have h_dt_lt : decisionTreeDepthBound < live.length := by rw [hd_dt_def]; omega
  -- Step 5: invoke the analytic core.
  obtain ⟨g, hg_width, _, hg_eval⟩ :=
    exists_narrow_dnf_from_good_restriction_dnf decisionTreeDepthBound f ρ hρ_not_bad
      live h_live_lt h_live_nodup h_live_eq deadBits h_card h_assemble h_dt_lt
  refine ⟨live, h_live_lt, h_live_nodup, h_live_big, deadBits,
          decisionTreeDepthBound, h_dt_lt, g, hg_width, hg_eval⟩

/- ===================================================================
   De Morgan dualization infrastructure for the CNF collapse.

   A width-`w` CNF `f` has a De Morgan dual DNF `cnfDual f` of width
   `w` computing `¬ f`.  We apply the switching machinery to that dual
   DNF, obtain its canonical decision tree, NEGATE that tree at the
   leaf level (which preserves depth and variable set, hence width),
   and convert to a narrow DNF computing `¬¬ f = f`.  Negating at the
   tree level — not at the formula level — is what keeps width bounded
   under duality.
   =================================================================== -/

/- Negate a decision tree by flipping every leaf.  Structure (hence
   depth and branching-variable set) is preserved. -/
def dtNegate : DecisionTrees.DecisionTree → DecisionTrees.DecisionTree
  | .dtLeaf b => .dtLeaf (not b)
  | .dtNode i l r => .dtNode i (dtNegate l) (dtNegate r)

lemma dtNegate_depth (t : DecisionTrees.DecisionTree) :
    DecisionTrees.decisionTreeDepth (dtNegate t) =
      DecisionTrees.decisionTreeDepth t := by
  induction t with
  | dtLeaf b => rfl
  | dtNode i l r ihl ihr =>
    simp only [dtNegate, DecisionTrees.decisionTreeDepth, ihl, ihr]

lemma dtNegate_dtCollectInputIndices (t : DecisionTrees.DecisionTree) :
    DecisionTrees.dtCollectInputIndices (dtNegate t) =
      DecisionTrees.dtCollectInputIndices t := by
  induction t with
  | dtLeaf b => rfl
  | dtNode i l r ihl ihr =>
    simp only [dtNegate, DecisionTrees.dtCollectInputIndices, ihl, ihr]

lemma dtNegate_eval :
    ∀ (t : DecisionTrees.DecisionTree) (xs : List Bool),
      (∀ i ∈ DecisionTrees.dtCollectInputIndices t, i < xs.length) →
      DecisionTrees.evalDecisionTree (dtNegate t) xs =
        not (DecisionTrees.evalDecisionTree t xs) := by
  intro t
  induction t with
  | dtLeaf b =>
    intro xs _h
    simp only [dtNegate, DecisionTrees.evalDecisionTree]
  | dtNode i l r ihl ihr =>
    intro xs h_range
    have hi_mem : i ∈ DecisionTrees.dtCollectInputIndices
        (DecisionTrees.DecisionTree.dtNode i l r) := by
      simp [DecisionTrees.dtCollectInputIndices]
    have hi_lt : i < xs.length := h_range i hi_mem
    have hget : xs[i]? = some xs[i] := by
      exact List.getElem?_eq_getElem hi_lt
    have h_range_l : ∀ j ∈ DecisionTrees.dtCollectInputIndices l, j < xs.length := by
      intro j hj; apply h_range
      simp only [DecisionTrees.dtCollectInputIndices, List.mem_append, List.mem_cons]
      tauto
    have h_range_r : ∀ j ∈ DecisionTrees.dtCollectInputIndices r, j < xs.length := by
      intro j hj; apply h_range
      simp only [DecisionTrees.dtCollectInputIndices, List.mem_append, List.mem_cons]
      tauto
    simp only [dtNegate, DecisionTrees.evalDecisionTree, hget]
    cases hv : xs[i] with
    | false => exact ihl xs h_range_l
    | true => exact ihr xs h_range_r

/- The CNF that a decision tree collapses to: dualize the DNF of the
   leaf-negated tree.  Computes exactly the same function as the tree. -/
def decisionTreeToCNF (t : DecisionTrees.DecisionTree) : UnboundedFanInFormula :=
  dnfDual (DecisionTrees.decisionTreeToDNF (dtNegate t))

lemma isCNF_decisionTreeToCNF (t : DecisionTrees.DecisionTree) :
    isCNF (decisionTreeToCNF t) = true :=
  isCNF_dnfDual _ (isDNF_decisionTreeToDNF (dtNegate t))

lemma decisionTreeToCNF_cnfWidth_le_decisionTreeDepth (t : DecisionTrees.DecisionTree) :
    cnfWidth (decisionTreeToCNF t) ≤ DecisionTrees.decisionTreeDepth t := by
  unfold decisionTreeToCNF
  rw [dnfDual_width _ (isDNF_decisionTreeToDNF (dtNegate t))]
  calc dnfWidth (DecisionTrees.decisionTreeToDNF (dtNegate t))
      ≤ DecisionTrees.decisionTreeDepth (dtNegate t) :=
        decisionTreeToDNF_dnfWidth_le_decisionTreeDepth (dtNegate t)
    _ = DecisionTrees.decisionTreeDepth t := dtNegate_depth t

/- `negLit`, `dualAndClause`, and `dnfDual` all preserve circuit size. -/
lemma negLit_ufiFormulaCircuitSize (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (negLit g) = ufiFormulaCircuitSize g := by
  cases g <;> simp [negLit, ufiFormulaCircuitSize]

lemma dualAndClause_ufiFormulaCircuitSize (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (dualAndClause g) = ufiFormulaCircuitSize g := by
  cases g with
  | andGate lits =>
      simp only [dualAndClause, ufiFormulaCircuitSize, List.map_map]
      have : (lits.map (ufiFormulaCircuitSize ∘ negLit))
          = lits.map ufiFormulaCircuitSize :=
        List.map_congr_left (fun l _ => negLit_ufiFormulaCircuitSize l)
      rw [this]
  | inputGate i b => rfl
  | constant b m => rfl
  | notGate g => rfl
  | orGate gs => rfl

lemma dnfDual_ufiFormulaCircuitSize (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (dnfDual g) = ufiFormulaCircuitSize g := by
  cases g with
  | orGate clauses =>
      simp only [dnfDual, ufiFormulaCircuitSize, List.map_map]
      have : (clauses.map (ufiFormulaCircuitSize ∘ dualAndClause))
          = clauses.map ufiFormulaCircuitSize :=
        List.map_congr_left (fun c _ => dualAndClause_ufiFormulaCircuitSize c)
      rw [this]
  | inputGate i b => rfl
  | constant b m => rfl
  | notGate g => rfl
  | andGate gs => rfl

/- `dtNegate` preserves circuit size. -/
lemma dtNegate_decisionTreeNodeCount (t : DecisionTrees.DecisionTree) :
    DecisionTrees.decisionTreeNodeCount (dtNegate t)
      = DecisionTrees.decisionTreeNodeCount t := by
  induction t with
  | dtLeaf b => rfl
  | dtNode i l r ihl ihr =>
      simp only [dtNegate, DecisionTrees.decisionTreeNodeCount, ihl, ihr]

/- The CNF of a decision tree has circuit size `≤ 1 + circuit_size·(depth+1)`. -/
lemma decisionTreeToCNF_ufiFormulaCircuitSize_le (t : DecisionTrees.DecisionTree) :
    ufiFormulaCircuitSize (decisionTreeToCNF t)
      ≤ 1 + DecisionTrees.decisionTreeNodeCount t
          * (DecisionTrees.decisionTreeDepth t + 1) := by
  unfold decisionTreeToCNF
  rw [dnfDual_ufiFormulaCircuitSize]
  have h := decisionTreeToDNF_ufiFormulaCircuitSize_le (dtNegate t)
  rw [dtNegate_depth, dtNegate_decisionTreeNodeCount] at h
  exact h

lemma decisionTreeToCNF_eval (t : DecisionTrees.DecisionTree) (xs : List Bool)
    (h_range : ∀ i ∈ DecisionTrees.dtCollectInputIndices t, i < xs.length) :
    DecisionTrees.evalDecisionTree t xs
      = ufiFormulaEval (decisionTreeToCNF t) xs := by
  have h_range_neg : ∀ i ∈ DecisionTrees.dtCollectInputIndices (dtNegate t),
      i < xs.length := by
    rw [dtNegate_dtCollectInputIndices]; exact h_range
  unfold decisionTreeToCNF
  rw [dnfDual_eval _ _ (isDNF_decisionTreeToDNF (dtNegate t)) (by
    intro i hi
    exact h_range_neg i
      (DecisionTrees.dnf_inputs_sub_dt_inputs (dtNegate t) i hi))]
  rw [← DecisionTrees.decisionTreeToDNF_eval_equiv (dtNegate t) xs h_range_neg]
  rw [dtNegate_eval t xs h_range]
  cases DecisionTrees.evalDecisionTree t xs <;> rfl

lemma mem_dtCollectInputIndices_of_mem_collect_decisionTreeToCNF (t : DecisionTrees.DecisionTree) (x : Nat)
    (hx : x ∈ ufiCollectInputIndices (decisionTreeToCNF t)) :
    x ∈ DecisionTrees.dtCollectInputIndices t := by
  unfold decisionTreeToCNF at hx
  rw [dnfDual_collect] at hx
  have hsub := DecisionTrees.dnf_inputs_sub_dt_inputs (dtNegate t) x hx
  rwa [dtNegate_dtCollectInputIndices] at hsub

/-- **CNF companion to `exists_narrow_dnf_from_good_restriction_dnf`.**  From a
    good restriction of a proper DNF `f`, produce a narrow **CNF** on the
    live coordinates computing `f` (same function, AND-rooted shape).
    Used to fold a `.dnf` bottom into its AND parent: the parent gate is
    an AND, so the bottom's restricted function must be presented as a
    CNF (AND-of-ORs) for the layers to flatten. -/
lemma exists_narrow_cnf_from_good_restriction_dnf
    {n : Nat} (decisionTreeDepthBound : Nat) {σ : OpenUnitIntervalQ}
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
    (hρ : ¬ isBadRestriction decisionTreeDepthBound n σ f ρ)
    (live : List Nat) (h_live_lt : ∀ v ∈ live, v < n)
    (h_live_nodup : live.Nodup)
    (h_live_eq : (live : Multiset Nat) = ρ.starAssignment.val.val.val)
    (deadBits : List Bool) (h_card : deadBits.length + live.length = n)
    (h_assemble : ∀ (liveBits : List Bool), liveBits.length = live.length →
        ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
          (assembleInput n live liveBits deadBits)[i]? = some b)
    (h_dt_lt : decisionTreeDepthBound < live.length) :
    ∃ (g : UnboundedFanInCNF live.length),
      cnfWidth g.val ≤ decisionTreeDepthBound ∧
      ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) ∧
      ∀ (liveBits : List Bool), liveBits.length = live.length →
        ufiFormulaEval f.val
            (assembleInput n live liveBits deadBits) =
        ufiFormulaEval g.val liveBits := by
  set tree :=
    canonicalDecisionTree f.val
      (mkAssignmentList ρ.starAssignment.val.val ρ.varAssignments n) with htree
  have h_depth_le : DecisionTrees.decisionTreeDepth tree ≤ decisionTreeDepthBound := by
    unfold isBadRestriction at hρ
    rw [properDNFCanonicalDecisionTree_eq_canonicalDecisionTree, ← htree] at hρ
    have : ¬ (decisionTreeDepthBound < DecisionTrees.decisionTreeDepth tree) := by
      intro hlt
      apply hρ
      simpa [decide_eq_true_eq] using hlt
    omega
  set rawFormula₀ : UnboundedFanInFormula := decisionTreeToCNF tree with hg₀_raw
  have h_width_g₀ : cnfWidth rawFormula₀ ≤ decisionTreeDepthBound := by
    have h₁ := decisionTreeToCNF_cnfWidth_le_decisionTreeDepth tree
    change cnfWidth (decisionTreeToCNF tree) ≤ decisionTreeDepthBound
    omega
  have h_branch_in_live :=
    mem_live_of_mem_dtCollectInputIndices_canonicalDecisionTree f ρ live h_live_eq
  have h_g₀_vars_subset :
      ∀ i ∈ ufiCollectInputIndices rawFormula₀, i ∈ live := by
    intro i hi
    have h_dt : i ∈ DecisionTrees.dtCollectInputIndices tree :=
      mem_dtCollectInputIndices_of_mem_collect_decisionTreeToCNF tree i hi
    exact h_branch_in_live i h_dt
  have h_g₀_inputs_lt : ufiLargestInput rawFormula₀ < n := by
    unfold ufiLargestInput
    apply Nat.lt_of_le_of_lt
      (adder_foldr_max_le_of_all_le
        (l := ufiCollectInputIndices rawFormula₀) (k := n - 1) ?_)
    · omega
    · intro i hi
      have hi_live := h_g₀_vars_subset i hi
      have hi_lt : i < n := h_live_lt i hi_live
      omega
  have h_g₀_is_cnf : isCNF rawFormula₀ = true :=
    isCNF_decisionTreeToCNF tree
  let g₀ : UnboundedFanInCNF n := ⟨rawFormula₀, h_g₀_inputs_lt, h_g₀_is_cnf⟩
  have h_g₀_vars_in_live :
      ∀ i ∈ ufiCollectInputIndices g₀.val, i ∈ live := h_g₀_vars_subset
  have h_live_pos : 0 < live.length := by omega
  obtain ⟨g, hg_width, hg_size, hg_eval₀⟩ :=
    exists_cnf_rekey_to_live live h_live_lt h_live_nodup h_live_pos g₀ decisionTreeDepthBound
      h_width_g₀ h_g₀_vars_in_live deadBits
  have h_size_g₀ :
      ufiFormulaCircuitSize rawFormula₀ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
    rw [hg₀_raw]
    have h₁ := decisionTreeToCNF_ufiFormulaCircuitSize_le tree
    have h₂ := decisionTreeNodeCount_succ_le_pow tree
    have hpow : (2 : Nat) ^ (DecisionTrees.decisionTreeDepth tree + 1)
        ≤ 2 ^ (decisionTreeDepthBound + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc ufiFormulaCircuitSize (decisionTreeToCNF tree)
        ≤ 1 + DecisionTrees.decisionTreeNodeCount tree
            * (DecisionTrees.decisionTreeDepth tree + 1) := h₁
      _ ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) := by
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul <;> omega
  have h_size_g : ufiFormulaCircuitSize g.val ≤ 1 + 2 ^ (decisionTreeDepthBound + 1) * (decisionTreeDepthBound + 1) :=
    le_trans hg_size h_size_g₀
  refine ⟨g, hg_width, h_size_g, ?_⟩
  intro liveBits h_lb_len
  set xs := assembleInput n live liveBits deadBits with hxs
  have hxs_len : xs.length = n :=
    length_assembleInput n live liveBits deadBits
  have hxs_consistent :
      ∀ i b, mkAssignment ρ.starAssignment.val.val ρ.varAssignments i = some b →
        xs[i]? = some b := h_assemble liveBits h_lb_len
  have h_dt_eq :
      DecisionTrees.evalDecisionTree tree xs =
        ufiFormulaEval f.val xs :=
    canonicalDecisionTree_eval_eq f ρ xs hxs_len hxs_consistent
  have h_cnf_eq :
      ufiFormulaEval rawFormula₀ xs =
        DecisionTrees.evalDecisionTree tree xs := by
    have h_range : ∀ i ∈ DecisionTrees.dtCollectInputIndices tree,
        i < xs.length := by
      intro i hi
      have hi_live := h_branch_in_live i hi
      have hi_lt : i < n := h_live_lt i hi_live
      rw [hxs_len]; exact hi_lt
    exact (decisionTreeToCNF_eval tree xs h_range).symm
  have h_g_eq :
      ufiFormulaEval g₀.val xs = ufiFormulaEval g.val liveBits :=
    hg_eval₀ liveBits h_lb_len
  change ufiFormulaEval f.val xs = ufiFormulaEval g.val liveBits
  rw [← h_dt_eq, ← h_cnf_eq]
  change ufiFormulaEval g₀.val xs = ufiFormulaEval g.val liveBits
  exact h_g_eq

end Circuits.HastadParity
