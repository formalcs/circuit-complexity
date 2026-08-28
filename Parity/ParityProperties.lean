import Mathlib.Data.List.Count
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Finset.Dedup
import Mathlib.Algebra.Ring.Parity
import Parity.DepthOneParity

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Circuits.CnfDnf.Families

open Circuits
open UnboundedFanInFormula

/- ============================================================
   Parity of bit lists
   ============================================================ -/

/-- Parity of a list of bits as a `Bool`. -/
def parityBit (bs : List Bool) : Bool :=
  if List.count true bs % 2 = 0 then false else true

/-- A formula computes parity on `n` variables when its evaluation agrees with
    `parityBit` on every input list of length `n`. -/
def FormulaComputesParity (n : Nat) (f : UnboundedFanInFormula) : Prop :=
  ∀ inputs : List Bool, inputs.length = n →
    ufiFormulaEval f inputs = parityBit inputs

def BFIFormulaComputesParity (n : Nat) (f : BoundedFanInFormula) : Prop :=
  ∀ inputs : List Bool, inputs.length = n →
    bfiFormulaEval f inputs = parityBit inputs

/-- Counting entries equal to `true` with `countP` agrees with `List.count`. -/
theorem countP_eq_count_true (l : List Bool) :
    l.countP (· == true) = List.count true l := by
  induction l <;> simp_all [List.count]

/-- A bit list has odd Hamming weight exactly when its parity bit is `true`. -/
theorem odd_countP_iff_parityBit (l : List Bool) :
    Odd (l.countP (· == true)) ↔ parityBit l = true := by
  rw [countP_eq_count_true, Nat.odd_iff]
  unfold parityBit
  by_cases h : List.count true l % 2 = 0
  · rw [if_pos h]
    constructor
    · intro hh; omega
    · intro hh; exact absurd hh (by decide)
  · rw [if_neg h]
    constructor
    · intro _; rfl
    · intro _; omega

/-- A formula computing PARITY on at least two inputs has depth at least two. -/
theorem two_le_depth_of_formula_computes_parity
    (n : Nat) (h_two_le_n : 2 ≤ n) (circuit : UnboundedFanInFormula)
    (h_parity : FormulaComputesParity n circuit) :
    2 ≤ ufiFormulaDepth circuit := by
  by_contra h_depth
  have h_depth_one : ufiFormulaDepth circuit ≤ 1 := by omega
  obtain ⟨inputs, hlen, hbad⟩ :=
    Circuits.depth_one_misclassifies n h_two_le_n circuit h_depth_one
  have hcorrect := h_parity inputs hlen
  rcases hbad with ⟨heval_zero, h_odd⟩ | ⟨heval_one, h_not_odd⟩
  · have hzero : ufiFormulaEval circuit inputs = false := by simpa using heval_zero
    have hparity_one : parityBit inputs = true :=
      (odd_countP_iff_parityBit inputs).mp h_odd
    rw [hzero, hparity_one] at hcorrect
    contradiction
  · have hone : ufiFormulaEval circuit inputs = true := by simpa using heval_one
    have hparity_one : parityBit inputs = true := by rw [← hcorrect, hone]
    exact h_not_odd ((odd_countP_iff_parityBit inputs).mpr hparity_one)

/- ============================================================
   Flipping one bit
   ============================================================ -/

/-- Flip the bit at index `i`, leaving the list unchanged when `i` is out of bounds. -/
def flipAt : List Bool → Nat → List Bool
  | [],      _     => []
  | b :: bs, 0     => Bool.not b :: bs
  | b :: bs, i + 1 => b :: flipAt bs i

@[simp] theorem length_flipAt : ∀ (bs : List Bool) (i : Nat),
    (flipAt bs i).length = bs.length
  | [],      _     => by simp [flipAt]
  | _ :: _,  0     => by simp [flipAt]
  | _ :: bs, i + 1 => by simp [flipAt, length_flipAt bs i]

theorem getElem_flipAt_of_ne : ∀ (bs : List Bool) (i j : Nat) (hj : j < bs.length),
    j ≠ i → (flipAt bs i)[j]'(by rw [length_flipAt]; exact hj) = bs[j]'hj
  | [],      _,     _, hj, _ => by simp at hj
  | _ :: _,  0,     0, _, hne => by exact absurd rfl hne
  | _ :: _,  0,     _ + 1, _, _ => by
      simp [flipAt]
  | _ :: _,  _ + 1, 0, _, _ => by
      simp [flipAt]
  | _ :: bs, i + 1, j + 1, hj, hne => by
      have hj' : j < bs.length := by
        simp at hj; omega
      have hne' : j ≠ i := by intro h; apply hne; simp [h]
      simp [flipAt]
      exact getElem_flipAt_of_ne bs i j hj' hne'

theorem count_true_flipAt_of_eq_false : ∀ (bs : List Bool) (i : Nat) (hi : i < bs.length),
    bs[i]'hi = false → List.count true (flipAt bs i) = List.count true bs + 1
  | [],      _,     hi, _   => by simp at hi
  | b :: bs, 0,     _,  h0  => by
      have hb : b = false := h0
      subst hb
      simp [flipAt, List.count, Bool.toNat, Bool.not]
  | b :: bs, i + 1, hi, h0  => by
      have hi' : i < bs.length := by simp at hi; omega
      have h0' : bs[i]'hi' = false := by
        have heq : (b :: bs)[i + 1]'hi = bs[i]'hi' := by simp
        rw [heq] at h0
        exact h0
      have ih := count_true_flipAt_of_eq_false bs i hi' h0'
      cases b <;> simp [flipAt, List.count] at ih ⊢ <;> omega

theorem parityBit_flipAt_ne_of_eq_false
    (bs : List Bool) (i : Nat) (hi : i < bs.length) (h0 : bs[i]'hi = false) :
    parityBit (flipAt bs i) ≠ parityBit bs := by
  unfold parityBit
  rw [count_true_flipAt_of_eq_false bs i hi h0]
  by_cases hp : List.count true bs % 2 = 0
  · simp [hp]
    have hpp : (List.count true bs + 1) % 2 = 1 := by omega
    simp [hpp]
  · simp [hp]
    have hpp : (List.count true bs + 1) % 2 = 0 := by omega
    simp [hpp]

/- ============================================================
   Assembling and restricting parity inputs
   ============================================================ -/

/-- Assemble a full `n`-bit input from a partial assignment.
    `live` is the list of live (unassigned) variable positions in `[0,n)`,
    `live_bits` are the values to place at those positions (paired
    positionally with `live`), and `dead_bits` are the values to place
    at the remaining positions in `[0,n)` *in increasing order of
    position*.

    For each output position `i ∈ [0,n)`:
    * if `i = live[j]` for some `j`, the value is `live_bits[j]`;
    * otherwise, `i` is the `k`-th non-live position in `[0,n)` (counting
      from `0`), and the value is `dead_bits[k]`.

    The circuit's input indices need not be a contiguous prefix, so downstream
    lemmas use the `assembleInput_*` helpers below. -/
def assembleInput
    (n : Nat) (live : List Nat) (live_bits : List Bool) (dead_bits : List Bool) :
    List Bool :=
  (List.range n).map (fun i =>
    match live.findIdx? (· = i) with
    | some j => live_bits.getD j false
    | none =>
        dead_bits.getD
          (((List.range i).filter (fun k => !live.contains k)).length) false)

/-- Length of an assembled input is always `n`. -/
theorem length_assembleInput
    (n : Nat) (live : List Nat) (live_bits dead_bits : List Bool) :
    (assembleInput n live live_bits dead_bits).length = n := by
  simp [assembleInput]

/-- Helper: the inner function used by `assembleInput`. -/
def assembleInputFn
    (live : List Nat) (live_bits dead_bits : List Bool) (i : Nat) : Bool :=
  match live.findIdx? (· = i) with
  | some j => live_bits.getD j false
  | none =>
      dead_bits.getD
        (((List.range i).filter (fun k => !live.contains k)).length) false

theorem assembleInput_eq_map
    (n : Nat) (live : List Nat) (live_bits dead_bits : List Bool) :
    assembleInput n live live_bits dead_bits =
      (List.range n).map (assembleInputFn live live_bits dead_bits) := by
  rfl

/-- Sub-lemma A.  On the live partition of `[0,n)`, the inner function
    of `assembleInput` produces a permutation of `live_bits`.

    Proof sketch.  `(List.range n).filter (live.contains ·)` is a
    permutation of `live` (since `live ⊆ [0,n)` and `live.Nodup`).
    On this list, `assembleInputFn` is `fun i => live_bits.getD
    (live.indexOf i) false`.  Mapping over `live` gives
    `live.map (fun i => live_bits.getD (live.indexOf i) false)`, which
    by `Nodup` reduces to `live_bits` (the standard "self-indexing"
    identity for `Nodup` lists). -/
theorem perm_map_assembleInputFn_filter_contains
    (n : Nat) (live : List Nat) (live_bits dead_bits : List Bool)
    (h_live_lt : ∀ v ∈ live, v < n) (h_live_nodup : live.Nodup)
    (h_live_len : live_bits.length = live.length) :
    (((List.range n).filter (fun i => live.contains i)).map
        (assembleInputFn live live_bits dead_bits)).Perm live_bits := by
  -- Key intermediate: `indices.map (assembleInputFn indices bits _) = bits`
  -- for nodup `indices`, proved by parallel induction on `indices` and `bits`.
  have h_eq : ∀ (indices : List Nat) (bits : List Bool),
      indices.Nodup → bits.length = indices.length →
      indices.map (assembleInputFn indices bits dead_bits) = bits := by
    intro indices
    induction indices with
    | nil =>
      intro bits _ hlen
      cases bits
      · rfl
      · simp at hlen
    | cons a rest ih =>
      intro bits hnodup hlen
      cases bits with
      | nil => simp at hlen
      | cons b rest_bits =>
        have h_a_notin : a ∉ rest := (List.nodup_cons.mp hnodup).1
        have h_rest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
        have h_rest_len : rest_bits.length = rest.length := by
          simp [List.length_cons] at hlen; omega
        rw [List.map_cons]
        refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
        · -- a entry: returns b
          show assembleInputFn (a :: rest) (b :: rest_bits) dead_bits a = b
          unfold assembleInputFn
          rw [List.findIdx?_cons]
          simp
        · -- rest entries: replace fn by `assembleInputFn rest rest_bits …`
          have h_rewrite :
              rest.map (assembleInputFn (a :: rest) (b :: rest_bits) dead_bits)
                = rest.map (assembleInputFn rest rest_bits dead_bits) := by
            apply List.map_congr_left
            intro i hi
            have h_i_ne_a : ¬ (a = i) := fun heq => h_a_notin (heq ▸ hi)
            unfold assembleInputFn
            rw [List.findIdx?_cons]
            simp only [decide_eq_true_eq, h_i_ne_a, if_false]
            cases h_find : rest.findIdx? (· = i) with
            | none =>
              rw [List.findIdx?_eq_none_iff] at h_find
              exact absurd (h_find i hi) (by simp)
            | some k =>
              simp [Option.map]
          rw [h_rewrite]
          exact ih rest_bits h_rest_nodup h_rest_len
  -- Now combine: filtered range ~ live, then map both sides.
  have hperm_live : ((List.range n).filter (fun i => live.contains i)).Perm live := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_range.filter _
    · exact h_live_nodup
    · ext x
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
      refine ⟨fun ⟨_, hx⟩ => List.mem_of_elem_eq_true hx,
        fun hx => ⟨h_live_lt x hx, List.elem_eq_true_of_mem hx⟩⟩
  have hperm_map := hperm_live.map (assembleInputFn live live_bits dead_bits)
  rw [h_eq live live_bits h_live_nodup h_live_len] at hperm_map
  exact hperm_map

/-- Helper B1.  For `i ∉ live`, `live.findIdx? (· = i) = none`. -/
theorem findIdx?_eq_none_of_notMem
    (live : List Nat) (i : Nat) (hi : i ∉ live) :
    live.findIdx? (· = i) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  simp only [decide_eq_false_iff_not]
  rintro rfl
  exact hi hx

/-- Helper B2 (generic rank-counting identity).  For any decidable
    `p : Nat → Bool` and any function `g : Nat → Bool`,

      `((range n).filter p).map (fun i => g ((range i).filter p).length)
        = (range ((range n).filter p).length).map g`.

    Proof: induction on `n`; at the successor step,
    `(range (n+1)).filter p = (range n).filter p` if `¬p n`, and
    `(range n).filter p ++ [n]` if `p n`.  The IH covers the prefix;
    the singleton at the end has rank-count `((range n).filter p).length`,
    matching the new last entry of the RHS. -/
theorem map_filter_range_eq_map_range_length
    (p : Nat → Bool) (g : Nat → Bool) :
    ∀ n, ((List.range n).filter p).map
            (fun i => g ((List.range i).filter p).length)
      = (List.range ((List.range n).filter p).length).map g := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, List.map_append]
    rw [ih]
    rcases hpn : p n with _ | _
    · -- p n = false
      simp
    · -- p n = true
      simp only [if_true, List.map_cons, List.map_nil,
        List.length_append, List.length_cons,
        List.length_nil, List.range_succ, List.map_append]

/-- Helper B3.  `(range values.length).map (fun i => values.getD i d) = values`. -/
theorem map_getD_range_length
    (values : List Bool) (d : Bool) :
    (List.range values.length).map (fun i => values.getD i d) = values := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    rw [ih]

/-- Helper: `xs ~ xs.filter p ++ xs.filter (¬p)` for any decidable `p`. -/
theorem perm_filter_append_filter_not {α : Type*}
    (xs : List α) (p : α → Bool) :
    xs.Perm (xs.filter p ++ xs.filter (fun a => !p a)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.not_true]
      exact ih.cons x
    · simp only [List.filter_cons, hpx, Bool.not_false]
      have := ih.cons x
      -- `x :: (xs.filter p ++ xs.filter (!p))
      --   ~ xs.filter p ++ x :: xs.filter (!p)`
      exact this.trans (List.perm_middle.symm)

/-- Helper B4.  Under `live ⊆ [0,n)`, `live.Nodup`, and length identity,
    `((range n).filter (¬live.contains)).length = dead_bits.length`. -/
theorem length_filter_not_contains
    (n : Nat) (live : List Nat)
    (h_live_lt : ∀ v ∈ live, v < n) (h_live_nodup : live.Nodup)
    (live_bits dead_bits : List Bool)
    (h_live_len : live_bits.length = live.length)
    (h_card : live_bits.length + dead_bits.length = n) :
    ((List.range n).filter (fun i => !live.contains i)).length
      = dead_bits.length := by
  -- (filter ¬p).length + (filter p).length = n
  have h_split :
      ((List.range n).filter (fun i => !live.contains i)).length
        + ((List.range n).filter (fun i => live.contains i)).length
        = n := by
    have hperm := perm_filter_append_filter_not (List.range n)
        (fun i => live.contains i)
    have hlen := hperm.length_eq
    simp only [List.length_append, List.length_range] at hlen
    omega
  -- (filter contains).length = live.length, since live ⊆ [0,n), Nodup.
  have h_contains_len :
      ((List.range n).filter (fun i => live.contains i)).length
        = live.length := by
    -- The filtered list is a permutation of `live` because both lists are
    -- duplicate-free and have the same underlying finset.
    have hperm : ((List.range n).filter (fun i => live.contains i)).Perm
        live := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact List.nodup_range.filter _
      · exact h_live_nodup
      · ext x
        simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
        constructor
        · rintro ⟨_, hx⟩
          -- `live.contains x = true` means `x ∈ live`.
          exact List.mem_of_elem_eq_true hx
        · intro hx
          refine ⟨h_live_lt x hx, ?_⟩
          exact List.elem_eq_true_of_mem hx
    exact hperm.length_eq
  omega

/-- Sub-lemma B.  On the dead partition of `[0,n)`, the inner function
    of `assembleInput` produces *exactly* `dead_bits` (up to length).

    Proof: combine `findIdx?_eq_none_of_notMem` (rewriting the
    inner function on filtered elements), `map_filter_range_eq_map_range_length` (the
    rank-counting identity), `length_filter_not_contains` (length
    matching), and `map_getD_range_length` (final cleanup). -/
theorem map_assembleInputFn_filter_not_contains
    (n : Nat) (live : List Nat) (live_bits dead_bits : List Bool)
    (h_live_lt : ∀ v ∈ live, v < n) (h_live_nodup : live.Nodup)
    (h_live_len : live_bits.length = live.length)
    (h_card : live_bits.length + dead_bits.length = n) :
    ((List.range n).filter (fun i => !live.contains i)).map
        (assembleInputFn live live_bits dead_bits)
      = dead_bits := by
  -- Step 1: rewrite `assembleInputFn` on filtered (non-live) elements.
  have h_fn :
      ((List.range n).filter (fun i => !live.contains i)).map
          (assembleInputFn live live_bits dead_bits)
        = ((List.range n).filter (fun i => !live.contains i)).map
            (fun i => dead_bits.getD
              (((List.range i).filter (fun k => !live.contains k)).length)
              false) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_filter] at hi
    obtain ⟨_, hni⟩ := hi
    have hni' : i ∉ live := by
      intro hmem
      have h_contains_true : live.contains i = true := by
        rw [List.contains_iff_exists_mem_beq]
        exact ⟨i, hmem, by simp⟩
      rw [h_contains_true] at hni
      exact absurd hni (by decide)
    have hfind := findIdx?_eq_none_of_notMem live i hni'
    unfold assembleInputFn
    rw [hfind]
  rw [h_fn]
  -- Step 2: apply the rank-counting identity to collapse to a
  -- range over `((range n).filter (¬live.contains)).length`.
  rw [map_filter_range_eq_map_range_length (fun i => !live.contains i)
      (fun k => dead_bits.getD k false) n]
  -- Step 3: replace the length with `dead_bits.length`.
  rw [length_filter_not_contains n live h_live_lt h_live_nodup
      live_bits dead_bits h_live_len h_card]
  -- Step 4: `(range L.length).map (L.getD · 0) = L`.
  exact map_getD_range_length dead_bits false

/-- The assembled input is a permutation of `live_bits ++ dead_bits`.

    Proof: split `(List.range n)` by `live.contains` into a live half
    and a dead half (`perm_filter_append_filter_not`); on the
    live half the map permutes to `live_bits` (sub-lemma A
    `perm_map_assembleInputFn_filter_contains`); on the dead half the map equals
    `dead_bits` literally (sub-lemma B `map_assembleInputFn_filter_not_contains`). -/
theorem perm_assembleInput_append
    (n : Nat) (live : List Nat) (live_bits dead_bits : List Bool)
    (h_live_lt : ∀ v ∈ live, v < n) (h_live_nodup : live.Nodup)
    (h_live_len : live_bits.length = live.length)
    (h_card : live_bits.length + dead_bits.length = n) :
    (assembleInput n live live_bits dead_bits).Perm
      (live_bits ++ dead_bits) := by
  rw [assembleInput_eq_map]
  -- Step 1: `range n ~ filter live ++ filter (!live)`.
  have hsplit :
      ((List.range n).map (assembleInputFn live live_bits dead_bits)).Perm
        (((List.range n).filter (fun i => live.contains i)).map
            (assembleInputFn live live_bits dead_bits)
          ++ ((List.range n).filter (fun i => !live.contains i)).map
            (assembleInputFn live live_bits dead_bits)) := by
    have := perm_filter_append_filter_not (List.range n)
              (fun i => live.contains i)
    have := this.map (assembleInputFn live live_bits dead_bits)
    simpa [List.map_append] using this
  -- Step 2: each piece simplifies via sub-lemmas A and B.
  refine hsplit.trans ?_
  rw [map_assembleInputFn_filter_not_contains n live live_bits dead_bits h_live_lt
      h_live_nodup h_live_len h_card]
  exact (perm_map_assembleInputFn_filter_contains n live live_bits dead_bits h_live_lt
      h_live_nodup h_live_len).append_right dead_bits

/-- The "count of ones" in an assembled input splits cleanly across the
    live and dead parts.  Used in `exists_offset_odd_countP_assembleInput_iff`.

    Reduced to `perm_assembleInput_append` via `Perm.countP_eq` and
    `List.countP_append`. -/
theorem countP_assembleInput
    (n : Nat) (live : List Nat) (live_bits dead_bits : List Bool)
    (h_live_lt : ∀ v ∈ live, v < n) (h_live_nodup : live.Nodup)
    (h_live_len : live_bits.length = live.length)
    (h_card : live_bits.length + dead_bits.length = n) :
    (assembleInput n live live_bits dead_bits).countP (· == true) =
      live_bits.countP (· == true) + dead_bits.countP (· == true) := by
  rw [(perm_assembleInput_append n live live_bits dead_bits h_live_lt
        h_live_nodup h_live_len h_card).countP_eq,
    List.countP_append]

/- ============================================================
   Parity under restrictions
   ============================================================ -/

/-- After fixing the values of the "dead" variables to `dead_bits`, the
    parity function on `n` bits, viewed as a function of the live bits,
    equals (the parity of the live bits) XOR (the parity of `dead_bits`).
    In particular, it equals the parity of the live coordinates up to a
    *fixed* Boolean offset determined by `dead_bits`.

    Proof idea: `Odd (xs ++ ys).countP P ↔ Odd (xs.countP P) XOR
    Odd (ys.countP P)` — standard.

    This lemma is the *only* place we use the algebraic
    structure of parity. -/
theorem exists_offset_odd_countP_assembleInput_iff
    (n : Nat) (live : List Nat) (dead_bits : List Bool)
    (h_live_lt : ∀ v ∈ live, v < n) (h_live_nodup : live.Nodup)
    (h_card : dead_bits.length + live.length = n) :
    ∃ (offset : Bool),
      ∀ (live_bits : List Bool), live_bits.length = live.length →
        (Odd ((assembleInput n live live_bits dead_bits).countP (· == true)) ↔
          (Odd (live_bits.countP (· == true)) ↔ offset = false)) := by
  -- The offset is determined by the parity of the dead bits' ones.
  refine ⟨decide (Odd (dead_bits.countP (· == true))), ?_⟩
  intro live_bits hlen
  rw [countP_assembleInput n live live_bits dead_bits h_live_lt h_live_nodup
        hlen (by omega),
    Nat.odd_add, decide_eq_false_iff_not,
    ← Nat.not_odd_iff_even]

end Circuits.CnfDnf.Families
