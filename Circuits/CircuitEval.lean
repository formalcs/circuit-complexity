import «Circuits».CircuitConversion

/-! # `eval` agrees with `evalCanonical` on canonical-input circuits

This file proves the headline equivalence between the general-purpose
`Circuit.eval` and the streamlined `Circuit.evalCanonical`:
whenever a circuit `c` has `HasCanonicalInputIds`, the two evaluators
return identical output lists on every input.

The argument is purely about the *initial environments*: the gate
fold and the output-mapping step are syntactically identical between
the two functions, so equal initial environments propagate to equal
final environments and hence equal output lists. -/

namespace Circuits

namespace Circuit

private def evalInitEnvFromIds (posIds negIds : List Nat)
    (inputValues : List Bool) (id : Nat) : Bool :=
  match (posIds.zip inputValues).find? (fun p => p.1 == id) with
  | some (_, v) => v
  | none =>
    match (negIds.zip inputValues).find? (fun p => p.1 == id) with
    | some (_, v) => v
    | none => false

private lemma find?_zip_eq_none_of_key_notMem
    (xs : List Nat) (vs : List Bool) (key : Nat) (hkey : key ∉ xs) :
    (xs.zip vs).find? (fun p => p.1 == key) = none := by
  induction xs generalizing vs with
  | nil => simp
  | cons x xs ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      have hx_ne : x ≠ key := fun h => hkey (h ▸ List.mem_cons.mpr (Or.inl rfl))
      have hk_tail : key ∉ xs := fun h => hkey (List.mem_cons.mpr (Or.inr h))
      have hbeq : (x == key) = false := by simp [hx_ne]
      simp only [List.zip_cons_cons, List.find?, hbeq]
      exact ih (vs := vs) hk_tail

private lemma find?_zip_eq_some_of_nodup_key
    (xs : List Nat) (vs : List Bool) (i : Nat) (key : Nat)
    (hxs_nd : xs.Nodup) (hi_xs : i < xs.length) (hi_vs : i < vs.length)
    (hkey : xs[i]'hi_xs = key) :
    (xs.zip vs).find? (fun p => p.1 == key) = some (key, vs[i]'hi_vs) := by
  induction xs generalizing vs i with
  | nil => exact absurd hi_xs (by simp)
  | cons x xs ih =>
    cases vs with
    | nil => exact absurd hi_vs (by simp)
    | cons v vs =>
      have hxnotin : x ∉ xs := (List.nodup_cons.mp hxs_nd).1
      have hxs_nd' : xs.Nodup := (List.nodup_cons.mp hxs_nd).2
      cases i with
      | zero =>
        have hx : x = key := by simpa using hkey
        subst key
        simp
      | succ k =>
        have hk_xs : k < xs.length := by simpa using hi_xs
        have hk_vs : k < vs.length := by simpa using hi_vs
        have hxk_mem : xs[k]'hk_xs ∈ xs := List.getElem_mem hk_xs
        have hxk_ne : x ≠ xs[k]'hk_xs := by
          intro hxk
          exact hxnotin (hxk ▸ hxk_mem)
        have hbeq : (x == key) = false := by
          have : xs[k]'hk_xs = key := by simpa using hkey
          simp [← this, hxk_ne]
        simp only [List.zip_cons_cons, List.find?, hbeq]
        exact ih (vs := vs) (i := k) hxs_nd' hk_xs hk_vs (by simpa using hkey)
/-- A general "key not found" criterion for `find?` on a zipped list:
    if no `xs[i]` (with `i` valid in *both* `xs` and `vs`) equals `key`,
    then the find on `xs.zip vs` returns `none`.  This is strictly
    stronger than `find?_zip_eq_none_of_notMem`, since it permits
    `key` to occur in `xs` past index `vs.length` (the zip silently
    drops those positions). -/
lemma find?_zip_eq_none_of_notMem_take
    {xs : List Nat} {vs : List Bool} {key : Nat}
    (h : ∀ i (h_xs : i < xs.length) (_ : i < vs.length), xs[i]'h_xs ≠ key) :
    (xs.zip vs).find? (fun p => p.1 == key) = none := by
  induction xs generalizing vs with
  | nil => simp
  | cons x xs ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      have hx_ne : x ≠ key :=
        h 0 (by simp) (by simp)
      have hbeq_x : (x == key) = false := by simp [hx_ne]
      simp only [List.zip_cons_cons, List.find?, hbeq_x]
      apply ih (vs := vs)
      intro i h_xs h_vs
      have h_succ_xs : i + 1 < (x :: xs).length := by simp; omega
      have h_succ_vs : i + 1 < (v :: vs).length := by simp; omega
      have := h (i + 1) h_succ_xs h_succ_vs
      simpa using this

/-- For the canonical positive list `List.range n`, if the inputs are
    too short to reach a key `key ≥ vs.length`, the find on the zip
    returns `none`.  (Even though `key` may live in `range n`, the zip
    truncates at `vs.length`, dropping that pair.) -/
lemma find?_zip_range_eq_none_of_le
    (n : Nat) (vs : List Bool) (key : Nat) (h : vs.length ≤ key) :
    ((List.range n).zip vs).find? (fun p => p.1 == key) = none := by
  apply find?_zip_eq_none_of_notMem_take
  intro i h_xs h_vs
  have hxi : (List.range n)[i]'h_xs = i := by rw [List.getElem_range]
  rw [hxi]; omega

/-- Same as `find?_zip_range_eq_none_of_le`, but for the canonical
    *negative* list `(List.range n).map (n + ·)` searching for
    `n + j` with `j ≥ vs.length`. -/
lemma find?_zip_neg_range_eq_none_of_le
    (n j : Nat) (vs : List Bool) (h : vs.length ≤ j) :
    (((List.range n).map (fun i => n + i)).zip vs).find?
        (fun p => p.1 == n + j) = none := by
  apply find?_zip_eq_none_of_notMem_take
  intro i h_xs h_vs
  have hxi : ((List.range n).map (fun i => n + i))[i]'h_xs = n + i := by
    rw [List.getElem_map, List.getElem_range]
  rw [hxi]; omega

/-- The crucial pointwise identity: on canonical id lists,
    `evalInitEnvFromIds` reduces to the positional `canonicalInitEnv`. -/
lemma evalInitEnvFromIds_canonical (n : Nat) (inputValues : List Bool) (id : Nat) :
    evalInitEnvFromIds (List.range n) ((List.range n).map (fun i => n + i))
        inputValues id = canonicalInitEnv n inputValues id := by
  unfold evalInitEnvFromIds canonicalInitEnv
  by_cases h1 : id < n
  · -- Case A: `id ∈ [0, n)` — the positive lookup either hits or misses
    -- depending on whether `id < inputValues.length`.
    rw [if_pos h1]
    have hkey : (List.range n)[id]'(by rw [List.length_range]; exact h1) = id := by
      rw [List.getElem_range]
    have hnd : (List.range n).Nodup := List.nodup_range
    by_cases hjv : id < inputValues.length
    · -- A1: in-range; positive find? hits at index `id`.
      rw [find?_zip_eq_some_of_nodup_key (List.range n) inputValues id id hnd
            (by rw [List.length_range]; exact h1) hjv hkey]
      rw [List.getElem?_eq_getElem hjv]; rfl
    · -- A2: out-of-range; both finds miss, result is `false`.
      push Not at hjv
      rw [find?_zip_range_eq_none_of_le n inputValues id hjv]
      have hnotin_neg : id ∉ ((List.range n).map (fun i => n + i)) := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨i, hi_mem, hi⟩
        omega
      rw [find?_zip_eq_none_of_key_notMem _ _ _ hnotin_neg]
      rw [List.getElem?_eq_none hjv]; rfl
  · -- Case B/C: `id ≥ n` — positive find? always misses.
    push Not at h1
    rw [if_neg (Nat.not_lt.mpr h1)]
    have hnotin_pos : id ∉ List.range n := by
      rw [List.mem_range]; omega
    rw [find?_zip_eq_none_of_key_notMem _ _ _ hnotin_pos]
    by_cases h2 : id < 2 * n
    · -- B: `id ∈ [n, 2 * n)`; let `j := id - n`, so `id = n + j` and `j < n`.
      rw [if_pos h2]
      have hjn : id - n < n := by omega
      have hkey :
          ((List.range n).map (fun i => n + i))[id - n]'(by
            rw [List.length_map, List.length_range]; exact hjn) = id := by
        rw [List.getElem_map, List.getElem_range]; omega
      have hnd_neg : ((List.range n).map (fun i => n + i)).Nodup := by
        apply List.Nodup.map
        · intro a b hab; simpa using hab
        · exact List.nodup_range
      by_cases hjv : (id - n) < inputValues.length
      · -- B1: in-range; negative find? hits at index `j = id - n`.
        rw [find?_zip_eq_some_of_nodup_key
              ((List.range n).map (fun i => n + i))
              inputValues (id - n) id hnd_neg
              (by rw [List.length_map, List.length_range]; exact hjn) hjv hkey]
        rw [List.getElem?_eq_getElem hjv]; rfl
      · -- B2: out-of-range; negative find? misses; result is `false`.
        push Not at hjv
        have hneg_eq :
            (((List.range n).map (fun i => n + i)).zip inputValues).find?
                (fun p => p.1 == id) = none := by
          have hbase :=
            find?_zip_neg_range_eq_none_of_le n (id - n) inputValues hjv
          have hid : n + (id - n) = id := by omega
          rwa [hid] at hbase
        rw [hneg_eq]
        rw [List.getElem?_eq_none hjv]; rfl
    · -- C: `id ≥ 2 * n`; not in either canonical list; result is `false`.
      push Not at h2
      rw [if_neg (Nat.not_lt.mpr h2)]
      have hnotin_neg : id ∉ ((List.range n).map (fun i => n + i)) := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨i, hi_mem, hi⟩
        rw [List.mem_range] at hi_mem
        omega
      rw [find?_zip_eq_none_of_key_notMem _ _ _ hnotin_neg]

/-- **Main equivalence.**  Whenever a circuit has its input ids in the
    canonical layout, `eval` and `evalCanonical` agree on every input. -/
theorem eval_eq_evalCanonical (c : Circuit) (inputValues : List Bool)
    (hcan : c.HasCanonicalInputIds) :
    c.eval inputValues = c.evalCanonical inputValues := by
  -- Both functions share the same input-width guard: when
  -- `inputValues.length < c.inputWidth`, both return the same
  -- `outputGateIds.map (fun _ => false)` list.
  unfold Circuit.eval Circuit.evalCanonical
  by_cases hlt : inputValues.length < c.inputWidth
  · simp [hlt]
  simp only [hlt, if_false]
  obtain ⟨hpos, hneg⟩ := hcan
  -- The two initial environments coincide as functions `Nat → Bool`.
  have h_init :
      (fun (id : Nat) =>
        match (c.positiveInputIds.zip inputValues).find?
                (fun p => p.1 == id) with
        | some (_, v) => v
        | none =>
          match (c.negativeInputIds.zip inputValues).find?
                  (fun p => p.1 == id) with
          | some (_, v) => v
          | none        => false)
      = canonicalInitEnv c.inputWidth inputValues := by
    funext id
    change evalInitEnvFromIds c.positiveInputIds c.negativeInputIds inputValues id = _
    rw [hpos, hneg]
    exact evalInitEnvFromIds_canonical c.inputWidth inputValues id
  -- Both `eval` and `evalCanonical` are
  -- `c.outputGateIds.map (c.gates.foldl folder initEnv)` with the same
  -- folder up to the captured `initEnv`.  Equal initial environments
  -- give equal folds and hence equal output lists.
  change c.outputGateIds.map (c.gates.foldl
        (fun (env : Nat → Bool) (g : Gate) =>
          let val := c.evalGate
            (fun id =>
              match (c.positiveInputIds.zip inputValues).find?
                      (fun p => p.1 == id) with
              | some (_, v) => v
              | none =>
                match (c.negativeInputIds.zip inputValues).find?
                        (fun p => p.1 == id) with
                | some (_, v) => v
                | none        => false) env g
          fun id => if id == g.id then val else env id)
        (fun id =>
          match (c.positiveInputIds.zip inputValues).find?
                  (fun p => p.1 == id) with
          | some (_, v) => v
          | none =>
            match (c.negativeInputIds.zip inputValues).find?
                    (fun p => p.1 == id) with
            | some (_, v) => v
            | none        => false))
      = c.outputGateIds.map (c.gates.foldl
        (fun (env : Nat → Bool) (g : Gate) =>
          let val := c.evalGate
            (canonicalInitEnv c.inputWidth inputValues) env g
          fun id => if id == g.id then val else env id)
        (canonicalInitEnv c.inputWidth inputValues))
  rw [h_init]

end Circuit

end Circuits
