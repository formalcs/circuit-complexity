/-
# Fan-in reduction: the kill-wide-gates moment bound

This file develops the combinatorial first-moment bound that is the analytic
heart of the Håstad "kill wide bottom gates" keystone for `PARITY ∉ AC0`.

## The probabilistic picture (for orientation)

In the random-restriction model `AssignedRandomRestriction σ n`, a live set
`S ⊆ range n` of size `s = ⌈σ·n⌉` is chosen uniformly, and every non-live
variable is given a uniform independent bit.  A bottom AND/OR gate with variable
set `V` is *not killed* iff every variable in `V` is either live, or assigned its
non-forcing value.  Conditioned on the live set `S`, this has probability
`(1/2)^{|V \ S|} = 2^{|V ∩ S|} / 2^{|V|}`, so

  `P[gate not killed] = (∑_{S} 2^{|S ∩ V|} / C(n,s)) · 2^{-|V|}`.

The content of this file is the closed-form upper bound

  `∑_{S ∈ powersetCard s (range n)} 2^{|S ∩ V|}  ≤  C(n,s) · (1 + s/n)^{|V|}`   (`moment_bound`)

which, at live density `s/n ≈ α`, gives
`P[not killed] ≤ ((1 + α)/2)^{|V|}`.  A caller chooses any rational upper
bound `q ≥ (1 + s/n)/2`; a union bound over the wide gates then produces a
restriction killing all of them.  Concrete choices of `α` and `q` live in the
separate `Parity.FaninReduction.*` specialization modules.

## Proof structure

* `sup_count`   — `#{S : |S|=s, T ⊆ S} = C(n-|T|, s-|T|)` via the bijection `S ↦ S \ T`.
* `dbl_count`   — double counting: `∑_S 2^{|S∩V|} = ∑_{T ⊆ V} #{S : T ⊆ S}`.
* `pset_sum`    — `∑_{T ⊆ V} x^{|T|} = (1+x)^{|V|}` via `Finset.prod_add`.
* `descFac_prod`— falling-factorial product bound `descFac s j · n^j ≤ descFac n j · s^j`.
* `choose_prod` — its binomial form `C(s,j)·n^j ≤ C(n,j)·s^j`.
* `nat_key`     — `C(n-j,s-j)·n^j ≤ C(n,s)·s^j` via `Nat.choose_mul`.
* `moment_bound`— assembles the four into the rational moment bound.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Count
import Mathlib.Data.Real.Basic
import Formulas.Basic
import Formulas.CnfDnf.SwitchingLemmaBasic

open Finset
open Circuits.CnfDnf.Restrictions
open Circuits

namespace Circuits.HastadParity.FaninReduction

/-- Number of size-`s` supersets (inside `range n`) of a fixed set `T` equals
`C(n - |T|, s - |T|)`, proved by the bijection `S ↦ S \ T`. -/
theorem sup_count (n s : ℕ) (T : Finset ℕ) (h_t : T ⊆ range n) (hcard : T.card ≤ s) :
    ((range n).powersetCard s |>.filter (fun S => T ⊆ S)).card
      = (n - T.card).choose (s - T.card) := by
  have hcardrange : (range n \ T).card = n - T.card := by
    rw [card_sdiff, card_range, inter_eq_left.2 h_t]
  rw [← hcardrange, ← card_powersetCard]
  apply Finset.card_nbij' (fun S => S \ T) (fun U => U ∪ T)
  · intro S h_s
    rw [Finset.mem_coe, mem_filter, mem_powersetCard] at h_s
    obtain ⟨⟨h_ssub, h_scard⟩, h_ts⟩ := h_s
    rw [Finset.mem_coe, mem_powersetCard]
    refine ⟨sdiff_subset_sdiff h_ssub (le_refl T), ?_⟩
    rw [card_sdiff, inter_eq_left.2 h_ts, h_scard]
  · intro U h_u
    rw [Finset.mem_coe, mem_powersetCard] at h_u
    obtain ⟨h_usub, h_ucard⟩ := h_u
    have h_udisj_t : Disjoint U T := by
      rw [Finset.disjoint_right]; intro a ha_t ha_u
      exact (mem_sdiff.1 (h_usub ha_u)).2 ha_t
    rw [Finset.mem_coe, mem_filter, mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, subset_union_right⟩
    · intro a ha
      rw [mem_union] at ha
      cases ha with
      | inl h => exact (mem_sdiff.1 (h_usub h)).1
      | inr h => exact h_t h
    · rw [card_union_of_disjoint h_udisj_t, h_ucard]; omega
  · intro S h_s
    rw [Finset.mem_coe, mem_filter, mem_powersetCard] at h_s
    exact sdiff_union_of_subset h_s.2
  · intro U h_u
    rw [Finset.mem_coe, mem_powersetCard] at h_u
    have h_udisj_t : Disjoint U T := by
      rw [Finset.disjoint_right]; intro a ha_t ha_u
      exact (mem_sdiff.1 (h_u.1 ha_u)).2 ha_t
    exact union_sdiff_cancel_right h_udisj_t

/-- Double counting: `∑_S 2^{|S∩V|} = ∑_{T ⊆ V} #{S : T ⊆ S}`. -/
theorem dbl_count (n s : ℕ) (V : Finset ℕ) :
    ∑ S ∈ (range n).powersetCard s, 2 ^ ((S ∩ V).card)
      = ∑ T ∈ V.powerset, ((range n).powersetCard s |>.filter (fun S => T ⊆ S)).card := by
  have hpow : ∀ S : Finset ℕ, 2 ^ ((S ∩ V).card)
      = (V.powerset.filter (fun T => T ⊆ S)).card := by
    intro S
    rw [← card_powerset]; congr 1; ext T
    simp only [mem_powerset, mem_filter, subset_inter_iff]; tauto
  simp_rw [hpow, card_filter]
  rw [Finset.sum_comm]

/-- `∑_{T ⊆ V} x^{|T|} = (1 + x)^{|V|}`. -/
theorem pset_sum (V : Finset ℕ) (x : ℚ) :
    ∑ T ∈ V.powerset, x ^ (T.card) = (1 + x) ^ (V.card) := by
  have h := Finset.prod_add (fun _ : ℕ => x) (fun _ : ℕ => (1:ℚ)) V
  simp only [Finset.prod_const, one_pow, mul_one] at h
  rw [add_comm]; exact h.symm

/-- Falling-factorial product bound: `descFac s j · n^j ≤ descFac n j · s^j`. -/
theorem descFac_prod (s n j : ℕ) (hsn : s ≤ n) :
    Nat.descFactorial s j * n ^ j ≤ Nat.descFactorial n j * s ^ j := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  have key : ∀ i ∈ range j, (s - i) * n ≤ (n - i) * s := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (s - i) * n = s * n - i * n := by rw [Nat.sub_mul]
    have h2 : (n - i) * s = n * s - i * s := by rw [Nat.sub_mul]
    rw [h1, h2, Nat.mul_comm s n]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hsn) (n * s)
  calc (∏ i ∈ range j, (s - i)) * n ^ j
      = ∏ i ∈ range j, ((s - i) * n) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, card_range]
    _ ≤ ∏ i ∈ range j, ((n - i) * s) := Finset.prod_le_prod' key
    _ = (∏ i ∈ range j, (n - i)) * s ^ j := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, card_range]

/-- Binomial form of the product bound: `C(s,j)·n^j ≤ C(n,j)·s^j`. -/
theorem choose_prod (s n j : ℕ) (hsn : s ≤ n) :
    Nat.choose s j * n ^ j ≤ Nat.choose n j * s ^ j := by
  have h_c1 := descFac_prod s n j hsn
  rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose] at h_c1
  have e1 : (Nat.factorial j * s.choose j) * n ^ j
      = Nat.factorial j * (s.choose j * n ^ j) := by ring
  have e2 : (Nat.factorial j * n.choose j) * s ^ j
      = Nat.factorial j * (n.choose j * s ^ j) := by ring
  rw [e1, e2] at h_c1
  exact Nat.le_of_mul_le_mul_left h_c1 (Nat.factorial_pos j)

/-- The key arithmetic inequality `C(n-j, s-j)·n^j ≤ C(n,s)·s^j`. -/
theorem nat_key (n s j : ℕ) (hjs : j ≤ s) (hsn : s ≤ n) :
    (n - j).choose (s - j) * n ^ j ≤ n.choose s * s ^ j := by
  have hcm : n.choose s * s.choose j = n.choose j * (n - j).choose (s - j) :=
    Nat.choose_mul hjs
  have hc2 := choose_prod s n j hsn
  have h3 : n.choose s * (s.choose j * n ^ j) ≤ n.choose s * (n.choose j * s ^ j) :=
    Nat.mul_le_mul_left _ hc2
  have e1 : n.choose s * (s.choose j * n ^ j)
      = n.choose j * ((n - j).choose (s - j) * n ^ j) := by
    rw [← mul_assoc, hcm, mul_assoc]
  have e2 : n.choose s * (n.choose j * s ^ j)
      = n.choose j * (n.choose s * s ^ j) := by ring
  rw [e1, e2] at h3
  exact Nat.le_of_mul_le_mul_left h3 (Nat.choose_pos (le_trans hjs hsn))

/-- **Moment bound.**  The first-moment heart of the kill-wide-gates argument:
`∑_{S ∈ powersetCard s (range n)} 2^{|S∩V|} ≤ C(n,s)·(1 + s/n)^{|V|}` over `ℚ`. -/
theorem moment_bound (n s : ℕ) (V : Finset ℕ) (h_v : V ⊆ range n)
    (hsn : s ≤ n) (hn : 0 < n) :
    ((∑ S ∈ (range n).powersetCard s, 2 ^ ((S ∩ V).card) : ℕ) : ℚ)
      ≤ (n.choose s : ℚ) * (1 + (s : ℚ) / n) ^ (V.card) := by
  rw [dbl_count, Nat.cast_sum]
  rw [← pset_sum V ((s : ℚ) / n), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T h_t_mem
  rw [mem_powerset] at h_t_mem
  have h_trange : T ⊆ range n := h_t_mem.trans h_v
  by_cases hjs : T.card ≤ s
  · rw [sup_count n s T h_trange hjs]
    have hkey := nat_key n s T.card hjs hsn
    rw [div_pow, ← mul_div_assoc,
        le_div_iff₀ (pow_pos (by exact_mod_cast hn : (0:ℚ) < n) T.card)]
    exact_mod_cast hkey
  · push Not at hjs
    have hempty : ((range n).powersetCard s |>.filter (fun S => T ⊆ S)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S h_s h_ts
      rw [mem_powersetCard] at h_s
      have hle := Finset.card_le_card h_ts
      omega
    rw [hempty, Nat.cast_zero]
    positivity

/-- Per-live-set term identity for the kill count.  For a fixed live set `S` of
size `s` and a gate with variable set `V`, the number of dead-bit assignments
that fail to kill the gate is `2^{(n-s) - |V \ S|}`, which equals
`2^{n-s} · 2^{|S ∩ V|} / 2^{|V|}` over `ℚ`.  (Each dead variable of the gate must
take its unique non-forcing value; the remaining `(n-s) - |V \ S|` dead variables
are free.) -/
theorem kill_term_eq (n s : ℕ) (V S : Finset ℕ) (h_ssub : S ⊆ range n)
    (h_scard : S.card = s) (h_v : V ⊆ range n) :
    ((2:ℚ) ^ ((n - s) - (V \ S).card))
      = 2 ^ (n - s) * (2:ℚ) ^ ((S ∩ V).card) / 2 ^ (V.card) := by
  have hab : (V \ S).card + (S ∩ V).card = V.card := by
    rw [inter_comm S V]; exact card_sdiff_add_card_inter V S
  have hsdiff : (range n \ S).card = n - s := by
    rw [card_sdiff, card_range, inter_eq_left.2 h_ssub, h_scard]
  have hsub : V \ S ⊆ range n \ S := by
    intro a ha; rw [mem_sdiff] at ha ⊢; exact ⟨h_v ha.1, ha.2⟩
  have hale : (V \ S).card ≤ n - s := by
    rw [← hsdiff]; exact Finset.card_le_card hsub
  have hnat : (2:ℕ) ^ ((n - s) - (V \ S).card) * 2 ^ V.card
      = 2 ^ (n - s) * 2 ^ ((S ∩ V).card) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hnat_q : (2:ℚ) ^ ((n - s) - (V \ S).card) * 2 ^ V.card
      = 2 ^ (n - s) * 2 ^ ((S ∩ V).card) := by exact_mod_cast hnat
  rw [eq_div_iff (by positivity)]; exact hnat_q

/-- **Per-gate kill count bound.**  Summing the per-live-set non-killing counts
`2^{(n-s) - |V \ S|}` over all live sets gives at most
`C(n,s)·2^{n-s}·((1 + s/n)/2)^{|V|}`.  This is the moment bound divided through
by `2^{|V|}`.  If `q ≤ 1` bounds `(1 + s/n)/2`, a gate with
`|V| ≥ t+1` survives under at most a `q^(t+1)` fraction of restrictions. -/
theorem moment_kill_bound (n s : ℕ) (V : Finset ℕ) (h_v : V ⊆ range n)
    (hsn : s ≤ n) (hn : 0 < n) :
    ((∑ S ∈ (range n).powersetCard s, 2 ^ ((n - s) - (V \ S).card) : ℕ) : ℚ)
      ≤ n.choose s * 2 ^ (n - s) * ((1 + s / n) / 2) ^ V.card := by
  rw [Nat.cast_sum]
  have hsum : ∑ S ∈ (range n).powersetCard s, ((2:ℚ) ^ ((n - s) - (V \ S).card))
      = 2 ^ (n - s) / 2 ^ (V.card)
          * ∑ S ∈ (range n).powersetCard s, (2:ℚ) ^ ((S ∩ V).card) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S h_s
    rw [mem_powersetCard] at h_s
    rw [kill_term_eq n s V S h_s.1 h_s.2 h_v]
    ring
  push_cast
  rw [hsum]
  have hmb := moment_bound n s V h_v hsn hn
  rw [Nat.cast_sum] at hmb
  push_cast at hmb
  calc 2 ^ (n - s) / 2 ^ (V.card)
          * ∑ S ∈ (range n).powersetCard s, (2:ℚ) ^ ((S ∩ V).card)
      ≤ 2 ^ (n - s) / 2 ^ (V.card)
          * (n.choose s * (1 + s / n) ^ V.card) := by
        apply mul_le_mul_of_nonneg_left hmb
        positivity
    _ = n.choose s * 2 ^ (n - s) * ((1 + s / n) / 2) ^ V.card := by
        rw [div_pow]; ring

/-! ### Union bound over the wide gates

The kill-wide-gates step needs: if the total count of restrictions that fail to
kill *some* wide gate is below the total number of restrictions, then a
restriction killing *all* of them exists.  These are the generic list-counting
primitives behind that union bound. -/

/-- `countP` of a binary disjunction is at most the sum of the two counts. -/
theorem countP_or_le {α : Type*} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

/-- Union bound: `countP` of a disjunction over a list of predicates is at most
the sum of the individual counts. -/
theorem countP_any_le {α : Type*} (l : List α) (ps : List (α → Bool)) :
    l.countP (fun x => ps.any (fun p => p x)) ≤ (ps.map (fun p => l.countP p)).sum := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hstep : l.countP (fun x => (p x || rest.any (fun q => q x)))
        ≤ l.countP p + l.countP (fun x => rest.any (fun q => q x)) :=
      countP_or_le l p (fun x => rest.any (fun q => q x))
    calc l.countP (fun x => (p :: rest).any (fun r => r x))
        = l.countP (fun x => (p x || rest.any (fun q => q x))) := by
          apply List.countP_congr; intro x _; simp [List.any_cons]
      _ ≤ l.countP p + l.countP (fun x => rest.any (fun q => q x)) := hstep
      _ ≤ l.countP p + (rest.map (fun p => l.countP p)).sum :=
          Nat.add_le_add_left ih _

/-
## Model identification: counting bit-lists that match a partial requirement

For a fixed live set `S`, every dead variable of a bottom gate forces one bit of
the `(n-s)`-long dead-bit list (its non-forcing value); the gate is *not killed*
iff that bit list matches the partial requirement `req`.  The number of matching
bit lists is exactly `2 ^ (#dead − #constrained)`.  `matchAt`/`numConstr` model
the requirement, and `bitcount` is the closed-form count over `allBitLists`.
-/

/-- `matchAt req l` is `true` iff every position `i` of `l` for which `req i`
is `some r` has `l[i] = r`. -/
def matchAt : (Nat → Option Bool) → List Bool → Bool
  | _, [] => true
  | req, b :: l =>
      (match req 0 with | some r => r == b | none => true) && matchAt (fun i => req (i+1)) l

theorem matchAt_cons (req : Nat → Option Bool) (b : Bool) (l : List Bool) :
    matchAt req (b :: l)
      = ((match req 0 with | some r => r == b | none => true) &&
          matchAt (fun i => req (i + 1)) l) := rfl

/-- Number of constrained positions among the first `k` of `req`. -/
def numConstr : (Nat → Option Bool) → Nat → Nat
  | _, 0 => 0
  | req, k+1 => (match req 0 with | some _ => 1 | none => 0) + numConstr (fun i => req (i+1)) k

theorem numConstr_le (req : Nat → Option Bool) (k : ℕ) : numConstr req k ≤ k := by
  induction k generalizing req with
  | zero => simp [numConstr]
  | succ k ih =>
    simp only [numConstr]; have := ih (fun i => req (i+1)); cases req 0 <;> simp <;> omega

theorem countP_doubled (p : List Bool → Bool) (L : List (List Bool)) :
    ((L.map (fun l => [false :: l, true :: l])).flatten).countP p
      = L.countP (fun l => p (false :: l)) + L.countP (fun l => p (true :: l)) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.flatten_cons, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add]; omega

/-- The closed-form count: exactly `2 ^ (k − #constrained)` of the `2^k`
bit-lists of length `k` match the partial requirement `req`. -/
theorem bitcount (req : Nat → Option Bool) (k : ℕ) :
    (allBitLists k).countP (matchAt req) = 2 ^ (k - numConstr req k) := by
  induction k generalizing req with
  | zero => simp [allBitLists, matchAt, numConstr]
  | succ k ih =>
    show (allBitLists (k+1)).countP (matchAt req) = _
    rw [allBitLists, countP_doubled]
    have ihk := ih (fun i => req (i+1))
    have hle := numConstr_le (fun i => req (i+1)) k
    cases hr : req 0 with
    | none =>
      have e0 : (fun l => matchAt req (false :: l)) = matchAt (fun i => req (i+1)) := by
        funext l; rw [matchAt_cons, hr]; simp
      have e1 : (fun l => matchAt req (true :: l)) = matchAt (fun i => req (i+1)) := by
        funext l; rw [matchAt_cons, hr]; simp
      rw [e0, e1, ihk, numConstr, hr]
      rw [show k + 1 - (0 + numConstr (fun i => req (i+1)) k)
            = (k - numConstr (fun i => req (i+1)) k) + 1 from by omega, pow_succ]
      ring
    | some r =>
      rw [numConstr, hr]
      cases r with
      | false =>
        have e0 : (fun l => matchAt req (false :: l)) = matchAt (fun i => req (i+1)) := by
          funext l; rw [matchAt_cons, hr]; rfl
        have e1 : (fun l => matchAt req (true :: l)) = (fun _ => false) := by
          funext l; rw [matchAt_cons, hr]; rfl
        rw [e0, e1, ihk]; simp; omega
      | true =>
        have e0 : (fun l => matchAt req (false :: l)) = (fun _ => false) := by
          funext l; rw [matchAt_cons, hr]; rfl
        have e1 : (fun l => matchAt req (true :: l)) = matchAt (fun i => req (i+1)) := by
          funext l; rw [matchAt_cons, hr]; rfl
        rw [e0, e1, ihk]; simp; omega

/-
## Rank map and project-model identification

In the project restriction model, a dead variable `v ∉ S` receives the dead-bit
at rank `rankS S v = #(range v \ S)` (the number of dead variables below it).
The next bricks identify the project's "gate survives" predicate over
`allBitLists (n-s)` with a `matchAt req` predicate, and compute the closed-form
survival count via `bitcount`.
-/

/-- Rank of a variable among the dead variables strictly below it. -/
def rankS (S : Finset Nat) (v : Nat) : Nat := (Finset.range v \ S).card

theorem rankS_strictMono (S : Finset Nat) {a b : Nat} (hab : a < b) (ha : a ∉ S) :
    rankS S a < rankS S b := by
  unfold rankS
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (by
    intro x hx; rw [Finset.mem_sdiff] at hx ⊢; rw [Finset.mem_range] at hx ⊢
    exact ⟨lt_trans hx.1 hab, hx.2⟩)]
  exact ⟨a, by rw [Finset.mem_sdiff, Finset.mem_range]; exact ⟨hab, ha⟩,
            by rw [Finset.mem_sdiff, Finset.mem_range]; simp⟩

theorem rankS_inj (S : Finset Nat) {a b : Nat} (ha : a ∉ S) (hb : b ∉ S)
    (h : rankS S a = rankS S b) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (rankS_strictMono S hlt ha))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (rankS_strictMono S hgt hb))

theorem rankS_lt (S : Finset Nat) {n v : Nat} (hv : v < n) (hv_s : v ∉ S) :
    rankS S v < (Finset.range n \ S).card := by
  unfold rankS
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (by
    intro x hx; rw [Finset.mem_sdiff] at hx ⊢; rw [Finset.mem_range] at hx ⊢
    exact ⟨lt_trans hx.1 hv, hx.2⟩)]
  exact ⟨v, by rw [Finset.mem_sdiff, Finset.mem_range]; exact ⟨hv, hv_s⟩,
            by rw [Finset.mem_sdiff, Finset.mem_range]; simp⟩

/-- `numConstr req k` counts the constrained positions in `range k`. -/
theorem numConstr_eq_card (req : Nat → Option Bool) (k : ℕ) :
    numConstr req k = ((Finset.range k).filter (fun r => (req r).isSome)).card := by
  rw [Finset.card_filter]
  induction k generalizing req with
  | zero => simp [numConstr]
  | succ k ih =>
    rw [numConstr, ih (fun i => req (i+1)), Finset.sum_range_succ', Nat.add_comm]
    congr 1; cases req 0 <;> simp

/-- `matchAt req l` holds iff every constrained position of `l` carries the
required value. -/
theorem matchAt_iff (req : Nat → Option Bool) (l : List Bool) :
    matchAt req l = true ↔ ∀ i, i < l.length → ∀ r, req i = some r → l[i]? = some r := by
  induction l generalizing req with
  | nil => simp [matchAt]
  | cons b l ih =>
    rw [matchAt_cons]
    constructor
    · intro h i hi r hr
      rw [Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      cases i with
      | zero =>
        rw [hr] at hhead
        simp only [beq_iff_eq] at hhead
        rw [hhead]
        rfl
      | succ i =>
        have hi' : i < l.length := by simp at hi; omega
        simpa using (ih (fun j => req (j+1))).mp htail i hi' r hr
    · intro h
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · cases hq : req 0 with
        | none => simp
        | some r =>
          have := h 0 (by simp) r hq
          have hrb : r = b := by simpa using this.symm
          simp [hrb]
      · rw [(ih (fun j => req (j+1)))]
        intro i hi r hr
        have := h (i+1) (by simp; omega) r hr
        simpa using this

/-- The partial requirement induced by a gate: position `i` is constrained iff it
is the rank of some dead variable `v ∈ W`, with required value `val v`. -/
noncomputable def reqOf (S W : Finset Nat) (val : Nat → Bool) (i : Nat) : Option Bool :=
  if h : ∃ v, v ∈ W ∧ rankS S v = i then some (val h.choose) else none

theorem reqOf_at (S W : Finset Nat) (val : Nat → Bool) {n v : Nat}
    (h_w : W ⊆ Finset.range n \ S) (hv : v ∈ W) :
    reqOf S W val (rankS S v) = some (val v) := by
  have hex : ∃ v', v' ∈ W ∧ rankS S v' = rankS S v := ⟨v, hv, rfl⟩
  unfold reqOf
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  have hc_s : hex.choose ∉ S := (Finset.mem_sdiff.mp (h_w hspec.1)).2
  have hv_s : v ∉ S := (Finset.mem_sdiff.mp (h_w hv)).2
  have : hex.choose = v := rankS_inj S hc_s hv_s hspec.2
  rw [this]

theorem reqOf_some_inv (S W : Finset Nat) (val : Nat → Bool) {i : Nat} {r : Bool}
    (h : reqOf S W val i = some r) : ∃ v, v ∈ W ∧ rankS S v = i ∧ r = val v := by
  unfold reqOf at h
  by_cases hex : ∃ v, v ∈ W ∧ rankS S v = i
  · rw [dif_pos hex] at h
    simp only [Option.some.injEq] at h
    exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, h.symm⟩
  · rw [dif_neg hex] at h; exact absurd h (by simp)

/-- **Survival count.** For a fixed live set `S ⊆ range n` and a dead-variable set
`W ⊆ range n \ S` with required values `val`, exactly `2 ^ ((n-s) - |W|)` of the
`2^(n-s)` dead-bit lists satisfy every constraint of `W`. -/
theorem survives_count (n : Nat) (S W : Finset Nat) (val : Nat → Bool)
    (h_w : W ⊆ Finset.range n \ S) :
    (allBitLists ((Finset.range n \ S).card)).countP
        (fun bits => decide (∀ v ∈ W, bits[(rankS S v)]? = some (val v)))
      = 2 ^ ((Finset.range n \ S).card - W.card) := by
  set k := (Finset.range n \ S).card with hk
  have hcongr : (allBitLists k).countP
        (fun bits => decide (∀ v ∈ W, bits[(rankS S v)]? = some (val v)))
      = (allBitLists k).countP (matchAt (reqOf S W val)) := by
    apply List.countP_congr
    intro bits hbits
    have hlen : bits.length = k := allBitLists_mem_length k bits hbits
    have hiff : (∀ v ∈ W, bits[(rankS S v)]? = some (val v))
        ↔ matchAt (reqOf S W val) bits = true := by
      constructor
      · intro hp
        rw [matchAt_iff]
        intro i hi r hr
        obtain ⟨v, hv_w, hrank, hrv⟩ := reqOf_some_inv S W val hr
        rw [← hrank, hrv]; exact hp v hv_w
      · intro hm v hv_w
        rw [matchAt_iff] at hm
        have hvn : v < n := Finset.mem_range.mp (Finset.mem_sdiff.mp (h_w hv_w)).1
        have hv_s : v ∉ S := (Finset.mem_sdiff.mp (h_w hv_w)).2
        have hlt : rankS S v < bits.length := by rw [hlen]; exact rankS_lt S hvn hv_s
        exact hm (rankS S v) hlt (val v) (reqOf_at S W val h_w hv_w)
    have heq : decide (∀ v ∈ W, bits[(rankS S v)]? = some (val v))
        = decide (matchAt (reqOf S W val) bits = true) := by
      rw [decide_eq_decide]; exact hiff
    rw [heq]; simp
  rw [hcongr, bitcount]
  have hnum : numConstr (reqOf S W val) k = W.card := by
    rw [numConstr_eq_card]
    have himg : (Finset.range k).filter (fun r => (reqOf S W val r).isSome)
        = W.image (rankS S) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨_, hsome⟩
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨v, hv_w, hrank, _⟩ := reqOf_some_inv S W val hr
        exact ⟨v, hv_w, hrank⟩
      · rintro ⟨v, hv_w, hrank⟩
        have hvn : v < n := Finset.mem_range.mp (Finset.mem_sdiff.mp (h_w hv_w)).1
        have hv_s : v ∉ S := (Finset.mem_sdiff.mp (h_w hv_w)).2
        refine ⟨?_, ?_⟩
        · rw [← hrank, hk]; exact rankS_lt S hvn hv_s
        · rw [← hrank, reqOf_at S W val h_w hv_w]; rfl
    have hinj : Set.InjOn (rankS S) ↑W := by
      intro a ha b hb hab
      exact rankS_inj S (Finset.mem_sdiff.mp (h_w (Finset.mem_coe.mp ha))).2
                        (Finset.mem_sdiff.mp (h_w (Finset.mem_coe.mp hb))).2 hab
    rw [himg, Finset.card_image_of_injOn hinj]
  rw [hnum]

/-
## Kill-wide-gates existence (Round 0 of the Håstad iteration)

Assembling the per-gate survival count (`survives_count`), the first-moment kill
bound (`moment_kill_bound`), and a union bound over the wide gates, we obtain a
single restriction `(S, bits)` that kills every wide bottom gate.  This is the
genuine missing Håstad keystone (the switching lemma does not provide it).
-/

/-- A gate with variable set `V` and forcing values `val` *survives* the
restriction with live set `S` and dead-bit list `bits` iff every dead variable of
the gate receives its forcing bit. -/
def survPred (S V : Finset Nat) (val : Nat → Bool) (bits : List Bool) : Bool :=
  decide (∀ v ∈ V \ S, bits[(rankS S v)]? = some (val v))

theorem card_sdiff_range {n s : Nat} {S : Finset Nat}
    (h_s : S ⊆ Finset.range n) (hcard : S.card = s) :
    (Finset.range n \ S).card = n - s := by
  rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.2 h_s, hcard]

/-- The total restriction-count of surviving dead-bit lists, summed over live sets
`S`, is bounded by the first moment `C(n,s)·2^(n-s)·((1+s/n)/2)^|V|`. -/
theorem gate_sum_bound (n s : ℕ) (V : Finset ℕ) (val : Nat → Bool)
    (h_v : V ⊆ range n) (hsn : s ≤ n) (hn : 0 < n) :
    ((∑ S ∈ (range n).powersetCard s,
        (allBitLists (n - s)).countP (survPred S V val) : ℕ) : ℚ)
      ≤ (n.choose s : ℚ) * 2 ^ (n - s) * ((1 + (s : ℚ) / n) / 2) ^ (V.card) := by
  have heq : (∑ S ∈ (range n).powersetCard s,
        (allBitLists (n - s)).countP (survPred S V val))
      = ∑ S ∈ (range n).powersetCard s, 2 ^ ((n - s) - (V \ S).card) := by
    apply Finset.sum_congr rfl
    intro S h_s
    rw [mem_powersetCard] at h_s
    obtain ⟨h_ssub, h_scard⟩ := h_s
    have hcard : (Finset.range n \ S).card = n - s := card_sdiff_range h_ssub h_scard
    have h_w : V \ S ⊆ Finset.range n \ S := by
      intro x hx; rw [Finset.mem_sdiff] at hx ⊢; exact ⟨h_v hx.1, hx.2⟩
    have := survives_count n S (V \ S) val h_w
    rw [hcard] at this
    rw [show (survPred S V val) = (fun bits => decide (∀ v ∈ V \ S,
          bits[(rankS S v)]? = some (val v))) from rfl]
    rw [this]
  rw [heq]
  exact moment_kill_bound n s V h_v hsn hn

/-- If over a finite index set `U` the total number of "surviving" elements is
strictly less than the total number of elements, some index has an escaping
element. -/
theorem exists_escaping_finset {ι : Type*} {α : Type*}
    (U : Finset ι) (lists : ι → List α) (surv : ι → α → Bool)
    (h : (U.sum fun i => (lists i).countP (surv i)) < (U.sum fun i => (lists i).length)) :
    ∃ i ∈ U, ∃ x ∈ lists i, surv i x = false := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ i ∈ U, (lists i).countP (surv i) = (lists i).length := by
    intro i hi
    rw [List.countP_eq_length]
    intro x hx
    by_contra hx'
    simp only [Bool.not_eq_true] at hx'
    exact (hcon i hi x hx) hx'
  have : (U.sum fun i => (lists i).countP (surv i)) = (U.sum fun i => (lists i).length) :=
    Finset.sum_congr rfl hall
  omega

theorem sum_finset_list {ι γ : Type*} (U : Finset ι) (gates : List γ) (c : ι → γ → ℕ) :
    (∑ i ∈ U, (gates.map (fun g => c i g)).sum)
      = (gates.map (fun g => ∑ i ∈ U, c i g)).sum := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-- Parameterized kill-wide-gates lemma.  The rational `q` is any upper bound
on the per-variable survival probability of the chosen live-set density. -/
theorem exists_kill_all_wide_of_bound (q : ℚ) (n s t : ℕ)
    (gates : List (Finset ℕ × (Nat → Bool)))
    (hsn : s ≤ n) (hn : 0 < n)
    (hsub : ∀ g ∈ gates, g.1 ⊆ range n)
    (hwide : ∀ g ∈ gates, t + 1 ≤ g.1.card)
    (hq1 : q ≤ 1)
    (hσ : (1 + (s : ℚ) / n) / 2 ≤ q)
    (hcount : (gates.length : ℚ) * q ^ (t + 1) < 1) :
    ∃ S ∈ (range n).powersetCard s, ∃ bits ∈ allBitLists (n - s),
      ∀ g ∈ gates, survPred S g.1 g.2 bits = false := by
  set U := (range n).powersetCard s with h_u
  set surv : Finset ℕ → List Bool → Bool :=
    fun S bits => gates.any (fun g => survPred S g.1 g.2 bits) with hsurv
  have hbase_nonneg : (0 : ℚ) ≤ (1 + (s : ℚ) / n) / 2 := by positivity
  have hbase_le1 : (1 + (s : ℚ) / n) / 2 ≤ 1 := le_trans hσ hq1
  have hper_s : ∀ S, (allBitLists (n - s)).countP (surv S)
      ≤ (gates.map (fun g =>
          (allBitLists (n - s)).countP (survPred S g.1 g.2))).sum := by
    intro S
    have h1 : (allBitLists (n - s)).countP (surv S)
        = (allBitLists (n - s)).countP
            (fun bits =>
              (gates.map (fun g => survPred S g.1 g.2)).any (fun p => p bits)) := by
      apply List.countP_congr
      intro bits _
      simp only [hsurv, List.any_map, Function.comp_def]
    rw [h1]
    have h_any := countP_any_le (allBitLists (n - s))
      (gates.map (fun g => survPred S g.1 g.2))
    rw [List.map_map] at h_any
    exact h_any
  have hgate : ∀ g ∈ gates,
      ((∑ S ∈ U,
          (allBitLists (n - s)).countP (survPred S g.1 g.2) : ℕ) : ℚ)
        ≤ (n.choose s : ℚ) * 2 ^ (n - s) * q ^ (t + 1) := by
    intro g hg
    have hb := gate_sum_bound n s g.1 g.2 (hsub g hg) hsn hn
    have hpow : ((1 + (s : ℚ) / n) / 2) ^ (g.1.card) ≤ q ^ (t + 1) := by
      calc
        ((1 + (s : ℚ) / n) / 2) ^ (g.1.card)
            ≤ ((1 + (s : ℚ) / n) / 2) ^ (t + 1) :=
          pow_le_pow_of_le_one hbase_nonneg hbase_le1 (hwide g hg)
        _ ≤ q ^ (t + 1) := by
          apply pow_le_pow_left₀ hbase_nonneg hσ
    have h_cnn : (0 : ℚ) ≤ (n.choose s : ℚ) * 2 ^ (n - s) := by positivity
    calc
      ((∑ S ∈ U,
          (allBitLists (n - s)).countP (survPred S g.1 g.2) : ℕ) : ℚ)
          ≤ (n.choose s : ℚ) * 2 ^ (n - s) *
              ((1 + (s : ℚ) / n) / 2) ^ (g.1.card) := hb
      _ ≤ (n.choose s : ℚ) * 2 ^ (n - s) * q ^ (t + 1) :=
        mul_le_mul_of_nonneg_left hpow h_cnn
  have hbad_le :
      ((∑ S ∈ U, (allBitLists (n - s)).countP (surv S) : ℕ) : ℚ)
        ≤ (gates.length : ℚ) *
            ((n.choose s : ℚ) * 2 ^ (n - s) * q ^ (t + 1)) := by
    have hstep1 :
        (∑ S ∈ U, (allBitLists (n - s)).countP (surv S))
          ≤ ∑ S ∈ U,
              (gates.map (fun g =>
                (allBitLists (n - s)).countP (survPred S g.1 g.2))).sum :=
      Finset.sum_le_sum (fun S _ => hper_s S)
    have hstep2 :=
      sum_finset_list U gates
        (fun S g => (allBitLists (n - s)).countP (survPred S g.1 g.2))
    calc
      ((∑ S ∈ U, (allBitLists (n - s)).countP (surv S) : ℕ) : ℚ)
          ≤ ((∑ S ∈ U,
              (gates.map (fun g =>
                (allBitLists (n - s)).countP
                  (survPred S g.1 g.2))).sum : ℕ) : ℚ) := by
            exact_mod_cast hstep1
      _ = ((gates.map (fun g =>
            ∑ S ∈ U, (allBitLists (n - s)).countP
              (survPred S g.1 g.2))).sum : ℚ) := by
          rw [hstep2]
      _ = (gates.map (fun g =>
            ((∑ S ∈ U, (allBitLists (n - s)).countP
              (survPred S g.1 g.2) : ℕ) : ℚ))).sum := by
          rw [Nat.cast_list_sum, List.map_map]
          rfl
      _ ≤ (gates.map (fun _ =>
            (n.choose s : ℚ) * 2 ^ (n - s) * q ^ (t + 1))).sum := by
          apply List.sum_le_sum
          intro x hx
          exact hgate x hx
      _ = (gates.length : ℚ) *
            ((n.choose s : ℚ) * 2 ^ (n - s) * q ^ (t + 1)) := by
          rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  have hchoose : 0 < n.choose s := Nat.choose_pos hsn
  have h_cpos : (0 : ℚ) < (n.choose s : ℚ) * 2 ^ (n - s) := by
    have : (0 : ℚ) < (n.choose s : ℚ) := by exact_mod_cast hchoose
    positivity
  have hlt :
      ((∑ S ∈ U, (allBitLists (n - s)).countP (surv S) : ℕ) : ℚ)
        < (n.choose s : ℚ) * 2 ^ (n - s) := by
    calc
      ((∑ S ∈ U, (allBitLists (n - s)).countP (surv S) : ℕ) : ℚ)
          ≤ (gates.length : ℚ) *
              ((n.choose s : ℚ) * 2 ^ (n - s) * q ^ (t + 1)) := hbad_le
      _ = ((n.choose s : ℚ) * 2 ^ (n - s)) *
            ((gates.length : ℚ) * q ^ (t + 1)) := by ring
      _ < ((n.choose s : ℚ) * 2 ^ (n - s)) * 1 :=
        mul_lt_mul_of_pos_left hcount h_cpos
      _ = (n.choose s : ℚ) * 2 ^ (n - s) := by ring
  have htotal :
      (∑ S ∈ U, (allBitLists (n - s)).length) =
        n.choose s * 2 ^ (n - s) := by
    rw [Finset.sum_const, smul_eq_mul, allBitLists_length, h_u,
      Finset.card_powersetCard, Finset.card_range]
  have h_nat :
      (∑ S ∈ U, (allBitLists (n - s)).countP (surv S))
        < (∑ S ∈ U, (allBitLists (n - s)).length) := by
    rw [htotal]
    have hcast :
        ((n.choose s : ℚ) * 2 ^ (n - s)) =
          ((n.choose s * 2 ^ (n - s) : ℕ) : ℚ) := by
      push_cast
      ring
    rw [hcast] at hlt
    exact_mod_cast hlt
  obtain ⟨S, h_su, bits, hbits, hfalse⟩ :=
    exists_escaping_finset U (fun _ => allBitLists (n - s)) surv h_nat
  refine ⟨S, h_su, bits, hbits, ?_⟩
  intro g hg
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have htrue : surv S bits = true := by
    simp only [hsurv]
    exact List.any_eq_true.mpr ⟨g, hg, hc⟩
  rw [htrue] at hfalse
  exact absurd hfalse (by simp)

/-
## Bridge to the project clause-kill predicate

Connecting the abstract `survPred` to the project's `isClauseKilled` under the
restriction `mkAssignment S bits`.  This lets the parameterized existence
keystone `exists_kill_all_wide_of_bound` speak about actual bottom DNF/CNF
clauses.
-/

/-- The set of variables appearing in a clause. -/
def clauseVars (c : List (Nat × Bool)) : Finset Nat := (c.map Prod.fst).toFinset

/-- The satisfying bit for variable `v` according to its (first) literal in `c`. -/
noncomputable def clauseVal (c : List (Nat × Bool)) : Nat → Bool := fun v =>
  match c.find? (fun p => p.1 == v) with
  | some (_, neg) => literalSatisfyingBit neg
  | none => false

theorem find_fst {c : List (Nat × Bool)} {v : Nat} {p : Nat × Bool}
    (h : c.find? (fun q => q.1 == v) = some p) : p.1 = v := by
  have := List.find?_some h
  simpa using this

theorem mem_clauseVars {c : List (Nat × Bool)} {v : Nat} :
    v ∈ clauseVars c ↔ ∃ neg, (v, neg) ∈ c := by
  unfold clauseVars
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨w, neg⟩, hmem, rfl⟩; exact ⟨neg, hmem⟩
  · rintro ⟨neg, hmem⟩; exact ⟨(v, neg), hmem, rfl⟩

theorem find_isSome_of_mem {c : List (Nat × Bool)} {v : Nat}
    (hv : v ∈ clauseVars c) : (c.find? (fun p => p.1 == v)).isSome := by
  rw [mem_clauseVars] at hv
  obtain ⟨neg, hmem⟩ := hv
  rw [List.find?_isSome]
  exact ⟨(v, neg), hmem, by simp⟩

/-- With NoDup variables, the literal `(v, neg) ∈ c` pins `clauseVal c v` to the
literal's satisfying bit. -/
theorem clauseVal_eq {c : List (Nat × Bool)} (hnd : (c.map Prod.fst).Nodup)
    {v : Nat} {neg : Bool} (hmem : (v, neg) ∈ c) :
    clauseVal c v = literalSatisfyingBit neg := by
  unfold clauseVal
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp
    (find_isSome_of_mem (mem_clauseVars.mpr ⟨neg, hmem⟩))
  rw [hp]
  obtain ⟨w, neg'⟩ := p
  have hwv : w = v := find_fst hp
  subst hwv
  have hpmem : (w, neg') ∈ c := List.mem_of_find?_eq_some hp
  have hpair : c.Pairwise (fun a b => a.1 ≠ b.1) := by
    rw [← List.pairwise_map]; exact hnd
  let hsymm : Std.Symm (fun (a b : Nat × Bool) => a.1 ≠ b.1) :=
    ⟨fun a b h => Ne.symm h⟩
  have hinj := @List.Pairwise.forall _ _ _ hsymm hpair
  have heq : (w, neg') = (w, neg) := by
    by_contra hne
    exact (hinj hpmem hmem hne) rfl
  have : neg' = neg := (Prod.mk.injEq _ _ _ _).mp heq |>.2
  rw [this]

/-- The restriction `mkAssignment S bits` evaluated at a dead variable equals the
bit at the variable's dead-rank. -/
theorem mkAssignment_dead (S : Finset Nat) (bits : List Bool) {v : Nat} (hv : v ∉ S) :
    mkAssignment S bits v = bits[(rankS S v)]? := by
  unfold mkAssignment rankS
  rw [if_neg hv]

/-- **Bridge brick.** A proper clause `c` (NoDup variables) is killed by the
restriction `mkAssignment S bits` iff the abstract survival predicate fails,
i.e. iff `survPred S (clauseVars c) (clauseVal c) bits = false`. Requires that the
dead variables of `c` are covered by `bits` (so their assignment is `some`). -/
theorem clause_killed_iff_survPred
    (S : Finset Nat) (bits : List Bool) (c : List (Nat × Bool))
    (hnd : (c.map Prod.fst).Nodup)
    (hcov : ∀ p ∈ c, p.1 ∉ S → (bits[(rankS S p.1)]?).isSome) :
    isClauseKilled c (mkAssignment S bits)
      = ! survPred S (clauseVars c) (clauseVal c) bits := by
  have claim2 : (! survPred S (clauseVars c) (clauseVal c) bits) = true
      ↔ ∃ v, v ∈ clauseVars c \ S ∧
              bits[(rankS S v)]? ≠ some (clauseVal c v) := by
    rw [Bool.not_eq_true', survPred, decide_eq_false_iff_not]
    push Not
    constructor
    · rintro ⟨v, hv, hne⟩; exact ⟨v, hv, hne⟩
    · rintro ⟨v, hv, hne⟩; exact ⟨v, hv, hne⟩
  have claim1 : isClauseKilled c (mkAssignment S bits) = true
      ↔ ∃ v, v ∈ clauseVars c \ S ∧
              bits[(rankS S v)]? ≠ some (clauseVal c v) := by
    unfold isClauseKilled
    rw [List.any_eq_true]
    constructor
    · rintro ⟨⟨v, neg⟩, hmem, hpred⟩
      dsimp only at hpred
      by_cases hv_s : v ∈ S
      · simp [mkAssignment, hv_s] at hpred
      · rw [mkAssignment_dead S bits hv_s] at hpred
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hcov (v, neg) hmem hv_s)
        rw [hb] at hpred
        simp only at hpred
        have hbne : b ≠ literalSatisfyingBit neg := by
          intro h; rw [h] at hpred; simp at hpred
        refine ⟨v, Finset.mem_sdiff.mpr ⟨mem_clauseVars.mpr ⟨neg, hmem⟩, hv_s⟩, ?_⟩
        rw [hb, clauseVal_eq hnd hmem]
        intro hcontra; exact hbne (Option.some.inj hcontra)
    · rintro ⟨v, hv, hne⟩
      rw [Finset.mem_sdiff] at hv
      obtain ⟨hv_vars, hv_s⟩ := hv
      obtain ⟨neg, hmem⟩ := mem_clauseVars.mp hv_vars
      refine ⟨(v, neg), hmem, ?_⟩
      dsimp only
      rw [mkAssignment_dead S bits hv_s]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hcov (v, neg) hmem hv_s)
      rw [hb]
      simp only
      have hbne : b ≠ literalSatisfyingBit neg := by
        intro h
        apply hne
        rw [hb, clauseVal_eq hnd hmem, h]
      simpa using hbne
  rw [← claim2] at claim1
  cases hk : isClauseKilled c (mkAssignment S bits) <;>
    cases hs : survPred S (clauseVars c) (clauseVal c) bits <;>
    simp_all

/-
## Round-0 assembly: kill all wide bottom clauses

Specializing the abstract keystone to a concrete list of clauses (proper, with
bounded variables), we obtain a single restriction that kills every wide
clause.  This is the density-neutral analytic core of the Round-0 bottom-fan-in
reduction.
-/

/-- `getElem?` is `isSome` whenever the index is within bounds. -/
theorem getElem?_isSome_of_lt {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    (l[i]?).isSome := by
  rw [List.getElem?_eq_getElem h]
  simp

/-- `clauseVars c ⊆ range n` when every variable of `c` is `< n`. -/
theorem clauseVars_subset_range {c : List (Nat × Bool)} {n : Nat}
    (h : ∀ p ∈ c, p.1 < n) : clauseVars c ⊆ range n := by
  intro v hv
  rw [mem_clauseVars] at hv
  obtain ⟨neg, hmem⟩ := hv
  rw [Finset.mem_range]
  exact h (v, neg) hmem

/-- Parameterized clause-level wrapper around
`exists_kill_all_wide_of_bound`. -/
theorem exists_kill_wide_clauses_of_bound (q : ℚ) (n s t : ℕ)
    (clauses : List (List (Nat × Bool)))
    (hsn : s ≤ n) (hn : 0 < n)
    (hnd : ∀ c ∈ clauses, (c.map Prod.fst).Nodup)
    (hvar : ∀ c ∈ clauses, ∀ p ∈ c, p.1 < n)
    (hwide : ∀ c ∈ clauses, t + 1 ≤ (clauseVars c).card)
    (hq1 : q ≤ 1)
    (hσ : (1 + (s : ℚ) / n) / 2 ≤ q)
    (hcount : (clauses.length : ℚ) * q ^ (t + 1) < 1) :
    ∃ S ∈ (range n).powersetCard s, ∃ bits ∈ allBitLists (n - s),
      ∀ c ∈ clauses, isClauseKilled c (mkAssignment S bits) = true := by
  set gates := clauses.map (fun c => (clauseVars c, clauseVal c)) with hgates
  have hsub : ∀ g ∈ gates, g.1 ⊆ range n := by
    intro g hg
    rw [hgates, List.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    exact clauseVars_subset_range (hvar c hc)
  have hwide' : ∀ g ∈ gates, t + 1 ≤ g.1.card := by
    intro g hg
    rw [hgates, List.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    exact hwide c hc
  have hlen : (gates.length : ℚ) = (clauses.length : ℚ) := by
    rw [hgates, List.length_map]
  have hcount' : (gates.length : ℚ) * q ^ (t + 1) < 1 := by
    rw [hlen]
    exact hcount
  obtain ⟨S, h_smem, bits, hbits, hkill⟩ :=
    exists_kill_all_wide_of_bound q n s t gates hsn hn hsub hwide'
      hq1 hσ hcount'
  refine ⟨S, h_smem, bits, hbits, ?_⟩
  rw [mem_powersetCard] at h_smem
  obtain ⟨h_ssub, h_scard⟩ := h_smem
  have hcard_sdiff : (Finset.range n \ S).card = n - s :=
    card_sdiff_range h_ssub h_scard
  have hbitslen : bits.length = n - s :=
    allBitLists_mem_length (n - s) bits hbits
  intro c hc
  have hcov : ∀ p ∈ c, p.1 ∉ S → (bits[(rankS S p.1)]?).isSome := by
    intro p hp hp_s
    have hpn : p.1 < n := hvar c hc p hp
    have hrank : rankS S p.1 < (Finset.range n \ S).card :=
      rankS_lt S hpn hp_s
    rw [hcard_sdiff, ← hbitslen] at hrank
    exact getElem?_isSome_of_lt bits _ hrank
  have hbridge := clause_killed_iff_survPred S bits c (hnd c hc) hcov
  have hsurv : survPred S (clauseVars c) (clauseVal c) bits = false := by
    have hgin : (clauseVars c, clauseVal c) ∈ gates := by
      rw [hgates, List.mem_map]
      exact ⟨c, hc, rfl⟩
    exact hkill _ hgin
  rw [hbridge, hsurv]
  rfl

/-- For a clause with no duplicated variables, the number of distinct variables
equals the clause length. -/
theorem clauseVars_card_eq_length {c : List (Nat × Bool)}
    (hnd : (c.map Prod.fst).Nodup) :
    (clauseVars c).card = c.length := by
  unfold clauseVars
  rw [List.toFinset_card_of_nodup hnd, List.length_map]

/-- A clause whose length is `≥ t+1` is wide in the distinct-variable sense. -/
theorem clauseVars_card_ge {c : List (Nat × Bool)} {t : Nat}
    (hnd : (c.map Prod.fst).Nodup) (hlen : t + 1 ≤ c.length) :
    t + 1 ≤ (clauseVars c).card := by
  rw [clauseVars_card_eq_length hnd]; exact hlen

/-
## Bottom-fan-in reduction: restricted DNF width bound

If every wide original clause is killed, the restricted DNF has small width.
-/

section WidthBound
open Circuits.CnfDnf UnboundedFanInFormula

/-- Bool: literal `(v, neg)` is killed by `asgn`. -/
def litKills (asgn : Nat → Option Bool) (p : Nat × Bool) : Bool :=
  match asgn p.1 with
  | none => false
  | some b => !(b == literalSatisfyingBit p.2)

theorem isClauseKilled_eq_any (clause : List (Nat × Bool)) (asgn : Nat → Option Bool) :
    isClauseKilled clause asgn = clause.any (litKills asgn) := rfl

/-- For an AND-gate of input literals, the kill test of `simpleRestrictTerm`
agrees with `isClauseKilled` on the extracted pair-clause. -/
theorem andgate_kill_test_eq (asgn : Nat → Option Bool) (lits : List UnboundedFanInFormula)
    (hin : ∀ l ∈ lits, ∃ i b, l = .inputGate i b) :
    ((lits.map (simpleRestrictLiteral asgn)).any
        (fun l => match l with | .constant false _ => true | _ => false))
      = isClauseKilled (lits.filterMap (fun lit =>
          match lit with | .inputGate i b => some (i, b) | _ => none)) asgn := by
  rw [isClauseKilled_eq_any]
  induction lits with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨i, b, rfl⟩ := hin l List.mem_cons_self
    have ih' := ih (fun x hx => hin x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.any_cons, List.filterMap_cons]
    rw [ih']
    have hhead : (match simpleRestrictLiteral asgn (inputGate i b) with
          | .constant false _ => true | _ => false)
        = litKills asgn (i, b) := by
      simp only [simpleRestrictLiteral, litKills]
      cases hasgn : asgn i with
      | none => rfl
      | some bv => cases b <;> cases bv <;> rfl
    rw [hhead]

/-- `filterMap` of all-input literals to pairs preserves length. -/
theorem inputs_filterMap_length (lits : List UnboundedFanInFormula)
    (hin : ∀ l ∈ lits, ∃ i b, l = .inputGate i b) :
    (lits.filterMap (fun lit => match lit with
        | .inputGate i b => some (i, b) | _ => none)).length = lits.length := by
  induction lits with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨i, b, rfl⟩ := hin l List.mem_cons_self
    have ih' := ih (fun x hx => hin x (List.mem_cons_of_mem _ hx))
    simp only [List.filterMap_cons, List.length_cons]
    rw [ih']

theorem foldl_max_le {L : List Nat} {t a : Nat} (ha : a ≤ t)
    (h : ∀ x ∈ L, x ≤ t) : L.foldl max a ≤ t := by
  induction L generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih (max_le ha (h x List.mem_cons_self))
    intro y hy; exact h y (List.mem_cons_of_mem _ hy)

/-- **Bottom-fan-in reduction width bound.** If every original clause of `dnf`
that is wide (length `≥ t+1`) is killed by `asgn`, then the restricted DNF has
width `≤ t`. -/
theorem restrictDNF_width_le (t : Nat) (asgn : Nat → Option Bool)
    (dnf : UnboundedFanInFormula) (hdnf : isDNF dnf = true)
    (hkill : ∀ c ∈ dnfClauses dnf, t + 1 ≤ c.length → isClauseKilled c asgn = true) :
    dnfWidth (simpleRestrictDNF asgn dnf) ≤ t := by
  obtain ⟨gates, rfl⟩ := isDNF_eq_orGate dnf hdnf
  rw [simpleRestrictDNF, dnfWidth]
  apply foldl_max_le (Nat.zero_le t)
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨gate', hgate'_mem, rfl⟩ := hx
  rw [List.mem_filterMap] at hgate'_mem
  obtain ⟨gate, hgate_mem, hrestrict⟩ := hgate'_mem
  obtain ⟨lits, rfl, hlits_in⟩ := mem_gates_of_dnf gates hdnf gate hgate_mem
  set oc := lits.filterMap (fun lit => match lit with
      | .inputGate i b => some (i, b) | _ => none) with hoc
  have hoc_mem : oc ∈ dnfClauses (orGate gates) := by
    simp only [dnfClauses, List.mem_map]
    exact ⟨.andGate lits, hgate_mem, rfl⟩
  simp only [simpleRestrictTerm] at hrestrict
  split at hrestrict
  · exact absurd hrestrict (by simp)
  · rename_i hkilltest
    simp only [Option.some.injEq] at hrestrict
    have htest := andgate_kill_test_eq asgn lits hlits_in
    have hnotkilled : isClauseKilled oc asgn = false := by
      rw [hoc, ← htest]
      rw [List.any_eq_false]
      intro l hl
      rw [List.mem_map] at hl
      obtain ⟨lit, hlit, rfl⟩ := hl
      have hmapped := List.mem_map_of_mem
        (f := simpleRestrictLiteral asgn) hlit
      cases hrestricted : simpleRestrictLiteral asgn lit with
      | constant b label =>
        cases b with
        | false =>
          exfalso
          apply hkilltest
          rw [List.any_eq_true]
          exact ⟨_, hmapped, by simp [hrestricted]⟩
        | true => simp
      | inputGate => simp
      | notGate => simp
      | andGate => simp
      | orGate => simp
    have hoc_len : oc.length ≤ t := by
      by_contra hlt
      push Not at hlt
      have := hkill oc hoc_mem hlt
      rw [hnotkilled] at this
      exact absurd this (by simp)
    rw [← hrestrict]
    have hoc_eq_lits : oc.length = lits.length := inputs_filterMap_length lits hlits_in
    calc ((lits.map (simpleRestrictLiteral asgn)).filter
            (fun l => match l with | .constant _ _ => false | _ => true)).length
        ≤ (lits.map (simpleRestrictLiteral asgn)).length := List.length_filter_le _ _
      _ = lits.length := List.length_map ..
      _ = oc.length := hoc_eq_lits.symm
      _ ≤ t := hoc_len

end WidthBound

/-
## Round-0 bottom fan-in reduction (assembly over a list of bottom DNFs)
-/

section Round0
open Circuits.CnfDnf

/-- All clauses (across all bottom DNFs) that are wide (length ≥ t+1). -/
def wideClauses (t : Nat) (dnfs : List UnboundedFanInFormula) : List (List (Nat × Bool)) :=
  (dnfs.flatMap dnfClauses).filter (fun clause => decide (t + 1 ≤ clause.length))

theorem mem_wideClauses {t dnfs c} :
    c ∈ wideClauses t dnfs ↔ (∃ d ∈ dnfs, c ∈ dnfClauses d) ∧ t + 1 ≤ c.length := by
  unfold wideClauses
  rw [List.mem_filter, List.mem_flatMap]
  simp only [decide_eq_true_eq]

/-- Parameterized Round-0 bottom fan-in reduction for an arbitrary rational
survival bound `q`. -/
theorem exists_restrict_bottoms_width_le_of_bound (q : ℚ) (n s t : Nat)
    (dnfs : List UnboundedFanInFormula)
    (hsn : s ≤ n) (hn : 0 < n)
    (hdnf : ∀ d ∈ dnfs, isDNF d = true)
    (hnd : ∀ d ∈ dnfs, ∀ c ∈ dnfClauses d, (c.map Prod.fst).Nodup)
    (hvar : ∀ d ∈ dnfs, ∀ c ∈ dnfClauses d, ∀ p ∈ c, p.1 < n)
    (hq1 : q ≤ 1)
    (hσ : (1 + (s : ℚ) / n) / 2 ≤ q)
    (hcount : ((wideClauses t dnfs).length : ℚ) * q ^ (t + 1) < 1) :
    ∃ S ∈ (range n).powersetCard s, ∃ bits ∈ allBitLists (n - s),
      ∀ d ∈ dnfs,
        dnfWidth (simpleRestrictDNF (mkAssignment S bits) d) ≤ t := by
  obtain ⟨S, h_s, bits, hbits, hkill⟩ :=
    exists_kill_wide_clauses_of_bound q n s t (wideClauses t dnfs)
      hsn hn
      (fun c hc =>
        hnd _ (mem_wideClauses.1 hc).1.choose_spec.1 c
          (mem_wideClauses.1 hc).1.choose_spec.2)
      (fun c hc =>
        hvar _ (mem_wideClauses.1 hc).1.choose_spec.1 c
          (mem_wideClauses.1 hc).1.choose_spec.2)
      (fun c hc =>
        clauseVars_card_ge
          (hnd _ (mem_wideClauses.1 hc).1.choose_spec.1 c
            (mem_wideClauses.1 hc).1.choose_spec.2)
          (mem_wideClauses.1 hc).2)
      hq1 hσ hcount
  refine ⟨S, h_s, bits, hbits, ?_⟩
  intro d hd
  apply restrictDNF_width_le t (mkAssignment S bits) d (hdnf d hd)
  intro c hc hwide
  exact hkill c (mem_wideClauses.2 ⟨⟨d, hd, hc⟩, hwide⟩)

end Round0

end Circuits.HastadParity.FaninReduction
