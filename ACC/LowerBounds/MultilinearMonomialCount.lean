import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sups

/-!
# A bound for low-degree multilinear monomials

A multilinear monomial in `n` variables is represented by the `Finset (Fin n)` of
variables occurring in it; its degree is the cardinality of that finset.
-/

open scoped BigOperators Real FinsetFamily

namespace MultilinearMonomialCount

noncomputable section

/-- Multilinear monomials whose degree is at most `n / 2 + √n / 2` (in `ℝ`). -/
def lowDegreeMonomials (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun s ↦
    (s.card : ℝ) ≤ (n : ℝ) / 2 + Real.sqrt n / 2

private lemma even_middle_choose_bound (m : ℕ) (hm : 0 < m) :
    Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ) <
      (799 / 1000 : ℝ) * (2 : ℝ) ^ (2 * m) := by
  let c : ℝ := Nat.choose (2 * m) m
  let q : ℝ := (2 : ℝ) ^ (2 * m)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
  have hq : 0 < q := by positivity
  have hfacNat := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
  have hfac : ((Nat.factorial (2 * m) : ℕ) : ℝ) =
      c * (Nat.factorial m : ℝ) ^ 2 := by
    have hfacCast :
        ((Nat.choose (2 * m) m * Nat.factorial m *
          Nat.factorial (2 * m - m) : ℕ) : ℝ) =
          ((Nat.factorial (2 * m) : ℕ) : ℝ) := by exact_mod_cast hfacNat
    push_cast at hfacCast
    simpa [c, show 2 * m - m = m by omega, pow_two, mul_assoc] using hfacCast.symm
  have hW : Real.Wallis.W m = q ^ 2 / (c ^ 2 * (2 * m + 1)) := by
    rw [Real.Wallis.W_eq_factorial_ratio, hfac]
    dsimp [q]
    field_simp
    ring
  have hWallis := Real.Wallis.le_W m
  rw [hW] at hWallis
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hden : 0 < c ^ 2 * ((2 * m : ℝ) + 1) := by positivity
  have hcross :
      c ^ 2 * ((2 * m : ℝ) + 1) ^ 2 * Real.pi ≤
        2 * q ^ 2 * ((2 * m : ℝ) + 2) := by
    rw [le_div_iff₀ hden] at hWallis
    have hmden : 0 < 2 * ((2 * m : ℝ) + 2) := by positivity
    have hrepackEq :
        c ^ 2 * ((2 * m : ℝ) + 1) ^ 2 * Real.pi /
            (2 * ((2 * m : ℝ) + 2)) =
          ((2 * m : ℝ) + 1) / ((2 * m : ℝ) + 2) * (Real.pi / 2) *
            (c ^ 2 * ((2 * m : ℝ) + 1)) := by
      field_simp
    have hrepack :
        c ^ 2 * ((2 * m : ℝ) + 1) ^ 2 * Real.pi /
            (2 * ((2 * m : ℝ) + 2)) ≤ q ^ 2 := by
      rw [hrepackEq]
      exact hWallis
    simpa [mul_assoc, mul_left_comm, mul_comm] using (div_le_iff₀ hmden).mp hrepack
  have hcore : c ^ 2 * (2 * m : ℝ) * Real.pi ≤ 2 * q ^ 2 := by
    have hsquare :
        (2 * m : ℝ) * ((2 * m : ℝ) + 2) ≤ ((2 * m : ℝ) + 1) ^ 2 := by
      nlinarith
    have hmul :
        c ^ 2 * (2 * m : ℝ) * ((2 * m : ℝ) + 2) * Real.pi ≤
          c ^ 2 * ((2 * m : ℝ) + 1) ^ 2 * Real.pi := by
      calc
        _ = (c ^ 2 * Real.pi) *
              ((2 * m : ℝ) * ((2 * m : ℝ) + 2)) := by ring
        _ ≤ (c ^ 2 * Real.pi) * ((2 * m : ℝ) + 1) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hsquare (mul_nonneg (sq_nonneg c) Real.pi_pos.le)
        _ = _ := by ring
    nlinarith
  have hrat : c ^ 2 * (2 * m : ℝ) < (799 / 1000 : ℝ) ^ 2 * q ^ 2 := by
    have hnum : (2 : ℝ) < 3.14 * (799 / 1000 : ℝ) ^ 2 := by norm_num
    have hnumq : 2 * q ^ 2 < 3.14 * (799 / 1000 : ℝ) ^ 2 * q ^ 2 := by
      nlinarith [sq_pos_of_pos hq]
    nlinarith
  have hsqrt : Real.sqrt (2 * m : ℝ) ^ 2 = (2 * m : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hleft : 0 ≤ Real.sqrt (2 * m : ℝ) * c := by positivity
  have hright : 0 ≤ (799 / 1000 : ℝ) * q := by positivity
  dsimp [c, q] at *
  nlinarith [sq_nonneg
    (Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ) -
      (799 / 1000 : ℝ) * (2 : ℝ) ^ (2 * m))]

private lemma middle_choose_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt n * (Nat.choose n (n / 2) : ℝ) <
      (799 / 1000 : ℝ) * (2 : ℝ) ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa [show 2 * m / 2 = m by omega] using even_middle_choose_bound m (by omega)
  · have hm : 0 < m := by omega
    have heven := even_middle_choose_bound m hm
    let c : ℝ := Nat.choose (2 * m) m
    let d : ℝ := Nat.choose (2 * m + 1) m
    let q : ℝ := (2 : ℝ) ^ (2 * m)
    have hcdNat := Nat.choose_mul_succ_eq (2 * m) m
    have hcd : c * (2 * m + 1 : ℝ) = d * (m + 1 : ℝ) := by
      dsimp [c, d]
      norm_cast
      simpa [show 2 * m + 1 - m = m + 1 by omega] using hcdNat
    have hmR : 0 < (m : ℝ) := by positivity
    have hc : 0 < c := by
      dsimp [c]
      exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
    have hd : 0 < d := by
      dsimp [d]
      exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m + 1)
    have hq : 0 < q := by positivity
    have hfactor : (2 * m + 1 : ℝ) ^ 3 ≤
        8 * (m : ℝ) * (m + 1) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm]
    have hsqrtEven : Real.sqrt (2 * m : ℝ) ^ 2 = (2 * m : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrtOdd : Real.sqrt (2 * m + 1 : ℝ) ^ 2 = (2 * m + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    dsimp [c, d, q] at *
    simp only [show (2 * m + 1) / 2 = m by omega]
    push_cast
    rw [pow_succ]
    have hnonnegEven :
        0 ≤ Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ) := by positivity
    have hnonnegOdd :
        0 ≤ Real.sqrt (2 * m + 1 : ℝ) * (Nat.choose (2 * m + 1) m : ℝ) := by positivity
    let E : ℝ := Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ)
    let O : ℝ := Real.sqrt (2 * m + 1 : ℝ) * (Nat.choose (2 * m + 1) m : ℝ)
    have hscale : 0 < (m + 1 : ℝ) ^ 2 := by positivity
    have hOE_sq : O ^ 2 ≤ (2 * E) ^ 2 := by
      refine le_of_mul_le_mul_right ?_ hscale
      calc
        O ^ 2 * (m + 1 : ℝ) ^ 2 =
            (Nat.choose (2 * m) m : ℝ) ^ 2 * (2 * m + 1 : ℝ) ^ 3 := by
          dsimp [O]
          rw [mul_pow, hsqrtOdd]
          calc
            _ = (2 * m + 1 : ℝ) *
                ((Nat.choose (2 * m + 1) m : ℝ) * (m + 1 : ℝ)) ^ 2 := by ring
            _ = (2 * m + 1 : ℝ) *
                ((Nat.choose (2 * m) m : ℝ) * (2 * m + 1 : ℝ)) ^ 2 := by rw [← hcd]
            _ = _ := by ring
        _ ≤ (Nat.choose (2 * m) m : ℝ) ^ 2 *
            (8 * (m : ℝ) * (m + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
        _ = (2 * E) ^ 2 * (m + 1 : ℝ) ^ 2 := by
          dsimp [E]
          rw [show (2 * (Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ))) ^ 2 =
              4 * (Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ)) ^ 2 by ring,
            show (Real.sqrt (2 * m : ℝ) * (Nat.choose (2 * m) m : ℝ)) ^ 2 =
              Real.sqrt (2 * m : ℝ) ^ 2 * (Nat.choose (2 * m) m : ℝ) ^ 2 by ring,
            hsqrtEven]
          ring
    have hOE : O ≤ 2 * E := by
      dsimp [O, E] at hOE_sq ⊢
      nlinarith
    dsimp [O, E] at hOE
    nlinarith

/-- For all sufficiently large `n`, at most nine tenths of the multilinear monomials
have degree at most `n / 2 + √n / 2`.

The explicit threshold `9,000,000` is chosen only to keep the numerical endgame simple;
the statement of interest is the existential "sufficiently large" conclusion below. -/
theorem lowDegreeMonomials_card_le (n : ℕ) (hn : 9_000_000 ≤ n) :
    ((lowDegreeMonomials n).card : ℝ) ≤ (9 / 10 : ℝ) * (2 : ℝ) ^ n := by
  classical
  let A : Finset (Finset (Fin n)) := lowDegreeMonomials n
  let B : Finset (Finset (Fin n)) := Aᶜˢ
  let I : Finset (Finset (Fin n)) := A ∩ B
  let r : ℕ := Nat.ceil (Real.sqrt n)
  let D : Finset ℕ := Finset.Icc ((n - r) / 2) ((n + r) / 2)
  -- Basic numerical facts about `n`, `√n`, and its ceiling.
  have hn2 : 2 ≤ n := by omega
  have hsqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hrceil : Real.sqrt n ≤ (r : ℝ) := by
    exact Nat.le_ceil (Real.sqrt n)
  have hrlt : (r : ℝ) < Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one hsqrt_nonneg
  -- Complementation pairs the low-degree family with an equinumerous family.
  have hBcard : B.card = A.card := by simp [B]
  have hunion : A ∪ B = Finset.univ := by
    ext s
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hs : s ∈ A
    · exact Or.inl hs
    · right
      rw [show B = Aᶜˢ by rfl, Finset.mem_compls]
      have hslt :
          (n : ℝ) / 2 + Real.sqrt n / 2 < (s.card : ℝ) := by
        simpa [A, lowDegreeMonomials] using hs
      have haddNat : s.card + sᶜ.card = n := by
        simpa only [Fintype.card_fin] using Finset.card_add_card_compl s
      have hadd : (s.card : ℝ) + (sᶜ.card : ℝ) = n := by exact_mod_cast haddNat
      simp only [A, lowDegreeMonomials, Finset.mem_filter, Finset.mem_univ, true_and]
      nlinarith
  -- Their intersection is supported on a short interval of degree layers.
  have hmaps : ∀ s ∈ I, s.card ∈ D := by
    intro s hsI
    have hsA : s ∈ A := (Finset.mem_inter.mp hsI).1
    have hsB : s ∈ B := (Finset.mem_inter.mp hsI).2
    have hscA : sᶜ ∈ A := by
      simpa [B] using hsB
    have hsdeg :
        (s.card : ℝ) ≤ (n : ℝ) / 2 + Real.sqrt n / 2 := by
      simpa [A, lowDegreeMonomials] using hsA
    have hscdeg :
        (sᶜ.card : ℝ) ≤ (n : ℝ) / 2 + Real.sqrt n / 2 := by
      simpa [A, lowDegreeMonomials] using hscA
    have haddNat : s.card + sᶜ.card = n := by
      simpa only [Fintype.card_fin] using Finset.card_add_card_compl s
    have hadd : (s.card : ℝ) + (sᶜ.card : ℝ) = n := by exact_mod_cast haddNat
    have huR : (2 * s.card : ℕ) ≤ n + r := by
      exact_mod_cast (show (2 * s.card : ℝ) ≤ (n + r : ℕ) by
        push_cast
        nlinarith)
    have hlR : n ≤ 2 * s.card + r := by
      exact_mod_cast (show (n : ℝ) ≤ (2 * s.card + r : ℕ) by
        push_cast
        nlinarith)
    simp only [D, Finset.mem_Icc]
    constructor <;> omega
  -- The interval has at most `⌈√n⌉ + 2` integer points.
  have hDcard : D.card ≤ r + 2 := by
    simp only [D, Nat.card_Icc]
    omega
  -- Every individual degree layer is bounded by the middle binomial coefficient.
  have hfiber : ∀ k ∈ D, {s ∈ I | s.card = k}.card ≤ Nat.choose n (n / 2) := by
    intro k _hk
    calc
      {s ∈ I | s.card = k}.card ≤
          ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter] at hs
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ s, hs.2⟩
      _ = Nat.choose n k := by simp
      _ ≤ Nat.choose n (n / 2) := Nat.choose_le_middle k n
  -- Sum the layer bounds over the short interval.
  have hIcardNat : I.card ≤ Nat.choose n (n / 2) * (r + 2) := by
    calc
      I.card ≤ Nat.choose n (n / 2) * D.card :=
        Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber
      _ ≤ Nat.choose n (n / 2) * (r + 2) := Nat.mul_le_mul_left _ hDcard
  -- Cast the resulting cardinality estimate to `ℝ`.
  have hIcard : (I.card : ℝ) ≤
      (Nat.choose n (n / 2) : ℝ) * (Real.sqrt n + 3) := by
    have hcast : (I.card : ℝ) ≤
        (Nat.choose n (n / 2) : ℝ) * (r + 2 : ℝ) := by exact_mod_cast hIcardNat
    have hwindow : (r + 2 : ℝ) ≤ Real.sqrt n + 3 := by
      linarith
    exact hcast.trans (mul_le_mul_of_nonneg_left hwindow (by positivity))
  -- The explicit threshold makes the small numerical slack below `4/5` sufficient.
  have hsqrt3000 : (3000 : ℝ) ≤ Real.sqrt n := by
    have hnR : (9_000_000 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hmiddle := middle_choose_bound n hn2
  have hchoose_nonneg : (0 : ℝ) ≤ Nat.choose n (n / 2) := by positivity
  have hscale :
      (Nat.choose n (n / 2) : ℝ) * (Real.sqrt n + 3) ≤
        (1001 / 1000 : ℝ) *
          (Real.sqrt n * (Nat.choose n (n / 2) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt3000 hchoose_nonneg
    nlinarith
  have hIbound : (I.card : ℝ) ≤ (4 / 5 : ℝ) * (2 : ℝ) ^ n := by
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    calc
      (I.card : ℝ) ≤ (Nat.choose n (n / 2) : ℝ) * (Real.sqrt n + 3) := hIcard
      _ ≤ (1001 / 1000 : ℝ) *
          (Real.sqrt n * (Nat.choose n (n / 2) : ℝ)) := hscale
      _ ≤ (1001 / 1000 : ℝ) * ((799 / 1000 : ℝ) * (2 : ℝ) ^ n) := by
        exact (by gcongr :
          (1001 / 1000 : ℝ) *
              (Real.sqrt n * (Nat.choose n (n / 2) : ℝ)) <
            (1001 / 1000 : ℝ) * ((799 / 1000 : ℝ) * (2 : ℝ) ^ n)).le
      _ ≤ (4 / 5 : ℝ) * (2 : ℝ) ^ n := by
        nlinarith
  -- Inclusion-exclusion for `A` and its complement image finishes the argument.
  have hcardIdentityNat : 2 * A.card = 2 ^ n + I.card := by
    have hcard := Finset.card_union_add_card_inter A B
    rw [hunion, Finset.card_univ, Fintype.card_finset, hBcard] at hcard
    simpa [I, two_mul, add_comm, add_left_comm, add_assoc] using hcard.symm
  have hcardIdentity : (2 : ℝ) * A.card = (2 : ℝ) ^ n + I.card := by
    exact_mod_cast hcardIdentityNat
  change (A.card : ℝ) ≤ (9 / 10 : ℝ) * (2 : ℝ) ^ n
  nlinarith

/-- The requested "for sufficiently large `n`" formulation. -/
theorem eventually_lowDegreeMonomials_card_le :
    ∃ N : ℕ, ∀ n ≥ N,
      ((lowDegreeMonomials n).card : ℝ) ≤ (9 / 10 : ℝ) * (2 : ℝ) ^ n := by
  exact ⟨9_000_000, fun n hn ↦ lowDegreeMonomials_card_le n hn⟩

end

end MultilinearMonomialCount
