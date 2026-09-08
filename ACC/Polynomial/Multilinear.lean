import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Circuits.ACC

/-! ## Expanded multilinear polynomials over `ZMod p`

A monomial is represented by a `Finset (Fin n)`, so every variable occurs
with exponent at most one. Repeated monomials are combined by evaluation.
-/

/-- An expanded multilinear polynomial over `ZMod p` in `n` variables. -/
structure MultilinearPolynomial (p n : Nat) where
  terms : List (ZMod p × Finset (Fin n))

namespace MultilinearPolynomial

/-- Evaluation on a Boolean assignment. -/
def eval {p n : Nat} (q : MultilinearPolynomial p n)
    (x : Fin n → Bool) : ZMod p :=
  (q.terms.map fun term =>
    term.1 * ∏ i ∈ term.2, ((x i).toNat : ZMod p)).sum

/-- All monomials occurring in `q` have degree at most `d`. -/
def DegreeAtMost {p n : Nat} (q : MultilinearPolynomial p n)
    (d : Nat) : Prop :=
  ∀ term ∈ q.terms, term.2.card ≤ d

def zero (p n : Nat) : MultilinearPolynomial p n := ⟨[]⟩

def one (p n : Nat) : MultilinearPolynomial p n :=
  ⟨[(1, ∅)]⟩

def X (p : Nat) {n : Nat} (i : Fin n) :
    MultilinearPolynomial p n :=
  ⟨[(1, {i})]⟩

def add {p n : Nat} (q r : MultilinearPolynomial p n) :
    MultilinearPolynomial p n :=
  ⟨q.terms ++ r.terms⟩

def neg {p n : Nat} (q : MultilinearPolynomial p n) :
    MultilinearPolynomial p n :=
  ⟨q.terms.map fun term => (-term.1, term.2)⟩

/-- Boolean multiplication of expanded multilinear polynomials.  Taking the
union of supports implements the Boolean identity `X_i^2 = X_i`. -/
def mul {p n : Nat} (q r : MultilinearPolynomial p n) :
    MultilinearPolynomial p n :=
  ⟨q.terms.flatMap fun left =>
    r.terms.map fun right => (left.1 * right.1, left.2 ∪ right.2)⟩

def pow {p n : Nat} (q : MultilinearPolynomial p n) :
    Nat → MultilinearPolynomial p n
  | 0 => one p n
  | k + 1 => mul q (pow q k)

private theorem boolCast_mul_self {p : Nat} (b : Bool) :
    ((b.toNat : ZMod p) * (b.toNat : ZMod p)) = (b.toNat : ZMod p) := by
  cases b <;> simp

private theorem monomialEval_union {p n : Nat} (x : Fin n → Bool)
    (s t : Finset (Fin n)) :
    (∏ i ∈ s ∪ t, ((x i).toNat : ZMod p)) =
      (∏ i ∈ s, ((x i).toNat : ZMod p)) *
        ∏ i ∈ t, ((x i).toNat : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hat : a ∈ t
      · cases hxa : x a with
        | false =>
            have hz : (∏ i ∈ t, ((x i).toNat : ZMod p)) = 0 := by
              apply Finset.prod_eq_zero hat
              simp [hxa]
            simp [hxa, hat, ha, ih, hz]
        | true => simp [hxa, hat, ha, ih]
      · simp only [Finset.insert_union, Finset.prod_insert, ha,
          not_false_eq_true, hat, Finset.mem_union, or_false, ih]
        exact (mul_assoc _ _ _).symm

@[simp] theorem eval_zero {p n : Nat} (x : Fin n → Bool) :
    eval (zero p n) x = 0 := by
  simp [eval, zero]

@[simp] theorem eval_one {p n : Nat} (x : Fin n → Bool) :
    eval (one p n) x = 1 := by
  simp [eval, one]

@[simp] theorem eval_variable {p n : Nat} (i : Fin n)
    (x : Fin n → Bool) :
    eval (X p i) x = (x i).toNat := by
  simp [eval, X]

@[simp] theorem eval_add {p n : Nat} (q r : MultilinearPolynomial p n)
    (x : Fin n → Bool) :
    eval (add q r) x = eval q x + eval r x := by
  simp [eval, add]

@[simp] theorem eval_neg {p n : Nat} (q : MultilinearPolynomial p n)
    (x : Fin n → Bool) :
    eval (neg q) x = -eval q x := by
  rcases q with ⟨terms⟩
  induction terms with
  | nil => simp [eval, neg]
  | cons term terms ih =>
      simp only [eval, neg, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
      rw [ih]
      simp [add_comm]

@[simp] theorem eval_mul {p n : Nat} (q r : MultilinearPolynomial p n)
    (x : Fin n → Bool) :
    eval (mul q r) x = eval q x * eval r x := by
  classical
  rcases q with ⟨q⟩
  rcases r with ⟨r⟩
  induction q with
  | nil => simp [eval, mul]
  | cons left q ih =>
      simp only [mul, eval] at ih ⊢
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_map, List.map_cons, List.sum_cons]
      rw [ih, add_mul]
      congr 1
      calc
        (List.map ((fun term =>
          term.1 * ∏ i ∈ term.2, ((x i).toNat : ZMod p)) ∘
            fun right =>
              (left.1 * right.1, left.2 ∪ right.2)) r).sum =
            (List.map (fun right =>
              left.1 * right.1 *
                ((∏ i ∈ left.2, ((x i).toNat : ZMod p)) *
                  ∏ i ∈ right.2, ((x i).toNat : ZMod p))) r).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro right hright
              simp only [Function.comp_apply]
              rw [monomialEval_union]
        _ =
            left.1 * (∏ i ∈ left.2, ((x i).toNat : ZMod p)) *
              (List.map (fun right =>
                right.1 * ∏ i ∈ right.2,
                  ((x i).toNat : ZMod p)) r).sum := by
              rw [← List.sum_map_mul_left]
              apply congrArg List.sum
              apply List.map_congr_left
              intro right hright
              ring
        _ = _ := rfl

@[simp] theorem eval_pow {p n : Nat} (q : MultilinearPolynomial p n)
    (k : Nat) (x : Fin n → Bool) :
    eval (pow q k) x = eval q x ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ']

theorem degreeAtMost_zero {p n d : Nat} :
    DegreeAtMost (zero p n) d := by
  simp [DegreeAtMost, zero]

theorem degreeAtMost_one {p n d : Nat} :
    DegreeAtMost (one p n) d := by
  simp [DegreeAtMost, one]

theorem degreeAtMost_variable {p n : Nat} (i : Fin n) :
    DegreeAtMost (X p i) 1 := by
  simp [DegreeAtMost, X]

theorem degreeAtMost_add {p n d : Nat} {q r : MultilinearPolynomial p n}
    (hq : DegreeAtMost q d) (hr : DegreeAtMost r d) :
    DegreeAtMost (add q r) d := by
  intro term hterm
  simp only [add, List.mem_append] at hterm
  exact hterm.elim (hq term) (hr term)

theorem degreeAtMost_neg {p n d : Nat} {q : MultilinearPolynomial p n}
    (hq : DegreeAtMost q d) : DegreeAtMost (neg q) d := by
  intro term hterm
  simp only [neg, List.mem_map] at hterm
  obtain ⟨source, hsource, rfl⟩ := hterm
  exact hq source hsource

theorem degreeAtMost_mono {p n : Nat} {q : MultilinearPolynomial p n}
    {a b : Nat} (hq : DegreeAtMost q a) (hab : a ≤ b) :
    DegreeAtMost q b := by
  intro term hterm
  exact (hq term hterm).trans hab

theorem degreeAtMost_mul {p n a b : Nat}
    {q r : MultilinearPolynomial p n}
    (hq : DegreeAtMost q a) (hr : DegreeAtMost r b) :
    DegreeAtMost (mul q r) (a + b) := by
  intro term hterm
  simp only [mul, List.mem_flatMap, List.mem_map] at hterm
  obtain ⟨left, hleft, right, hright, rfl⟩ := hterm
  exact (Finset.card_union_le left.2 right.2).trans
    (Nat.add_le_add (hq left hleft) (hr right hright))

theorem degreeAtMost_pow {p n d : Nat} {q : MultilinearPolynomial p n}
    (hq : DegreeAtMost q d) (k : Nat) :
    DegreeAtMost (pow q k) (k * d) := by
  induction k with
  | zero => simpa [pow] using (degreeAtMost_one (p := p) (n := n) (d := 0))
  | succ k ih =>
      simpa [pow, Nat.succ_mul, Nat.add_comm] using degreeAtMost_mul hq ih

end MultilinearPolynomial

end Circuits.ACC
