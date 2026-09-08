import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Circuits.ACC

/-!
# Roots of unity in finite fields

Euler's theorem gives `r ∣ p ^ φ(r) - 1` when `r` and `p` are coprime.  Since
the unit group of `GF(p ^ φ(r))` is cyclic of order `p ^ φ(r) - 1`, it has an
element of order exactly `r`.
-/

/-- If `p` is prime and `r` is coprime to `p`, then some finite extension of
`GF(p)` contains a primitive `r`-th root of unity. -/
theorem exists_primitiveRoot_galoisField
    (p r : ℕ) (hp : p.Prime) (hr : r ≠ 1) (hcop : r.Coprime p) :
    ∃ k : ℕ, 0 < k ∧
      ∃ ω : @GaloisField p ⟨hp⟩ k, IsPrimitiveRoot ω r := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    simp only [Nat.coprime_zero_left] at hcop
    exact hp.ne_one hcop
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  let k := Nat.totient r
  have hk : 0 < k := Nat.totient_pos.mpr hrpos
  have hmod : p ^ k ≡ 1 [MOD r] := by
    simpa only [k] using Nat.ModEq.pow_totient hcop.symm
  have hone_le : 1 ≤ p ^ k := one_le_pow₀ hp.pos
  have hr_dvd : r ∣ p ^ k - 1 :=
    (Nat.modEq_iff_dvd' hone_le).mp hmod.symm
  let F := GaloisField p k
  let _ : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p ^ k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p k hk.ne'
  have hr_dvd_units : r ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units, hcard]
    exact hr_dvd
  have hcard_orders :
      (Finset.univ.filter fun u : Fˣ => orderOf u = r).card = Nat.totient r :=
    IsCyclic.card_orderOf_eq_totient hr_dvd_units
  have hnonempty :
      (Finset.univ.filter fun u : Fˣ => orderOf u = r).Nonempty := by
    rw [← Finset.card_pos, hcard_orders]
    exact Nat.totient_pos.mpr hrpos
  obtain ⟨u, hu⟩ := hnonempty
  have hu_order : orderOf u = r := by simpa using hu
  refine ⟨k, hk, (u : F), ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
  exact hu_order

/-- The requested consequence: some `GF(p^k)` contains an `r`-th root of unity. -/
theorem exists_rootOfUnity_galoisField
    (p r : ℕ) (hp : p.Prime) (hr : r ≠ 1) (hcop : r.Coprime p) :
    ∃ k : ℕ, 0 < k ∧ ∃ ω : @GaloisField p ⟨hp⟩ k, ω ^ r = 1 := by
  obtain ⟨k, hk, ω, hω⟩ := exists_primitiveRoot_galoisField p r hp hr hcop
  exact ⟨k, hk, ω, hω.pow_eq_one⟩

/-- In fact, the root can be chosen nontrivial. -/
theorem exists_nontrivial_rootOfUnity_galoisField
    (p r : ℕ) (hp : p.Prime) (hr : r ≠ 1) (hcop : r.Coprime p) :
    ∃ k : ℕ, 0 < k ∧
      ∃ ω : @GaloisField p ⟨hp⟩ k, ω ≠ 1 ∧ ω ^ r = 1 := by
  obtain ⟨k, hk, ω, hω⟩ := exists_primitiveRoot_galoisField p r hp hr hcop
  have hr_gt_one : 1 < r := by
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      simp only [Nat.coprime_zero_left] at hcop
      exact hp.ne_one hcop
    omega
  exact ⟨k, hk, ω, hω.ne_one hr_gt_one, hω.pow_eq_one⟩

end Circuits.ACC
