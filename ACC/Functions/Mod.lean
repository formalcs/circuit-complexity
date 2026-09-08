import ACC.Formula.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi

namespace Circuits.ACC

/-! ## Boolean modulo functions

The convention agrees with `ACCFormula.modGate`: the function is true when
the Hamming weight of the input is congruent to zero. -/

/-- `MOD_r` on `n` Boolean variables. -/
def modFunction (r : ℕ) {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide ((∑ j, (x j).toNat) % r = 0)

/-- `MOD_r` on a list of Boolean inputs. -/
def modFunctionList (r : ℕ) (inputs : List Bool) : Bool :=
  decide ((inputs.map Bool.toNat).sum % r = 0)

private theorem sum_ofFn_nat {n : ℕ} (f : Fin n → ℕ) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.ofFn_succ, Fin.sum_univ_succ, ih]

@[simp] theorem modFunctionList_ofFn (r : ℕ) {n : ℕ}
    (x : Fin n → Bool) :
    modFunctionList r (List.ofFn x) = modFunction r x := by
  simp [modFunctionList, modFunction, sum_ofFn_nat]

end Circuits.ACC
