import ACC.Formula.Probabilistic.Basic

namespace Circuits.ACC.ProbabilisticACCFormula

/-! ## Structural properties of probabilistic ACC formulas -/

/-- A probabilistic ACC formula has order `r` when every AND gate occurring
anywhere in its syntax tree has at most `r` children. -/
def IsOfOrder {p : Nat} : ProbabilisticACCFormula p → Nat → Prop
  | .input _ _, _ => True
  | .constant _ _, _ => True
  | .notGate formula, r => IsOfOrder formula r
  | .andGate formulas, r =>
      formulas.length ≤ r ∧ ∀ formula ∈ formulas, IsOfOrder formula r
  | .orGate formulas, r => ∀ formula ∈ formulas, IsOfOrder formula r
  | .modGate formulas, r => ∀ formula ∈ formulas, IsOfOrder formula r

/-- Every internal node is either an AND gate or a modulo gate. -/
def HasOnlyAndModGates {p : Nat} : ProbabilisticACCFormula p → Prop
  | .input _ _ => True
  | .constant _ _ => True
  | .notGate _ => False
  | .andGate formulas => ∀ formula ∈ formulas, HasOnlyAndModGates formula
  | .orGate _ => False
  | .modGate formulas => ∀ formula ∈ formulas, HasOnlyAndModGates formula

/-- Increasing the allowed fan-in preserves the order predicate. -/
theorem isOfOrder_mono {p : Nat} (formula : ProbabilisticACCFormula p)
    {left right : Nat} (h_order : IsOfOrder formula left)
    (h_le : left ≤ right) : IsOfOrder formula right := by
  match formula with
  | .input .. => simp [IsOfOrder]
  | .constant .. => simp [IsOfOrder]
  | .notGate child =>
      simpa only [ProbabilisticACCFormula.IsOfOrder] using
        isOfOrder_mono child
          (by simpa only [ProbabilisticACCFormula.IsOfOrder] using h_order) h_le
  | .andGate children =>
      simp only [IsOfOrder] at h_order ⊢
      exact ⟨h_order.1.trans h_le, fun child h_child =>
        isOfOrder_mono child (h_order.2 child h_child) h_le⟩
  | .orGate children =>
      simp only [IsOfOrder] at h_order ⊢
      intro child h_child
      exact isOfOrder_mono child (h_order child h_child) h_le
  | .modGate children =>
      simp only [IsOfOrder] at h_order ⊢
      intro child h_child
      exact isOfOrder_mono child (h_order child h_child) h_le

end Circuits.ACC.ProbabilisticACCFormula
