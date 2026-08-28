import Parity.Leveling.Invariants

/-!
# constant-free formulas and constant absorption

This module contains the dependency-light core of constant normalization.
It lives below the bottom-layer extraction and switching-lemma development so
the general formula-normalization pipeline can remove `constant` constructors
before those phases begin.
-/

namespace Circuits.HastadParity
open Circuits
open UnboundedFanInFormula

/-- A UFI formula is **constant-free** when it contains no `constant` leaf.

This is a syntactic invariant, not the assertion that the computed Boolean
function is nonconstant. -/
def IsConstantFree : UnboundedFanInFormula → Prop
  | .inputGate _ _ => True
  | .constant _ _ => False
  | .notGate g => IsConstantFree g
  | .andGate gates => ∀ g ∈ gates, IsConstantFree g
  | .orGate gates => ∀ g ∈ gates, IsConstantFree g

/-- Syntactic test for the canonical true constant `andGate []`. -/
def isCanonicalTrue : UnboundedFanInFormula → Bool
  | .andGate [] => true
  | _ => false

/-- Syntactic test for the canonical false constant `orGate []`. -/
def isCanonicalFalse : UnboundedFanInFormula → Bool
  | .orGate [] => true
  | _ => false

mutual

/-- Replace `constant` leaves by canonical empty gates and absorb canonical
constants through AND/OR gates. -/
def simplifyConstants : UnboundedFanInFormula → UnboundedFanInFormula
  | .inputGate x b => .inputGate x b
  | .constant b _ =>
      match b with
      | true => .andGate []
      | false => .orGate []
  | .notGate g => .notGate (simplifyConstants g)
  | .andGate gs =>
      let cs := simplifyConstantsList gs
      if cs.any isCanonicalFalse then .orGate []
      else .andGate (cs.filter (fun g => !isCanonicalTrue g))
  | .orGate gs =>
      let cs := simplifyConstantsList gs
      if cs.any isCanonicalTrue then .andGate []
      else .orGate (cs.filter (fun g => !isCanonicalFalse g))

def simplifyConstantsList : List UnboundedFanInFormula → List UnboundedFanInFormula
  | [] => []
  | g :: gs => simplifyConstants g :: simplifyConstantsList gs

end

end Circuits.HastadParity
