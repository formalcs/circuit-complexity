import Formulas.CnfDnf.RandomRestriction
import Formulas.CnfDnf.SwitchingLemmaBasic
import Formulas.CnfDnf.SwitchingLemmaCanonicalDT

namespace Circuits.CnfDnf.Restrictions
open Circuits.CnfDnf.Families
open DecisionTrees

def randomRestrictionToMap
    (n : Nat)
    (σ : OpenUnitIntervalQ)
    (ρ : AssignedRandomRestriction σ n) : Nat → Option Bool :=
  mkAssignment ρ.starAssignment.val.val ρ.varAssignments

/-- "Bad restriction" predicate for the encoder: the full-query canonical
    DT of the restricted DNF has depth strictly greater than `d`. -/
def isBadRestriction
    (d n : Nat)
    (σ : OpenUnitIntervalQ)
    (f : UnboundedFanInProperDNF n)
    (ρ : AssignedRandomRestriction σ n)
  : Bool :=
  decisionTreeDepth
    (properDNFCanonicalDecisionTree f ρ) > d

/-- The total number of assigned random restrictions with parameters (σ, n):
    C(n, s) · 2^(n - s), where s = ⌈σ · n⌉. -/
def totalRestrictionCount (n : Nat) (σ : OpenUnitIntervalQ) : ℚ :=
  let s := Nat.ceil (σ.val * (n : ℚ))
  ↑(Nat.choose n s * 2 ^ (n - s))

/-- Enumerate all assigned random restrictions with live-set size `ceil (σ * n)`.

    The outer loop chooses the live variables `S`; the inner loop chooses the
    dead-variable bit list.  Using attached bit lists gives the length proof
    needed to build `AssignedRandomRestriction` directly. -/
def generateAllRestrictions (n : Nat) (σ : OpenUnitIntervalQ) :
    Multiset (AssignedRandomRestriction σ n) :=
  let s := Nat.ceil (σ.val * ↑n)
  let subsets := (Finset.range n).powersetCard s
  let subsetsWithMembership := subsets.attach
  (subsetsWithMembership.val.bind fun ⟨S, h_smem⟩ =>
    let h_s := Finset.mem_powersetCard.mp h_smem
    let bitLists := allBitLists (n - s)
    let bitListsWithMembership := bitLists.attach
    (bitListsWithMembership.map fun bitsWithMembership =>
      let bits := bitsWithMembership.val
      {
        starAssignment := ⟨⟨S, h_s.1⟩, h_s.2⟩
        varAssignments := bits
        non_starred_vars_fully_assigned := by
          have h : bits.length = n - s :=
            by
              apply allBitLists_mem_length
              apply bitsWithMembership.property
          rw [h, h_s.2]
          have hsn : s ≤ n := ceil_sigma_n_le σ n
          apply Nat.add_sub_of_le hsn
      } : List (AssignedRandomRestriction σ n)))

def badRestrictionCount
    (n d : Nat) (f : UnboundedFanInProperDNF n) (σ : OpenUnitIntervalQ) : ℚ :=
  ((generateAllRestrictions n σ).countP fun ρ =>
    isBadRestriction d n σ f ρ)

end Circuits.CnfDnf.Restrictions
