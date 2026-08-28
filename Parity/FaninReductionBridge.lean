/-
# Fan-in reduction → project restriction bridge

This density-neutral module packages an abstract Round-0 restriction `(S,
bits)` as the project restriction type consumed by the switching framework.
Concrete liveness densities and their arithmetic calibrations live in
`Parity.FaninReduction.OneFifth`, `.OneThird`, and `.TwoFifths`.
-/
import Parity.FaninReduction
import Formulas.CnfDnf.SwitchingLemmaCore

open Finset
open Circuits
open Circuits.CnfDnf Circuits.CnfDnf.Restrictions
open Circuits.HastadParity.FaninReduction

namespace Circuits.HastadParity.FaninReduction

/-- Package a Round-0 explicit restriction `(S, bits)` as a project
`AssignedRandomRestriction σ n`, provided `σ` is calibrated so that
`⌈σ·n⌉ = |S|`. -/
def round0ToRestriction (n s : Nat) (σ : OpenUnitIntervalQ)
    (S : Finset Nat) (bits : List Bool)
    (h_ssub : S ⊆ range n) (h_scard : S.card = s)
    (hbitslen : bits.length = n - s) (hsn : s ≤ n)
    (hceil : Nat.ceil (σ.val * (n : ℚ)) = s) :
    AssignedRandomRestriction σ n :=
  { starAssignment := ⟨⟨S, h_ssub⟩, by rw [h_scard, hceil]⟩
    varAssignments := bits
    non_starred_vars_fully_assigned := by
      have : S.card + bits.length = n := by rw [h_scard, hbitslen]; omega
      exact this }

/-- The packaged restriction map is exactly `mkAssignment S bits`. -/
theorem round0ToRestriction_map (n s : Nat) (σ : OpenUnitIntervalQ)
    (S : Finset Nat) (bits : List Bool)
    (h_ssub : S ⊆ range n) (h_scard : S.card = s)
    (hbitslen : bits.length = n - s) (hsn : s ≤ n)
    (hceil : Nat.ceil (σ.val * (n : ℚ)) = s) :
    randomRestrictionToMap n σ
        (round0ToRestriction n s σ S bits h_ssub h_scard hbitslen hsn hceil)
      = mkAssignment S bits := rfl

/-- The arithmetic data needed to instantiate the density-neutral Round-0
fan-in reduction.  Concrete density modules provide small calibration
theorems; the structural parity proof consumes only this common interface. -/
structure RoundZeroCalibration (q : ℚ) (n s : Nat) : Prop where
  q_pos : 0 < q
  q_le_one : q ≤ 1
  n_pos : 0 < n
  live_le : s ≤ n
  sigma_exists : ∃ σ : OpenUnitIntervalQ,
    Nat.ceil (σ.val * (n : ℚ)) = s ∧
    (1 + (s : ℚ) / n) / 2 ≤ q

/-- Density-neutral Round-0 capstone.  A caller supplies a calibrated live-set
size `s`, survival bound `q`, and project restriction parameter `σ`; the shared
parameterized fan-in theorem supplies the restriction itself. -/
theorem exists_round0_restriction_width_le_card_of_bound
    (q : ℚ) (n s t : Nat)
    (σ : OpenUnitIntervalQ)
    (hsn : s ≤ n) (hn : 0 < n)
    (hceil : Nat.ceil (σ.val * (n : ℚ)) = s)
    (hq1 : q ≤ 1)
    (hσ : (1 + (s : ℚ) / n) / 2 ≤ q)
    (dnfs : List UnboundedFanInFormula)
    (hdnf : ∀ d ∈ dnfs, isDNF d = true)
    (hnd : ∀ d ∈ dnfs, ∀ c ∈ dnfClauses d, (c.map Prod.fst).Nodup)
    (hvar : ∀ d ∈ dnfs, ∀ c ∈ dnfClauses d, ∀ p ∈ c, p.1 < n)
    (hcount : ((wideClauses t dnfs).length : ℚ) * q ^ (t + 1) < 1) :
  ∃ ρ : AssignedRandomRestriction σ n,
    ρ.starAssignment.val.val.card = s ∧
    ∀ d ∈ dnfs,
      dnfWidth (simpleRestrictDNF (randomRestrictionToMap n σ ρ) d) ≤ t := by
  obtain ⟨S, h_s, bits, hbits, hwidth⟩ :=
    exists_restrict_bottoms_width_le_of_bound q n s t dnfs
      hsn hn hdnf hnd hvar hq1 hσ hcount
  rw [Finset.mem_powersetCard] at h_s
  obtain ⟨h_ssub, h_scard⟩ := h_s
  have hbitslen : bits.length = n - s := allBitLists_mem_length _ _ hbits
  refine ⟨round0ToRestriction n s σ S bits h_ssub h_scard hbitslen hsn hceil,
    ?_, ?_⟩
  · have hlv :
        (round0ToRestriction n s σ S bits h_ssub h_scard hbitslen hsn
          hceil).starAssignment.val.val = S := rfl
    rw [hlv, h_scard]
  · intro d hd
    rw [round0ToRestriction_map n s σ S bits h_ssub h_scard hbitslen hsn hceil]
    exact hwidth d hd

/-- A calibration supplies a project restriction with the calibrated live-set
cardinality whenever the corresponding first-moment bound holds. -/
theorem RoundZeroCalibration.exists_restriction_width_le_card
    {q : ℚ}
    {n s : Nat}
    (cal : RoundZeroCalibration q n s)
    (t : Nat)
    (dnfs : List UnboundedFanInFormula)
    (hdnf : ∀ d ∈ dnfs, isDNF d = true)
    (hnd : ∀ d ∈ dnfs, ∀ c ∈ dnfClauses d, (c.map Prod.fst).Nodup)
    (hvar : ∀ d ∈ dnfs, ∀ c ∈ dnfClauses d, ∀ p ∈ c, p.1 < n)
    (hcount : ((wideClauses t dnfs).length : ℚ) * q ^ (t + 1) < 1) :
  ∃ (σ : OpenUnitIntervalQ) (ρ : AssignedRandomRestriction σ n),
    ρ.starAssignment.val.val.card = s ∧
    ∀ d ∈ dnfs,
      dnfWidth (simpleRestrictDNF (randomRestrictionToMap n σ ρ) d) ≤ t := by
  obtain ⟨σ, hceil, hsurvival⟩ := cal.sigma_exists
  obtain ⟨ρ, hcard, hwidth⟩ :=
    exists_round0_restriction_width_le_card_of_bound
      q n s t σ cal.live_le cal.n_pos hceil cal.q_le_one hsurvival
      dnfs hdnf hnd hvar hcount
  exact ⟨σ, ρ, hcard, hwidth⟩

end Circuits.HastadParity.FaninReduction
