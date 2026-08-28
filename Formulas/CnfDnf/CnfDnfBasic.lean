import Formulas.Basic
import Formulas.Eval
import Lists.ListLemmas

namespace Circuits.CnfDnf
open UnboundedFanInFormula
open Lists.ListLemmas

def isAndOfInputsOnly (gate : UnboundedFanInFormula) : Bool :=
  match gate with
  | andGate gates => (gates.all isInput)
  | _ => false

def isOrOfInputsOnly (gate : UnboundedFanInFormula) : Bool :=
  match gate with
  | orGate gates => (gates.all isInput)
  | _ => false

def isCNF (gate : UnboundedFanInFormula) : Bool :=
  match gate with
  | andGate gates => (gates.all isOrOfInputsOnly)
  | _ => false

def isDNF (gate : UnboundedFanInFormula) : Bool :=
  match gate with
  | orGate gates => (gates.all isAndOfInputsOnly)
  | _ => false

/-- `isDNF dnf = true` implies that `dnf` is an `orGate`. -/
theorem isDNF_eq_orGate (dnf : UnboundedFanInFormula) (h : isDNF dnf = true) :
    ∃ gates : List UnboundedFanInFormula, dnf = orGate gates := by
  cases dnf with
  | orGate gates => exact ⟨gates, rfl⟩
  | inputGate _ _ => simp [isDNF] at h
  | constant _ _ => simp [isDNF] at h
  | notGate _ => simp [isDNF] at h
  | andGate _ => simp [isDNF] at h

/-- Every child of a well-formed DNF root is an `andGate` containing only
    input literals. -/
theorem mem_gates_of_dnf
    (gates : List UnboundedFanInFormula) (h : isDNF (orGate gates) = true)
    (g : UnboundedFanInFormula) (hg : g ∈ gates) :
    ∃ lits : List UnboundedFanInFormula,
      g = andGate lits ∧ ∀ l ∈ lits, ∃ v b, l = inputGate v b := by
  have h_all : ∀ g ∈ gates, isAndOfInputsOnly g = true := by
    simpa only [isDNF, List.all_eq_true] using h
  have h_and : isAndOfInputsOnly g = true := h_all g hg
  cases g with
  | andGate lits =>
    refine ⟨lits, rfl, ?_⟩
    have h_inputs : ∀ l ∈ lits, isInput l = true := by
      simpa only [isAndOfInputsOnly, List.all_eq_true] using h_and
    intro l hl
    have hin : isInput l = true := h_inputs l hl
    cases l with
    | inputGate v b => exact ⟨v, b, rfl⟩
    | constant _ _ => simp [isInput] at hin
    | notGate _ => simp [isInput] at hin
    | andGate _ => simp [isInput] at hin
    | orGate _ => simp [isInput] at hin
  | inputGate _ _ => simp [isAndOfInputsOnly] at h_and
  | constant _ _ => simp [isAndOfInputsOnly] at h_and
  | notGate _ => simp [isAndOfInputsOnly] at h_and
  | orGate _ => simp [isAndOfInputsOnly] at h_and

def dnfWidth (dnf : UnboundedFanInFormula) : Nat :=
  match dnf with
  | orGate gates =>
      (gates.map
        (fun gate => match gate with
                     | andGate literals => literals.length
                     | _ => 0)
      ).foldl max 0
  | _ => 0

def cnfWidth (cnf : UnboundedFanInFormula) : Nat :=
  match cnf with
  | andGate gates =>
      (gates.map
        (fun gate => match gate with
                     | orGate literals => literals.length
                     | _ => 0)
      ).foldl max 0
  | _ => 0

def cnfSize (cnf : UnboundedFanInFormula) : Nat :=
  match cnf with
  | andGate gates => gates.length
  | _ => 0

def dnfSize (dnf : UnboundedFanInFormula) : Nat :=
  match dnf with
  | orGate gates => gates.length
  | _ => 0

/-- Given a DNF circuit, extract the list of clauses as lists of (variable, negated) pairs.
    For a well-formed DNF `orGate [andGate [...], ...]`, each clause becomes a list of
    `(input_index, negation_flag)` pairs. Non-inputGate children are dropped. -/
def dnfClauses (dnf : UnboundedFanInFormula) : List (List (Nat × Bool)) :=
  match dnf with
  | .orGate gates => gates.map fun gate =>
      match gate with
      | .andGate lits => lits.filterMap fun lit =>
          match lit with
          | .inputGate i b => some (i, b)
          | _ => none
      | _ => []
  | _ => []

/-- Given a CNF circuit, extract the list of clauses as lists of (variable, negated) pairs.
    For a well-formed CNF `andGate [orGate [...], ...]`, each clause becomes a list of
    `(input_index, negation_flag)` pairs. Non-inputGate children are dropped. -/
def cnfClauses (cnf : UnboundedFanInFormula) : List (List (Nat × Bool)) :=
  match cnf with
  | .andGate gates => gates.map fun gate =>
      match gate with
      | .orGate lits => lits.filterMap fun lit =>
          match lit with
          | .inputGate i b => some (i, b)
          | _ => none
      | _ => []
  | _ => []

/-- filterMap with a partial function produces a list no longer than the original. -/
theorem filterMap_circuit_to_pair_length_le
    (lits : List UnboundedFanInFormula) :
    (lits.filterMap (fun lit =>
      match lit with
      | .inputGate i b => some (i, b)
      | _ => none)).length ≤ lits.length := by
  induction lits with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filterMap_cons]
    split <;> simp_all [List.length_cons]; omega

/-- Each clause in a well-formed DNF with width ≤ w has at most w literals.
    Therefore `findPositionInClause'` returns a value < w when the variable
    appears in the clause. -/
lemma clause_length_le_dnfWidth (dnf : UnboundedFanInFormula)
    (hd : isDNF dnf = true) (clause : List (Nat × Bool))
    (hc : clause ∈ dnfClauses dnf) :
    clause.length ≤ dnfWidth dnf := by
  simp only [dnfClauses] at hc
  match dnf, hd with
  | .orGate gates, hd =>
    rw [List.mem_map] at hc
    obtain ⟨gate, hgate_mem, hgate_eq⟩ := hc
    have h_aoi : isAndOfInputsOnly gate = true := by
      simp only [isDNF, List.all_eq_true] at hd; exact hd gate hgate_mem
    match gate, h_aoi, hgate_mem, hgate_eq with
    | .andGate lits, _, hgate_mem, hgate_eq =>
      subst hgate_eq
      simp only [dnfWidth]
      calc (lits.filterMap _).length
          ≤ lits.length := filterMap_circuit_to_pair_length_le lits
        _ ≤ (gates.map fun gate => match gate with
              | .andGate literals => literals.length
              | _ => 0).foldl max 0 := by
            have hmem : lits.length ∈ (gates.map fun gate => match gate with
                | .andGate literals => literals.length
                | _ => 0) := by
              rw [List.mem_map]; exact ⟨.andGate lits, hgate_mem, rfl⟩
            exact mem_le_foldl_max hmem
    | .orGate _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi
    | .inputGate _ _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi
    | .constant _ _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi
    | .notGate _, h_aoi, _, _ => simp [isAndOfInputsOnly] at h_aoi

/-- A formula is a **proper CNF**: it has the `isCNF` shape, every
    clause is nonempty, and no clause repeats a variable. -/
def IsProperCNF (f : UnboundedFanInFormula) : Prop :=
  isCNF f = true ∧
  (∀ c ∈ cnfClauses f, c ≠ []) ∧
  (∀ c ∈ cnfClauses f, (c.map Prod.fst).Nodup)

/-- A formula is a **proper DNF**: it has the `isDNF` shape, every
    clause is nonempty, and no clause repeats a variable. -/
def IsProperDNF (f : UnboundedFanInFormula) : Prop :=
  isDNF f = true ∧
  (∀ c ∈ dnfClauses f, c ≠ []) ∧
  (∀ c ∈ dnfClauses f, (c.map Prod.fst).Nodup)

end Circuits.CnfDnf
