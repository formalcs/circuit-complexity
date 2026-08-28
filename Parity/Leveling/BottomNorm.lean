import Parity.Properize
import Parity.Leveling.Invariants

/-!
Kernel for `proper_bottoms_contract_explicit` at depth at least two: the bottom-layer
AND→CNF normalizer with constant folding + bare-literal wrapping,
and its eval-correctness lemma.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.style.show false

namespace Circuits.HastadParity.BottomNorm
open Circuits
open Circuits.CnfDnf
open Circuits.HastadParity.ProperizeProto
open DecisionTrees
open UnboundedFanInFormula

/-- A child of a bottom AND/OR gate is a *leaf* (inputGate or constant). -/
def IsLeaf : UnboundedFanInFormula → Prop
  | .inputGate _ _ => True
  | .constant _ _ => True
  | _ => False

/-- Collapse an OR-of-leaves into a clause (`List (Nat × Bool)`),
    constant-folding: `constant one` ⟹ whole clause satisfied (`none`);
    `constant zero` ⟹ literal dropped; `inputGate i b` ⟹ kept. -/
def orChildLiterals : List UnboundedFanInFormula → Option (List (Nat × Bool))
  | [] => some []
  | (.inputGate i b) :: rest => (orChildLiterals rest).map (fun c => (i, b) :: c)
  | (.constant true _) :: _ => none
  | (.constant false _) :: rest => orChildLiterals rest
  | _ :: rest => orChildLiterals rest

/-- eval of an `orGate (g :: rest)` reduces to an `if`. -/
theorem eval_orGate_cons (g : UnboundedFanInFormula)
    (rest : List UnboundedFanInFormula) (inputs : List Bool) :
    ufiFormulaEval (orGate (g :: rest)) inputs =
      (match ufiFormulaEval g inputs with
       | false => ufiFormulaEval (orGate rest) inputs
       | true => true) := by
  cases h : ufiFormulaEval g inputs <;> simp only [ufiFormulaEval, h]

theorem eval_andGate_cons (g : UnboundedFanInFormula)
    (rest : List UnboundedFanInFormula) (inputs : List Bool) :
    ufiFormulaEval (andGate (g :: rest)) inputs =
      (match ufiFormulaEval g inputs with
       | false => false
       | true => ufiFormulaEval (andGate rest) inputs) := by
  cases h : ufiFormulaEval g inputs <;> simp only [ufiFormulaEval, h]

/-- Correctness of `orChildLiterals` for an OR-of-leaves. -/
theorem orChildLiterals_correct (inputs : List Bool) (lits : List UnboundedFanInFormula)
    (hstruct : ∀ x ∈ lits, IsLeaf x) :
    match orChildLiterals lits with
    | none => ufiFormulaEval (orGate lits) inputs = true
    | some c => ufiFormulaEval (orGate lits) inputs = evalDisj inputs c := by
  induction lits with
  | nil => simp [orChildLiterals, ufiFormulaEval, evalDisj]
  | cons g rest ih =>
    have hrest : ∀ x ∈ rest, IsLeaf x := fun x hx => hstruct x (List.mem_cons_of_mem _ hx)
    have hg : IsLeaf g := hstruct g List.mem_cons_self
    have ihr := ih hrest
    cases g with
    | inputGate i b =>
      simp only [orChildLiterals]
      rw [eval_orGate_cons]
      -- eval (inputGate i b) = evalLiteral inputs (i,b)
      have hlit : ufiFormulaEval (inputGate i b) inputs = evalLiteral inputs (i, b) := by
        unfold ufiFormulaEval evalLiteral
        cases inputs[i]? <;> cases b <;> rfl
      cases hev : orChildLiterals rest with
      | none =>
        simp only [Option.map_none]
        rw [hev] at ihr
        rw [hlit]
        cases hl : evalLiteral inputs (i, b) <;> simp [ihr]
      | some c =>
        simp only [Option.map_some]
        rw [hev] at ihr
        rw [hlit, evalDisj]
        cases hl : evalLiteral inputs (i, b) <;> simp [ihr]
    | constant bit lbl =>
      cases bit with
      | true =>
        simp only [orChildLiterals]
        rw [eval_orGate_cons]
        simp [ufiFormulaEval]
      | false =>
        simp only [orChildLiterals]
        rw [eval_orGate_cons]
        have : ufiFormulaEval (constant false lbl) inputs = false := by
          simp only [ufiFormulaEval]
        rw [this]
        exact ihr
    | notGate g => exact absurd hg (by simp [IsLeaf])
    | andGate gs => exact absurd hg (by simp [IsLeaf])
    | orGate gs => exact absurd hg (by simp [IsLeaf])

/-- A child of a bottom AND gate: a leaf, or an OR-of-leaves. -/
def IsAndChild : UnboundedFanInFormula → Prop
  | .inputGate _ _ => True
  | .constant _ _ => True
  | .orGate lits => ∀ x ∈ lits, IsLeaf x
  | _ => False

/-- Collapse a bottom AND-of-(leaf | OR-of-leaves) into a clause list,
    constant-folding.  `none` means the AND is identically `zero`. -/
def andClauses : List UnboundedFanInFormula → Option (List (List (Nat × Bool)))
  | [] => some []
  | g :: rest =>
    match andClauses rest with
    | none => none
    | some cs =>
      match g with
      | .inputGate i b => some ([(i, b)] :: cs)
      | .constant true _ => some cs
      | .constant false _ => none
      | .orGate literals =>
          match orChildLiterals literals with
          | none => some cs
          | some [] => none
          | some c => some (c :: cs)
      | _ => some cs

theorem evalConj_cons (inputs : List Bool) (c : List (Nat × Bool))
    (rest : List (List (Nat × Bool))) :
    evalConj inputs (c :: rest) =
      (match evalDisj inputs c with
       | false => false
       | true => evalConj inputs rest) := by
  rfl

theorem evalDisj_singleton (inputs : List Bool) (lit : Nat × Bool) :
    evalDisj inputs [lit] = evalLiteral inputs lit := by
  simp only [evalDisj]
  cases evalLiteral inputs lit <;> rfl

/-- Correctness of `andClauses` for a bottom AND. -/
theorem andClauses_correct (inputs : List Bool) (gs : List UnboundedFanInFormula)
    (hstruct : ∀ g ∈ gs, IsAndChild g) :
    match andClauses gs with
    | none => ufiFormulaEval (andGate gs) inputs = false
    | some cs => ufiFormulaEval (andGate gs) inputs = evalConj inputs cs := by
  induction gs with
  | nil => simp [andClauses, ufiFormulaEval, evalConj]
  | cons g rest ih =>
    have hrest : ∀ x ∈ rest, IsAndChild x :=
      fun x hx => hstruct x (List.mem_cons_of_mem _ hx)
    have hg : IsAndChild g := hstruct g List.mem_cons_self
    have ihr := ih hrest
    cases hrc : andClauses rest with
    | none =>
      rw [hrc] at ihr
      simp only [andClauses, hrc]
      rw [eval_andGate_cons]
      cases hev : ufiFormulaEval g inputs <;> simp [ihr]
    | some cs =>
      rw [hrc] at ihr
      cases g with
      | inputGate i b =>
        simp only [andClauses, hrc]
        rw [eval_andGate_cons, evalConj_cons, evalDisj_singleton]
        have hlit : ufiFormulaEval (inputGate i b) inputs = evalLiteral inputs (i, b) := by
          unfold ufiFormulaEval evalLiteral
          cases inputs[i]? <;> cases b <;> rfl
        rw [hlit]
        cases evalLiteral inputs (i, b) <;> simp [ihr]
      | constant bit lbl =>
        cases bit with
        | true =>
          simp only [andClauses, hrc]
          rw [eval_andGate_cons]
          have : ufiFormulaEval (constant true lbl) inputs = true := by
            simp only [ufiFormulaEval]
          rw [this]; exact ihr
        | false =>
          simp only [andClauses, hrc]
          rw [eval_andGate_cons]
          have : ufiFormulaEval (constant false lbl) inputs = false := by
            simp only [ufiFormulaEval]
          rw [this]
      | orGate lits =>
        have hlits : ∀ x ∈ lits, IsLeaf x := by
          have := hg; simp only [IsAndChild] at this; exact this
        have horc := orChildLiterals_correct inputs lits hlits
        cases hoc : orChildLiterals lits with
        | none =>
          rw [hoc] at horc
          simp only [andClauses, hrc, hoc]
          rw [eval_andGate_cons, horc]; exact ihr
        | some c =>
          rw [hoc] at horc
          cases c with
          | nil =>
            simp only [andClauses, hrc, hoc]
            rw [eval_andGate_cons, horc]
            simp only [evalDisj]
          | cons hd tl =>
            simp only [andClauses, hrc, hoc]
            rw [eval_andGate_cons, evalConj_cons, horc]
            cases evalDisj inputs (hd :: tl) <;> simp [ihr]
      | notGate g => exact absurd hg (by simp [IsAndChild])
      | andGate gs => exact absurd hg (by simp [IsAndChild])

/- ===================================================================
   DNF dual: bottom OR → proper-shaped DNF
   =================================================================== -/

/-- A child of a bottom OR gate: a leaf, or an AND-of-leaves. -/
def IsOrChild : UnboundedFanInFormula → Prop
  | .inputGate _ _ => True
  | .constant _ _ => True
  | .andGate lits => ∀ x ∈ lits, IsLeaf x
  | _ => False

/-- Collapse an AND-of-leaves into a clause (`List (Nat × Bool)`),
    constant-folding: `constant zero` ⟹ whole AND is false (`none`);
    `constant one` ⟹ literal dropped; `inputGate i b` ⟹ kept. -/
def andChildLiterals : List UnboundedFanInFormula → Option (List (Nat × Bool))
  | [] => some []
  | (.inputGate i b) :: rest => (andChildLiterals rest).map (fun c => (i, b) :: c)
  | (.constant false _) :: _ => none
  | (.constant true _) :: rest => andChildLiterals rest
  | _ :: rest => andChildLiterals rest

/-- Correctness of `andChildLiterals` for an AND-of-leaves. -/
theorem andChildLiterals_correct (inputs : List Bool) (lits : List UnboundedFanInFormula)
    (hstruct : ∀ x ∈ lits, IsLeaf x) :
    match andChildLiterals lits with
    | none => ufiFormulaEval (andGate lits) inputs = false
    | some c => ufiFormulaEval (andGate lits) inputs = evalClause inputs c := by
  induction lits with
  | nil => simp [andChildLiterals, ufiFormulaEval, evalClause]
  | cons g rest ih =>
    have hrest : ∀ x ∈ rest, IsLeaf x := fun x hx => hstruct x (List.mem_cons_of_mem _ hx)
    have hg : IsLeaf g := hstruct g List.mem_cons_self
    have ihr := ih hrest
    cases g with
    | inputGate i b =>
      simp only [andChildLiterals]
      rw [eval_andGate_cons]
      have hlit : ufiFormulaEval (inputGate i b) inputs = evalLiteral inputs (i, b) := by
        unfold ufiFormulaEval evalLiteral
        cases inputs[i]? <;> cases b <;> rfl
      cases hev : andChildLiterals rest with
      | none =>
        simp only [Option.map_none]
        rw [hev] at ihr
        rw [hlit]
        cases hl : evalLiteral inputs (i, b) <;> simp [ihr]
      | some c =>
        simp only [Option.map_some]
        rw [hev] at ihr
        rw [hlit, evalClause]
        cases hl : evalLiteral inputs (i, b) <;> simp [ihr]
    | constant bit lbl =>
      cases bit with
      | false =>
        simp only [andChildLiterals]
        rw [eval_andGate_cons]
        have : ufiFormulaEval (constant false lbl) inputs = false := by
          simp only [ufiFormulaEval]
        rw [this]
      | true =>
        simp only [andChildLiterals]
        rw [eval_andGate_cons]
        have : ufiFormulaEval (constant true lbl) inputs = true := by
          simp only [ufiFormulaEval]
        rw [this]; exact ihr
    | notGate g => exact absurd hg (by simp [IsLeaf])
    | andGate gs => exact absurd hg (by simp [IsLeaf])
    | orGate gs => exact absurd hg (by simp [IsLeaf])

/-- Collapse a bottom OR-of-(leaf | AND-of-leaves) into a clause list,
    constant-folding. `none` means the OR is identically `true`. -/
def orClauses : List UnboundedFanInFormula → Option (List (List (Nat × Bool)))
  | []        => some []
  | g :: rest => match orClauses rest with
                 | none    => none
                 | some cs => match g with
                              | .inputGate i b        => some ([(i, b)] :: cs)
                              | .constant false _ => some cs
                              | .constant true _  => none
                              | .andGate literals =>
                                  match andChildLiterals literals with
                                  | none => some cs
                                  | some [] => none
                                  | some c => some (c :: cs)
                              | _ => some cs

theorem evalClauses_cons (inputs : List Bool) (c : List (Nat × Bool))
    (rest : List (List (Nat × Bool))) :
    evalClauses inputs (c :: rest) =
      (match evalClause inputs c with
       | true => true
       | false => evalClauses inputs rest) := by
  rfl

theorem evalClause_singleton (inputs : List Bool) (lit : Nat × Bool) :
    evalClause inputs [lit] = evalLiteral inputs lit := by
  simp only [evalClause]
  cases evalLiteral inputs lit <;> rfl

/-- Correctness of `orClauses` for a bottom OR. -/
theorem orClauses_correct (inputs : List Bool) (gs : List UnboundedFanInFormula)
    (hstruct : ∀ g ∈ gs, IsOrChild g) :
    match orClauses gs with
    | none => ufiFormulaEval (orGate gs) inputs = true
    | some cs => ufiFormulaEval (orGate gs) inputs = evalClauses inputs cs := by
  induction gs with
  | nil => simp [orClauses, ufiFormulaEval, evalClauses]
  | cons g rest ih =>
    have hrest : ∀ x ∈ rest, IsOrChild x :=
      fun x hx => hstruct x (List.mem_cons_of_mem _ hx)
    have hg : IsOrChild g := hstruct g List.mem_cons_self
    have ihr := ih hrest
    cases hrc : orClauses rest with
    | none =>
      rw [hrc] at ihr
      simp only [orClauses, hrc]
      rw [eval_orGate_cons]
      cases hev : ufiFormulaEval g inputs <;> simp [ihr]
    | some cs =>
      rw [hrc] at ihr
      cases g with
      | inputGate i b =>
        simp only [orClauses, hrc]
        rw [eval_orGate_cons, evalClauses_cons, evalClause_singleton]
        have hlit : ufiFormulaEval (inputGate i b) inputs = evalLiteral inputs (i, b) := by
          unfold ufiFormulaEval evalLiteral
          cases inputs[i]? <;> cases b <;> rfl
        rw [hlit]
        cases evalLiteral inputs (i, b) <;> simp [ihr]
      | constant bit lbl =>
        cases bit with
        | false =>
          simp only [orClauses, hrc]
          rw [eval_orGate_cons]
          have : ufiFormulaEval (constant false lbl) inputs = false := by
            simp only [ufiFormulaEval]
          rw [this]; exact ihr
        | true =>
          simp only [orClauses, hrc]
          rw [eval_orGate_cons]
          have : ufiFormulaEval (constant true lbl) inputs = true := by
            simp only [ufiFormulaEval]
          rw [this]
      | andGate lits =>
        have hlits : ∀ x ∈ lits, IsLeaf x := by
          have := hg; simp only [IsOrChild] at this; exact this
        have hacl := andChildLiterals_correct inputs lits hlits
        cases hac : andChildLiterals lits with
        | none =>
          rw [hac] at hacl
          simp only [orClauses, hrc, hac]
          rw [eval_orGate_cons, hacl]; exact ihr
        | some c =>
          rw [hac] at hacl
          cases c with
          | nil =>
            simp only [orClauses, hrc, hac]
            rw [eval_orGate_cons, hacl]
            simp only [evalClause]
          | cons hd tl =>
            simp only [orClauses, hrc, hac]
            rw [eval_orGate_cons, evalClauses_cons, hacl]
            cases evalClause inputs (hd :: tl) <;> simp [ihr]
      | notGate g => exact absurd hg (by simp [IsOrChild])
      | orGate gs => exact absurd hg (by simp [IsOrChild])

/- ===================================================================
   Structural lemmas for CNF/DNF bottoms: depth, strict-leveling, proper
   =================================================================== -/

/-- A `cnfFromClauses` is an AND of OR-of-inputs, hence depth ≤ 2. -/
theorem depth_cnfFromClauses_le (cs : List (List (Nat × Bool))) :
    ufiFormulaDepth (cnfFromClauses cs) ≤ 2 := by
  simp only [cnfFromClauses, ufiFormulaDepth]
  have : (List.foldr max 0) ((cs.map clauseToOr).map ufiFormulaDepth) ≤ 1 := by
    apply foldr_max_map_le
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨c, _, rfl⟩ := hg
    simp only [clauseToOr, ufiFormulaDepth]
    have : (List.foldr max 0) ((c.map litToInput).map ufiFormulaDepth) ≤ 0 := by
      apply foldr_max_map_le
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput, ufiFormulaDepth]; omega
    omega
  omega

theorem depth_dnfFromClauses_le (cs : List (List (Nat × Bool))) :
    ufiFormulaDepth (dnfFromClauses cs) ≤ 2 := by
  simp only [dnfFromClauses, ufiFormulaDepth]
  have : (List.foldr max 0) ((cs.map clauseToAnd).map ufiFormulaDepth) ≤ 1 := by
    apply foldr_max_map_le
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨c, _, rfl⟩ := hg
    simp only [clauseToAnd, ufiFormulaDepth]
    have : (List.foldr max 0) ((c.map litToInput).map ufiFormulaDepth) ≤ 0 := by
      apply foldr_max_map_le
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput, ufiFormulaDepth]; omega
    omega
  omega

/-- `cnfFromClauses cs` is strictly assigned-leveled at any level `≥ 1`. -/
theorem isAlternatingAndLeveledAt_cnfFromClauses (cs : List (List (Nat × Bool)))
    (lvl : Nat) (hlvl : 1 ≤ lvl) :
    IsAlternatingAndLeveledAt (cnfFromClauses cs) lvl := by
  simp only [cnfFromClauses, IsAlternatingAndLeveledAt]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg inner
    rw [List.mem_map] at hg
    obtain ⟨c, _, rfl⟩ := hg
    simp only [clauseToOr]
    exact fun h => by injection h
  · intro g hg _
    exact hlvl
  · intro g hg
    rw [List.mem_map] at hg
    obtain ⟨c, _, rfl⟩ := hg
    simp only [clauseToOr, IsAlternatingAndLeveledAt]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx inner
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput]
      exact fun h => by injection h
    · intro x hx h_ao
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput, IsAndOr] at h_ao
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput, IsAlternatingAndLeveledAt]

theorem isAlternatingAndLeveledAt_dnfFromClauses (cs : List (List (Nat × Bool)))
    (lvl : Nat) (hlvl : 1 ≤ lvl) :
    IsAlternatingAndLeveledAt (dnfFromClauses cs) lvl := by
  simp only [dnfFromClauses, IsAlternatingAndLeveledAt]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg inner
    rw [List.mem_map] at hg
    obtain ⟨c, _, rfl⟩ := hg
    simp only [clauseToAnd]
    exact fun h => by injection h
  · intro g hg _
    exact hlvl
  · intro g hg
    rw [List.mem_map] at hg
    obtain ⟨c, _, rfl⟩ := hg
    simp only [clauseToAnd, IsAlternatingAndLeveledAt]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx inner
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput]
      exact fun h => by injection h
    · intro x hx h_ao
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput, IsAndOr] at h_ao
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx
      simp only [litToInput, IsAlternatingAndLeveledAt]

/-- `properizeCNF g` is always a `cnfFromClauses` (an andGate of OR-clauses). -/
theorem properizeCNF_eq_cnfFromClauses (g : UnboundedFanInFormula) :
    ∃ cs, properizeCNF g = cnfFromClauses cs := by
  simp only [properizeCNF]
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem]; exact ⟨_, rfl⟩
  · rw [if_neg hmem]; exact ⟨_, rfl⟩

theorem properizeDNF_eq_dnfFromClauses (g : UnboundedFanInFormula) :
    ∃ cs, properizeDNF g = dnfFromClauses cs := by
  simp only [properizeDNF]
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem]; exact ⟨_, rfl⟩
  · rw [if_neg hmem]; exact ⟨_, rfl⟩

/-- `properizeCNF g` is proper-leveled at any bottom level `lvl ≤ 2`. -/
theorem hasProperBottomsAt_properizeCNF (g : UnboundedFanInFormula)
    (lvl : Nat) (hlvl : lvl ≤ 2) :
    HasProperBottomsAt (properizeCNF g) lvl := by
  obtain ⟨gates, hg⟩ : ∃ gates, properizeCNF g = andGate gates := by
    obtain ⟨cs, hcs⟩ := properizeCNF_eq_cnfFromClauses g
    exact ⟨cs.map clauseToOr, by rw [hcs]; rfl⟩
  rw [hg]
  simp only [HasProperBottomsAt, if_pos hlvl]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hg]; exact isCNF_properizeCNF g
  · intro c hc; rw [← hg] at hc; exact properizeCNF_clauses_ne_nil g c hc
  · intro c hc; rw [← hg] at hc; exact properizeCNF_clauses_nodup g c hc

theorem hasProperBottomsAt_properizeDNF (g : UnboundedFanInFormula)
    (lvl : Nat) (hlvl : lvl ≤ 2) :
    HasProperBottomsAt (properizeDNF g) lvl := by
  obtain ⟨gates, hg⟩ : ∃ gates, properizeDNF g = orGate gates := by
    obtain ⟨cs, hcs⟩ := properizeDNF_eq_dnfFromClauses g
    exact ⟨cs.map clauseToAnd, by rw [hcs]; rfl⟩
  rw [hg]
  simp only [HasProperBottomsAt, if_pos hlvl]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hg]; exact isDNF_properizeDNF g
  · intro c hc; rw [← hg] at hc; exact properizeDNF_clauses_ne_nil g c hc
  · intro c hc; rw [← hg] at hc; exact properizeDNF_clauses_nodup g c hc

/- ===================================================================
   Proper-shaped bottom transforms (output is a *proper* CNF/DNF)
   =================================================================== -/

/-- Bottom AND → proper CNF (constant-folds to `constant zero` when identically false). -/
def properizeBottomAnd (gs : List UnboundedFanInFormula) : UnboundedFanInFormula :=
  match andClauses gs with
  | none => constant false 0
  | some cs => properizeCNF (cnfFromClauses cs)

/-- Bottom OR → proper DNF (constant-folds to `constant one` when identically true). -/
def properizeBottomOr (gs : List UnboundedFanInFormula) : UnboundedFanInFormula :=
  match orClauses gs with
  | none => constant true 0
  | some cs => properizeDNF (dnfFromClauses cs)

theorem eval_properizeBottomAnd (inputs : List Bool) (gs : List UnboundedFanInFormula)
    (hstruct : ∀ g ∈ gs, IsAndChild g) (hpos : 0 < inputs.length)
    (hbound : ∀ cs, andClauses gs = some cs →
      ∀ i ∈ ufiCollectInputIndices (cnfFromClauses cs), i < inputs.length) :
    ufiFormulaEval (properizeBottomAnd gs) inputs = ufiFormulaEval (andGate gs) inputs := by
  have h := andClauses_correct inputs gs hstruct
  unfold properizeBottomAnd
  cases hac : andClauses gs with
  | none =>
    rw [hac] at h
    rw [h]; simp only [ufiFormulaEval]
  | some cs =>
    rw [hac] at h
    rw [eval_properizeCNF _ (isCNF_cnfFromClauses cs) inputs hpos,
      eval_cnfFromClauses, h]
    exact hbound cs hac

theorem eval_properizeBottomOr (inputs : List Bool) (gs : List UnboundedFanInFormula)
    (hstruct : ∀ g ∈ gs, IsOrChild g) (hpos : 0 < inputs.length) :
    ufiFormulaEval (properizeBottomOr gs) inputs = ufiFormulaEval (orGate gs) inputs := by
  have h := orClauses_correct inputs gs hstruct
  unfold properizeBottomOr
  cases hoc : orClauses gs with
  | none =>
    rw [hoc] at h
    rw [h]; simp only [ufiFormulaEval]
  | some cs =>
    rw [hoc] at h
    rw [eval_properizeDNF _ (isDNF_dnfFromClauses cs) inputs hpos,
      eval_dnfFromClauses, h]

theorem depth_properizeBottomAnd_le (gs : List UnboundedFanInFormula) :
    ufiFormulaDepth (properizeBottomAnd gs) ≤ 2 := by
  unfold properizeBottomAnd
  cases andClauses gs with
  | none => simp only [ufiFormulaDepth]; omega
  | some cs =>
    show ufiFormulaDepth (properizeCNF (cnfFromClauses cs)) ≤ 2
    obtain ⟨cs', hcs'⟩ := properizeCNF_eq_cnfFromClauses (cnfFromClauses cs)
    rw [hcs']; exact depth_cnfFromClauses_le cs'

theorem depth_properizeBottomOr_le (gs : List UnboundedFanInFormula) :
    ufiFormulaDepth (properizeBottomOr gs) ≤ 2 := by
  unfold properizeBottomOr
  cases orClauses gs with
  | none => simp only [ufiFormulaDepth]; omega
  | some cs =>
    show ufiFormulaDepth (properizeDNF (dnfFromClauses cs)) ≤ 2
    obtain ⟨cs', hcs'⟩ := properizeDNF_eq_dnfFromClauses (dnfFromClauses cs)
    rw [hcs']; exact depth_dnfFromClauses_le cs'

theorem hasProperBottomsAt_properizeBottomAnd (gs : List UnboundedFanInFormula)
    (lvl : Nat) (hlvl : lvl ≤ 2) :
    HasProperBottomsAt (properizeBottomAnd gs) lvl := by
  unfold properizeBottomAnd
  cases andClauses gs with
  | none => simp only [HasProperBottomsAt]
  | some cs => exact hasProperBottomsAt_properizeCNF (cnfFromClauses cs) lvl hlvl

theorem hasProperBottomsAt_properizeBottomOr (gs : List UnboundedFanInFormula)
    (lvl : Nat) (hlvl : lvl ≤ 2) :
    HasProperBottomsAt (properizeBottomOr gs) lvl := by
  unfold properizeBottomOr
  cases orClauses gs with
  | none => simp only [HasProperBottomsAt]
  | some cs => exact hasProperBottomsAt_properizeDNF (dnfFromClauses cs) lvl hlvl

theorem isAlternatingAndLeveledAt_properizeBottomAnd (gs : List UnboundedFanInFormula)
    (lvl : Nat) (hlvl : 1 ≤ lvl) :
    IsAlternatingAndLeveledAt (properizeBottomAnd gs) lvl := by
  unfold properizeBottomAnd
  cases andClauses gs with
  | none => simp only [IsAlternatingAndLeveledAt]
  | some cs =>
    show IsAlternatingAndLeveledAt (properizeCNF (cnfFromClauses cs)) lvl
    obtain ⟨cs', hcs'⟩ := properizeCNF_eq_cnfFromClauses (cnfFromClauses cs)
    rw [hcs']; exact isAlternatingAndLeveledAt_cnfFromClauses cs' lvl hlvl

theorem isAlternatingAndLeveledAt_properizeBottomOr (gs : List UnboundedFanInFormula)
    (lvl : Nat) (hlvl : 1 ≤ lvl) :
    IsAlternatingAndLeveledAt (properizeBottomOr gs) lvl := by
  unfold properizeBottomOr
  cases orClauses gs with
  | none => simp only [IsAlternatingAndLeveledAt]
  | some cs =>
    show IsAlternatingAndLeveledAt (properizeDNF (dnfFromClauses cs)) lvl
    obtain ⟨cs', hcs'⟩ := properizeDNF_eq_dnfFromClauses (dnfFromClauses cs)
    rw [hcs']; exact isAlternatingAndLeveledAt_dnfFromClauses cs' lvl hlvl

/- ===================================================================
   Variable-bound preservation for the bottom transforms
   =================================================================== -/

theorem mem_collect_or_tail {x : Nat} (g : UnboundedFanInFormula)
    (rest : List UnboundedFanInFormula)
    (h : x ∈ ufiCollectInputIndices (orGate rest)) :
    x ∈ ufiCollectInputIndices (orGate (g :: rest)) := by
  simp only [ufiCollectInputIndices, List.flatMap_cons, List.mem_append]
  right; simpa only [ufiCollectInputIndices] using h

theorem mem_collect_or_head {x : Nat} (g : UnboundedFanInFormula)
    (rest : List UnboundedFanInFormula)
    (h : x ∈ ufiCollectInputIndices g) :
    x ∈ ufiCollectInputIndices (orGate (g :: rest)) := by
  simp only [ufiCollectInputIndices, List.flatMap_cons, List.mem_append]
  left; exact h

theorem mem_collect_and_tail {x : Nat} (g : UnboundedFanInFormula)
    (rest : List UnboundedFanInFormula)
    (h : x ∈ ufiCollectInputIndices (andGate rest)) :
    x ∈ ufiCollectInputIndices (andGate (g :: rest)) := by
  simp only [ufiCollectInputIndices, List.flatMap_cons, List.mem_append]
  right; simpa only [ufiCollectInputIndices] using h

theorem mem_collect_and_head {x : Nat} (g : UnboundedFanInFormula)
    (rest : List UnboundedFanInFormula)
    (h : x ∈ ufiCollectInputIndices g) :
    x ∈ ufiCollectInputIndices (andGate (g :: rest)) := by
  simp only [ufiCollectInputIndices, List.flatMap_cons, List.mem_append]
  left; exact h

/-- Every variable surviving `orChildLiterals` came from an `inputGate` in the OR. -/
theorem orChildLiterals_vars (lits : List UnboundedFanInFormula) (c : List (Nat × Bool))
    (hoc : orChildLiterals lits = some c) :
    ∀ p ∈ c, p.1 ∈ ufiCollectInputIndices (orGate lits) := by
  induction lits generalizing c with
  | nil =>
    simp only [orChildLiterals, Option.some.injEq] at hoc
    subst hoc; intro p hp; exact absurd hp (by simp)
  | cons g rest ih =>
    cases g with
    | inputGate i b =>
      simp only [orChildLiterals] at hoc
      cases hrest : orChildLiterals rest with
      | none => rw [hrest] at hoc; simp at hoc
      | some c0 =>
        rw [hrest] at hoc
        simp only [Option.map_some, Option.some.injEq] at hoc
        subst hoc
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact mem_collect_or_head (inputGate i b) rest (by simp [ufiCollectInputIndices])
        · exact mem_collect_or_tail _ rest (ih c0 hrest p hp)
    | constant bit lbl =>
      cases bit with
      | true => simp [orChildLiterals] at hoc
      | false =>
        simp only [orChildLiterals] at hoc
        intro p hp
        exact mem_collect_or_tail _ rest (ih c hoc p hp)
    | notGate g =>
      simp only [orChildLiterals] at hoc
      intro p hp
      exact mem_collect_or_tail _ rest (ih c hoc p hp)
    | andGate gs =>
      simp only [orChildLiterals] at hoc
      intro p hp
      exact mem_collect_or_tail _ rest (ih c hoc p hp)
    | orGate gs =>
      simp only [orChildLiterals] at hoc
      intro p hp
      exact mem_collect_or_tail _ rest (ih c hoc p hp)

theorem andChildLiterals_vars (lits : List UnboundedFanInFormula) (c : List (Nat × Bool))
    (hac : andChildLiterals lits = some c) :
    ∀ p ∈ c, p.1 ∈ ufiCollectInputIndices (andGate lits) := by
  induction lits generalizing c with
  | nil =>
    simp only [andChildLiterals, Option.some.injEq] at hac
    subst hac; intro p hp; exact absurd hp (by simp)
  | cons g rest ih =>
    cases g with
    | inputGate i b =>
      simp only [andChildLiterals] at hac
      cases hrest : andChildLiterals rest with
      | none => rw [hrest] at hac; simp at hac
      | some c0 =>
        rw [hrest] at hac
        simp only [Option.map_some, Option.some.injEq] at hac
        subst hac
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact mem_collect_and_head (inputGate i b) rest (by simp [ufiCollectInputIndices])
        · exact mem_collect_and_tail _ rest (ih c0 hrest p hp)
    | constant bit lbl =>
      cases bit with
      | false => simp [andChildLiterals] at hac
      | true =>
        simp only [andChildLiterals] at hac
        intro p hp
        exact mem_collect_and_tail _ rest (ih c hac p hp)
    | notGate g =>
      simp only [andChildLiterals] at hac
      intro p hp
      exact mem_collect_and_tail _ rest (ih c hac p hp)
    | andGate gs =>
      simp only [andChildLiterals] at hac
      intro p hp
      exact mem_collect_and_tail _ rest (ih c hac p hp)
    | orGate gs =>
      simp only [andChildLiterals] at hac
      intro p hp
      exact mem_collect_and_tail _ rest (ih c hac p hp)

/-- Every variable in the clause list produced by `andClauses` came from the AND. -/
theorem andClauses_vars (gs : List UnboundedFanInFormula) (cs : List (List (Nat × Bool)))
    (hac : andClauses gs = some cs) :
    ∀ c ∈ cs, ∀ p ∈ c, p.1 ∈ ufiCollectInputIndices (andGate gs) := by
  induction gs generalizing cs with
  | nil =>
    simp only [andClauses, Option.some.injEq] at hac
    subst hac; intro c hc; exact absurd hc (by simp)
  | cons g rest ih =>
    cases hrc : andClauses rest with
    | none => simp [andClauses, hrc] at hac
    | some cs0 =>
      have ihr := ih cs0 hrc
      cases g with
      | inputGate i b =>
        simp only [andClauses, hrc, Option.some.injEq] at hac
        subst hac
        intro c hc p hp
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · simp only [List.mem_singleton] at hp
          subst hp
          exact mem_collect_and_head (inputGate i b) rest (by simp [ufiCollectInputIndices])
        · exact mem_collect_and_tail _ rest (ihr c hc p hp)
      | constant bit lbl =>
        cases bit with
        | true =>
          simp only [andClauses, hrc, Option.some.injEq] at hac
          subst hac
          intro c hc p hp
          exact mem_collect_and_tail _ rest (ihr c hc p hp)
        | false => simp [andClauses, hrc] at hac
      | orGate lits =>
        simp only [andClauses, hrc] at hac
        cases hocl : orChildLiterals lits with
        | none =>
          rw [hocl] at hac
          simp only [Option.some.injEq] at hac
          subst hac
          intro c hc p hp
          exact mem_collect_and_tail _ rest (ihr c hc p hp)
        | some c1 =>
          rw [hocl] at hac
          cases c1 with
          | nil => simp at hac
          | cons hd tl =>
            simp only [Option.some.injEq] at hac
            subst hac
            intro c hc p hp
            simp only [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact mem_collect_and_head (orGate lits) rest
                (orChildLiterals_vars lits (hd :: tl) hocl p hp)
            · exact mem_collect_and_tail _ rest (ihr c hc p hp)
      | notGate g =>
        simp only [andClauses, hrc, Option.some.injEq] at hac
        subst hac
        intro c hc p hp
        exact mem_collect_and_tail _ rest (ihr c hc p hp)
      | andGate gs2 =>
        simp only [andClauses, hrc, Option.some.injEq] at hac
        subst hac
        intro c hc p hp
        exact mem_collect_and_tail _ rest (ihr c hc p hp)

theorem orClauses_vars (gs : List UnboundedFanInFormula) (cs : List (List (Nat × Bool)))
    (hoc : orClauses gs = some cs) :
    ∀ c ∈ cs, ∀ p ∈ c, p.1 ∈ ufiCollectInputIndices (orGate gs) := by
  induction gs generalizing cs with
  | nil =>
    simp only [orClauses, Option.some.injEq] at hoc
    subst hoc; intro c hc; exact absurd hc (by simp)
  | cons g rest ih =>
    cases hrc : orClauses rest with
    | none => simp [orClauses, hrc] at hoc
    | some cs0 =>
      have ihr := ih cs0 hrc
      cases g with
      | inputGate i b =>
        simp only [orClauses, hrc, Option.some.injEq] at hoc
        subst hoc
        intro c hc p hp
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · simp only [List.mem_singleton] at hp
          subst hp
          exact mem_collect_or_head (inputGate i b) rest (by simp [ufiCollectInputIndices])
        · exact mem_collect_or_tail _ rest (ihr c hc p hp)
      | constant bit lbl =>
        cases bit with
        | false =>
          simp only [orClauses, hrc, Option.some.injEq] at hoc
          subst hoc
          intro c hc p hp
          exact mem_collect_or_tail _ rest (ihr c hc p hp)
        | true => simp [orClauses, hrc] at hoc
      | andGate lits =>
        simp only [orClauses, hrc] at hoc
        cases hacl : andChildLiterals lits with
        | none =>
          rw [hacl] at hoc
          simp only [Option.some.injEq] at hoc
          subst hoc
          intro c hc p hp
          exact mem_collect_or_tail _ rest (ihr c hc p hp)
        | some c1 =>
          rw [hacl] at hoc
          cases c1 with
          | nil => simp at hoc
          | cons hd tl =>
            simp only [Option.some.injEq] at hoc
            subst hoc
            intro c hc p hp
            simp only [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact mem_collect_or_head (andGate lits) rest
                (andChildLiterals_vars lits (hd :: tl) hacl p hp)
            · exact mem_collect_or_tail _ rest (ihr c hc p hp)
      | notGate g =>
        simp only [orClauses, hrc, Option.some.injEq] at hoc
        subst hoc
        intro c hc p hp
        exact mem_collect_or_tail _ rest (ihr c hc p hp)
      | orGate gs2 =>
        simp only [orClauses, hrc, Option.some.injEq] at hoc
        subst hoc
        intro c hc p hp
        exact mem_collect_or_tail _ rest (ihr c hc p hp)

/-- Variable bound preserved by the proper bottom-AND transform. -/
theorem vars_properizeBottomAnd (gs : List UnboundedFanInFormula) (n : Nat) (hn : 0 < n)
    (hbound : ∀ i ∈ ufiCollectInputIndices (andGate gs), i < n) :
    ∀ i ∈ ufiCollectInputIndices (properizeBottomAnd gs), i < n := by
  unfold properizeBottomAnd
  cases hac : andClauses gs with
  | none =>
    show ∀ i ∈ ufiCollectInputIndices (constant false 0), i < n
    intro i hi; simp only [ufiCollectInputIndices] at hi
    exact absurd hi (by simp)
  | some cs =>
    show ∀ i ∈ ufiCollectInputIndices (properizeCNF (cnfFromClauses cs)), i < n
    intro i hi
    refine properizeCNF_vars (cnfFromClauses cs) (isCNF_cnfFromClauses cs) n hn ?_ i hi
    intro j hj
    rw [ufi_collect_cnfFromClauses] at hj
    simp only [List.mem_flatMap] at hj
    obtain ⟨c, hc, hjc⟩ := hj
    rw [List.mem_map] at hjc
    obtain ⟨p, hp, rfl⟩ := hjc
    exact hbound p.1 (andClauses_vars gs cs hac c hc p hp)

theorem vars_properizeBottomOr (gs : List UnboundedFanInFormula) (n : Nat) (hn : 0 < n)
    (hbound : ∀ i ∈ ufiCollectInputIndices (orGate gs), i < n) :
    ∀ i ∈ ufiCollectInputIndices (properizeBottomOr gs), i < n := by
  unfold properizeBottomOr
  cases hoc : orClauses gs with
  | none =>
    show ∀ i ∈ ufiCollectInputIndices (constant true 0), i < n
    intro i hi; simp only [ufiCollectInputIndices] at hi
    exact absurd hi (by simp)
  | some cs =>
    show ∀ i ∈ ufiCollectInputIndices (properizeDNF (dnfFromClauses cs)), i < n
    intro i hi
    refine properizeDNF_vars (dnfFromClauses cs) (isDNF_dnfFromClauses cs) n hn ?_ i hi
    intro j hj
    rw [ufi_collect_dnfFromClauses] at hj
    simp only [List.mem_flatMap] at hj
    obtain ⟨c, hc, hjc⟩ := hj
    rw [List.mem_map] at hjc
    obtain ⟨p, hp, rfl⟩ := hjc
    exact hbound p.1 (orClauses_vars gs cs hoc c hc p hp)

/- ===================================================================
   Recursive tree properizer + structural derivation lemmas.
   =================================================================== -/

/-- A depth-0 formula is a leaf. -/
theorem isLeaf_of_depth_zero (x : UnboundedFanInFormula)
    (h : ufiFormulaDepth x = 0) : IsLeaf x := by
  cases x with
  | inputGate i b => trivial
  | constant c l => trivial
  | notGate g => simp only [ufiFormulaDepth] at h; omega
  | andGate gs => simp only [ufiFormulaDepth] at h; omega
  | orGate gs => simp only [ufiFormulaDepth] at h; omega

/-- A child of a depth-≤2 strictly-leveled AND gate (no `notGate`s) is an
    `IsAndChild` (leaf or OR-of-leaves). -/
theorem isAndChild_of_child (gs : List UnboundedFanInFormula) (lvl : Nat)
    (hstrict : IsAlternatingAndLeveledAt (andGate gs) lvl)
    (hdepth : ufiFormulaDepth (andGate gs) ≤ 2)
    (hnn : Circuits.Leveling.HasNoNotGates (andGate gs)) :
    ∀ g ∈ gs, IsAndChild g := by
  intro g hg
  simp only [IsAlternatingAndLeveledAt] at hstrict
  obtain ⟨h_no_and, _, _⟩ := hstrict
  simp only [Circuits.Leveling.HasNoNotGates] at hnn
  have hnng : Circuits.Leveling.HasNoNotGates g := hnn g hg
  have hdg : ufiFormulaDepth g ≤ 1 := by
    have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
      mem_le_foldr_max_map hg
    simp only [ufiFormulaDepth] at hdepth
    omega
  cases g with
  | inputGate i b => trivial
  | constant c l => trivial
  | notGate g' => simp only [Circuits.Leveling.HasNoNotGates] at hnng
  | andGate inner => exact absurd rfl (h_no_and (andGate inner) hg inner)
  | orGate lits =>
    show ∀ x ∈ lits, IsLeaf x
    intro x hx
    have hdx : ufiFormulaDepth x ≤ (List.foldr max 0) (lits.map ufiFormulaDepth) :=
      mem_le_foldr_max_map hx
    simp only [ufiFormulaDepth] at hdg
    exact isLeaf_of_depth_zero x (by omega)

/-- A child of a depth-≤2 strictly-leveled OR gate (no `notGate`s) is an
    `IsOrChild` (leaf or AND-of-leaves). -/
theorem isOrChild_of_child (gs : List UnboundedFanInFormula) (lvl : Nat)
    (hstrict : IsAlternatingAndLeveledAt (orGate gs) lvl)
    (hdepth : ufiFormulaDepth (orGate gs) ≤ 2)
    (hnn : Circuits.Leveling.HasNoNotGates (orGate gs)) :
    ∀ g ∈ gs, IsOrChild g := by
  intro g hg
  simp only [IsAlternatingAndLeveledAt] at hstrict
  obtain ⟨h_no_or, _, _⟩ := hstrict
  simp only [Circuits.Leveling.HasNoNotGates] at hnn
  have hnng : Circuits.Leveling.HasNoNotGates g := hnn g hg
  have hdg : ufiFormulaDepth g ≤ 1 := by
    have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
      mem_le_foldr_max_map hg
    simp only [ufiFormulaDepth] at hdepth
    omega
  cases g with
  | inputGate i b => trivial
  | constant c l => trivial
  | notGate g' => simp only [Circuits.Leveling.HasNoNotGates] at hnng
  | orGate inner => exact absurd rfl (h_no_or (orGate inner) hg inner)
  | andGate lits =>
    show ∀ x ∈ lits, IsLeaf x
    intro x hx
    have hdx : ufiFormulaDepth x ≤ (List.foldr max 0) (lits.map ufiFormulaDepth) :=
      mem_le_foldr_max_map hx
    simp only [ufiFormulaDepth] at hdg
    exact isLeaf_of_depth_zero x (by omega)

/- Recursive tree properizer: at level ≤2 convert the whole subtree into a
   proper CNF/DNF (bottom transform); otherwise recurse into children. -/
mutual
def properizeTree : Nat → UnboundedFanInFormula → UnboundedFanInFormula
  | _, .inputGate i b => .inputGate i b
  | _, .constant c l => .constant c l
  | _, .notGate g => .notGate g
  | lvl, .andGate gs =>
      if lvl ≤ 2 then properizeBottomAnd gs
      else .andGate (properizeTreeList (lvl - 1) gs)
  | lvl, .orGate gs =>
      if lvl ≤ 2 then properizeBottomOr gs
      else .orGate (properizeTreeList (lvl - 1) gs)
def properizeTreeList : Nat → List UnboundedFanInFormula → List UnboundedFanInFormula
  | _, [] => []
  | lvl, g :: gs => properizeTree lvl g :: properizeTreeList lvl gs
end

/- ===================================================================
   Eval preservation for the recursive tree properizer.
   =================================================================== -/

mutual
theorem eval_properizeTree (inputs : List Bool) (lvl : Nat) (f : UnboundedFanInFormula)
    (hnn : Circuits.Leveling.HasNoNotGates f)
    (hstrict : IsAlternatingAndLeveledAt f lvl)
    (hlvl : 2 ≤ lvl) (hdepth : ufiFormulaDepth f ≤ lvl)
    (hpos : 0 < inputs.length)
    (hbound : ∀ i ∈ ufiCollectInputIndices f, i < inputs.length) :
    ufiFormulaEval (properizeTree lvl f) inputs = ufiFormulaEval f inputs := by
  cases f with
  | inputGate i b => simp only [properizeTree]
  | constant c l => simp only [properizeTree]
  | notGate g => simp only [properizeTree]
  | andGate gs =>
    by_cases hc : lvl ≤ 2
    · have hl2 : lvl = 2 := by omega
      have h_ac : ∀ g ∈ gs, IsAndChild g :=
        isAndChild_of_child gs lvl hstrict (by omega) hnn
      simp only [properizeTree, if_pos hc]
      apply eval_properizeBottomAnd inputs gs h_ac hpos
      intro cs hac i hi
      rw [ufi_collect_cnfFromClauses] at hi
      simp only [List.mem_flatMap] at hi
      obtain ⟨c, hc, hic⟩ := hi
      rw [List.mem_map] at hic
      obtain ⟨p, hp, rfl⟩ := hic
      exact hbound p.1 (andClauses_vars gs cs hac c hc p hp)
    · have hgt : 2 < lvl := by omega
      simp only [properizeTree, if_neg hc]
      have hnn' : ∀ g ∈ gs, Circuits.Leveling.HasNoNotGates g := by
        simpa only [Circuits.Leveling.HasNoNotGates] using hnn
      have hstrict' : ∀ g ∈ gs,
          IsAlternatingAndLeveledAt g (lvl - 1) := by
        simp only [IsAlternatingAndLeveledAt] at hstrict
        exact hstrict.2.2
      have hdepth' : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl - 1 := by
        intro g hg
        have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        simp only [ufiFormulaDepth] at hdepth
        omega
      have hmap := map_ufiFormulaEval_properizeTreeList inputs (lvl - 1) gs hnn' hstrict'
        (by omega) hdepth' hpos (by
          intro g hg i hi
          apply hbound
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨g, hg, hi⟩)
      rw [ufi_eval_andGate_eq_all, ufi_eval_andGate_eq_all, hmap]
  | orGate gs =>
    by_cases hc : lvl ≤ 2
    · have hl2 : lvl = 2 := by omega
      have h_oc : ∀ g ∈ gs, IsOrChild g :=
        isOrChild_of_child gs lvl hstrict (by omega) hnn
      simp only [properizeTree, if_pos hc]
      exact eval_properizeBottomOr inputs gs h_oc hpos
    · have hgt : 2 < lvl := by omega
      simp only [properizeTree, if_neg hc]
      have hnn' : ∀ g ∈ gs, Circuits.Leveling.HasNoNotGates g := by
        simpa only [Circuits.Leveling.HasNoNotGates] using hnn
      have hstrict' : ∀ g ∈ gs,
          IsAlternatingAndLeveledAt g (lvl - 1) := by
        simp only [IsAlternatingAndLeveledAt] at hstrict
        exact hstrict.2.2
      have hdepth' : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl - 1 := by
        intro g hg
        have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        simp only [ufiFormulaDepth] at hdepth
        omega
      have hmap := map_ufiFormulaEval_properizeTreeList inputs (lvl - 1) gs hnn' hstrict'
        (by omega) hdepth' hpos (by
          intro g hg i hi
          apply hbound
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨g, hg, hi⟩)
      rw [ufi_eval_orGate_eq_any, ufi_eval_orGate_eq_any, hmap]

theorem map_ufiFormulaEval_properizeTreeList (inputs : List Bool) (lvl : Nat)
    (gs : List UnboundedFanInFormula)
    (hnn : ∀ g ∈ gs, Circuits.Leveling.HasNoNotGates g)
    (hstrict : ∀ g ∈ gs, IsAlternatingAndLeveledAt g lvl)
    (hlvl : 2 ≤ lvl) (hdepth : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl)
    (hpos : 0 < inputs.length)
    (hbound : ∀ g ∈ gs, ∀ i ∈ ufiCollectInputIndices g, i < inputs.length) :
    (properizeTreeList lvl gs).map (fun c => ufiFormulaEval c inputs) =
      gs.map (fun c => ufiFormulaEval c inputs) := by
  cases gs with
  | nil => simp only [properizeTreeList]
  | cons g gs =>
    simp only [properizeTreeList, List.map_cons]
    have hhead : ufiFormulaEval (properizeTree lvl g) inputs =
        ufiFormulaEval g inputs :=
      eval_properizeTree inputs lvl g (hnn g (by simp))
        (hstrict g (by simp)) hlvl (hdepth g (by simp)) hpos (hbound g (by simp))
    have htail := map_ufiFormulaEval_properizeTreeList inputs lvl gs
      (fun x hx => hnn x (by simp [hx]))
      (fun x hx => hstrict x (by simp [hx])) hlvl
      (fun x hx => hdepth x (by simp [hx])) hpos
      (fun x hx => hbound x (by simp [hx]))
    rw [hhead, htail]
end

/- ===================================================================
   Depth preservation for the recursive tree properizer.
   =================================================================== -/

mutual
theorem depth_properizeTree_le (lvl : Nat) (f : UnboundedFanInFormula)
    (hlvl : 2 ≤ lvl) (hdepth : ufiFormulaDepth f ≤ lvl) :
    ufiFormulaDepth (properizeTree lvl f) ≤ lvl := by
  cases f with
  | inputGate i b => simp only [properizeTree, ufiFormulaDepth]; omega
  | constant c l => simp only [properizeTree, ufiFormulaDepth]; omega
  | notGate g => simp only [properizeTree]; exact hdepth
  | andGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      have := depth_properizeBottomAnd_le gs
      omega
    · simp only [properizeTree, if_neg hc, ufiFormulaDepth]
      have hd : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl - 1 := by
        intro g hg
        have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        simp only [ufiFormulaDepth] at hdepth
        omega
      have hchild := depth_properizeTreeList_le (lvl - 1) gs (by omega) hd
      have := foldr_max_map_le ufiFormulaDepth (properizeTreeList (lvl - 1) gs)
        (lvl - 1) hchild
      omega
  | orGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      have := depth_properizeBottomOr_le gs
      omega
    · simp only [properizeTree, if_neg hc, ufiFormulaDepth]
      have hd : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl - 1 := by
        intro g hg
        have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        simp only [ufiFormulaDepth] at hdepth
        omega
      have hchild := depth_properizeTreeList_le (lvl - 1) gs (by omega) hd
      have := foldr_max_map_le ufiFormulaDepth (properizeTreeList (lvl - 1) gs)
        (lvl - 1) hchild
      omega

theorem depth_properizeTreeList_le (lvl : Nat) (gs : List UnboundedFanInFormula)
    (hlvl : 2 ≤ lvl) (hdepth : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl) :
    ∀ g' ∈ properizeTreeList lvl gs, ufiFormulaDepth g' ≤ lvl := by
  cases gs with
  | nil => intro g' hg'; simp only [properizeTreeList] at hg'; exact absurd hg' (by simp)
  | cons g gs =>
    intro g' hg'
    simp only [properizeTreeList, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact depth_properizeTree_le lvl g hlvl (hdepth g (by simp))
    · exact depth_properizeTreeList_le lvl gs hlvl
        (fun x hx => hdepth x (by simp [hx])) g' hg'
end

/- ===================================================================
   Shape lemmas: properizeTree preserves the top constructor kind.
   =================================================================== -/

theorem properizeBottomOr_ne_andGate (gs : List UnboundedFanInFormula)
    (inner : List UnboundedFanInFormula) : properizeBottomOr gs ≠ andGate inner := by
  unfold properizeBottomOr
  cases orClauses gs with
  | none => intro h; exact absurd h (by simp)
  | some cs =>
    obtain ⟨cs', hcs'⟩ := properizeDNF_eq_dnfFromClauses (dnfFromClauses cs)
    show properizeDNF (dnfFromClauses cs) ≠ andGate inner
    rw [hcs']; simp only [dnfFromClauses]; intro h; exact absurd h (by simp)

theorem properizeBottomAnd_ne_orGate (gs : List UnboundedFanInFormula)
    (inner : List UnboundedFanInFormula) : properizeBottomAnd gs ≠ orGate inner := by
  unfold properizeBottomAnd
  cases andClauses gs with
  | none => intro h; exact absurd h (by simp)
  | some cs =>
    obtain ⟨cs', hcs'⟩ := properizeCNF_eq_cnfFromClauses (cnfFromClauses cs)
    show properizeCNF (cnfFromClauses cs) ≠ orGate inner
    rw [hcs']; simp only [cnfFromClauses]; intro h; exact absurd h (by simp)

theorem properizeTree_andGate_imp (m : Nat) (g : UnboundedFanInFormula)
    (inner : List UnboundedFanInFormula) (h : properizeTree m g = andGate inner) :
    ∃ gs, g = andGate gs := by
  cases g with
  | inputGate i b => simp only [properizeTree] at h; exact absurd h (by simp)
  | constant c l => simp only [properizeTree] at h; exact absurd h (by simp)
  | notGate g' => simp only [properizeTree] at h; exact absurd h (by simp)
  | andGate gs => exact ⟨gs, rfl⟩
  | orGate gs =>
    by_cases hc : m ≤ 2
    · simp only [properizeTree, if_pos hc] at h
      exact absurd h (properizeBottomOr_ne_andGate gs inner)
    · simp only [properizeTree, if_neg hc] at h
      exact absurd h (by simp)

theorem properizeTree_orGate_imp (m : Nat) (g : UnboundedFanInFormula)
    (inner : List UnboundedFanInFormula) (h : properizeTree m g = orGate inner) :
    ∃ gs, g = orGate gs := by
  cases g with
  | inputGate i b => simp only [properizeTree] at h; exact absurd h (by simp)
  | constant c l => simp only [properizeTree] at h; exact absurd h (by simp)
  | notGate g' => simp only [properizeTree] at h; exact absurd h (by simp)
  | orGate gs => exact ⟨gs, rfl⟩
  | andGate gs =>
    by_cases hc : m ≤ 2
    · simp only [properizeTree, if_pos hc] at h
      exact absurd h (properizeBottomAnd_ne_orGate gs inner)
    · simp only [properizeTree, if_neg hc] at h
      exact absurd h (by simp)

theorem mem_properizeTreeList (m : Nat) (gs : List UnboundedFanInFormula)
    (g' : UnboundedFanInFormula) (h : g' ∈ properizeTreeList m gs) :
    ∃ g ∈ gs, g' = properizeTree m g := by
  induction gs with
  | nil => simp only [properizeTreeList] at h; exact absurd h (by simp)
  | cons g gs ih =>
    simp only [properizeTreeList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨g, by simp, rfl⟩
    · obtain ⟨g0, hg0, rfl⟩ := ih h; exact ⟨g0, by simp [hg0], rfl⟩

/- ===================================================================
   Strict-leveling preservation for the recursive tree properizer.
   =================================================================== -/

mutual
theorem strict_properizeTree (lvl : Nat) (f : UnboundedFanInFormula)
    (hstrict : IsAlternatingAndLeveledAt f lvl)
    (hlvl : 2 ≤ lvl) (hdepth : ufiFormulaDepth f ≤ lvl) :
    IsAlternatingAndLeveledAt (properizeTree lvl f) lvl := by
  cases f with
  | inputGate i b => simp only [properizeTree]; trivial
  | constant c l => simp only [properizeTree]; trivial
  | notGate g => simp only [IsAlternatingAndLeveledAt] at hstrict
  | andGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      exact isAlternatingAndLeveledAt_properizeBottomAnd gs lvl (by omega)
    · simp only [properizeTree, if_neg hc]
      simp only [IsAlternatingAndLeveledAt] at hstrict ⊢
      have hdepth' : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl - 1 := by
        intro g hg
        have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        simp only [ufiFormulaDepth] at hdepth
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg' inner hcontra
        obtain ⟨g, hg, rfl⟩ := mem_properizeTreeList (lvl - 1) gs g' hg'
        obtain ⟨gs', hgs'⟩ := properizeTree_andGate_imp (lvl - 1) g inner hcontra
        exact (hstrict.1 g hg gs') hgs'
      · intro g' _ _; omega
      · exact strict_properizeTreeList (lvl - 1) gs hstrict.2.2 (by omega) hdepth'
  | orGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      exact isAlternatingAndLeveledAt_properizeBottomOr gs lvl (by omega)
    · simp only [properizeTree, if_neg hc]
      simp only [IsAlternatingAndLeveledAt] at hstrict ⊢
      have hdepth' : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl - 1 := by
        intro g hg
        have hmem : ufiFormulaDepth g ≤ (List.foldr max 0) (gs.map ufiFormulaDepth) :=
          mem_le_foldr_max_map hg
        simp only [ufiFormulaDepth] at hdepth
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro g' hg' inner hcontra
        obtain ⟨g, hg, rfl⟩ := mem_properizeTreeList (lvl - 1) gs g' hg'
        obtain ⟨gs', hgs'⟩ := properizeTree_orGate_imp (lvl - 1) g inner hcontra
        exact (hstrict.1 g hg gs') hgs'
      · intro g' _ _; omega
      · exact strict_properizeTreeList (lvl - 1) gs hstrict.2.2 (by omega) hdepth'

theorem strict_properizeTreeList (lvl : Nat) (gs : List UnboundedFanInFormula)
    (hstrict : ∀ g ∈ gs, IsAlternatingAndLeveledAt g lvl)
    (hlvl : 2 ≤ lvl) (hdepth : ∀ g ∈ gs, ufiFormulaDepth g ≤ lvl) :
    ∀ g' ∈ properizeTreeList lvl gs,
      IsAlternatingAndLeveledAt g' lvl := by
  cases gs with
  | nil => intro g' hg'; simp only [properizeTreeList] at hg'; exact absurd hg' (by simp)
  | cons g gs =>
    intro g' hg'
    simp only [properizeTreeList, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact strict_properizeTree lvl g (hstrict g (by simp)) hlvl
        (hdepth g (by simp))
    · exact strict_properizeTreeList lvl gs
        (fun x hx => hstrict x (by simp [hx])) hlvl
        (fun x hx => hdepth x (by simp [hx])) g' hg'
end

/- ===================================================================
   Proper-leveling preservation for the recursive tree properizer.
   =================================================================== -/

mutual
theorem proper_properizeTree (lvl : Nat) (f : UnboundedFanInFormula)
    (hnn : Circuits.Leveling.HasNoNotGates f) :
    HasProperBottomsAt (properizeTree lvl f) lvl := by
  cases f with
  | inputGate i b => simp only [properizeTree, HasProperBottomsAt]
  | constant c l => simp only [properizeTree, HasProperBottomsAt]
  | notGate g => simp only [Circuits.Leveling.HasNoNotGates] at hnn
  | andGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      exact hasProperBottomsAt_properizeBottomAnd gs lvl hc
    · simp only [properizeTree, if_neg hc]
      simp only [HasProperBottomsAt, if_neg hc]
      exact proper_properizeTreeList (lvl - 1) gs
        (by simpa only [Circuits.Leveling.HasNoNotGates] using hnn)
  | orGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      exact hasProperBottomsAt_properizeBottomOr gs lvl hc
    · simp only [properizeTree, if_neg hc]
      simp only [HasProperBottomsAt, if_neg hc]
      exact proper_properizeTreeList (lvl - 1) gs
        (by simpa only [Circuits.Leveling.HasNoNotGates] using hnn)

theorem proper_properizeTreeList (lvl : Nat) (gs : List UnboundedFanInFormula)
    (hnn : ∀ g ∈ gs, Circuits.Leveling.HasNoNotGates g) :
    ∀ g' ∈ properizeTreeList lvl gs, HasProperBottomsAt g' lvl := by
  cases gs with
  | nil => intro g' hg'; simp only [properizeTreeList] at hg'; exact absurd hg' (by simp)
  | cons g gs =>
    intro g' hg'
    simp only [properizeTreeList, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact proper_properizeTree lvl g (hnn g (by simp))
    · exact proper_properizeTreeList lvl gs (fun x hx => hnn x (by simp [hx])) g' hg'
end

/- ===================================================================
   Variable-bound preservation for the recursive tree properizer.
   =================================================================== -/

mutual
theorem vars_properizeTree (lvl : Nat) (f : UnboundedFanInFormula) (n : Nat)
    (hn : 0 < n) (hbound : ∀ i ∈ ufiCollectInputIndices f, i < n) :
    ∀ i ∈ ufiCollectInputIndices (properizeTree lvl f), i < n := by
  cases f with
  | inputGate i b => simp only [properizeTree]; exact hbound
  | constant c l =>
    simp only [properizeTree]; intro i hi
    simp only [ufiCollectInputIndices] at hi; exact absurd hi (by simp)
  | notGate g => simp only [properizeTree]; exact hbound
  | andGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      exact vars_properizeBottomAnd gs n hn hbound
    · simp only [properizeTree, if_neg hc]
      have hb' : ∀ g ∈ gs, ∀ i ∈ ufiCollectInputIndices g, i < n := by
        intro g hg i hi
        apply hbound
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨g, hg, hi⟩
      intro i hi
      simp only [ufiCollectInputIndices, List.mem_flatMap] at hi
      obtain ⟨g', hg', hi'⟩ := hi
      exact vars_properizeTreeList (lvl - 1) gs n hn hb' g' hg' i hi'
  | orGate gs =>
    by_cases hc : lvl ≤ 2
    · simp only [properizeTree, if_pos hc]
      exact vars_properizeBottomOr gs n hn hbound
    · simp only [properizeTree, if_neg hc]
      have hb' : ∀ g ∈ gs, ∀ i ∈ ufiCollectInputIndices g, i < n := by
        intro g hg i hi
        apply hbound
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨g, hg, hi⟩
      intro i hi
      simp only [ufiCollectInputIndices, List.mem_flatMap] at hi
      obtain ⟨g', hg', hi'⟩ := hi
      exact vars_properizeTreeList (lvl - 1) gs n hn hb' g' hg' i hi'

theorem vars_properizeTreeList (lvl : Nat) (gs : List UnboundedFanInFormula)
    (n : Nat) (hn : 0 < n)
    (hbound : ∀ g ∈ gs, ∀ i ∈ ufiCollectInputIndices g, i < n) :
    ∀ g' ∈ properizeTreeList lvl gs, ∀ i ∈ ufiCollectInputIndices g', i < n := by
  cases gs with
  | nil => intro g' hg'; simp only [properizeTreeList] at hg'; exact absurd hg' (by simp)
  | cons g gs =>
    intro g' hg'
    simp only [properizeTreeList, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact vars_properizeTree lvl g n hn (hbound g (by simp))
    · exact vars_properizeTreeList lvl gs n hn
        (fun x hx => hbound x (by simp [hx])) g' hg'
end

/- ===================================================================
   Circuit-size preservation helpers
   =================================================================== -/

/-- A proof-local structural presentation of circuit size plus input occurrences. -/
private def circuitSizeWithInputs : UnboundedFanInFormula → Nat
  | .inputGate _ _ => 1
  | .constant _ _ => 1
  | .notGate g => circuitSizeWithInputs g + 1
  | .andGate gs | .orGate gs => (gs.map circuitSizeWithInputs).sum + 1

private theorem circuitSizeWithInputs_pos (f : UnboundedFanInFormula) :
    1 ≤ circuitSizeWithInputs f := by
  cases f <;> simp [circuitSizeWithInputs]

mutual
private theorem circuitSizeWithInputs_eq_size_add_inputs :
    ∀ f : UnboundedFanInFormula,
      circuitSizeWithInputs f = ufiFormulaCircuitSize f +
        (ufiCollectInputIndices f).length
  | .inputGate i b => by simp [circuitSizeWithInputs, ufiFormulaCircuitSize,
      ufiCollectInputIndices]
  | .constant b i => by simp [circuitSizeWithInputs, ufiFormulaCircuitSize,
      ufiCollectInputIndices]
  | .notGate g => by
      simp only [circuitSizeWithInputs, ufiFormulaCircuitSize,
        ufiCollectInputIndices]
      rw [circuitSizeWithInputs_eq_size_add_inputs g]
      omega
  | .andGate gs => by
      simp only [circuitSizeWithInputs, ufiFormulaCircuitSize,
        ufiCollectInputIndices, List.length_flatMap]
      have h := circuitSizeWithInputs_list_eq_size_add_inputs gs
      omega
  | .orGate gs => by
      simp only [circuitSizeWithInputs, ufiFormulaCircuitSize,
        ufiCollectInputIndices, List.length_flatMap]
      have h := circuitSizeWithInputs_list_eq_size_add_inputs gs
      omega

private theorem circuitSizeWithInputs_list_eq_size_add_inputs :
    ∀ gs : List UnboundedFanInFormula,
      (gs.map circuitSizeWithInputs).sum =
        (gs.map ufiFormulaCircuitSize).sum +
          (gs.map (fun g => (ufiCollectInputIndices g).length)).sum
  | [] => by simp
  | g :: gs => by
      simp only [List.map_cons, List.sum_cons,
        circuitSizeWithInputs_eq_size_add_inputs g,
        circuitSizeWithInputs_list_eq_size_add_inputs gs]
      omega
end

/- ===================================================================
   Circuit-size preservation for the recursive tree properizer.

   Circuit size assigns zero cost to input leaves, so the proof-local
   budget below adds the number of input occurrences.  Stage 3 bounds
   that occurrence term from the input universe and local child
   deduplication; it is not part of any normalization contract.
   =================================================================== -/

private lemma sum_circuitSizeWithInputs (gs : List UnboundedFanInFormula) :
    (gs.map circuitSizeWithInputs).sum =
      (gs.map ufiFormulaCircuitSize).sum +
        (gs.map (fun g => (ufiCollectInputIndices g).length)).sum := by
  exact circuitSizeWithInputs_list_eq_size_add_inputs gs

private lemma circuitSizeWithInputs_gate (gs : List UnboundedFanInFormula) :
    circuitSizeWithInputs (andGate gs) =
      1 + (gs.map circuitSizeWithInputs).sum := by
  simp only [circuitSizeWithInputs, ufiFormulaCircuitSize,
    ufiCollectInputIndices, List.length_flatMap, List.map_map]
  rw [sum_circuitSizeWithInputs]
  omega

private lemma circuitSizeWithInputs_orGate (gs : List UnboundedFanInFormula) :
    circuitSizeWithInputs (orGate gs) =
      1 + (gs.map circuitSizeWithInputs).sum := by
  simp only [circuitSizeWithInputs, ufiFormulaCircuitSize,
    ufiCollectInputIndices, List.length_flatMap, List.map_map]
  rw [sum_circuitSizeWithInputs]
  omega

private theorem andClauses_length_le_circuitSizeWithInputs
    (gs : List UnboundedFanInFormula) (cs : List (List (Nat × Bool)))
    (h : andClauses gs = some cs) :
    cs.length ≤ (gs.map circuitSizeWithInputs).sum := by
  induction gs generalizing cs with
  | nil =>
      simp only [andClauses, Option.some.injEq] at h
      subst cs
      simp
  | cons g rest ih =>
      cases hrest : andClauses rest with
      | none => simp [andClauses, hrest] at h
      | some cs0 =>
          have htail := ih cs0 hrest
          cases g with
          | inputGate i b =>
              simp only [andClauses, hrest, Option.some.injEq] at h
              subst cs
              simp only [List.length_cons, List.map_cons, List.sum_cons,
                circuitSizeWithInputs, ufiFormulaCircuitSize,
                ufiCollectInputIndices]
              omega
          | constant bit lbl =>
              cases bit <;> simp [andClauses, hrest] at h ⊢
              subst cs
              omega
          | notGate g' =>
              simp only [andClauses, hrest, Option.some.injEq] at h
              subst cs
              simp only [List.map_cons, List.sum_cons]
              omega
          | andGate inner =>
              simp only [andClauses, hrest, Option.some.injEq] at h
              subst cs
              simp only [List.map_cons, List.sum_cons]
              omega
          | orGate lits =>
              cases hc : orChildLiterals lits with
              | none =>
                  simp only [andClauses, hrest, hc, Option.some.injEq] at h
                  subst cs
                  simp only [List.map_cons, List.sum_cons]
                  omega
              | some c =>
                  cases c with
                  | nil => simp [andClauses, hrest, hc] at h
                  | cons p ps =>
                      simp only [andClauses, hrest, hc, Option.some.injEq] at h
                      subst cs
                      simp only [List.length_cons, List.map_cons, List.sum_cons]
                      have hp := circuitSizeWithInputs_pos (orGate lits)
                      omega

private theorem orClauses_length_le_circuitSizeWithInputs
    (gs : List UnboundedFanInFormula) (cs : List (List (Nat × Bool)))
    (h : orClauses gs = some cs) :
    cs.length ≤ (gs.map circuitSizeWithInputs).sum := by
  induction gs generalizing cs with
  | nil =>
      simp only [orClauses, Option.some.injEq] at h
      subst cs
      simp
  | cons g rest ih =>
      cases hrest : orClauses rest with
      | none => simp [orClauses, hrest] at h
      | some cs0 =>
          have htail := ih cs0 hrest
          cases g with
          | inputGate i b =>
              simp only [orClauses, hrest, Option.some.injEq] at h
              subst cs
              simp only [List.length_cons, List.map_cons, List.sum_cons,
                circuitSizeWithInputs, ufiFormulaCircuitSize,
                ufiCollectInputIndices]
              omega
          | constant bit lbl =>
              cases bit <;> simp [orClauses, hrest] at h ⊢
              subst cs
              omega
          | notGate g' =>
              simp only [orClauses, hrest, Option.some.injEq] at h
              subst cs
              simp only [List.map_cons, List.sum_cons]
              omega
          | orGate inner =>
              simp only [orClauses, hrest, Option.some.injEq] at h
              subst cs
              simp only [List.map_cons, List.sum_cons]
              omega
          | andGate lits =>
              cases hc : andChildLiterals lits with
              | none =>
                  simp only [orClauses, hrest, hc, Option.some.injEq] at h
                  subst cs
                  simp only [List.map_cons, List.sum_cons]
                  omega
              | some c =>
                  cases c with
                  | nil => simp [orClauses, hrest, hc] at h
                  | cons p ps =>
                      simp only [orClauses, hrest, hc, Option.some.injEq] at h
                      subst cs
                      simp only [List.length_cons, List.map_cons, List.sum_cons]
                      have hp := circuitSizeWithInputs_pos (andGate lits)
                      omega

private theorem circuit_size_properizeBottomAnd_le (gs : List UnboundedFanInFormula) :
    ufiFormulaCircuitSize (properizeBottomAnd gs) ≤
      3 * (circuitSizeWithInputs (andGate gs) *
        circuitSizeWithInputs (andGate gs)) := by
  have hpos := circuitSizeWithInputs_pos (andGate gs)
  cases hac : andClauses gs with
  | none =>
      simp only [properizeBottomAnd, hac, ufiFormulaCircuitSize]
      nlinarith
  | some cs =>
      rw [show properizeBottomAnd gs = properizeCNF (cnfFromClauses cs) by
        simp [properizeBottomAnd, hac]]
      have hc := andClauses_length_le_circuitSizeWithInputs gs cs hac
      have hp := properizeCNF_circuit_size_le (cnfFromClauses cs)
      rw [cnfSize_cnfFromClauses] at hp
      have hm : max 2 cs.length ≤ 2 + (gs.map circuitSizeWithInputs).sum :=
        max_le (by omega) (by omega)
      have hsq := Nat.mul_le_mul hpos hpos
      rw [circuitSizeWithInputs_gate] at hpos ⊢
      nlinarith

private theorem circuit_size_properizeBottomOr_le (gs : List UnboundedFanInFormula) :
    ufiFormulaCircuitSize (properizeBottomOr gs) ≤
      3 * (circuitSizeWithInputs (orGate gs) *
        circuitSizeWithInputs (orGate gs)) := by
  have hpos := circuitSizeWithInputs_pos (orGate gs)
  cases hoc : orClauses gs with
  | none =>
      simp only [properizeBottomOr, hoc, ufiFormulaCircuitSize]
      nlinarith
  | some cs =>
      rw [show properizeBottomOr gs = properizeDNF (dnfFromClauses cs) by
        simp [properizeBottomOr, hoc]]
      have hc := orClauses_length_le_circuitSizeWithInputs gs cs hoc
      have hp := properizeDNF_circuit_size_le (dnfFromClauses cs)
      rw [dnfSize_dnfFromClauses] at hp
      have hm : max 2 cs.length ≤ 2 + (gs.map circuitSizeWithInputs).sum :=
        max_le (by omega) (by omega)
      have hsq := Nat.mul_le_mul hpos hpos
      rw [circuitSizeWithInputs_orGate] at hpos ⊢
      nlinarith

mutual
theorem circuit_size_properizeTree_le (lvl : Nat) (f : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (properizeTree lvl f) ≤
      3 * (circuitSizeWithInputs f * circuitSizeWithInputs f) := by
  cases f with
  | inputGate i b => simp [properizeTree, circuitSizeWithInputs, ufiFormulaCircuitSize,
      ufiCollectInputIndices]
  | constant c l => simp [properizeTree, circuitSizeWithInputs, ufiFormulaCircuitSize,
      ufiCollectInputIndices]
  | notGate g =>
      simp only [properizeTree]
      have hp := circuitSizeWithInputs_pos (notGate g)
      have hle : ufiFormulaCircuitSize g + 1 ≤ circuitSizeWithInputs (notGate g) := by
        have hg := circuitSizeWithInputs_eq_size_add_inputs g
        simp only [circuitSizeWithInputs]
        omega
      have hsq := Nat.mul_le_mul hp hp
      simp only [ufiFormulaCircuitSize]
      nlinarith
  | andGate gs =>
      by_cases hc : lvl ≤ 2
      · simp only [properizeTree, if_pos hc]
        exact circuit_size_properizeBottomAnd_le gs
      · simp only [properizeTree, if_neg hc, ufiFormulaCircuitSize]
        have htail := circuit_size_properizeTreeList_le (lvl - 1) gs
        rw [circuitSizeWithInputs_gate]
        set S := (gs.map circuitSizeWithInputs).sum
        nlinarith
  | orGate gs =>
      by_cases hc : lvl ≤ 2
      · simp only [properizeTree, if_pos hc]
        exact circuit_size_properizeBottomOr_le gs
      · simp only [properizeTree, if_neg hc, ufiFormulaCircuitSize]
        have htail := circuit_size_properizeTreeList_le (lvl - 1) gs
        rw [circuitSizeWithInputs_orGate]
        set S := (gs.map circuitSizeWithInputs).sum
        nlinarith

theorem circuit_size_properizeTreeList_le (lvl : Nat)
    (gs : List UnboundedFanInFormula) :
    ((properizeTreeList lvl gs).map ufiFormulaCircuitSize).sum ≤
      3 * ((gs.map circuitSizeWithInputs).sum *
        (gs.map circuitSizeWithInputs).sum) := by
  cases gs with
  | nil => simp [properizeTreeList]
  | cons g gs =>
      simp only [properizeTreeList, List.map_cons, List.sum_cons]
      have hhead := circuit_size_properizeTree_le lvl g
      have htail := circuit_size_properizeTreeList_le lvl gs
      have hpos := circuitSizeWithInputs_pos g
      set a := circuitSizeWithInputs g
      set S := (gs.map circuitSizeWithInputs).sum
      nlinarith
end

theorem properizeTree_circuit_size_le (lvl : Nat) (f : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (properizeTree lvl f) ≤
      3 * ((ufiFormulaCircuitSize f + (ufiCollectInputIndices f).length) *
        (ufiFormulaCircuitSize f + (ufiCollectInputIndices f).length)) := by
  simpa only [circuitSizeWithInputs_eq_size_add_inputs] using
    circuit_size_properizeTree_le lvl f

end Circuits.HastadParity.BottomNorm
