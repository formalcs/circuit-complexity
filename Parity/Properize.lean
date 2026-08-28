/-
  Properize: turn a narrow DNF/CNF into a *proper* one (clauses nonempty,
  per-clause variables Nodup) while preserving eval.  Works at the
  pair-clause level (`List (Nat × Bool)`) then bridges to formulas.

  Supplies proper splice bases for the iterated-switching argument in
  `Parity/HastadParityProof/DepthReduction.lean`. Factored out into its own
  file to contain the size of the main proof file.

  Master theorems delivered (both polarities):
  * `properizeDNF` / `properizeCNF`            (the transforms)
  * `eval_properizeDNF` / `eval_properizeCNF`  (eval-preserving)
  * `isDNF_properizeDNF` / `isCNF_properizeCNF`
  * `properize_*_clauses_ne_nil`                 (clauses nonempty)
  * `properize_*_clauses_nodup`                  (per-clause vars Nodup)
  * `properize_*_vars`                           (variable index bound)
-/

import Formulas.Basic
import Formulas.Eval
import Formulas.Properties
import Formulas.ConversionDepth
import Formulas.CnfDnf.CnfDnfBasic
import DecisionTrees.DecisionTree
import Lists.ListLemmas

namespace Circuits.HastadParity
open Circuits
open Circuits.CnfDnf
open UnboundedFanInFormula
open DecisionTrees

namespace ProperizeProto

/- Pair-level characterizations of evalClause / evalClauses. -/
theorem evalClause_eq_one_iff (inputs : List Bool) (c : List (Nat × Bool)) :
    evalClause inputs c = true ↔ ∀ lit ∈ c, evalLiteral inputs lit = true := by
  induction c with
  | nil => simp [evalClause]
  | cons lit rest ih =>
    simp only [evalClause, List.mem_cons]
    cases hlit : evalLiteral inputs lit with
    | false =>
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd (h lit (Or.inl rfl)) (by rw [hlit]; simp)
    | true =>
      rw [ih]
      constructor
      · intro h lit' hlit'
        rcases hlit' with rfl | hmem
        · exact hlit
        · exact h lit' hmem
      · intro h lit' hlit'
        exact h lit' (Or.inr hlit')

theorem evalClauses_eq_one_iff (inputs : List Bool) (cs : List (List (Nat × Bool))) :
    evalClauses inputs cs = true ↔ ∃ c ∈ cs, evalClause inputs c = true := by
  induction cs with
  | nil => simp [evalClauses]
  | cons c rest ih =>
    simp only [evalClauses, List.mem_cons]
    cases hc : evalClause inputs c with
    | true =>
      constructor
      · intro _; exact ⟨c, Or.inl rfl, hc⟩
      · intro _; rfl
    | false =>
      rw [ih]
      constructor
      · rintro ⟨c', hc', hev⟩; exact ⟨c', Or.inr hc', hev⟩
      · rintro ⟨c', rfl | hmem, hev⟩
        · rw [hc] at hev; exact absurd hev (by simp)
        · exact ⟨c', hmem, hev⟩

theorem evalClause_eq_zero_iff (inputs : List Bool) (c : List (Nat × Bool)) :
    evalClause inputs c = false ↔ ∃ lit ∈ c, evalLiteral inputs lit = false := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have : evalClause inputs c = true := by
      rw [evalClause_eq_one_iff]
      intro lit hlit
      cases hev : evalLiteral inputs lit with
      | true => rfl
      | false => exact absurd hev (by have := hcon lit hlit; simpa using this)
    rw [this] at h; exact absurd h (by simp)
  · rintro ⟨lit, hlit, hev⟩
    by_contra hcon
    have hone : evalClause inputs c = true := by
      cases h : evalClause inputs c with
      | true => rfl
      | false => exact absurd h hcon
    rw [evalClause_eq_one_iff] at hone
    have := hone lit hlit
    rw [hev] at this; exact absurd this (by simp)

theorem bit_eq_of_one_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/- Pair-level dedup keeping last occurrence. -/
def pairLevelDedup : List (Nat × Bool) → List (Nat × Bool)
  | [] => []
  | x :: xs => if x ∈ pairLevelDedup xs then pairLevelDedup xs else x :: pairLevelDedup xs

theorem mem_pdedup (a : Nat × Bool) (l : List (Nat × Bool)) :
    a ∈ pairLevelDedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [pairLevelDedup]
  | cons x xs ih =>
    by_cases hx : x ∈ pairLevelDedup xs
    · rw [pairLevelDedup, if_pos hx, List.mem_cons, ih]
      constructor
      · intro h; exact Or.inr h
      · rintro (rfl | h)
        · exact ih.mp hx
        · exact h
    · rw [pairLevelDedup, if_neg hx, List.mem_cons, List.mem_cons, ih]

theorem pdedup_nodup (l : List (Nat × Bool)) : (pairLevelDedup l).Nodup := by
  induction l with
  | nil => simp [pairLevelDedup]
  | cons x xs ih =>
    by_cases hx : x ∈ pairLevelDedup xs
    · rw [pairLevelDedup, if_pos hx]; exact ih
    · rw [pairLevelDedup, if_neg hx]; exact List.nodup_cons.mpr ⟨hx, ih⟩

theorem evalClause_pdedup (inputs : List Bool) (c : List (Nat × Bool)) :
    evalClause inputs (pairLevelDedup c) = evalClause inputs c := by
  apply bit_eq_of_one_iff
  rw [evalClause_eq_one_iff, evalClause_eq_one_iff]
  constructor
  · intro h lit hlit; exact h lit ((mem_pdedup lit c).mpr hlit)
  · intro h lit hlit; exact h lit ((mem_pdedup lit c).mp hlit)

/- Conflict clause evaluates to zero. -/
theorem evalLiteral_opp (inputs : List Bool) (v : Nat) (hv : v < inputs.length) :
    evalLiteral inputs (v, true) = Bool.not (evalLiteral inputs (v, false)) := by
  simp only [evalLiteral]
  rw [List.getElem?_eq_getElem hv]

theorem evalClause_zero_of_conflict (inputs : List Bool) (c : List (Nat × Bool)) (v : Nat)
    (ht : (v, true) ∈ c) (hf : (v, false) ∈ c) :
    evalClause inputs c = false := by
  rw [evalClause_eq_zero_iff]
  cases hv : inputs[v]? with
  | none =>
      exact ⟨(v, false), hf, by simp [evalLiteral, hv]⟩
  | some b =>
      cases b with
      | false => exact ⟨(v, false), hf, by simp [evalLiteral, hv]⟩
      | true => exact ⟨(v, true), ht, by simp [evalLiteral, hv]⟩

theorem conflict_of_pairs_nodup_vars_not_nodup (c : List (Nat × Bool))
    (hnd : c.Nodup) (hvars : ¬ (c.map Prod.fst).Nodup) :
    ∃ v, (v, true) ∈ c ∧ (v, false) ∈ c := by
  induction c with
  | nil => simp at hvars
  | cons p ps ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hp, hps⟩ := hnd
    rw [List.map_cons, List.nodup_cons] at hvars
    by_cases hin : p.1 ∈ ps.map Prod.fst
    · rw [List.mem_map] at hin
      obtain ⟨q, hq, hq1⟩ := hin
      have hqp : q ≠ p := fun h => hp (h ▸ hq)
      have hsnd : q.2 ≠ p.2 := fun h => hqp (Prod.ext hq1 h)
      cases hp2 : p.2 with
      | true =>
        have hq2 : q.2 = false := by
          cases hqv : q.2 with
          | false => rfl
          | true => exact absurd (hqv.trans hp2.symm) hsnd
        refine ⟨p.1, ?_, ?_⟩
        · have : p = (p.1, true) := by rw [← hp2]
          rw [← this]; exact List.mem_cons_self
        · have : q = (p.1, false) := by rw [← hq1, ← hq2]
          rw [← this]; exact List.mem_cons_of_mem p hq
      | false =>
        have hq2 : q.2 = true := by
          cases hqv : q.2 with
          | true => rfl
          | false => exact absurd (hqv.trans hp2.symm) hsnd
        refine ⟨p.1, ?_, ?_⟩
        · have : q = (p.1, true) := by rw [← hq1, ← hq2]
          rw [← this]; exact List.mem_cons_of_mem p hq
        · have : p = (p.1, false) := by rw [← hp2]
          rw [← this]; exact List.mem_cons_self
    · have hps_not : ¬ (ps.map Prod.fst).Nodup := by
        intro hcon; exact hvars ⟨hin, hcon⟩
      obtain ⟨v, ht, hf⟩ := ih hps hps_not
      exact ⟨v, List.mem_cons_of_mem p ht, List.mem_cons_of_mem p hf⟩

theorem evalClause_zero_of_pdedup_vars_not_nodup (inputs : List Bool) (c : List (Nat × Bool))
    (h : ¬ ((pairLevelDedup c).map Prod.fst).Nodup) :
    evalClause inputs c = false := by
  obtain ⟨v, ht, hf⟩ := conflict_of_pairs_nodup_vars_not_nodup (pairLevelDedup c)
                                                               (pdedup_nodup c)
                                                               h
  rw [← evalClause_pdedup]
  exact evalClause_zero_of_conflict inputs (pairLevelDedup c) v ht hf

def properizeClauses (clauses : List (List (Nat × Bool))) : List (List (Nat × Bool)) :=
  (clauses.map pairLevelDedup).filter (fun c => decide ((c.map Prod.fst).Nodup))

theorem properizeClauses_nodup_vars (cs : List (List (Nat × Bool)))
    (c : List (Nat × Bool)) (hc : c ∈ properizeClauses cs) :
    (c.map Prod.fst).Nodup := by
  rw [properizeClauses, List.mem_filter] at hc
  exact of_decide_eq_true hc.2

theorem evalClauses_properizeClauses (inputs : List Bool) (cs : List (List (Nat × Bool))) :
    evalClauses inputs (properizeClauses cs) = evalClauses inputs cs := by
  apply bit_eq_of_one_iff
  rw [evalClauses_eq_one_iff, evalClauses_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hev⟩
    rw [properizeClauses, List.mem_filter, List.mem_map] at hc
    obtain ⟨⟨c', hc', rfl⟩, _⟩ := hc
    exact ⟨c', hc', by rw [← evalClause_pdedup]; exact hev⟩
  · rintro ⟨c, hc, hev⟩
    refine ⟨pairLevelDedup c, ?_, by rw [evalClause_pdedup]; exact hev⟩
    rw [properizeClauses, List.mem_filter, List.mem_map]
    refine ⟨⟨c, hc, rfl⟩, ?_⟩
    rw [decide_eq_true_eq]
    by_contra hnd
    have : evalClause inputs c = false :=
      evalClause_zero_of_pdedup_vars_not_nodup inputs c hnd
    rw [this] at hev; exact absurd hev (by simp)

/- Formula bridge: clauses ↔ DNF formula. -/
def litToInput : Nat × Bool → UnboundedFanInFormula := fun p => inputGate p.1 p.2
def clauseToAnd (c : List (Nat × Bool)) : UnboundedFanInFormula := andGate (c.map litToInput)
def dnfFromClauses (cs : List (List (Nat × Bool))) : UnboundedFanInFormula :=
  orGate (cs.map clauseToAnd)

theorem extract_clauseToAnd (c : List (Nat × Bool)) :
    extractAndLiterals (clauseToAnd c) = c := by
  simp only [clauseToAnd, extractAndLiterals]
  induction c with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.filterMap_cons, litToInput]
    rw [ih]

theorem dnfClauses_eq_map_extract (gates : List UnboundedFanInFormula) :
    dnfClauses (orGate gates) = gates.map extractAndLiterals := by
  simp only [dnfClauses]
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

theorem isDNF_dnfFromClauses (cs : List (List (Nat × Bool))) :
    isDNF (dnfFromClauses cs) = true := by
  simp only [dnfFromClauses, isDNF, List.all_map, List.all_eq_true]
  intro c _
  simp only [Function.comp, clauseToAnd, isAndOfInputsOnly, List.all_map,
    List.all_eq_true]
  intro p _
  simp [litToInput, isInput]

theorem eval_dnfFromClauses (inputs : List Bool) (cs : List (List (Nat × Bool))) :
    ufiFormulaEval (dnfFromClauses cs) inputs = evalClauses inputs cs := by
  have hall : (cs.map clauseToAnd).all isAndOfInputsOnly = true := by
    simp only [List.all_map, List.all_eq_true]
    intro c _
    simp only [Function.comp, clauseToAnd, isAndOfInputsOnly, List.all_map,
      List.all_eq_true]
    intro p _; simp [litToInput, isInput]
  have h := evalClauses_eq_dnf inputs (cs.map clauseToAnd) hall
  rw [List.map_map] at h
  have hmap : (cs.map (extractAndLiterals ∘ clauseToAnd)) = cs := by
    rw [show (extractAndLiterals ∘ clauseToAnd) = id from
      funext (fun c => extract_clauseToAnd c)]
    exact List.map_id cs
  rw [hmap] at h
  rw [dnfFromClauses]; exact h.symm

theorem dnfClauses_dnfFromClauses (cs : List (List (Nat × Bool))) :
    dnfClauses (dnfFromClauses cs) = cs := by
  rw [dnfFromClauses, dnfClauses_eq_map_extract, List.map_map]
  rw [show (extractAndLiterals ∘ clauseToAnd) = id from
    funext (fun c => extract_clauseToAnd c)]
  exact List.map_id cs

theorem eval_eq_evalClauses_of_isDNF (g : UnboundedFanInFormula) (h : isDNF g = true)
    (inputs : List Bool) :
    ufiFormulaEval g inputs = evalClauses inputs (dnfClauses g) := by
  cases g with
  | orGate gates =>
    have hall : gates.all isAndOfInputsOnly = true := by
      simpa only [isDNF] using h
    rw [dnfClauses_eq_map_extract]
    exact (evalClauses_eq_dnf inputs gates hall).symm
  | _ => simp [isDNF] at h

/- Variable index plumbing. -/
theorem ufi_collect_clauseToAnd (c : List (Nat × Bool)) :
    ufiCollectInputIndices (clauseToAnd c) = c.map Prod.fst := by
  simp only [clauseToAnd, ufiCollectInputIndices]
  induction c with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatMap_cons, litToInput, ufiCollectInputIndices]
    rw [ih]; rfl

theorem ufi_collect_dnfFromClauses (cs : List (List (Nat × Bool))) :
    ufiCollectInputIndices (dnfFromClauses cs) = cs.flatMap (fun c => c.map Prod.fst) := by
  simp only [dnfFromClauses, ufiCollectInputIndices, List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  exact ufi_collect_clauseToAnd c

theorem dnfClauses_var_mem (g : UnboundedFanInFormula) (h : isDNF g = true)
    (c : List (Nat × Bool)) (hc : c ∈ dnfClauses g) (p : Nat × Bool) (hp : p ∈ c) :
    p.1 ∈ ufiCollectInputIndices g := by
  cases g with
  | orGate gates =>
    rw [dnfClauses_eq_map_extract, List.mem_map] at hc
    obtain ⟨gate, hgate, rfl⟩ := hc
    simp only [extractAndLiterals] at hp
    cases gate with
    | andGate lits =>
      rw [List.mem_filterMap] at hp
      obtain ⟨lit, hlit, hsome⟩ := hp
      cases lit with
      | inputGate i b =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨andGate lits, hgate, by
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨inputGate i b, hlit, by simp [ufiCollectInputIndices]⟩⟩
      | _ => simp at hsome
    | _ => simp only [List.mem_nil_iff] at hp
  | _ => simp [isDNF] at h

/- Top-level properize (DNF). -/
def properizeDNF (g : UnboundedFanInFormula) : UnboundedFanInFormula :=
  let cs := properizeClauses (dnfClauses g)
  if [] ∈ cs then dnfFromClauses [[(0, true)], [(0, false)]]
  else dnfFromClauses cs

theorem evalClauses_taut (inputs : List Bool) (hpos : 0 < inputs.length) :
    evalClauses inputs [[(0, true)], [(0, false)]] = true := by
  rw [evalClauses_eq_one_iff]
  rcases hb : evalLiteral inputs (0, false) with _ | _
  · refine ⟨[(0, true)], by simp, ?_⟩
    rw [evalClause_eq_one_iff]; intro lit hlit
    simp only [List.mem_singleton] at hlit; subst hlit
    rw [evalLiteral_opp inputs 0 hpos, hb]; rfl
  · refine ⟨[(0, false)], by simp, ?_⟩
    rw [evalClause_eq_one_iff]; intro lit hlit
    simp only [List.mem_singleton] at hlit; subst hlit; exact hb

theorem eval_properizeDNF (g : UnboundedFanInFormula) (h : isDNF g = true)
    (inputs : List Bool) (hpos : 0 < inputs.length) :
    ufiFormulaEval (properizeDNF g) inputs = ufiFormulaEval g inputs := by
  rw [eval_eq_evalClauses_of_isDNF g h]
  simp only [properizeDNF]
  set cs := properizeClauses (dnfClauses g) with hcs
  by_cases hmem : [] ∈ cs
  · rw [if_pos hmem, eval_dnfFromClauses, evalClauses_taut inputs hpos]
    rw [← evalClauses_properizeClauses, ← hcs]
    symm
    rw [evalClauses_eq_one_iff]
    exact ⟨[], hmem, rfl⟩
  · rw [if_neg hmem, eval_dnfFromClauses, hcs, evalClauses_properizeClauses]

theorem isDNF_properizeDNF (g : UnboundedFanInFormula) :
    isDNF (properizeDNF g) = true := by
  simp only [properizeDNF]
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem]; exact isDNF_dnfFromClauses _
  · rw [if_neg hmem]; exact isDNF_dnfFromClauses _

theorem properizeDNF_clauses_ne_nil (g : UnboundedFanInFormula)
    (c : List (Nat × Bool)) (hc : c ∈ dnfClauses (properizeDNF g)) : c ≠ [] := by
  simp only [properizeDNF] at hc
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem, dnfClauses_dnfFromClauses] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  · rw [if_neg hmem, dnfClauses_dnfFromClauses] at hc
    intro hnil; subst hnil; exact hmem hc

theorem properizeDNF_clauses_nodup (g : UnboundedFanInFormula)
    (c : List (Nat × Bool)) (hc : c ∈ dnfClauses (properizeDNF g)) :
    (c.map Prod.fst).Nodup := by
  simp only [properizeDNF] at hc
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem, dnfClauses_dnfFromClauses] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  · rw [if_neg hmem, dnfClauses_dnfFromClauses] at hc
    exact properizeClauses_nodup_vars _ c hc

theorem properizeDNF_vars (g : UnboundedFanInFormula) (h : isDNF g = true) (n : Nat)
    (h_n : 0 < n) (hbound : ∀ i ∈ ufiCollectInputIndices g, i < n)
    (i : Nat) (hi : i ∈ ufiCollectInputIndices (properizeDNF g)) : i < n := by
  simp only [properizeDNF] at hi
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem, ufi_collect_dnfFromClauses] at hi
    simp only [List.mem_flatMap, List.mem_cons] at hi
    obtain ⟨c, hcmem, hic⟩ := hi
    rcases hcmem with rfl | rfl | hfalse <;> simp_all
  · rw [if_neg hmem, ufi_collect_dnfFromClauses] at hi
    simp only [List.mem_flatMap] at hi
    obtain ⟨c, hcmem, hic⟩ := hi
    rw [List.mem_map] at hic
    obtain ⟨p, hp, rfl⟩ := hic
    rw [properizeClauses, List.mem_filter, List.mem_map] at hcmem
    obtain ⟨⟨c0, hc0, rfl⟩, _⟩ := hcmem
    have hp0 : p ∈ c0 := (mem_pdedup p c0).mp hp
    exact hbound p.1 (dnfClauses_var_mem g h c0 hc0 p hp0)

/- CNF (conjunction-of-disjunctions) dual. -/
def evalDisj (inputs : List Bool) : List (Nat × Bool) → Bool
  | [] => false
  | lit :: rest =>
    match evalLiteral inputs lit with
    | true => true
    | false => evalDisj inputs rest

def evalConj (inputs : List Bool) : List (List (Nat × Bool)) → Bool
  | [] => true
  | c :: rest =>
    match evalDisj inputs c with
    | false => false
    | true => evalConj inputs rest

theorem evalDisj_eq_zero_iff (inputs : List Bool) (c : List (Nat × Bool)) :
    evalDisj inputs c = false ↔ ∀ lit ∈ c, evalLiteral inputs lit = false := by
  induction c with
  | nil => simp [evalDisj]
  | cons lit rest ih =>
    simp only [evalDisj, List.mem_cons]
    cases hlit : evalLiteral inputs lit with
    | true =>
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd (h lit (Or.inl rfl)) (by rw [hlit]; simp)
    | false =>
      rw [ih]
      constructor
      · intro h lit' hlit'
        rcases hlit' with rfl | hmem
        · exact hlit
        · exact h lit' hmem
      · intro h lit' hlit'
        exact h lit' (Or.inr hlit')

theorem evalDisj_eq_one_iff (inputs : List Bool) (c : List (Nat × Bool)) :
    evalDisj inputs c = true ↔ ∃ lit ∈ c, evalLiteral inputs lit = true := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have : evalDisj inputs c = false := by
      rw [evalDisj_eq_zero_iff]
      intro lit hlit
      cases hev : evalLiteral inputs lit with
      | false => rfl
      | true => exact absurd hev (by have := hcon lit hlit; simpa using this)
    rw [this] at h; exact absurd h (by simp)
  · rintro ⟨lit, hlit, hev⟩
    by_contra hcon
    have hzero : evalDisj inputs c = false := by
      cases h : evalDisj inputs c with
      | false => rfl
      | true => exact absurd h hcon
    rw [evalDisj_eq_zero_iff] at hzero
    have := hzero lit hlit
    rw [hev] at this; exact absurd this (by simp)

theorem evalConj_eq_one_iff (inputs : List Bool) (cs : List (List (Nat × Bool))) :
    evalConj inputs cs = true ↔ ∀ c ∈ cs, evalDisj inputs c = true := by
  induction cs with
  | nil => simp [evalConj]
  | cons c rest ih =>
    simp only [evalConj, List.mem_cons]
    cases hc : evalDisj inputs c with
    | false =>
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd (h c (Or.inl rfl)) (by rw [hc]; simp)
    | true =>
      rw [ih]
      constructor
      · intro h c' hc'
        rcases hc' with rfl | hmem
        · exact hc
        · exact h c' hmem
      · intro h c' hc'
        exact h c' (Or.inr hc')

theorem evalConj_eq_zero_iff (inputs : List Bool) (cs : List (List (Nat × Bool))) :
    evalConj inputs cs = false ↔ ∃ c ∈ cs, evalDisj inputs c = false := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have : evalConj inputs cs = true := by
      rw [evalConj_eq_one_iff]
      intro c hc
      cases hev : evalDisj inputs c with
      | true => rfl
      | false => exact absurd hev (by have := hcon c hc; simpa using this)
    rw [this] at h; exact absurd h (by simp)
  · rintro ⟨c, hc, hev⟩
    by_contra hcon
    have hone : evalConj inputs cs = true := by
      cases h : evalConj inputs cs with
      | true => rfl
      | false => exact absurd h hcon
    rw [evalConj_eq_one_iff] at hone
    have := hone c hc
    rw [hev] at this; exact absurd this (by simp)

theorem evalDisj_pdedup (inputs : List Bool) (c : List (Nat × Bool)) :
    evalDisj inputs (pairLevelDedup c) = evalDisj inputs c := by
  apply bit_eq_of_one_iff
  rw [evalDisj_eq_one_iff, evalDisj_eq_one_iff]
  constructor
  · rintro ⟨lit, hlit, hev⟩; exact ⟨lit, (mem_pdedup lit c).mp hlit, hev⟩
  · rintro ⟨lit, hlit, hev⟩; exact ⟨lit, (mem_pdedup lit c).mpr hlit, hev⟩

theorem evalDisj_one_of_conflict (inputs : List Bool) (c : List (Nat × Bool)) (v : Nat)
    (hv : v < inputs.length) (ht : (v, true) ∈ c) (hf : (v, false) ∈ c) :
    evalDisj inputs c = true := by
  rw [evalDisj_eq_one_iff]
  rcases hb : evalLiteral inputs (v, false) with _ | _
  · refine ⟨(v, true), ht, ?_⟩
    rw [evalLiteral_opp inputs v hv, hb]; rfl
  · exact ⟨(v, false), hf, hb⟩

theorem evalDisj_one_of_pdedup_vars_not_nodup (inputs : List Bool) (c : List (Nat × Bool))
    (hbound : ∀ p ∈ c, p.1 < inputs.length)
    (h : ¬ ((pairLevelDedup c).map Prod.fst).Nodup) :
    evalDisj inputs c = true := by
  obtain ⟨v, ht, hf⟩ := conflict_of_pairs_nodup_vars_not_nodup (pairLevelDedup c)
                                                               (pdedup_nodup c)
                                                               h
  rw [← evalDisj_pdedup]
  exact evalDisj_one_of_conflict inputs (pairLevelDedup c) v
    (hbound (v, true) ((mem_pdedup (v, true) c).mp ht)) ht hf

theorem evalConj_properizeClauses (inputs : List Bool) (cs : List (List (Nat × Bool)))
    (hbound : ∀ c ∈ cs, ∀ p ∈ c, p.1 < inputs.length) :
    evalConj inputs (properizeClauses cs) = evalConj inputs cs := by
  apply bit_eq_of_one_iff
  rw [evalConj_eq_one_iff, evalConj_eq_one_iff]
  constructor
  · intro h c hc
    by_cases hnd : ((pairLevelDedup c).map Prod.fst).Nodup
    · have hmem : pairLevelDedup c ∈ properizeClauses cs := by
        rw [properizeClauses, List.mem_filter]
        exact ⟨List.mem_map.mpr ⟨c, hc, rfl⟩, by rw [decide_eq_true_eq]; exact hnd⟩
      rw [← evalDisj_pdedup]; exact h (pairLevelDedup c) hmem
    · exact evalDisj_one_of_pdedup_vars_not_nodup inputs c (hbound c hc) hnd
  · intro h c hc
    rw [properizeClauses, List.mem_filter, List.mem_map] at hc
    obtain ⟨⟨c', hc', rfl⟩, _⟩ := hc
    rw [evalDisj_pdedup]; exact h c' hc'

/- Formula bridge: clauses ↔ CNF formula. -/
def clauseToOr (clause : List (Nat × Bool)) : UnboundedFanInFormula :=
  orGate (clause.map litToInput)

def cnfFromClauses (clauses : List (List (Nat × Bool))) : UnboundedFanInFormula :=
  andGate (clauses.map clauseToOr)

def extractOr (gate : UnboundedFanInFormula) : List (Nat × Bool) :=
  match gate with
  | orGate lits => lits.filterMap fun lit =>
      match lit with
      | inputGate i b => some (i, b)
      | _ => none
  | _ => []

theorem extractOr_clauseToOr (c : List (Nat × Bool)) :
    extractOr (clauseToOr c) = c := by
  simp only [clauseToOr, extractOr]
  induction c with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.filterMap_cons, litToInput]
    rw [ih]

theorem cnfClauses_eq_map_extract (gates : List UnboundedFanInFormula) :
    cnfClauses (andGate gates) = gates.map extractOr := by
  simp only [cnfClauses]
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

theorem isCNF_cnfFromClauses (cs : List (List (Nat × Bool))) :
    isCNF (cnfFromClauses cs) = true := by
  simp only [cnfFromClauses, isCNF, List.all_map, List.all_eq_true]
  intro c _
  simp only [Function.comp, clauseToOr, isOrOfInputsOnly, List.all_map,
    List.all_eq_true]
  intro p _
  simp [litToInput, isInput]

theorem eval_input_eq_literal (inputs : List Bool) (p : Nat × Bool) :
    ufiFormulaEval (inputGate p.1 p.2) inputs = evalLiteral inputs p := by
  unfold evalLiteral
  unfold ufiFormulaEval
  rcases inputs[p.1]? with _ | v
  · cases p.2 <;> rfl
  · cases p.2 <;> cases v <;> rfl

theorem ite_bit_one_iff (cond : Bool) :
    (if cond then true else false) = true ↔ cond = true := by
  cases cond <;> simp

theorem eval_clauseToOr_one_iff (inputs : List Bool) (c : List (Nat × Bool)) :
    ufiFormulaEval (clauseToOr c) inputs = true
      ↔ ∃ p ∈ c, evalLiteral inputs p = true := by
  rw [clauseToOr, ufi_eval_orGate_eq_any, ite_bit_one_iff, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxone⟩
    rw [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [List.mem_map] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    refine ⟨p, hp, ?_⟩
    rw [← eval_input_eq_literal]
    simp only [litToInput] at hxone ⊢
    simpa using hxone
  · rintro ⟨p, hp, hpone⟩
    refine ⟨ufiFormulaEval (litToInput p) inputs, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨litToInput p, List.mem_map.mpr ⟨p, hp, rfl⟩, rfl⟩
    · simp only [litToInput, eval_input_eq_literal, hpone, beq_self_eq_true]

theorem eval_clauseToOr (inputs : List Bool) (c : List (Nat × Bool)) :
    ufiFormulaEval (clauseToOr c) inputs = evalDisj inputs c := by
  apply bit_eq_of_one_iff
  rw [evalDisj_eq_one_iff]
  exact eval_clauseToOr_one_iff inputs c

theorem eval_orGate_inputs_eq_disj (inputs : List Bool) (gate : UnboundedFanInFormula)
    (h : isOrOfInputsOnly gate = true) :
    ufiFormulaEval gate inputs = evalDisj inputs (extractOr gate) := by
  cases gate with
  | orGate lits =>
    simp only [isOrOfInputsOnly] at h
    apply bit_eq_of_one_iff
    rw [ufi_eval_orGate_eq_any, ite_bit_one_iff, List.any_eq_true, evalDisj_eq_one_iff]
    constructor
    · rintro ⟨x, hx, hxone⟩
      rw [List.mem_map] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      have hli : isInput l = true := List.all_eq_true.mp h l hl
      cases l with
      | inputGate i b =>
        refine ⟨(i, b), ?_, ?_⟩
        · simp only [extractOr, List.mem_filterMap]
          exact ⟨inputGate i b, hl, rfl⟩
        · rw [← eval_input_eq_literal]; simpa using hxone
      | _ => simp [isInput] at hli
    · rintro ⟨p, hpmem, hpone⟩
      simp only [extractOr, List.mem_filterMap] at hpmem
      obtain ⟨l, hl, hsome⟩ := hpmem
      cases l with
      | inputGate i b =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        refine ⟨ufiFormulaEval (inputGate i b) inputs, ?_, ?_⟩
        · rw [List.mem_map]; exact ⟨inputGate i b, hl, rfl⟩
        · have hpe : ufiFormulaEval (inputGate i b) inputs = evalLiteral inputs (i, b) :=
            eval_input_eq_literal inputs (i, b)
          simp only [hpe, hpone, beq_self_eq_true]
      | _ => simp at hsome
  | _ => simp [isOrOfInputsOnly] at h

theorem eval_andGate_eq_conj (inputs : List Bool) (gates : List UnboundedFanInFormula)
    (hall : gates.all isOrOfInputsOnly = true) :
    ufiFormulaEval (andGate gates) inputs = evalConj inputs (gates.map extractOr) := by
  apply bit_eq_of_one_iff
  rw [ufi_eval_andGate_eq_all, ite_bit_one_iff, List.all_eq_true, evalConj_eq_one_iff]
  constructor
  · intro h c hc
    rw [List.mem_map] at hc
    obtain ⟨gate, hgate, rfl⟩ := hc
    have hone := h (ufiFormulaEval gate inputs) (List.mem_map.mpr ⟨gate, hgate, rfl⟩)
    rw [beq_iff_eq] at hone
    rw [← eval_orGate_inputs_eq_disj inputs gate (List.all_eq_true.mp hall gate hgate)]
    exact hone
  · intro h x hx
    rw [List.mem_map] at hx
    obtain ⟨gate, hgate, rfl⟩ := hx
    rw [beq_iff_eq, eval_orGate_inputs_eq_disj inputs gate (List.all_eq_true.mp hall gate hgate)]
    exact h (extractOr gate) (List.mem_map.mpr ⟨gate, hgate, rfl⟩)

theorem cnfClauses_cnfFromClauses (cs : List (List (Nat × Bool))) :
    cnfClauses (cnfFromClauses cs) = cs := by
  rw [cnfFromClauses, cnfClauses_eq_map_extract, List.map_map]
  rw [show (extractOr ∘ clauseToOr) = id from
    funext (fun c => extractOr_clauseToOr c)]
  exact List.map_id cs

theorem eval_eq_evalConj_of_isCNF (g : UnboundedFanInFormula) (h : isCNF g = true)
    (inputs : List Bool) :
    ufiFormulaEval g inputs = evalConj inputs (cnfClauses g) := by
  cases g with
  | andGate gates =>
    have hall : gates.all isOrOfInputsOnly = true := by
      simpa only [isCNF] using h
    rw [cnfClauses_eq_map_extract]
    exact eval_andGate_eq_conj inputs gates hall
  | _ => simp [isCNF] at h

theorem eval_cnfFromClauses (inputs : List Bool) (cs : List (List (Nat × Bool))) :
    ufiFormulaEval (cnfFromClauses cs) inputs = evalConj inputs cs := by
  apply bit_eq_of_one_iff
  rw [cnfFromClauses, ufi_eval_andGate_eq_all, ite_bit_one_iff, List.all_eq_true,
    evalConj_eq_one_iff]
  constructor
  · intro h c hc
    have hone := h (ufiFormulaEval (clauseToOr c) inputs)
      (List.mem_map.mpr ⟨clauseToOr c, List.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩)
    rw [beq_iff_eq, eval_clauseToOr] at hone
    exact hone
  · intro h x hx
    rw [List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [List.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    rw [beq_iff_eq, eval_clauseToOr]
    exact h c hc

/- Variable index plumbing (CNF). -/
theorem ufi_collect_clauseToOr (c : List (Nat × Bool)) :
    ufiCollectInputIndices (clauseToOr c) = c.map Prod.fst := by
  simp only [clauseToOr, ufiCollectInputIndices]
  induction c with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatMap_cons, litToInput, ufiCollectInputIndices]
    rw [ih]; rfl

theorem ufi_collect_cnfFromClauses (cs : List (List (Nat × Bool))) :
    ufiCollectInputIndices (cnfFromClauses cs) = cs.flatMap (fun c => c.map Prod.fst) := by
  simp only [cnfFromClauses, ufiCollectInputIndices, List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  exact ufi_collect_clauseToOr c

theorem cnfClauses_var_mem (g : UnboundedFanInFormula) (h : isCNF g = true)
    (c : List (Nat × Bool)) (hc : c ∈ cnfClauses g) (p : Nat × Bool) (hp : p ∈ c) :
    p.1 ∈ ufiCollectInputIndices g := by
  cases g with
  | andGate gates =>
    rw [cnfClauses_eq_map_extract, List.mem_map] at hc
    obtain ⟨gate, hgate, rfl⟩ := hc
    simp only [extractOr] at hp
    cases gate with
    | orGate lits =>
      rw [List.mem_filterMap] at hp
      obtain ⟨lit, hlit, hsome⟩ := hp
      cases lit with
      | inputGate i b =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        simp only [ufiCollectInputIndices, List.mem_flatMap]
        exact ⟨orGate lits, hgate, by
          simp only [ufiCollectInputIndices, List.mem_flatMap]
          exact ⟨inputGate i b, hlit, by simp [ufiCollectInputIndices]⟩⟩
      | _ => simp at hsome
    | _ => simp only [List.mem_nil_iff] at hp
  | _ => simp [isCNF] at h

/- Top-level properize (CNF). -/
def properizeCNF (g : UnboundedFanInFormula) : UnboundedFanInFormula :=
  let cs := properizeClauses (cnfClauses g)
  if [] ∈ cs then cnfFromClauses [[(0, true)], [(0, false)]]
  else cnfFromClauses cs

theorem evalConj_contra (inputs : List Bool) (hpos : 0 < inputs.length) :
    evalConj inputs [[(0, true)], [(0, false)]] = false := by
  rw [evalConj_eq_zero_iff]
  rcases hb : evalLiteral inputs (0, false) with _ | _
  · refine ⟨[(0, false)], by simp, ?_⟩
    rw [evalDisj_eq_zero_iff]; intro lit hlit
    simp only [List.mem_singleton] at hlit; subst hlit; exact hb
  · refine ⟨[(0, true)], by simp, ?_⟩
    rw [evalDisj_eq_zero_iff]; intro lit hlit
    simp only [List.mem_singleton] at hlit; subst hlit
    rw [evalLiteral_opp inputs 0 hpos, hb]; rfl

theorem eval_properizeCNF (g : UnboundedFanInFormula) (h : isCNF g = true)
    (inputs : List Bool) (hpos : 0 < inputs.length)
    (hbound : ∀ i ∈ ufiCollectInputIndices g, i < inputs.length) :
    ufiFormulaEval (properizeCNF g) inputs = ufiFormulaEval g inputs := by
  rw [eval_eq_evalConj_of_isCNF g h]
  simp only [properizeCNF]
  set cs := properizeClauses (cnfClauses g) with hcs
  have hproper : evalConj inputs (properizeClauses (cnfClauses g)) =
      evalConj inputs (cnfClauses g) := by
    apply evalConj_properizeClauses
    intro c hc p hp
    exact hbound p.1 (cnfClauses_var_mem g h c hc p hp)
  by_cases hmem : [] ∈ cs
  · rw [if_pos hmem, eval_cnfFromClauses, evalConj_contra inputs hpos]
    rw [← hproper, ← hcs]
    symm
    rw [evalConj_eq_zero_iff]
    exact ⟨[], hmem, rfl⟩
  · rw [if_neg hmem, eval_cnfFromClauses, hcs, hproper]

theorem isCNF_properizeCNF (g : UnboundedFanInFormula) :
    isCNF (properizeCNF g) = true := by
  simp only [properizeCNF]
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem]; exact isCNF_cnfFromClauses _
  · rw [if_neg hmem]; exact isCNF_cnfFromClauses _

theorem properizeCNF_clauses_ne_nil (g : UnboundedFanInFormula)
    (c : List (Nat × Bool)) (hc : c ∈ cnfClauses (properizeCNF g)) : c ≠ [] := by
  simp only [properizeCNF] at hc
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem, cnfClauses_cnfFromClauses] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  · rw [if_neg hmem, cnfClauses_cnfFromClauses] at hc
    intro hnil; subst hnil; exact hmem hc

theorem properizeCNF_clauses_nodup (g : UnboundedFanInFormula)
    (c : List (Nat × Bool)) (hc : c ∈ cnfClauses (properizeCNF g)) :
    (c.map Prod.fst).Nodup := by
  simp only [properizeCNF] at hc
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem, cnfClauses_cnfFromClauses] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  · rw [if_neg hmem, cnfClauses_cnfFromClauses] at hc
    exact properizeClauses_nodup_vars _ c hc

theorem properizeCNF_vars (g : UnboundedFanInFormula) (h : isCNF g = true) (n : Nat)
    (h_n : 0 < n) (hbound : ∀ i ∈ ufiCollectInputIndices g, i < n)
    (i : Nat) (hi : i ∈ ufiCollectInputIndices (properizeCNF g)) : i < n := by
  simp only [properizeCNF] at hi
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem, ufi_collect_cnfFromClauses] at hi
    simp only [List.mem_flatMap, List.mem_cons] at hi
    obtain ⟨c, hcmem, hic⟩ := hi
    rcases hcmem with rfl | rfl | hfalse <;> simp_all
  · rw [if_neg hmem, ufi_collect_cnfFromClauses] at hi
    simp only [List.mem_flatMap] at hi
    obtain ⟨c, hcmem, hic⟩ := hi
    rw [List.mem_map] at hic
    obtain ⟨p, hp, rfl⟩ := hic
    rw [properizeClauses, List.mem_filter, List.mem_map] at hcmem
    obtain ⟨⟨c0, hc0, rfl⟩, _⟩ := hcmem
    have hp0 : p ∈ c0 := (mem_pdedup p c0).mp hp
    exact hbound p.1 (cnfClauses_var_mem g h c0 hc0 p hp0)

/- ### Consumer-facing bridges: package a narrow DNF/CNF (bounded variable
   indices `< m`) plus `properize_*` into a proper splice base (clauses
   nonempty, per-clause vars Nodup), with variable indices
   still `< m`, eval preserved. These feed the substitution map. -/

theorem foldr_max_lt_of_forall_lt {l : List Nat} {m : Nat} (hm : 0 < m)
    (h : ∀ i ∈ l, i < m) : (List.foldr max 0) l < m := by
  induction l with
  | nil => simpa [List.foldr_cons, List.foldr_nil] using hm
  | cons x xs ih =>
    have hx : x < m := h x List.mem_cons_self
    have hxs : (List.foldr max 0) xs < m := ih (fun i hi => h i (List.mem_cons_of_mem x hi))
    simp only [List.foldr_cons]
    exact max_lt hx hxs

theorem properize_narrow_dnf (m : Nat) (hm : 0 < m) (g : UnboundedFanInFormula)
    (hdnf : isDNF g = true) (hbnd : ufiLargestInput g < m) :
    isDNF (properizeDNF g) = true ∧
    (∀ c ∈ dnfClauses (properizeDNF g), c ≠ []) ∧
    (∀ c ∈ dnfClauses (properizeDNF g), (c.map Prod.fst).Nodup) ∧
    ufiLargestInput (properizeDNF g) < m ∧
    (∀ inputs, inputs.length = m →
      ufiFormulaEval (properizeDNF g) inputs = ufiFormulaEval g inputs) := by
  have hb : ∀ i ∈ ufiCollectInputIndices g, i < m := by
    intro i hi
    have hle : i ≤ (List.foldr max 0) (ufiCollectInputIndices g) := mem_le_foldr_max hi
    have : (List.foldr max 0) (ufiCollectInputIndices g) < m := hbnd
    omega
  refine ⟨isDNF_properizeDNF g, properizeDNF_clauses_ne_nil g,
    properizeDNF_clauses_nodup g, ?_, fun inputs hlen =>
      eval_properizeDNF g hdnf inputs (by omega)⟩
  unfold ufiLargestInput
  exact foldr_max_lt_of_forall_lt hm (fun i hi => properizeDNF_vars g hdnf m hm hb i hi)

theorem properize_narrow_cnf (m : Nat) (hm : 0 < m) (g : UnboundedFanInFormula)
    (hcnf : isCNF g = true) (hbnd : ufiLargestInput g < m) :
    isCNF (properizeCNF g) = true ∧
    (∀ c ∈ cnfClauses (properizeCNF g), c ≠ []) ∧
    (∀ c ∈ cnfClauses (properizeCNF g), (c.map Prod.fst).Nodup) ∧
    ufiLargestInput (properizeCNF g) < m ∧
    (∀ inputs, inputs.length = m →
      ufiFormulaEval (properizeCNF g) inputs = ufiFormulaEval g inputs) := by
  have hb : ∀ i ∈ ufiCollectInputIndices g, i < m := by
    intro i hi
    have hle : i ≤ (List.foldr max 0) (ufiCollectInputIndices g) := mem_le_foldr_max hi
    have : (List.foldr max 0) (ufiCollectInputIndices g) < m := hbnd
    omega
  refine ⟨isCNF_properizeCNF g, properizeCNF_clauses_ne_nil g,
    properizeCNF_clauses_nodup g, ?_, fun inputs hlen =>
      eval_properizeCNF g hcnf inputs (by omega) (by simpa [hlen] using hb)⟩
  unfold ufiLargestInput
  exact foldr_max_lt_of_forall_lt hm (fun i hi => properizeCNF_vars g hcnf m hm hb i hi)

/- ===================================================================== -/
/- Width preservation: properize does not increase clause width (beyond  -/
/- the width-1 tautology/contradiction floor).  Feeds the bottom-fan-in  -/
/- invariant `HasBottomFanInLE` in the iterated-switching argument.       -/
/- ===================================================================== -/

/- pdedup shortens lists. -/
theorem pdedup_length_le (l : List (Nat × Bool)) : (pairLevelDedup l).length ≤ l.length := by
  induction l with
  | nil => simp [pairLevelDedup]
  | cons x xs ih =>
    by_cases hx : x ∈ pairLevelDedup xs
    · rw [pairLevelDedup, if_pos hx, List.length_cons]; omega
    · rw [pairLevelDedup, if_neg hx]; simp only [List.length_cons]; omega

/- `filterMap` length is preserved when the function always returns `some`. -/
theorem length_filterMap_all_some {α β : Type*} (f : α → Option β) (l : List α)
    (h : ∀ a ∈ l, (f a).isSome) : (l.filterMap f).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    have hx := h x List.mem_cons_self
    cases hf : f x with
    | none => rw [hf] at hx; simp at hx
    | some b =>
      simp only [List.length_cons]
      rw [ih (fun a ha => h a (List.mem_cons_of_mem x ha))]

/- `dnfWidth` of `dnfFromClauses` = `foldl max` over clause lengths. -/
theorem dnfWidth_dnfFromClauses (cs : List (List (Nat × Bool))) :
    dnfWidth (dnfFromClauses cs) = (cs.map (fun c => c.length)).foldl max 0 := by
  simp only [dnfFromClauses, dnfWidth, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, clauseToAnd, List.length_map]

/- For a genuine DNF, `dnfWidth` equals the `foldl max` over extracted clause lengths. -/
theorem dnfWidth_eq_clauses_foldl (g : UnboundedFanInFormula) (h : isDNF g = true) :
    dnfWidth g = (dnfClauses g |>.map (fun c => c.length)).foldl max 0 := by
  cases g with
  | orGate gates =>
    simp only [dnfWidth, dnfClauses, List.map_map]
    congr 1
    apply List.map_congr_left
    intro gate hgate
    simp only [isDNF, List.all_eq_true] at h
    have hgi := h gate hgate
    cases gate with
    | andGate lits =>
      simp only [Function.comp]
      simp only [isAndOfInputsOnly, List.all_eq_true] at hgi
      rw [length_filterMap_all_some]
      intro lit hlit
      have := hgi lit hlit
      cases lit with
      | inputGate i b => simp
      | _ => simp [isInput] at this
    | _ => simp [isAndOfInputsOnly] at hgi
  | _ => simp [isDNF] at h

/- Every clause of `properizeClauses cs` is `pdedup c'` for some `c' ∈ cs`, hence
   has length `≤` the `foldl max` clause length of `cs`. -/
theorem properizeClauses_mem_length_le (cs : List (List (Nat × Bool)))
    (c : List (Nat × Bool)) (hc : c ∈ properizeClauses cs) :
    c.length ≤ (cs.map (fun c => c.length)).foldl max 0 := by
  rw [properizeClauses, List.mem_filter, List.mem_map] at hc
  obtain ⟨⟨c', hc', rfl⟩, _⟩ := hc
  have h1 : (pairLevelDedup c').length ≤ c'.length := pdedup_length_le c'
  have h2 : c'.length ≤ (cs.map (fun c => c.length)).foldl max 0 :=
    Lists.ListLemmas.mem_le_foldl_max (List.mem_map_of_mem hc')
  omega

/- Properize does not increase DNF width (beyond the width-1 tautology floor). -/
theorem properizeDNF_width_le (g : UnboundedFanInFormula) (h : isDNF g = true) :
    dnfWidth (properizeDNF g) ≤ max 1 (dnfWidth g) := by
  simp only [properizeDNF]
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem, dnfWidth_dnfFromClauses]
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      List.foldl_cons, List.foldl_nil]
    omega
  · rw [if_neg hmem, dnfWidth_dnfFromClauses]
    apply Lists.ListLemmas.foldl_max_le_of_forall
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hle := properizeClauses_mem_length_le (dnfClauses g) c hc
    rw [← dnfWidth_eq_clauses_foldl g h] at hle
    omega

/- `cnfWidth` of `cnfFromClauses` = `foldl max` over clause lengths. -/
theorem cnfWidth_cnfFromClauses (cs : List (List (Nat × Bool))) :
    cnfWidth (cnfFromClauses cs) = (cs.map (fun c => c.length)).foldl max 0 := by
  simp only [cnfFromClauses, cnfWidth, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, clauseToOr, List.length_map]

/- For a genuine CNF, `cnfWidth` equals the `foldl max` over extracted clause lengths. -/
theorem cnfWidth_eq_clauses_foldl (g : UnboundedFanInFormula) (h : isCNF g = true) :
    cnfWidth g = (cnfClauses g |>.map (fun c => c.length)).foldl max 0 := by
  cases g with
  | andGate gates =>
    simp only [cnfWidth, cnfClauses, List.map_map]
    congr 1
    apply List.map_congr_left
    intro gate hgate
    simp only [isCNF, List.all_eq_true] at h
    have hgi := h gate hgate
    cases gate with
    | orGate lits =>
      simp only [Function.comp]
      simp only [isOrOfInputsOnly, List.all_eq_true] at hgi
      rw [length_filterMap_all_some]
      intro lit hlit
      have := hgi lit hlit
      cases lit with
      | inputGate i b => simp
      | _ => simp [isInput] at this
    | _ => simp [isOrOfInputsOnly] at hgi
  | _ => simp [isCNF] at h

/- Properize does not increase CNF width (beyond the width-1 contradiction floor). -/
theorem properizeCNF_width_le (g : UnboundedFanInFormula) (h : isCNF g = true) :
    cnfWidth (properizeCNF g) ≤ max 1 (cnfWidth g) := by
  simp only [properizeCNF]
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem, cnfWidth_cnfFromClauses]
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      List.foldl_cons, List.foldl_nil]
    omega
  · rw [if_neg hmem, cnfWidth_cnfFromClauses]
    apply Lists.ListLemmas.foldl_max_le_of_forall
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hle := properizeClauses_mem_length_le (cnfClauses g) c hc
    rw [← cnfWidth_eq_clauses_foldl g h] at hle
    omega

/- ===================================================================== -/
/- Arithmetic helpers and direct circuit-size/input-occurrence bounds for -/
/- the properization stage.                                              -/
/- ===================================================================== -/

/- Sum of a constant-`1` map is the length. -/
theorem sum_map_one {α : Type*} (l : List α) :
    (l.map (fun _ => (1 : Nat))).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

/- If every element of a `Nat` list is `≤ n`, the sum is `≤ length * n`. -/

/- Clause count of `cnfFromClauses`/`dnfFromClauses`. -/
theorem cnfSize_cnfFromClauses (cs : List (List (Nat × Bool))) :
    cnfSize (cnfFromClauses cs) = cs.length := by
  simp only [cnfFromClauses, cnfSize, List.length_map]

theorem dnfSize_dnfFromClauses (cs : List (List (Nat × Bool))) :
    dnfSize (dnfFromClauses cs) = cs.length := by
  simp only [dnfFromClauses, dnfSize, List.length_map]

theorem circuit_size_cnfFromClauses (cs : List (List (Nat × Bool))) :
    ufiFormulaCircuitSize (cnfFromClauses cs) = 1 + cs.length := by
  have hclause : ∀ c, ufiFormulaCircuitSize (clauseToOr c) = 1 := by
    intro c
    simp only [clauseToOr, ufiFormulaCircuitSize]
    have hmap : (c.map litToInput).map ufiFormulaCircuitSize = c.map (fun _ => 0) := by
      rw [List.map_map]
      exact List.map_congr_left (fun ⟨i, b⟩ _ => by
        simp [litToInput, ufiFormulaCircuitSize])
    rw [hmap]
    simp
  simp only [cnfFromClauses, ufiFormulaCircuitSize, List.map_map]
  have hmap : cs.map (ufiFormulaCircuitSize ∘ clauseToOr) = cs.map (fun _ => 1) :=
    List.map_congr_left (fun c _ => hclause c)
  rw [hmap, sum_map_one]
  omega

theorem circuit_size_dnfFromClauses (cs : List (List (Nat × Bool))) :
    ufiFormulaCircuitSize (dnfFromClauses cs) = 1 + cs.length := by
  have hclause : ∀ c, ufiFormulaCircuitSize (clauseToAnd c) = 1 := by
    intro c
    simp only [clauseToAnd, ufiFormulaCircuitSize]
    have hmap : (c.map litToInput).map ufiFormulaCircuitSize = c.map (fun _ => 0) := by
      rw [List.map_map]
      exact List.map_congr_left (fun ⟨i, b⟩ _ => by
        simp [litToInput, ufiFormulaCircuitSize])
    rw [hmap]
    simp
  simp only [dnfFromClauses, ufiFormulaCircuitSize, List.map_map]
  have hmap : cs.map (ufiFormulaCircuitSize ∘ clauseToAnd) = cs.map (fun _ => 1) :=
    List.map_congr_left (fun c _ => hclause c)
  rw [hmap, sum_map_one]
  omega

private theorem length_le_sum_map_of_pointwise {α : Type*} (l : List α) (f : α → Nat)
    (h : ∀ x ∈ l, 1 ≤ f x) : l.length ≤ (l.map f).sum := by
  rw [← sum_map_one l]
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem cnfSize_le_circuit_size (g : UnboundedFanInFormula) (h : isCNF g = true) :
    cnfSize g ≤ ufiFormulaCircuitSize g := by
  cases g with
  | andGate gates =>
      simp only [isCNF, List.all_eq_true] at h
      simp only [cnfSize, ufiFormulaCircuitSize]
      have hpoint : ∀ gate ∈ gates, 1 ≤ ufiFormulaCircuitSize gate := by
        intro gate hgate
        specialize h gate hgate
        cases gate <;> simp_all [isOrOfInputsOnly, ufiFormulaCircuitSize]
      exact le_trans (length_le_sum_map_of_pointwise gates _ hpoint) (Nat.le_add_right _ _)
  | inputGate _ _ | constant _ _ | notGate _ | orGate _ => simp [isCNF] at h

theorem dnfSize_le_circuit_size (g : UnboundedFanInFormula) (h : isDNF g = true) :
    dnfSize g ≤ ufiFormulaCircuitSize g := by
  cases g with
  | orGate gates =>
      simp only [isDNF, List.all_eq_true] at h
      simp only [dnfSize, ufiFormulaCircuitSize]
      have hpoint : ∀ gate ∈ gates, 1 ≤ ufiFormulaCircuitSize gate := by
        intro gate hgate
        specialize h gate hgate
        cases gate <;> simp_all [isAndOfInputsOnly, ufiFormulaCircuitSize]
      exact le_trans (length_le_sum_map_of_pointwise gates _ hpoint) (Nat.le_add_right _ _)
  | inputGate _ _ | constant _ _ | notGate _ | andGate _ => simp [isDNF] at h

/- `properizeClauses` does not increase the clause count. -/
theorem properizeClauses_length_le (cs : List (List (Nat × Bool))) :
    (properizeClauses cs).length ≤ cs.length := by
  simp only [properizeClauses]
  have h1 := List.length_filter_le
    (fun c => decide ((c.map Prod.fst).Nodup)) (cs.map pairLevelDedup)
  rw [List.length_map] at h1
  exact h1

/- Properize does not increase the clause count (beyond the width-1 floor of 2). -/

theorem properizeCNF_circuit_size_le (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (properizeCNF g) ≤ 1 + max 2 (cnfSize g) := by
  simp only [properizeCNF]
  by_cases hmem : [] ∈ properizeClauses (cnfClauses g)
  · rw [if_pos hmem, circuit_size_cnfFromClauses]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [if_neg hmem, circuit_size_cnfFromClauses]
    exact Nat.add_le_add_left (le_trans (properizeClauses_length_le _) (by
      cases g <;> simp [cnfClauses, cnfSize])) 1

theorem properizeDNF_circuit_size_le (g : UnboundedFanInFormula) :
    ufiFormulaCircuitSize (properizeDNF g) ≤ 1 + max 2 (dnfSize g) := by
  simp only [properizeDNF]
  by_cases hmem : [] ∈ properizeClauses (dnfClauses g)
  · rw [if_pos hmem, circuit_size_dnfFromClauses]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [if_neg hmem, circuit_size_dnfFromClauses]
    exact Nat.add_le_add_left (le_trans (properizeClauses_length_le _) (by
      cases g <;> simp [dnfClauses, dnfSize])) 1

end ProperizeProto
end Circuits.HastadParity
