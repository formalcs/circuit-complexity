import ACC.LowerBounds.Smolensky.Formula
import ACC.Circuit.Semantics
import ACC.Conversion.CircuitToFormula.Family

namespace Circuits.ACC

/-- **Smolensky's theorem for ACC circuit families.**

Let `p` be prime and let `r > 1` be coprime to `p`. Every polynomial-size,
constant-depth `ACCCircuitFamily[p]` disagrees with `MOD_r` at every
sufficiently large input length. -/
theorem smolensky_mod_eventually_disagrees
    (p r : ℕ) (hp : p.Prime) (hr : 1 < r) (hcop : r.Coprime p) :
    ∀ (sizeCoefficient sizeExponent depthBound : ℕ)
      (family : DAG.ACCCircuit.ACCCircuitFamily p sizeCoefficient sizeExponent
        depthBound),
      ∃ n₀ : ℕ, ∀ N : PNat, N.val > n₀ →
        ¬DAG.ACCCircuit.ComputesAtLength (family N).val N.val
          (modFunctionList r) := by
  intro sizeCoefficient sizeExponent depthBound family
  obtain ⟨formulaCoefficient, formulaExponent, formulaDepth, formulaFamily,
      hformula⟩ := DAG.ACCCircuit.exists_accFormula_family_exact family
  obtain ⟨n₀, hn₀⟩ :=
    smolensky_mod_formula_eventually_disagrees p r hp hr hcop
      formulaCoefficient formulaExponent formulaDepth formulaFamily
  refine ⟨n₀, ?_⟩
  intro N hN hcomputes
  apply hn₀ N hN
  intro inputs hlength
  calc
    ACC.ACCFormula.eval (formulaFamily N).val inputs =
        ((family N).val.evalCanonical inputs).head?.getD false :=
      hformula N inputs hlength.symm
    _ = modFunctionList r inputs := hcomputes inputs hlength

#print axioms smolensky_mod_eventually_disagrees

/-- **Smolensky's theorem for languages in `ACC[p]`.**

Let `p` be prime and let `r > 1` be coprime to `p`. Every language in
nonuniform `ACC[p]` disagrees with `MOD_r` at every sufficiently large input
length. -/
theorem smolensky_mod_inACC_eventually_disagrees
    (p r : ℕ) (hp : p.Prime) (hr : 1 < r) (hcop : r.Coprime p) :
    ∀ (language : Set (List Bool)), InACC p language →
      ∃ n₀ : ℕ, ∀ N : PNat, N.val > n₀ →
        ∃ inputs : List Bool, inputs.length = N.val ∧
          ¬((inputs ∈ language) ↔ modFunctionList r inputs = true) := by
  intro language hACC
  obtain ⟨sizeCoefficient, sizeExponent, depthBound, family, hrecognizes⟩ :=
    hACC
  obtain ⟨n₀, hdisagrees⟩ :=
    smolensky_mod_eventually_disagrees p r hp hr hcop
      sizeCoefficient sizeExponent depthBound family
  refine ⟨n₀, ?_⟩
  intro N hN
  simp only [DAG.ACCCircuit.ComputesAtLength, not_forall] at hdisagrees
  obtain ⟨inputs, hlength, hne⟩ := hdisagrees N hN
  refine ⟨inputs, hlength, ?_⟩
  have hrecognized := hrecognizes N inputs hlength
  rw [← hrecognized]
  exact fun hiff ↦ hne (Bool.eq_iff_iff.mpr hiff)

#print axioms smolensky_mod_inACC_eventually_disagrees

end Circuits.ACC
