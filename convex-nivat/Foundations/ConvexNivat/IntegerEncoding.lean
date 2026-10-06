import Mathlib

open scoped BigOperators

namespace ConvexNivat

noncomputable section

/-- The finite hyperplane avoidance statement used in Lemma 2.2.
Every indexed complex linear form is nonzero; integer weights can avoid all
their kernels while assigning distinct integers to distinct colours. -/
theorem finite_integer_encoding {Color Condition : Type*}
    [Fintype Color] [Fintype Condition]
    (coeff : Condition → Color → ℂ)
    (hcoeff : ∀ b, ∃ a, coeff b a ≠ 0) :
    ∃ w : Color → ℤ, Function.Injective w ∧
      ∀ b, (∑ a, (w a : ℂ) * coeff b a) ≠ 0 := by
  classical
  let e : Color → ℕ := fun a => (Fintype.equivFin Color a).val
  have he : Function.Injective e :=
    Fin.val_injective.comp (Fintype.equivFin Color).injective
  let p : Condition → Polynomial ℂ := fun b =>
    ∑ a, Polynomial.monomial (e a) (coeff b a)
  have hp : ∀ b, p b ≠ 0 := by
    intro b
    obtain ⟨a, ha⟩ := hcoeff b
    have hpa : (p b).coeff (e a) = coeff b a := by
      simp [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, he.eq_iff]
    intro hzero
    exact ha (by simpa [hzero] using hpa.symm)
  let q : Polynomial ℂ := ∏ b, p b
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun b _ => hp b)
  have hi : Function.Injective (fun n : ℕ => (n : ℂ) + 2) := by
    intro n m h
    exact Nat.cast_injective (add_right_cancel h)
  have hf : Set.Finite ((fun n : ℕ => (n : ℂ) + 2) ⁻¹'
      {z : ℂ | q.IsRoot z}) :=
    Set.Finite.preimage hi.injOn (Polynomial.finite_setOfPred_isRoot hq)
  obtain ⟨n, hn⟩ := hf.exists_notMem
  change q.eval ((n : ℂ) + 2) ≠ 0 at hn
  have hpn : ∀ b, (p b).eval ((n : ℂ) + 2) ≠ 0 := by
    intro b
    dsimp [q] at hn
    rw [Polynomial.eval_prod] at hn
    exact Finset.prod_ne_zero_iff.mp hn b (Finset.mem_univ b)
  refine ⟨fun a => ((n : ℤ) + 2) ^ e a, ?_, ?_⟩
  · intro a a' h
    apply he
    exact (pow_right_strictMono₀ (show 1 < (n : ℤ) + 2 by omega)).injective h
  · intro b
    simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]
      using hpn b

end
end ConvexNivat
