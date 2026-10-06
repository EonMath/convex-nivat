import NivatTrial.LaurentDilation

/-! Frobenius and integer bounds propagate an annihilator to all exponent
dilations coprime to one fixed factorial. -/

namespace NivatTrial.AnnihilatorDilation

open NivatTrial.LaurentAction NivatTrial.LaurentDilation
open scoped Classical
noncomputable section

theorem frobenius_eq_dilate (p : ℕ) [Fact p.Prime] (f : RingLaurent (ZMod p)) :
    f ^ p = dilate p f := by
  have : CharP (RingLaurent (ZMod p)) p :=
    charP_of_injective_algebraMap' (ZMod p) p
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, sum_pow_char]
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum, map_sum, AddMonoidAlgebra.single_pow,
    ZMod.pow_card, dilate_single]

theorem prime_dilation_mod (p : ℕ) (hp : p.Prime)
    (f : RingLaurent ℤ) (x : Lattice → ℤ) (hf : act f x = 0) :
    ∀ z, ((act (dilate p f) x z : ℤ) : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hh := act_pow_eq_zero (map_annihilates φ hf) hp.pos
  rw [frobenius_eq_dilate, ← map_dilate] at hh
  intro z
  have hz := congrFun hh z
  change φ (act (dilate p f) x z) = 0
  rw [← act_mapCoefficients]
  exact hz

/-- The bound depends only on the original coefficients, even when the
annihilator at the current induction stage has already been dilated. -/
theorem prime_step (p n : ℕ) (hp : p.Prime)
    (f : RingLaurent ℤ) (x : Lattice → ℤ) (B : ℤ)
    (hB : ∀ z, |x z| ≤ B)
    (hbound : (∑ u ∈ f.coeff.support, |f.coeff u|) * B < p)
    (hf : act (dilate n f) x = 0) : act (dilate (p*n) f) x = 0 := by
  funext z
  have hmod := prime_dilation_mod p hp (dilate n f) x hf z
  rw [dilate_comp] at hmod
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hmod
  have hlt : |act (dilate (p*n) f) x z| < (p:ℤ) :=
    (abs_act_dilate_le (p*n) f x B hB z).trans_lt hbound
  have hab : (act (dilate (p*n) f) x z).natAbs < (p:ℤ).natAbs := by
    have hh : ((act (dilate (p*n) f) x z).natAbs : ℤ) < (p:ℤ) := by
      simpa only [Int.natCast_natAbs] using hlt
    simpa only [Int.natAbs_natCast] using (show (act (dilate (p*n) f) x z).natAbs < p by
      exact_mod_cast hh)
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hab

theorem coprime_dilation (f : RingLaurent ℤ) (x : Lattice → ℤ) (B : ℤ)
    (hB : ∀ z, |x z| ≤ B) (C : ℕ)
    (hC : (∑ u ∈ f.coeff.support, |f.coeff u|) * B ≤ C)
    (hf : act f x = 0) :
    ∀ n : ℕ, 0 < n → n.Coprime C.factorial → act (dilate n f) x = 0 := by
  apply induction_on_primes
  · intro h
    omega
  · intro _ _
    simpa using hf
  · intro p n hp ih hn hc
    have hcop := Nat.coprime_mul_iff_left.mp hc
    have hpC : C < p := by
      by_contra h
      have hdiv : p ∣ C.factorial := Nat.dvd_factorial hp.pos (by omega)
      exact (hp.coprime_iff_not_dvd.mp hcop.1) hdiv
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by intro h; simp [h] at hn)
    exact prime_step p n hp f x B hB
      (hC.trans_lt (by exact_mod_cast hpC)) (ih hnpos hcop.2)

theorem exists_dilation_progression (f : RingLaurent ℤ) (x : Lattice → ℤ)
    (hx : (Set.range x).Finite) (hf : act f x = 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ k : ℕ, act (dilate (1+k*r) f) x = 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ z, |x z| ≤ B := by
    obtain ⟨B, hB⟩ := (hx.image abs).bddAbove
    exact ⟨B, fun z => hB ⟨x z, ⟨z,rfl⟩,rfl⟩⟩
  let C := ((∑ u ∈ f.coeff.support, |f.coeff u|)*B).natAbs
  have hC : (∑ u ∈ f.coeff.support, |f.coeff u|)*B ≤ (C:ℤ) :=
    Int.le_natAbs
  refine ⟨C.factorial, Nat.factorial_pos C, ?_⟩
  intro k
  apply coprime_dilation f x B hB C hC hf (1+k*C.factorial) (by omega)
  exact (Nat.coprime_add_mul_right_left 1 C.factorial k).mpr
    (Nat.coprime_one_left C.factorial)

end
end NivatTrial.AnnihilatorDilation
