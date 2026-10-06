import ConvexNivat.SpectralLaurentBridge

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

/-- The explicit binomial primeness obligation used in Lemma 2.4(d). -/
theorem primitive_translation_binomial_prime (v : Lattice) (hv : Primitive v)
    (ζ : ℂ) (hζ : ζ ≠ 0) :
    Prime (translationMonomial v - AddMonoidAlgebra.single 0 ζ) := by
  classical
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv 1
  have hbasis : det v u = 1 := hu
  have hζ0 := hζ
  have hself (q : Lattice) : det q q = 0 := by simp [det, mul_comm]
  have hdetadd (q r s : Lattice) : det (q + r) s = det q s + det r s := by
    simp only [det, Prod.fst_add, Prod.snd_add]
    ring
  have hadddet (q r s : Lattice) : det q (r + s) = det q r + det q s := height_add q r s
  have hleft0 (q : Lattice) : det 0 q = 0 := by simp [det]
  have hright0 (q : Lattice) : det q 0 = 0 := by simp [det]
  let χ : Multiplicative Lattice →* AddMonoidAlgebra ℂ ℤ :=
    { toFun := fun q => AddMonoidAlgebra.single (det v q.toAdd) (ζ ^ (det q.toAdd u))
      map_one' := by
        change AddMonoidAlgebra.single (det v 0) (ζ ^ (det 0 u)) = 1
        rw [hleft0, hright0, zpow_zero]
        rfl
      map_mul' := by
        intro q r
        change AddMonoidAlgebra.single (det v (q.toAdd + r.toAdd))
          (ζ ^ (det (q.toAdd + r.toAdd) u)) = _
        rw [hdetadd, hadddet, zpow_add₀ hζ, AddMonoidAlgebra.single_mul_single] }
  let E : LaurentPolynomial →+* AddMonoidAlgebra ℂ ℤ :=
    AddMonoidAlgebra.liftNCRingHom AddMonoidAlgebra.singleZeroRingHom χ
      (fun _ _ => Commute.all _ _)
  have hE (q : Lattice) (a : ℂ) : E (AddMonoidAlgebra.single q a) =
      AddMonoidAlgebra.single (det v q) (a * ζ ^ (det q u)) := by
    simp [E, AddMonoidAlgebra.liftNCRingHom_single, χ,
      mul_assoc]
  have hEb : E (translationMonomial v - AddMonoidAlgebra.single 0 ζ) = 0 := by
    simp only [translationMonomial, map_sub, hE, hself, hbasis, hleft0, hright0,
      zpow_one, zpow_zero, one_mul, mul_one, sub_self]
  have hker (p : LaurentPolynomial) : E p = 0 ↔
      translationMonomial v - AddMonoidAlgebra.single 0 ζ ∣ p := by
    constructor
    · intro hp
      let g : ℤ →₀ ℂ := p.coeff.sum
        (fun q a => Finsupp.single (det v q) (a * ζ ^ (det q u)))
      have hg : g = 0 := by
        have heq : (E p).coeff = g := by
          conv_lhs => rhs; rw [← AddMonoidAlgebra.sum_coeff_single p]
          rw [map_finsuppSum, AddMonoidAlgebra.coeff_finsuppSum]
          simp only [hE, AddMonoidAlgebra.coeff_single]
          rfl
        rw [← heq, hp]
        rfl
      let J : Ideal LaurentPolynomial :=
        Ideal.span {translationMonomial v - AddMonoidAlgebra.single 0 ζ}
      let π := Ideal.Quotient.mk J
      let C : ℂ →+* LaurentPolynomial ⧸ J :=
        π.comp AddMonoidAlgebra.singleZeroRingHom
      let M : Lattice → LaurentPolynomial ⧸ J :=
        fun q => π (AddMonoidAlgebra.single q 1)
      have hM (q r : Lattice) : M (q + r) = M q * M r := by
        simp [M, ← map_mul, AddMonoidAlgebra.single_mul_single]
      have hM0 : M 0 = 1 := by
        simp [M, ← AddMonoidAlgebra.one_def]
      have hMv : M v = C ζ := by
        apply Ideal.Quotient.eq.mpr
        exact Ideal.mem_span_singleton_self _
      have hMs (s : ℤ) : M (s • v) = C (ζ ^ s) := by
        induction s using Int.induction_on with
        | zero => simp [hM0]
        | succ s hs =>
          rw [add_smul, one_smul, hM, hs, hMv, zpow_add₀ hζ0, zpow_one, map_mul]
        | pred s hs =>
          have hstep : M ((-(s : ℤ) - 1) • v) * C ζ = C (ζ ^ (-(s : ℤ))) := by
            have hvec : ((-(s : ℤ) - 1) • v) + v = (-(s : ℤ)) • v := by
              simp only [sub_smul, one_smul]
              abel
            rw [← hMv, ← hM, hvec, hs]
          have hunit : C ζ * C ζ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hζ0, map_one]
          calc
            M ((-(s : ℤ) - 1) • v) = (M ((-(s : ℤ) - 1) • v) * C ζ) * C ζ⁻¹ := by rw [mul_assoc, hunit, mul_one]
            _ = C (ζ ^ (-(s : ℤ))) * C ζ⁻¹ := by rw [hstep]
            _ = C (ζ ^ (-(s : ℤ) - 1)) := by rw [← map_mul, zpow_sub₀ hζ0, zpow_one, div_eq_mul_inv]
      have hb (q : Lattice) : q = (det q u) • v + (det v q) • u := by
        ext <;> simp [det] at hbasis ⊢
        · linear_combination -q.1 * hbasis
        · linear_combination -q.2 * hbasis
      have hsingle (q : Lattice) (a : ℂ) :
          π (AddMonoidAlgebra.single q a) =
          π (AddMonoidAlgebra.single ((det v q) • u) (a * ζ ^ (det q u))) := by
        have hsplit (r : Lattice) (b : ℂ) :
            π (AddMonoidAlgebra.single r b) = C b * M r := by
          simp [C, M, ← map_mul, AddMonoidAlgebra.single_mul_single]
        rw [hsplit, hsplit, map_mul]
        conv_lhs => rhs; rw [hb q, hM, hMs]
        ring
      have hπ : π p = 0 := by
        have heq : π p = g.sum (fun β a => π (AddMonoidAlgebra.single (β • u) a)) := by
          rw [show p = p.coeff.sum AddMonoidAlgebra.single from (AddMonoidAlgebra.sum_coeff_single p).symm,
            map_finsuppSum]
          dsimp [g]
          rw [Finsupp.sum_sum_index]
          · apply Finset.sum_congr rfl
            intro q hq
            simpa only [Finsupp.sum_single_index, AddMonoidAlgebra.single_zero, map_zero] using hsingle q (p.coeff q)
          · intro i; simp
          · intro i a b; simp [map_add, AddMonoidAlgebra.single_add]
        rw [heq, hg]
        simp
      exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hπ)
    · rintro ⟨q, rfl⟩
      rw [map_mul, hEb, zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro hb
    have hcoeff := congrArg (fun p : LaurentPolynomial => p.coeff v) hb
    have hv0 := primitive_ne_zero v hv
    simp [translationMonomial, AddMonoidAlgebra.coeff_sub,
      AddMonoidAlgebra.coeff_single, hv0] at hcoeff
  · intro hb
    have hunit := hb.map E
    rw [hEb] at hunit
    exact not_isUnit_zero hunit
  · intro p q hpq
    have hzero := (hker (p * q)).mpr hpq
    rw [map_mul] at hzero
    exact (mul_eq_zero.mp hzero).elim
      (fun hp => Or.inl ((hker p).mp hp))
      (fun hq => Or.inr ((hker q).mp hq))



end
end ConvexNivat
