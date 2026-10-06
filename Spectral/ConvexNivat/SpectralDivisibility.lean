import ConvexNivat.SpectralLaurentBridge

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

/-- Source Lemma 2.3, with both one-sided alternatives and genuine ring divisibility. -/
theorem one_sided_spectral_divisibility (v : Lattice) (hv : Primitive v)
    (κ : ℕ) (hκ : 0 < κ) (ζ : ℂ) (hζ : ζ ^ κ = 1)
    (d : ScalarField) (hd : HasPeriod d ((κ : ℤ) • v))
    (hside : ∃ b : ℤ, (∀ z, b < height v z → d z = 0) ∨
      (∀ z, height v z < b → d z = 0))
    (hoccurs : spectralOccurs v κ ζ d)
    (f : LaurentPolynomial) (hf : applyLaurent f d = 0) :
    translationMonomial v - AddMonoidAlgebra.single 0 ζ ∣ f := by
  classical
  obtain ⟨u, hu⟩ := primitive_height_surjective v hv 1
  have hbasis : det v u = 1 := hu
  have hζ0 : ζ ≠ 0 := by
    intro hz
    simp [hz, Nat.ne_of_gt hκ] at hζ
  let c := spectralRowCoefficient v u κ ζ d
  have hc : ∃ t, c t ≠ 0 :=
    (spectral_occurs_iff_row v u κ hbasis hκ ζ hζ d hd).mp hoccurs
  have hcside : ∃ b : ℤ, (∀ t, b < t → c t = 0) ∨
      (∀ t, t < b → c t = 0) := by
    obtain ⟨b, hs | hs⟩ := hside
    · refine ⟨b, Or.inl ?_⟩
      intro t ht
      dsimp [c, spectralRowCoefficient]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro k hk
      rw [hs _ (by simpa only [height_add, height_zsmul, height_self, hu, mul_zero, mul_one, zero_add] using ht), mul_zero]
    · refine ⟨b, Or.inr ?_⟩
      intro t ht
      dsimp [c, spectralRowCoefficient]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro k hk
      rw [hs _ (by simpa only [height_add, height_zsmul, height_self, hu, mul_zero, mul_one, zero_add] using ht), mul_zero]
  let g : ℤ →₀ ℂ := f.coeff.sum (fun q a => Finsupp.single (det v q) (a * ζ ^ (det q u)))
  have hsum (t : ℤ) : ∑ β ∈ g.support, g β * c (t + β) =
      ∑ q ∈ f.coeff.support, f.coeff q * ζ ^ (det q u) * c (t + det v q) := by
    change g.sum (fun β a => a * c (t + β)) = _
    dsimp [g]
    rw [Finsupp.sum_sum_index]
    · apply Finset.sum_congr rfl
      intro q hq
      exact Finsupp.sum_single_index (by simp)
    · intro i; simp
    · intro i a b; simp [add_mul]
  have hrec (t : ℤ) : ∑ β ∈ g.support, g β * c (t + β) = 0 := by
    rw [hsum]
    have hcomm := spectral_projection_commutes_laurent v κ ζ d f
    rw [hf] at hcomm
    have hz := congrFun hcomm (t • u)
    have hr := spectral_laurent_row_formula v u hbasis κ hκ ζ hζ d hd f 0 t
    simp only [zero_smul, zero_add, zpow_zero, one_mul] at hr
    rw [hr] at hz
    simpa [spectralProjection, c] using hz.symm
  have hg : g = 0 := one_sided_recurrence_zero g c hc hcside hrec
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
  have hπ : π f = 0 := by
    have heq : π f = g.sum (fun β a => π (AddMonoidAlgebra.single (β • u) a)) := by
      rw [show f = f.coeff.sum AddMonoidAlgebra.single from (AddMonoidAlgebra.sum_coeff_single f).symm,
        map_finsuppSum]
      dsimp [g]
      rw [Finsupp.sum_sum_index]
      · apply Finset.sum_congr rfl
        intro q hq
        simpa only [Finsupp.sum_single_index, AddMonoidAlgebra.single_zero, map_zero] using hsingle q (f.coeff q)
      · intro i; simp
      · intro i a b; simp [map_add, AddMonoidAlgebra.single_add]
    rw [heq, hg]
    simp
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hπ)


end
end ConvexNivat
