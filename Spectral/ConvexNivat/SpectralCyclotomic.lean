import ConvexNivat.SpectralGalois

open scoped BigOperators
namespace ConvexNivat
noncomputable section

private def rationalDifference {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (side : TailSide) (a : ZMod p) (z : Lattice) : ℚ :=
  (if isolatingConfiguration star i σ z = a then 1 else 0) -
    (if pureRayBackground star i σ side z = a then 1 else 0)

private lemma rationalDifference_cast {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (side : TailSide) (a : ZMod p) (z : Lattice) :
    (rationalDifference star i σ side a z : ℂ) =
      exceptionalDifference star i σ side a z := by
  simp only [rationalDifference, exceptionalDifference, Pi.sub_apply, colorIndicator]
  split_ifs <;> simp

private def projectionNumerator {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) (z : Lattice) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (periods.multiplier i),
    Polynomial.monomial k (rationalDifference star i σ side a
      (z + (k : ℤ) • (star.component i).direction))

private lemma projectionNumerator_eval {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) (z : Lattice) (ζ : ℂ) :
    spectralProjection (star.component i).direction (periods.multiplier i) ζ
      (exceptionalDifference star i σ side a) z =
    (periods.multiplier i : ℂ)⁻¹ * Polynomial.aeval (ζ⁻¹)
      (projectionNumerator star periods i σ side a z) := by
  simp [spectralProjection, projectionNumerator, Polynomial.aeval_monomial,
    rationalDifference_cast, zpow_neg, mul_comm]

private lemma primitive_projection_zero {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (σ : RayOrientation)
    (side : TailSide) (a : ZMod p) (n : ℕ) (hn : 0 < n) (ζ μ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) (hμ : IsPrimitiveRoot μ n) (z : Lattice) :
    spectralProjection (star.component i).direction (periods.multiplier i) ζ
      (exceptionalDifference star i σ side a) z = 0 ↔
    spectralProjection (star.component i).direction (periods.multiplier i) μ
      (exceptionalDifference star i σ side a) z = 0 := by
  have hκ : (periods.multiplier i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (periods.positive i).ne'
  rw [projectionNumerator_eval, projectionNumerator_eval]
  simp only [mul_eq_zero, inv_eq_zero, hκ, false_or]
  rw [← minpoly.dvd_iff, ← minpoly.dvd_iff,
    ← Polynomial.cyclotomic_eq_minpoly_rat hζ.inv hn,
    ← Polynomial.cyclotomic_eq_minpoly_rat hμ.inv hn]

private lemma primitive_spectrum_saturated {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) (n : ℕ) (hn : 0 < n)
    (ζ μ : ℂ) (hζ : ζ ∈ exceptionalSpectrum star periods i)
    (hζn : IsPrimitiveRoot ζ n) (hμn : IsPrimitiveRoot μ n) :
    μ ∈ exceptionalSpectrum star periods i := by
  classical
  obtain ⟨hr, σ, side, a, ho⟩ := Finset.mem_filter.mp hζ
  have hdiv : n ∣ periods.multiplier i :=
    hζn.dvd_of_pow_eq_one _ (exceptional_spectrum_root star periods i ζ hζ)
  refine Finset.mem_filter.mpr ⟨?_, σ, side, a, ?_⟩
  · exact (Polynomial.mem_nthRootsFinset (periods.positive i) 1).mpr
      ((hμn.pow_eq_one_iff_dvd _).mpr hdiv)
  · intro hz
    apply ho
    ext z
    exact (primitive_projection_zero star periods i σ side a n hn ζ μ hζn hμn z).mpr
      (congrFun hz z)

/-- Remark 2.1': A_i is a product of distinct cyclotomic polynomials, indexed
by actual divisors of the tangential period. -/
theorem exceptional_univariate_cyclotomic_factors {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    ∃ orders : Finset ℕ,
      (∀ n ∈ orders, 0 < n ∧ n ∣ periods.multiplier i) ∧
      exceptionalUnivariate star periods i = ∏ n ∈ orders, Polynomial.cyclotomic n ℂ := by
  classical
  let orders := (exceptionalSpectrum star periods i).image orderOf
  have hpos (n : ℕ) (hn : n ∈ orders) : 0 < n := by
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨k, hk, hprim⟩ := IsPrimitiveRoot.exists_pos
      (exceptional_spectrum_root star periods i ζ hζ) (periods.positive i).ne'
    rwa [hprim.eq_orderOf] at hk
  refine ⟨orders, ?_, ?_⟩
  · intro n hn
    refine ⟨hpos n hn, ?_⟩
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.mp hn
    exact orderOf_dvd_of_pow_eq_one (exceptional_spectrum_root star periods i ζ hζ)
  · have hset : exceptionalSpectrum star periods i =
        orders.biUnion (fun n => primitiveRoots n ℂ) := by
      ext ζ
      constructor
      · intro hζ
        exact Finset.mem_biUnion.mpr ⟨orderOf ζ, Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩,
          (mem_primitiveRoots (hpos _ (Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩))).mpr
            (IsPrimitiveRoot.orderOf ζ)⟩
      · intro hζ
        obtain ⟨n, hn, hζn⟩ := Finset.mem_biUnion.mp hζ
        obtain ⟨μ, hμ, hm⟩ := Finset.mem_image.mp hn
        exact primitive_spectrum_saturated star periods i n (hpos n hn) μ ζ hμ
          (hm ▸ IsPrimitiveRoot.orderOf μ)
          (isPrimitiveRoot_of_mem_primitiveRoots hζn)
    rw [exceptionalUnivariate, hset, Finset.prod_biUnion]
    · apply Finset.prod_congr rfl
      intro n hn
      exact (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots
        (Complex.isPrimitiveRoot_exp n (hpos n hn).ne')).symm
    · intro n hn m hm hnm
      exact IsPrimitiveRoot.disjoint hnm

/-- Remark 2.1', integer coefficient conclusion for A_i. -/
theorem exceptional_univariate_integer_coefficients {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (i : Fin star.m) :
    ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℂ) = exceptionalUnivariate star periods i := by
  obtain ⟨orders, _, horders⟩ := exceptional_univariate_cyclotomic_factors star periods i
  refine ⟨∏ n ∈ orders, Polynomial.cyclotomic n ℤ, ?_⟩
  rw [Polynomial.map_prod]
  simpa only [Polynomial.map_cyclotomic_int] using horders.symm

end
end ConvexNivat
