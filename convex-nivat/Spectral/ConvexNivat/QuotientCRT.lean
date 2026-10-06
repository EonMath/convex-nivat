import ConvexNivat.QuotientFoundation
import ConvexNivat.QuotientComaximal

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

private def firstCharacter : Multiplicative Lattice →* WitnessLaurentAlgebra where
  toFun u := AddMonoidAlgebra.single (-u.toAdd)
    (algebraMap LaurentPolynomial LaurentRationalField (translationMonomial u.toAdd))
  map_one' := by change AddMonoidAlgebra.single 0 ((algebraMap LaurentPolynomial LaurentRationalField) 1) = 1; simp [AddMonoidAlgebra.one_def]
  map_mul' u v := by
    change AddMonoidAlgebra.single (-(u.toAdd + v.toAdd)) _ = _
    rw [neg_add, AddMonoidAlgebra.single_mul_single]
    congr 1
    rw [← map_mul]
    congr 1
    simp [translationMonomial, AddMonoidAlgebra.single_mul_single]

private def firstHom : LaurentPolynomial →+* WitnessLaurentAlgebra :=
  AddMonoidAlgebra.liftNCRingHom
    ((AddMonoidAlgebra.singleZeroRingHom).comp (algebraMap ℂ LaurentRationalField))
    firstCharacter (fun _ _ => Commute.all _ _)

private theorem firstHom_apply (p : LaurentPolynomial) :
    firstHom p = firstPointRecursionPolynomial p := by
  unfold firstHom AddMonoidAlgebra.liftNCRingHom AddMonoidAlgebra.liftNC
  unfold firstPointRecursionPolynomial
  apply Finsupp.sum_congr
  intro s hs
  change AddMonoidAlgebra.single 0 _ * AddMonoidAlgebra.single (-s) _ = _
  simp [AddMonoidAlgebra.single_mul_single]

private def secondHom : LaurentPolynomial →+* WitnessLaurentAlgebra :=
  AddMonoidAlgebra.mapRingHom Lattice (algebraMap ℂ LaurentRationalField)

private theorem secondHom_apply (p : LaurentPolynomial) :
    secondHom p = differenceRecursionPolynomial p := rfl

/-- Canonical projection of the whole quotient onto a pair factor. -/
def spectralPairProjection {m : ℕ} (family : FiniteSpectralFamily m) (i j : Fin m) :
    BiRecursionQuotient family.polynomial →ₐ[LaurentRationalField] family.PairQuotient i j :=
  Ideal.Quotient.factorₐ LaurentRationalField (spectral_bi_ideal_le_pair family i j)

abbrev DistinctDirectionPair (m : ℕ) := {ij : Fin m × Fin m // ij.1 ≠ ij.2}

/-- Natural projections in source (5.2), bundled as an algebra map. -/
def spectralQuotientProjection {m : ℕ} (family : FiniteSpectralFamily m) :
    BiRecursionQuotient family.polynomial →ₐ[LaurentRationalField]
      (∀ ij : DistinctDirectionPair m, family.PairQuotient ij.val.1 ij.val.2) :=
  AlgHom.pi (fun ij => spectralPairProjection family ij.val.1 ij.val.2)


private theorem relative_product_inf {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] (H : Ideal R) (f : ι → R)
    (h : ∀ i j, i ≠ j → H ⊔ Ideal.span ({f i,f j} : Set R) = ⊤) :
    H ⊔ Ideal.span ({∏ i, f i} : Set R) =
      ⨅ i, H ⊔ Ideal.span ({f i} : Set R) := by
  let q := Ideal.Quotient.mk H
  have lift (p : R) : Ideal.comap q (Ideal.span ({q p} : Set (R ⧸ H))) =
      H ⊔ Ideal.span ({p} : Set R) := by
    simpa only [Ideal.map_span, Set.image_singleton] using
      Ideal.comap_map_quotientMk H (Ideal.span ({p} : Set R))
  have hc : ∀ i j, i ≠ j → IsCoprime (q (f i)) (q (f j)) := by
    intro i j hij
    have he := congrArg (Ideal.map q) (h i j hij)
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_insert_eq,
      Set.image_singleton, Ideal.map_top] at he
    have hz : Ideal.map q H = ⊥ := Ideal.map_quotient_self H
    rw [hz, bot_sup_eq, Ideal.span_insert] at he
    exact Ideal.sup_eq_top_iff_isCoprime _ _ |>.mp he
  calc
    _ = Ideal.comap q (Ideal.span ({q (∏ i, f i)} : Set (R ⧸ H))) := (lift _).symm
    _ = Ideal.comap q (⨅ i, Ideal.span ({q (f i)} : Set (R ⧸ H))) := by
      rw [map_prod, Ideal.iInf_span_singleton hc]
    _ = _ := by rw [Ideal.comap_iInf]; simp_rw [lift]

private theorem whole_ideal_eq_all_pairs {m : ℕ} (family : FiniteSpectralFamily m) :
    biRecursionIdeal family.polynomial = ⨅ i, ⨅ j, family.pairIdeal i j := by
  let a := family.secondPointFactor
  let c := family.firstPointFactor
  have hA : differenceRecursionPolynomial family.polynomial = ∏ i, a i := by
    change secondHom (∏ i, family.directionPolynomial i) = _
    rw [map_prod]
    rfl
  have hC : firstPointRecursionPolynomial family.polynomial = ∏ i, c i := by
    rw [← firstHom_apply]
    change firstHom (∏ i, family.directionPolynomial i) = _
    simp only [map_prod, firstHom_apply]
    rfl
  have h1 : ∀ i k, i ≠ k → Ideal.span ({∏ j, c j} : Set WitnessLaurentAlgebra) ⊔
      Ideal.span ({a i,a k} : Set WitnessLaurentAlgebra) = ⊤ := by
    intro i k hik
    have h := spectral_two_second_point_factors_coprime family i k hik
    rw [hC] at h
    simpa only [Ideal.span_insert, sup_comm, sup_left_comm, sup_assoc] using h
  have h2 (i) : ∀ j l, j ≠ l → Ideal.span ({a i} : Set WitnessLaurentAlgebra) ⊔
      Ideal.span ({c j,c l} : Set WitnessLaurentAlgebra) = ⊤ := by
    intro j l hjl
    simpa only [Ideal.span_insert] using spectral_two_first_point_factors_coprime family i j l hjl
  calc
    _ = Ideal.span ({∏ j, c j} : Set WitnessLaurentAlgebra) ⊔ Ideal.span {∏ i, a i} := by
      rw [biRecursionIdeal, hA, hC, Ideal.span_insert, sup_comm]
    _ = ⨅ i, Ideal.span ({∏ j, c j} : Set WitnessLaurentAlgebra) ⊔ Ideal.span {a i} :=
      relative_product_inf _ a h1
    _ = _ := by
      congr 1
      funext i
      rw [sup_comm, relative_product_inf _ c (h2 i)]
      simp only [FiniteSpectralFamily.pairIdeal, Ideal.span_insert]
      rfl


private theorem distinct_pair_coprime {m : ℕ} (family : FiniteSpectralFamily m) :
    Pairwise (fun ij kl : DistinctDirectionPair m =>
      IsCoprime (family.pairIdeal ij.val.1 ij.val.2) (family.pairIdeal kl.val.1 kl.val.2)) := by
  intro ij kl hne
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  by_cases hi : ij.val.1 = kl.val.1
  · have hj : ij.val.2 ≠ kl.val.2 := by
      intro hj
      exact hne (Subtype.ext (Prod.ext hi hj))
    rw [← spectral_two_first_point_factors_coprime family ij.val.1 ij.val.2 kl.val.2 hj]
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Ideal.mem_sup_left (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
    · exact Ideal.mem_sup_left (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
  · rw [← spectral_two_second_point_factors_coprime family ij.val.1 kl.val.1 hi]
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Ideal.mem_sup_left (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
    · exact Ideal.mem_sup_left (spectral_bi_ideal_le_pair family ij.val.1 ij.val.2
        (Ideal.subset_span (by simp [biRecursionIdeal])))

/-- Exact bijectivity of the source's natural CRT map (5.2). -/
theorem spectral_quotient_projection_bijective {m : ℕ}
    (family : FiniteSpectralFamily m) (hm : 2 ≤ m) :
    Function.Bijective (spectralQuotientProjection family) := by
  classical
  constructor
  · apply (injective_iff_map_eq_zero (spectralQuotientProjection family)).mpr
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [whole_ideal_eq_all_pairs]
    simp only [Ideal.mem_iInf]
    intro i j
    by_cases hij : i = j
    · subst j
      rw [spectral_same_direction_pair_ideal_top]
      trivial
    · have hp := congrFun hx (⟨(i,j),hij⟩ : DistinctDirectionPair m)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hp
  · intro x
    obtain ⟨p,hp⟩ := Ideal.pi_quotient_surjective (distinct_pair_coprime family) x
    refine ⟨Ideal.Quotient.mk _ p, ?_⟩
    funext ij
    exact hp ij

/-- The actual algebra equivalence in (5.2), constructed from the natural map. -/
def spectralQuotientCRT {m : ℕ} (family : FiniteSpectralFamily m) (hm : 2 ≤ m) :
    BiRecursionQuotient family.polynomial ≃ₐ[LaurentRationalField]
      (∀ ij : DistinctDirectionPair m, family.PairQuotient ij.val.1 ij.val.2) :=
  AlgEquiv.ofBijective (spectralQuotientProjection family)
    (spectral_quotient_projection_bijective family hm)


end
end ConvexNivat
