import ConvexNivat.QuotientDefinitions

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


private def scalarK : LaurentRationalField →+* WitnessLaurentAlgebra :=
  AddMonoidAlgebra.singleZeroRingHom

private def scalarC : ℂ →+* WitnessLaurentAlgebra :=
  scalarK.comp (algebraMap ℂ LaurentRationalField)

private def secondCharacter : Multiplicative Lattice →* WitnessLaurentAlgebra :=
  AddMonoidAlgebra.of LaurentRationalField Lattice

private def xCharacter : Multiplicative Lattice →* LaurentRationalField :=
  (algebraMap LaurentPolynomial LaurentRationalField).toMonoidHom.comp
    (AddMonoidAlgebra.of ℂ Lattice)

private theorem second_first (u : Multiplicative Lattice) :
    secondCharacter u * firstCharacter u = scalarK (xCharacter u) := by
  change AddMonoidAlgebra.single u.toAdd 1 * AddMonoidAlgebra.single (-u.toAdd) _ = _
  simp [AddMonoidAlgebra.single_mul_single, scalarK, xCharacter,
    AddMonoidAlgebra.singleZeroRingHom, translationMonomial]

private theorem scalar_obstruction {F : Type*} [Field F]
    (q : WitnessLaurentAlgebra →+* F) (u : Lattice) (hu : u ≠ 0) (c : ℂ) :
    q (scalarK (xCharacter (.ofAdd u))) ≠ q (scalarC c) := by
  intro h
  have h1 := (q.comp scalarK).injective h
  change algebraMap LaurentPolynomial LaurentRationalField (translationMonomial u) =
    algebraMap ℂ LaurentRationalField c at h1
  rw [IsScalarTower.algebraMap_apply ℂ LaurentPolynomial LaurentRationalField] at h1
  have h2 := (IsFractionRing.injective LaurentPolynomial LaurentRationalField) h1
  have h3 := congrArg (fun p : LaurentPolynomial => p.coeff u) h2
  simpa [translationMonomial, AddMonoidAlgebra.algebraMap_def, hu] using h3

private theorem second_root {F : Type*} [Field F]
    (q : WitnessLaurentAlgebra →+* F) {m : ℕ} (family : FiniteSpectralFamily m)
    (i : Fin m) (hi : q (family.secondPointFactor i) = 0) :
    ∃ c ∈ family.spectrum i,
      q (secondCharacter (.ofAdd (family.direction i))) = q (scalarC c) := by
  classical
  change q (secondHom (family.directionPolynomial i)) = 0 at hi
  simp only [FiniteSpectralFamily.directionPolynomial, map_prod, map_sub] at hi
  obtain ⟨c, hc, he⟩ := Finset.prod_eq_zero_iff.mp hi
  refine ⟨c, hc, ?_⟩
  simpa [secondHom, translationMonomial, secondCharacter, scalarC, scalarK,
    sub_eq_zero] using he

private theorem first_root {F : Type*} [Field F]
    (q : WitnessLaurentAlgebra →+* F) {m : ℕ} (family : FiniteSpectralFamily m)
    (i : Fin m) (hi : q (family.firstPointFactor i) = 0) :
    ∃ c ∈ family.spectrum i,
      q (firstCharacter (.ofAdd (family.direction i))) = q (scalarC c) := by
  classical
  change q (firstPointRecursionPolynomial (family.directionPolynomial i)) = 0 at hi
  rw [← firstHom_apply] at hi
  simp only [FiniteSpectralFamily.directionPolynomial, map_prod, map_sub] at hi
  obtain ⟨c, hc, he⟩ := Finset.prod_eq_zero_iff.mp hi
  refine ⟨c, hc, ?_⟩
  simpa [firstHom, translationMonomial, scalarC, scalarK,
    firstCharacter, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC,
    AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def, sub_eq_zero] using he

/-- Lemma 5.2, Step 1(i): (a_i,c_i) is the whole ring. -/
theorem spectral_same_direction_pair_ideal_top {m : ℕ}
    (family : FiniteSpectralFamily m) (i : Fin m) : family.pairIdeal i i = ⊤ := by
  classical
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (family.pairIdeal i i) h
  letI := hM
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  have ha : q (family.secondPointFactor i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal])))
  have hc : q (family.firstPointFactor i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal])))
  obtain ⟨c, _, hy⟩ := second_root q family i ha
  obtain ⟨d, _, hw⟩ := first_root q family i hc
  have hu : family.direction i ≠ 0 := by
    intro hu
    have hp := family.primitive i
    simpa [Primitive, hu] using hp
  apply scalar_obstruction q (family.direction i) hu (c * d)
  rw [← second_first, map_mul, hy, hw, ← map_mul, ← map_mul]


private theorem character_det {F : Type*} [Field F]
    (χ : Multiplicative Lattice →* F) (σ : ℂ →+* F)
    (u v w : Lattice) (a b : ℂ)
    (ha : χ (.ofAdd u) = σ a) (hb : χ (.ofAdd v) = σ b) :
    χ (.ofAdd (det u v • w)) = σ (a ^ det w v * b ^ det u w) := by
  have hid : det u v • w = det w v • u + det u w • v := by
    ext <;> simp [det, smul_eq_mul] <;> ring
  rw [hid, ofAdd_add, map_mul, ofAdd_zsmul, ofAdd_zsmul,
    map_zpow, map_zpow, ha, hb, ← map_zpow₀, ← map_zpow₀, ← map_mul]

private theorem three_roots_impossible {F : Type*} [Field F]
    (q : WitnessLaurentAlgebra →+* F)
    (χ ψ : Multiplicative Lattice →* F)
    (hprod : ∀ u, χ u * ψ u = q (scalarK (xCharacter u)))
    (u v w : Lattice) (hdet : det u v ≠ 0) (hw : w ≠ 0)
    (a b c : ℂ) (ha : χ (.ofAdd u) = q (scalarC a))
    (hb : χ (.ofAdd v) = q (scalarC b))
    (hc : ψ (.ofAdd w) = q (scalarC c)) : False := by
  have hχ := character_det χ (q.comp scalarC) u v w a b ha hb
  have hψ : ψ (.ofAdd (det u v • w)) = (q.comp scalarC) (c ^ det u v) := by
    rw [ofAdd_zsmul, map_zpow, hc, map_zpow₀]
    rfl
  apply scalar_obstruction q (det u v • w) (smul_ne_zero hdet hw)
    ((a ^ det w v * b ^ det u w) * c ^ det u v)
  rw [← hprod, hχ, hψ, ← map_mul]
  rfl

private theorem direction_ne_zero {m : ℕ} (family : FiniteSpectralFamily m) (i : Fin m) :
    family.direction i ≠ 0 := by
  intro h
  have hp := family.primitive i
  simpa [Primitive, h] using hp

/-- Lemma 5.2, Step 1(ii): two a-factors and the product c generate one. -/
theorem spectral_two_second_point_factors_coprime {m : ℕ}
    (family : FiniteSpectralFamily m) (i k : Fin m) (hik : i ≠ k) :
    Ideal.span ({family.secondPointFactor i, family.secondPointFactor k,
      firstPointRecursionPolynomial family.polynomial} : Set WitnessLaurentAlgebra) = ⊤ := by
  classical
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  letI := hM
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  have ha : q (family.secondPointFactor i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hb : q (family.secondPointFactor k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hc : q (firstPointRecursionPolynomial family.polynomial) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  rw [← firstHom_apply] at hc
  simp only [FiniteSpectralFamily.polynomial, map_prod] at hc
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hc
  rw [firstHom_apply] at hj
  obtain ⟨a, _, hai⟩ := second_root q family i ha
  obtain ⟨b, _, hbk⟩ := second_root q family k hb
  obtain ⟨c, _, hcj⟩ := first_root q family j hj
  exact three_roots_impossible q (q.toMonoidHom.comp secondCharacter)
    (q.toMonoidHom.comp firstCharacter)
    (fun u => by change q (secondCharacter u) * q (firstCharacter u) = _; rw [← map_mul, second_first])
    (family.direction i) (family.direction k) (family.direction j)
    (family.pairwise_nonparallel i k hik) (direction_ne_zero family j) a b c hai hbk hcj

/-- Lemma 5.2, Step 1(iii): two c-factors and each a_i generate one. -/
theorem spectral_two_first_point_factors_coprime {m : ℕ}
    (family : FiniteSpectralFamily m) (i j l : Fin m) (hjl : j ≠ l) :
    Ideal.span ({family.secondPointFactor i, family.firstPointFactor j,
      family.firstPointFactor l} : Set WitnessLaurentAlgebra) = ⊤ := by
  classical
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  letI := hM
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  have ha : q (family.secondPointFactor i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hb : q (family.firstPointFactor j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hc : q (family.firstPointFactor l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  obtain ⟨a, _, hai⟩ := second_root q family i ha
  obtain ⟨b, _, hbj⟩ := first_root q family j hb
  obtain ⟨c, _, hcl⟩ := first_root q family l hc
  exact three_roots_impossible q (q.toMonoidHom.comp firstCharacter)
    (q.toMonoidHom.comp secondCharacter)
    (fun u => by change q (firstCharacter u) * q (secondCharacter u) = _; rw [← map_mul, mul_comm (firstCharacter u), second_first])
    (family.direction j) (family.direction l) (family.direction i)
    (family.pairwise_nonparallel j l hjl) (direction_ne_zero family i) b c a hbj hcl hai

end
end ConvexNivat
