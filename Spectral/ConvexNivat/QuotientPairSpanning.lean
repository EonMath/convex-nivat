import ConvexNivat.QuotientDefinitions

open scoped BigOperators
open Polynomial
namespace ConvexNivat
noncomputable section

private theorem unit_zpow_span {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (u : Sˣ) (p : K[X]) (hp : p.Monic) (hp0 : p.coeff 0 ≠ 0)
    (hu : aeval (u : S) p = 0) (n : ℤ) :
    ((u ^ n : Sˣ) : S) ∈
      Submodule.span K (Set.range (fun r : Fin p.natDegree => (u : S) ^ r.val)) := by
  let r : K[X] := C (-(p.coeff 0)⁻¹) * p.divX
  have hx : (u : S) * aeval (u : S) p.divX = -algebraMap K S (p.coeff 0) := by
    have h := congrArg (aeval (u : S)) (X_mul_divX_add p)
    simpa only [map_add, map_mul, aeval_X, aeval_C, hu, add_eq_zero_iff_eq_neg] using h
  have hr : (u : S) * aeval (u : S) r = 1 := by
    simp only [r, map_mul, aeval_C]
    rw [mul_left_comm, hx, map_neg, neg_mul_neg, ← map_mul, inv_mul_cancel₀ hp0, map_one]
  have hinv : ((u⁻¹ : Sˣ) : S) = aeval (u : S) r := by
    calc
      _ = (↑u⁻¹ : S) * 1 := (mul_one _).symm
      _ = (↑u⁻¹ : S) * ((u : S) * aeval (u : S) r) := by rw [hr]
      _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hex : ∃ f : K[X], ((u ^ n : Sˣ) : S) = aeval (u : S) f := by
    cases n with
    | ofNat k => exact ⟨X ^ k, by simp⟩
    | negSucc k => exact ⟨r ^ (k + 1), by simp [zpow_negSucc, hinv]⟩
  obtain ⟨f,hf⟩ := hex
  apply PowerBasis.mem_span_pow'.mpr
  refine ⟨f %ₘ p, (degree_modByMonic_lt f hp).trans_le degree_le_natDegree, ?_⟩
  rw [aeval_modByMonic_eq_self_of_root hu, hf]


private theorem floor_decomposition (u v z : Lattice) (hdet : det u v ≠ 0) :
    ∃ (r : Lattice) (n k : ℤ) (α β : ℝ),
      0 ≤ α ∧ α < 1 ∧ 0 ≤ β ∧ β < 1 ∧
      embed r = α • embed u + β • embed v ∧ z = r + n • u + k • v := by
  let s : ℝ := (det z v : ℝ) / (det u v : ℝ)
  let t : ℝ := (det u z : ℝ) / (det u v : ℝ)
  have hd : (det u v : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hz : embed z = s • embed u + t • embed v := by
    apply Prod.ext
    · change (z.1 : ℝ) = s * (u.1 : ℝ) + t * (v.1 : ℝ)
      dsimp [s,t]
      field_simp [hd]
      simp only [det,Int.cast_sub,Int.cast_mul]
      ring
    · change (z.2 : ℝ) = s * (u.2 : ℝ) + t * (v.2 : ℝ)
      dsimp [s,t]
      field_simp [hd]
      simp only [det,Int.cast_sub,Int.cast_mul]
      ring
  refine ⟨z - ⌊s⌋ • u - ⌊t⌋ • v, ⌊s⌋, ⌊t⌋, s - ⌊s⌋, t - ⌊t⌋,
    sub_nonneg.mpr (Int.floor_le s), ?_, sub_nonneg.mpr (Int.floor_le t), ?_, ?_, ?_⟩
  · have h := Int.lt_floor_add_one s; linarith
  · have h := Int.lt_floor_add_one t; linarith
  · have he (a b : Lattice) : embed (a-b) = embed a - embed b := by ext <;> simp [embed]
    have hs (k : ℤ) (a : Lattice) : embed (k • a) = (k : ℝ) • embed a := by ext <;> simp [embed]
    rw [he, he, hs, hs, hz]
    module
  · abel

private theorem root_power_span {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    {ι : Type*} (s : Finset ι) (c : ι → K) (hc : ∀ t ∈ s, c t ≠ 0)
    (u : Sˣ) (hu : ∏ t ∈ s, ((u : S) - algebraMap K S (c t)) = 0) (n : ℤ) :
    ((u ^ n : Sˣ) : S) ∈ Submodule.span K
      (Set.range (fun r : Fin s.card => (u : S) ^ r.val)) := by
  classical
  let p : K[X] := ∏ t ∈ s, (X - C (c t))
  have hp : p.Monic := monic_prod_X_sub_C c s
  have hpdeg : p.natDegree = s.card := natDegree_finsetProd_X_sub_C_eq_card s c
  have hp0 : p.coeff 0 ≠ 0 := by
    change (∏ t ∈ s, (X - C (c t))).coeff 0 ≠ 0
    rw [coeff_zero_eq_eval_zero, eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    exact Finset.prod_ne_zero_iff.mpr (fun t ht => neg_ne_zero.mpr (hc t ht))
  have hup : aeval (u : S) p = 0 := by simpa [p] using hu
  apply Submodule.span_mono (s := Set.range (fun r : Fin p.natDegree => (u : S) ^ r.val)) ?_
    (unit_zpow_span u p hp hp0 hup n)
  rintro x ⟨r,rfl⟩
  exact ⟨⟨r.val, by simpa only [hpdeg] using r.isLt⟩, rfl⟩

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



private theorem monomial_product (r u v : Lattice) (n k : ℤ) :
    AddMonoidAlgebra.single r (1 : LaurentRationalField) *
      secondCharacter (.ofAdd (n • u)) * firstCharacter (.ofAdd (k • v)) =
    xCharacter (.ofAdd (k • v)) •
      AddMonoidAlgebra.single (r + n • u - k • v) (1 : LaurentRationalField) := by
  simp [secondCharacter, firstCharacter, xCharacter, translationMonomial,
    AddMonoidAlgebra.single_mul_single, sub_eq_add_neg, Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_root_second {m : ℕ} (family : FiniteSpectralFamily m) (i j : Fin m) :
    ∏ t ∈ family.spectrum i,
      (Ideal.Quotient.mk (family.pairIdeal i j) (secondCharacter (.ofAdd (family.direction i))) -
        Ideal.Quotient.mk (family.pairIdeal i j) (scalarC t)) = 0 := by
  have h : Ideal.Quotient.mk (family.pairIdeal i j) (family.secondPointFactor i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
  change Ideal.Quotient.mk _ (secondHom (family.directionPolynomial i)) = 0 at h
  simpa [FiniteSpectralFamily.directionPolynomial, secondHom, secondCharacter,
    translationMonomial, scalarC, scalarK] using h

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_root_first {m : ℕ} (family : FiniteSpectralFamily m) (i j : Fin m) :
    ∏ t ∈ family.spectrum j,
      (Ideal.Quotient.mk (family.pairIdeal i j) (firstCharacter (.ofAdd (family.direction j))) -
        Ideal.Quotient.mk (family.pairIdeal i j) (scalarC t)) = 0 := by
  have h : Ideal.Quotient.mk (family.pairIdeal i j) (family.firstPointFactor j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [FiniteSpectralFamily.pairIdeal]))
  change Ideal.Quotient.mk _ (firstPointRecursionPolynomial (family.directionPolynomial j)) = 0 at h
  rw [← firstHom_apply] at h
  simp only [FiniteSpectralFamily.directionPolynomial, map_prod, map_sub] at h
  simpa [firstHom, translationMonomial, firstCharacter, AddMonoidAlgebra.liftNCRingHom,
    AddMonoidAlgebra.liftNC, AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def,
    scalarC, scalarK] using h


private theorem character_zpow {S : Type*} [Monoid S]
    (χ : Multiplicative Lattice →* S) (u : Lattice) (n : ℤ) :
    ((χ.toHomUnits (.ofAdd u) ^ n : Sˣ) : S) = χ (.ofAdd (n • u)) := by
  change _ = ((χ.toHomUnits (.ofAdd (n • u)) : Sˣ) : S)
  rw [ofAdd_zsmul, map_zpow]

private theorem character_natpow {S : Type*} [Monoid S]
    (χ : Multiplicative Lattice →* S) (u : Lattice) (n : ℕ) :
    χ (.ofAdd ((n : ℤ) • u)) = χ (.ofAdd u) ^ n := by
  rw [natCast_zsmul, ofAdd_nsmul, map_pow]

private theorem pair_monomial_mem {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) (hij : i ≠ j) (z : Lattice) :
    Ideal.Quotient.mk (family.pairIdeal i j) (AddMonoidAlgebra.single z (1 : LaurentRationalField)) ∈
      Submodule.span LaurentRationalField
        ((fun d : Lattice => Ideal.Quotient.mk (family.pairIdeal i j)
          (AddMonoidAlgebra.single d (1 : LaurentRationalField))) ''
            latticePoints (spectralPairParallelogram family i j)) := by
  classical
  let Q := family.PairQuotient i j
  let q : WitnessLaurentAlgebra →ₐ[LaurentRationalField] Q :=
    Ideal.Quotient.mkₐ LaurentRationalField (family.pairIdeal i j)
  let y : Multiplicative Lattice →* Q := q.toMonoidHom.comp secondCharacter
  let w : Multiplicative Lattice →* Q := q.toMonoidHom.comp firstCharacter
  let V := Submodule.span LaurentRationalField
    ((fun d : Lattice => q (AddMonoidAlgebra.single d (1 : LaurentRationalField))) ''
      latticePoints (spectralPairParallelogram family i j))
  have hd : det (family.direction i) (-family.direction j) ≠ 0 := by
    have he : det (family.direction i) (-family.direction j) = -det (family.direction i) (family.direction j) := by simp [det]; ring
    rw [he]
    exact neg_ne_zero.mpr (family.pairwise_nonparallel i j hij)
  obtain ⟨r,n,k,α,β,hα,hα1,hβ,hβ1,hr,hz⟩ :=
    floor_decomposition (family.direction i) (-family.direction j) z hd
  have hs (l : Fin m) : ∀ t ∈ family.spectrum l,
      algebraMap ℂ LaurentRationalField t ≠ 0 := by
    intro t ht
    exact (_root_.map_ne_zero _).mpr (family.spectrum_nonzero l t ht)
  have hy := root_power_span (K := LaurentRationalField) (S := Q)
    (family.spectrum i) (algebraMap ℂ LaurentRationalField)
    (hs i) (y.toHomUnits (.ofAdd (family.direction i)))
    (by exact quotient_root_second family i j) n
  have hw := root_power_span (K := LaurentRationalField) (S := Q)
    (family.spectrum j) (algebraMap ℂ LaurentRationalField)
    (hs j) (w.toHomUnits (.ofAdd (family.direction j)))
    (by exact quotient_root_first family i j) k
  rw [character_zpow] at hy hw
  have hgen (a : Fin (family.spectrum i).card) (b : Fin (family.spectrum j).card) :
      q (AddMonoidAlgebra.single r 1) * y (.ofAdd (family.direction i)) ^ a.val *
        w (.ofAdd (family.direction j)) ^ b.val ∈ V := by
    rw [← character_natpow, ← character_natpow]
    change q (AddMonoidAlgebra.single r 1) * q (secondCharacter _) * q (firstCharacter _) ∈ V
    rw [← map_mul, ← map_mul, monomial_product, map_smul]
    apply V.smul_mem
    apply Submodule.subset_span
    refine ⟨r + (a.val : ℤ) • family.direction i - (b.val : ℤ) • family.direction j, ?_, rfl⟩
    change ∃ x b' : ℝ, 0 ≤ x ∧ x ≤ ((family.spectrum i).card : ℝ) ∧
      0 ≤ b' ∧ b' ≤ ((family.spectrum j).card : ℝ) ∧ _
    refine ⟨α + a.val, β + b.val, by positivity, ?_, by positivity, ?_, ?_⟩
    · have ha : (a.val : ℝ) + 1 ≤ ((family.spectrum i).card : ℝ) := by exact_mod_cast a.isLt
      linarith
    · have hb : (b.val : ℝ) + 1 ≤ ((family.spectrum j).card : ℝ) := by exact_mod_cast b.isLt
      linarith
    · have he : embed (r + (a.val : ℤ) • family.direction i - (b.val : ℤ) • family.direction j) =
          embed r + (a.val : ℝ) • embed (family.direction i) - (b.val : ℝ) • embed (family.direction j) := by
        ext <;> simp [embed]
      rw [he,hr]
      have hneg : embed (-family.direction j) = -embed (family.direction j) := by ext <;> simp [embed]
      rw [hneg]
      module
  have hmul : q (AddMonoidAlgebra.single r 1) * y (.ofAdd (n • family.direction i)) *
      w (.ofAdd (k • family.direction j)) ∈ V := by
    generalize hy0 : y (.ofAdd (n • family.direction i)) = y0 at hy ⊢
    generalize hw0 : w (.ofAdd (k • family.direction j)) = w0 at hw ⊢
    clear hy0 hw0
    induction hy, hw using Submodule.span_induction₂ with
    | mem_mem u v hu hv =>
      obtain ⟨a,rfl⟩ := hu
      obtain ⟨b,rfl⟩ := hv
      exact hgen a b
    | zero_left v hv =>
      change q (AddMonoidAlgebra.single r 1) * (0 : Q) * v ∈ V
      rw [mul_zero (q (AddMonoidAlgebra.single r 1)), zero_mul v]
      exact V.zero_mem
    | zero_right u hu =>
      change (q (AddMonoidAlgebra.single r 1) * u) * (0 : Q) ∈ V
      rw [mul_zero (q (AddMonoidAlgebra.single r 1) * u)]
      exact V.zero_mem
    | add_left u₁ u₂ v hu₁ hu₂ hv h₁ h₂ => simpa [mul_add, add_mul] using V.add_mem h₁ h₂
    | add_right u v₁ v₂ hu hv₁ hv₂ h₁ h₂ => simpa [mul_add, add_mul] using V.add_mem h₁ h₂
    | smul_left a u v hu hv huv => simpa [mul_smul_comm, smul_mul_assoc] using V.smul_mem a huv
    | smul_right a u v hu hv huv => simpa [mul_smul_comm] using V.smul_mem a huv
  change q (AddMonoidAlgebra.single r 1) * q (secondCharacter _) * q (firstCharacter _) ∈ V at hmul
  rw [← map_mul, ← map_mul, monomial_product, map_smul] at hmul
  have hxnz : xCharacter (.ofAdd (k • family.direction j)) ≠ 0 :=
    (xCharacter.toHomUnits _).ne_zero
  have hz' : r + n • family.direction i - k • family.direction j = z := by
    rw [hz, smul_neg, sub_eq_add_neg]
  rw [hz'] at hmul
  exact (V.smul_mem_iff hxnz).mp hmul

/-- Lemma 5.2, Step 2: each pair quotient has monomial generators in P_ij. -/
theorem spectral_pair_quotient_spanned {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) (hij : i ≠ j) :
    Submodule.span LaurentRationalField
      ((fun d : Lattice => Ideal.Quotient.mk (family.pairIdeal i j)
        (AddMonoidAlgebra.single d (1 : LaurentRationalField))) ''
          latticePoints (spectralPairParallelogram family i j)) = ⊤ := by
  classical
  apply top_unique
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  clear hx
  induction p using AddMonoidAlgebra.induction_on with
  | of z => exact pair_monomial_mem family i j hij z
  | add p r hp hr => simpa only [map_add] using Submodule.add_mem _ hp hr
  | smul a p hp =>
    exact Submodule.smul_mem _ a hp

end
end ConvexNivat
