import ConvexNivat.QuotientCRT
import ConvexNivat.QuotientSelectors
import ConvexNivat.QuotientPairSpanning

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

private theorem product_support_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → WitnessLaurentAlgebra) (z : Lattice)
    (hz : z ∈ (∏ i ∈ s, f i).coeff.support) :
    ∃ a : ι → Lattice, (∀ i ∈ s, a i ∈ (f i).coeff.support) ∧ z = ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
    have hz0 : z = 0 := by simpa [AddMonoidAlgebra.one_def] using hz
    exact ⟨fun _ => 0, by simp, by simpa using hz0⟩
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi] at hz
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hz)
    obtain ⟨a,ha,rfl⟩ := ih v hv
    refine ⟨Function.update a i u, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hu
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using ha j hj
    · rw [Finset.sum_insert hi, Function.update_self]
      rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _)]
      exact huv.symm

private theorem binomial_support {ι : Type*} (s : Finset ι) (v : Lattice)
    (b c : ι → LaurentRationalField) (z : Lattice)
    (hz : z ∈ (∏ i ∈ s, (AddMonoidAlgebra.single v (b i) -
      AddMonoidAlgebra.single 0 (c i))).coeff.support) :
    ∃ n : ℕ, n ≤ s.card ∧ z = n • v := by
  classical
  obtain ⟨a,ha,rfl⟩ := product_support_sum s _ z hz
  have hm : ∀ i ∈ s, a i = v ∨ a i = 0 := by
    intro i hi
    by_contra h
    push_neg at h
    have hx := Finsupp.mem_support_iff.mp (ha i hi)
    simp [AddMonoidAlgebra.coeff_sub, h.1, h.1.symm, h.2, h.2.symm] at hx
  refine ⟨(s.filter (fun i => a i = v)).card, Finset.card_filter_le _ _, ?_⟩
  calc
    _ = ∑ i ∈ s, if a i = v then v else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hm i hi with h | h <;> simp [h]
    _ = _ := by simp [Finset.sum_ite]

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


private theorem second_support {m : ℕ} (family : FiniteSpectralFamily m) (i : Fin m)
    (z : Lattice) (hz : z ∈ (family.secondPointFactor i).coeff.support) :
    ∃ n : ℕ, n ≤ (family.spectrum i).card ∧ z = n • family.direction i := by
  change z ∈ (secondHom (family.directionPolynomial i)).coeff.support at hz
  simp only [FiniteSpectralFamily.directionPolynomial, map_prod, map_sub] at hz
  apply binomial_support (family.spectrum i) (family.direction i) (fun _ => 1)
      (algebraMap ℂ LaurentRationalField) z
  simpa [secondHom, translationMonomial] using hz

private theorem first_support {m : ℕ} (family : FiniteSpectralFamily m) (i : Fin m)
    (z : Lattice) (hz : z ∈ (family.firstPointFactor i).coeff.support) :
    ∃ n : ℕ, n ≤ (family.spectrum i).card ∧ z = n • (-family.direction i) := by
  change z ∈ (firstPointRecursionPolynomial (family.directionPolynomial i)).coeff.support at hz
  rw [← firstHom_apply] at hz
  simp only [FiniteSpectralFamily.directionPolynomial, map_prod, map_sub] at hz
  have he := binomial_support (family.spectrum i) (-family.direction i)
    (fun _ => algebraMap LaurentPolynomial LaurentRationalField (translationMonomial (family.direction i)))
    (algebraMap ℂ LaurentRationalField) z
  apply he
  simpa [firstHom, firstCharacter, translationMonomial, AddMonoidAlgebra.liftNCRingHom,
    AddMonoidAlgebra.liftNC, AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def] using hz


private theorem bounded_product_support {m : ℕ} (s : Finset (Fin m))
    (v : Fin m → Lattice) (d : Fin m → ℕ) (f : Fin m → WitnessLaurentAlgebra)
    (hf : ∀ i ∈ s, ∀ z ∈ (f i).coeff.support, ∃ n : ℕ, n ≤ d i ∧ z = n • v i)
    (z : Lattice) (hz : z ∈ (∏ i ∈ s, f i).coeff.support) :
    ∃ n : Fin m → ℕ, (∀ i, n i ≤ d i) ∧ (∀ i ∉ s, n i = 0) ∧ z = ∑ i, n i • v i := by
  classical
  obtain ⟨a,ha,hz⟩ := product_support_sum s f z hz
  have hn : ∀ i, ∃ n : ℕ, n ≤ d i ∧ (i ∈ s → a i = n • v i) ∧ (i ∉ s → n = 0) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨n,hn,he⟩ := hf i hi (a i) (ha i hi)
      exact ⟨n,hn,fun _ => he,fun h => False.elim (h hi)⟩
    · exact ⟨0,Nat.zero_le _,fun h => False.elim (hi h),fun _ => rfl⟩
  choose n hn using hn
  refine ⟨n,fun i => (hn i).1,fun i hi => (hn i).2.2 hi, ?_⟩
  rw [hz, Finset.sum_congr rfl (fun i hi => (hn i).2.1 hi)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [(hn i).2.2 hi, zero_smul])

private theorem embed_sum_nsmul {m : ℕ} (n : Fin m → ℕ) (v : Fin m → Lattice) :
    embed (∑ i, n i • v i) = ∑ i, (n i : ℝ) • embed (v i) := by
  ext <;> simp [embed, Prod.fst_sum, Prod.snd_sum]

private theorem selector_support {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) (e : Lattice) (he : e ∈ latticePoints (spectralPairParallelogram family i j))
    (z : Lattice) (hz : z ∈ (spectralPairSelector family i j *
      AddMonoidAlgebra.single e (1 : LaurentRationalField)).coeff.support) :
    z ∈ latticePoints (family.zonotope.carrier - family.zonotope.carrier) := by
  classical
  obtain ⟨t,ht,e',he',hte⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hz)
  have heq : e' = e := by simpa using he'
  subst e'
  unfold spectralPairSelector at ht
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ ht)
  obtain ⟨n,hn,hni,hp⟩ := bounded_product_support (Finset.univ.erase i) family.direction
    (fun k => (family.spectrum k).card) family.secondPointFactor
    (fun k _ z hz => second_support family k z hz) p hp
  obtain ⟨k,hk,hkj,hq⟩ := bounded_product_support (Finset.univ.erase j) (fun l => -family.direction l)
    (fun l => (family.spectrum l).card) family.firstPointFactor
    (fun l _ z hz => first_support family l z hz) q hq
  have hni0 : n i = 0 := hni i (Finset.notMem_erase i _)
  have hkj0 : k j = 0 := hkj j (Finset.notMem_erase j _)
  obtain ⟨α,β,hα,hαd,hβ,hβd,he⟩ := he
  let a : Fin m → ℝ := fun l => (n l : ℝ) + if l = i then α else 0
  let b : Fin m → ℝ := fun l => (k l : ℝ) + if l = j then β else 0
  have ha : ∀ l, 0 ≤ a l ∧ a l ≤ ((family.spectrum l).card : ℝ) := by
    intro l
    by_cases hli : l = i
    · subst l
      simpa [a,hni0] using And.intro hα hαd
    · simpa [a,hli] using And.intro (Nat.cast_nonneg (n l) : (0 : ℝ) ≤ n l) (Nat.cast_le.mpr (hn l) : (n l : ℝ) ≤ (family.spectrum l).card)
  have hb : ∀ l, 0 ≤ b l ∧ b l ≤ ((family.spectrum l).card : ℝ) := by
    intro l
    by_cases hlj : l = j
    · subst l
      simpa [b,hkj0] using And.intro hβ hβd
    · simpa [b,hlj] using And.intro (Nat.cast_nonneg (k l) : (0 : ℝ) ≤ k l) (Nat.cast_le.mpr (hk l) : (k l : ℝ) ≤ (family.spectrum l).card)
  have hasum : (∑ l, a l • embed (family.direction l)) = embed p + α • embed (family.direction i) := by
    rw [hp,embed_sum_nsmul]
    simp [a, add_smul, Finset.sum_add_distrib, ite_smul]
  have hbsum : (∑ l, b l • embed (family.direction l)) = -embed q + β • embed (family.direction j) := by
    rw [hq,embed_sum_nsmul]
    have hneg (l : Fin m) : embed (-family.direction l) = -embed (family.direction l) := by ext <;> simp [embed]
    simp [b,add_smul,Finset.sum_add_distrib,ite_smul,hneg,smul_neg]
  change embed z ∈ family.zonotope.carrier - family.zonotope.carrier
  refine Set.mem_sub.mpr ⟨∑ l, a l • embed (family.direction l), ⟨a,ha,rfl⟩,
    ∑ l, b l • embed (family.direction l), ⟨b,hb,rfl⟩, ?_⟩
  rw [hasum,hbsum,← hte,← hpq]
  have hadd (u v : Lattice) : embed (u+v) = embed u + embed v := by ext <;> simp [embed]
  rw [hadd,hadd,he]
  module


private theorem selector_monomial_mem {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) (e : Lattice) (he : e ∈ latticePoints (spectralPairParallelogram family i j)) :
    Ideal.Quotient.mk (biRecursionIdeal family.polynomial)
      (spectralPairSelector family i j * AddMonoidAlgebra.single e (1 : LaurentRationalField)) ∈
    Submodule.span LaurentRationalField
      (quotientMonomial family.polynomial ''
        latticePoints (family.zonotope.carrier - family.zonotope.carrier)) := by
  let p := spectralPairSelector family i j * AddMonoidAlgebra.single e (1 : LaurentRationalField)
  let q := Ideal.Quotient.mkₐ LaurentRationalField (biRecursionIdeal family.polynomial)
  have hp := AddMonoidAlgebra.mem_span_support_coeff p
  have hq : q p ∈ Submodule.map q.toLinearMap
      (Submodule.span LaurentRationalField
        (AddMonoidAlgebra.of' LaurentRationalField Lattice '' (p.coeff.support : Set Lattice))) :=
    Submodule.mem_map.mpr ⟨p,hp,rfl⟩
  rw [Submodule.map_span] at hq
  apply Submodule.span_mono ?_ hq
  rintro x ⟨a,⟨d,hd,rfl⟩,rfl⟩
  exact ⟨d,selector_support family i j e he d hd,rfl⟩

/-- Full standalone Lemma 5.2: the actual K-vector-space quotient is spanned by
actual Laurent monomial images with lattice exponents in the actual Z-Z. -/
theorem quotient_spanned_by_spectral_difference_body {m : ℕ}
    (family : FiniteSpectralFamily m) (hm : 2 ≤ m) :
    QuotientSpannedBy family.polynomial
      (latticePoints (family.zonotope.carrier - family.zonotope.carrier)) := by
  classical
  let V := Submodule.span LaurentRationalField
    (quotientMonomial family.polynomial ''
      latticePoints (family.zonotope.carrier - family.zonotope.carrier))
  let e := spectralQuotientCRT family hm
  let q := Ideal.Quotient.mkₐ LaurentRationalField (biRecursionIdeal family.polynomial)
  let lift (ij : DistinctDirectionPair m) := e.symm.toLinearMap.comp
    (LinearMap.single LaurentRationalField (fun ij : DistinctDirectionPair m =>
      family.PairQuotient ij.val.1 ij.val.2) ij)
  have hproj (p : WitnessLaurentAlgebra) (ij : DistinctDirectionPair m) :
      e (q p) ij = Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2) p := rfl
  have hbase (ij : DistinctDirectionPair m) (d : Lattice)
      (hd : d ∈ latticePoints (spectralPairParallelogram family ij.val.1 ij.val.2)) :
      lift ij (Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2)
        (spectralPairSelector family ij.val.1 ij.val.2) *
        Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2)
          (AddMonoidAlgebra.single d (1 : LaurentRationalField))) ∈ V := by
    have heq : lift ij (Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2)
        (spectralPairSelector family ij.val.1 ij.val.2) *
        Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2)
          (AddMonoidAlgebra.single d (1 : LaurentRationalField))) =
        q (spectralPairSelector family ij.val.1 ij.val.2 * AddMonoidAlgebra.single d 1) := by
      apply e.injective
      change e (e.symm (Pi.single ij _)) = _
      rw [e.apply_symm_apply]
      funext kl
      rw [hproj,map_mul]
      by_cases hkl : kl = ij
      · subst kl
        rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hkl, spectral_pair_selector_vanishes_other]
        · exact (zero_mul (Ideal.Quotient.mk (family.pairIdeal kl.val.1 kl.val.2) (AddMonoidAlgebra.single d 1))).symm
        · by_contra h
          push_neg at h
          exact hkl (Subtype.ext (Prod.ext h.1 h.2))
    rw [heq]
    exact selector_monomial_mem family ij.val.1 ij.val.2 d hd
  have hcoord (ij : DistinctDirectionPair m) (x : family.PairQuotient ij.val.1 ij.val.2) :
      lift ij x ∈ V := by
    let E := Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2)
      (spectralPairSelector family ij.val.1 ij.val.2)
    obtain ⟨u,hu⟩ := spectral_pair_selector_unit family ij.val.1 ij.val.2 ij.property
    have hy : ∀ y : family.PairQuotient ij.val.1 ij.val.2, lift ij (E * y) ∈ V := by
      intro y
      have hy : y ∈ Submodule.span LaurentRationalField
          ((fun d : Lattice => Ideal.Quotient.mk (family.pairIdeal ij.val.1 ij.val.2)
            (AddMonoidAlgebra.single d (1 : LaurentRationalField))) ''
              latticePoints (spectralPairParallelogram family ij.val.1 ij.val.2)) := by
        rw [spectral_pair_quotient_spanned family ij.val.1 ij.val.2 ij.property]
        trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨d,hd,rfl⟩ := hy
        exact hbase ij d hd
      | zero =>
        rw [mul_zero E, map_zero]
        exact V.zero_mem
      | add y z hy hz hy' hz' => simpa only [mul_add, map_add] using V.add_mem hy' hz'
      | smul a y hy hy' => simpa only [mul_smul_comm, map_smul] using V.smul_mem a hy'
    have hx : E * ((u⁻¹ : (family.PairQuotient ij.val.1 ij.val.2)ˣ) : family.PairQuotient ij.val.1 ij.val.2) * x = x := by
      change (↑u : family.PairQuotient ij.val.1 ij.val.2) = E at hu
      rw [← hu, Units.mul_inv, one_mul]
    have h := hy (((u⁻¹ : (family.PairQuotient ij.val.1 ij.val.2)ˣ) : family.PairQuotient ij.val.1 ij.val.2) * x)
    rw [← mul_assoc E (↑u⁻¹) x, hx] at h
    exact h
  change V = ⊤
  apply top_unique
  intro x hx
  have hsum : (∑ ij : DistinctDirectionPair m, lift ij (e x ij)) ∈ V :=
    V.sum_mem (fun ij _ => hcoord ij (e x ij))
  have heq : (∑ ij : DistinctDirectionPair m, lift ij (e x ij)) = x := by
    change (∑ ij : DistinctDirectionPair m, e.symm (Pi.single ij (e x ij))) = x
    rw [← map_sum]
    have hh := Finset.univ_sum_single (e x)
    rw [hh,e.symm_apply_apply]
  rwa [heq] at hsum

end
end ConvexNivat
