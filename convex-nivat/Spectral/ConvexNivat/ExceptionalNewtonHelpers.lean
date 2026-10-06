import ConvexNivat.ExceptionalPolynomialDefinitions
import ConvexNivat.CoreLattice

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

private lemma binomial_support (v : Lattice) (hv : v ≠ 0) (ζ : ℂ) (hζ : ζ ≠ 0) :
    (translationMonomial v - AddMonoidAlgebra.single 0 ζ).coeff.support = {0, v} := by
  classical
  ext z
  simp only [Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_sub,
    translationMonomial, AddMonoidAlgebra.coeff_single, Finsupp.sub_apply,
    Finsupp.single_apply, Finset.mem_insert, Finset.mem_singleton]
  by_cases hz : z = 0
  · subst z
    simp [hv, hζ]
  · by_cases hzv : z = v
    · subst z
      simp [hv, Ne.symm hv]
    · simp [hz, hzv, Ne.symm hz, Ne.symm hzv]

private lemma binomial_newton (v : Lattice) (hv : v ≠ 0) (ζ : ℂ) (hζ : ζ ≠ 0) :
    newtonPolygon (translationMonomial v - AddMonoidAlgebra.single 0 ζ) =
      (fun t : ℝ => t • embed v) '' Set.Icc (0 : ℝ) 1 := by
  rw [newtonPolygon, binomial_support v hv ζ hζ]
  simp only [windowHull, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton]
  have hz : embed (0 : Lattice) = 0 := by ext <;> simp [embed]
  rw [hz, convexHull_pair, segment_eq_image]
  simp

private lemma interval_segment_add (v : RealPlane) (n : ℕ) :
    ((fun t : ℝ => t • v) '' Set.Icc (0 : ℝ) 1) +
      ((fun t : ℝ => t • v) '' Set.Icc (0 : ℝ) n) =
      (fun t : ℝ => t • v) '' Set.Icc (0 : ℝ) (n + 1 : ℕ) := by
  ext x
  constructor
  · rintro ⟨a, ⟨s, hs, rfl⟩, b, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨s + t, ⟨add_nonneg hs.1 ht.1, ?_⟩, add_smul _ _ _⟩
    push_cast
    linarith [hs.2, ht.2]
  · rintro ⟨t, ht, rfl⟩
    by_cases h : t ≤ 1
    · exact ⟨t • v, ⟨t, ⟨ht.1, h⟩, rfl⟩, 0, ⟨0, ⟨le_rfl, Nat.cast_nonneg n⟩,
        by simp⟩, by simp⟩
    · refine ⟨1 • v, ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩,
        (t - 1) • v, ⟨t - 1, ⟨by linarith, ?_⟩, rfl⟩, ?_⟩
      · push_cast at ht
        linarith [ht.2]
      · change 1 • v + (t - 1) • v = t • v
        rw [← add_smul]
        congr 1
        ring

lemma finite_binomial_newton (hmul : ∀ f g : LaurentPolynomial, f ≠ 0 → g ≠ 0 →
      windowHull (f * g).coeff.support = windowHull f.coeff.support + windowHull g.coeff.support)
    (v : Lattice) (hv : v ≠ 0) (s : Finset ℂ) (hs : ∀ ζ ∈ s, ζ ≠ 0) :
    newtonPolygon (∏ ζ ∈ s, (translationMonomial v - AddMonoidAlgebra.single 0 ζ)) =
      (fun t : ℝ => t • embed v) '' Set.Icc (0 : ℝ) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty]
      have hone : (1 : LaurentPolynomial).coeff.support = {0} := by
        simp [AddMonoidAlgebra.one_def]
      rw [newtonPolygon, hone]
      simp [windowHull, embed, convexHull_singleton]
  | @insert ζ s hζs ih =>
      have hζ := hs ζ (by simp)
      have hrest : ∀ μ ∈ s, μ ≠ 0 := fun μ hμ => hs μ (Finset.mem_insert_of_mem hμ)
      have hne (μ : ℂ) : translationMonomial v - AddMonoidAlgebra.single 0 μ ≠ 0 := by
        intro h
        have hc := congrArg (fun f : LaurentPolynomial => f.coeff v) h
        simp [translationMonomial, AddMonoidAlgebra.coeff_sub, hv] at hc
      rw [Finset.prod_insert hζs, newtonPolygon, hmul _ _ (hne ζ)
        (Finset.prod_ne_zero_iff.mpr fun μ _ => hne μ)]
      change newtonPolygon _ + newtonPolygon _ = _
      rw [binomial_newton v hv ζ hζ, ih hrest, Finset.card_insert_of_notMem hζs]
      exact interval_segment_add _ _

lemma finite_product_newton {ι : Type*}
    (hmul : ∀ f g : LaurentPolynomial, f ≠ 0 → g ≠ 0 →
      windowHull (f * g).coeff.support = windowHull f.coeff.support + windowHull g.coeff.support)
    (s : Finset ι) (f : ι → LaurentPolynomial) (hf : ∀ i ∈ s, f i ≠ 0) :
    newtonPolygon (∏ i ∈ s, f i) = ∑ i ∈ s, newtonPolygon (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hone : (1 : LaurentPolynomial).coeff.support = {0} := by
        simp [AddMonoidAlgebra.one_def]
      simp only [Finset.prod_empty, Finset.sum_empty]
      rw [newtonPolygon, hone]
      simp only [windowHull, Finset.coe_singleton, Set.image_singleton,
        convexHull_singleton]
      ext z
      simp [embed]
      rfl
  | @insert i s hi ih =>
      have hrest : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, newtonPolygon, hmul _ _ (hf i (by simp))
        (Finset.prod_ne_zero_iff.mpr hrest)]
      change newtonPolygon (f i) + newtonPolygon (∏ j ∈ s, f j) = _
      rw [ih hrest, Finset.sum_insert hi]

lemma sum_parameter_segments {ι : Type*} [Fintype ι] (v : ι → RealPlane) (n : ι → ℕ) :
    (∑ i, (fun t : ℝ => t • v i) '' Set.Icc (0 : ℝ) (n i)) =
      {x | ∃ t : ι → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ (n i : ℝ)) ∧ x = ∑ i, t i • v i} := by
  classical
  ext x
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨g, hg, hx⟩
    choose t ht he using hg
    refine ⟨t, ht, ?_⟩
    rw [← hx]
    apply Finset.sum_congr rfl
    intro i _
    exact (he i).symm
  · rintro ⟨t, ht, rfl⟩
    exact ⟨fun i => t i • v i, fun i => ⟨t i, ht i, rfl⟩, rfl⟩

end
end ConvexNivat
