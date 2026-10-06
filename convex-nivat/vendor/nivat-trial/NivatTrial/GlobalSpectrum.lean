import NivatTrial.Star
import NivatTrial.Spectral

/-! The spectral polynomial is constructed from the original star data.  Both
longitudinal limits are used.  Right defects alone suffice: they are nonzero,
one-sided, and provide all the cancellation needed for the periodic background. -/

namespace NivatTrial.GlobalSpectrum

open NivatTrial.Algebra NivatTrial.Periodicity NivatTrial.Isolation
open NivatTrial.Components NivatTrial.Spectral NivatTrial.Divisibility
open NivatTrial.Dynamics
open scoped Classical

noncomputable section

variable {ι α : Type*} [Fintype ι] [AddCommGroup α] (T : Star.Data ι α)

def complement (i : ι) : G :=
  Classical.choose (Geometry.exists_unimodular_complement (T.direction i) (T.primitive i))

theorem complement_spec (i : ι) : Geometry.det (T.direction i) (complement T i) = 1 :=
  Classical.choose_spec (Geometry.exists_unimodular_complement (T.direction i) (T.primitive i))

def coordinates (i : ι) : G ≃+ G :=
  basisEquiv (T.direction i) (complement T i) (complement_spec T i)

@[simp] theorem coordinates_first (i : ι) : coordinates T i (1, 0) = T.direction i :=
  basisEquiv_first _ _ _

@[simp] theorem coordinates_transverse (i : ι) (z : G) :
    ((coordinates T i).symm z).2 = Geometry.det (T.direction i) z := rfl

instance multiplierNeZero (i : ι) : NeZero (T.commonMultiplier i) :=
  ⟨Nat.ne_of_gt (T.commonMultiplier_spec i).1⟩

def ray (i : ι) (σ : Bool) : G := if σ then T.normalized.period i else -T.normalized.period i

def isolatedField (i : ι) (σ : Bool) : G → α := isolated T.normalized i (ray T i σ)

def tailField (i : ι) (σ : Bool) : G → α := pureRight T.normalized i (ray T i σ)

theorem isolatedField_period (i : ι) (σ : Bool) :
    IsPeriod (isolatedField T i σ) (T.normalized.period i) := by
  intro z
  simp only [isolatedField, isolated, T.normalized.component_period i z,
    background_common_period T.normalized i i (ray T i σ) z]

theorem tailField_period (i j : ι) (σ : Bool) :
    IsPeriod (tailField T i σ) (T.normalized.period j) :=
  pureRight_common_period T.normalized i j (ray T i σ)

theorem isolatedField_mem_languageHull (i : ι) (σ : Bool) :
    isolatedField T i σ ∈ languageHull T.total := by
  cases σ
  · exact isolated_negative_mem_languageHull T.normalized i (T.normalized_transverse · i)
  · exact isolated_positive_mem_languageHull T.normalized i (T.normalized_transverse · i)

theorem tailField_agreement (i : ι) (σ : Bool) (z : G)
    (hz : T.upper i < Geometry.det (T.direction i) z) :
    isolatedField T i σ z = tailField T i σ z :=
  isolated_right_agreement T.normalized i (ray T i σ) z hz

theorem isolatedField_ne_tailField (i : ι) (σ : Bool) :
    isolatedField T i σ ≠ tailField T i σ := by
  intro h
  apply T.component_ne_rightTail i
  funext z
  exact add_right_cancel (congrFun h z)

theorem alongPeriodic_of_period (i : ι) (J : G → ℂ)
    (hp : IsPeriod J (T.normalized.period i)) :
    AlongPeriodic (coordinates T i) (T.commonMultiplier i) J := by
  intro s t
  have heq : (s + (T.commonMultiplier i : ℤ), t) =
      (s, t) + T.commonMultiplier i • ((1, 0) : G) := by ext <;> simp
  change J (coordinates T i _) = J (coordinates T i _)
  rw [heq, map_add, map_nsmul, coordinates_first]
  exact hp _

theorem tailField_mem_languageHull [Nontrivial ι] (i : ι) (σ : Bool) :
    tailField T i σ ∈ languageHull T.total := by
  obtain ⟨j, hji⟩ := exists_ne i
  have hdet := T.normalized_transverse i j (Ne.symm hji)
  apply languageHull_trans (isolatedField_mem_languageHull T i σ)
  by_cases hpos : 0 < Geometry.det (T.direction i) (T.normalized.period j)
  · exact right_tail_mem_languageHull (isolatedField T i σ) (tailField T i σ)
      (T.direction i) (T.normalized.period j) (T.upper i)
      (tailField_period T i j σ) hpos (tailField_agreement T i σ)
  · have hneg : 0 < Geometry.det (T.direction i) (-T.normalized.period j) := by
      rw [Geometry.det_neg_right]
      change Geometry.det (T.direction i) (T.normalized.period j) ≠ 0 at hdet
      omega
    exact right_tail_mem_languageHull (isolatedField T i σ) (tailField T i σ)
      (T.direction i) (-T.normalized.period j) (T.upper i)
      (tailField_period T i j σ).neg hneg (tailField_agreement T i σ)

variable [Fintype α]

def frequencies (i : ι) : Finset (ZMod (T.commonMultiplier i)) :=
  Finset.univ.filter fun k => ∃ σ : Bool, ∃ a : α,
    projectAlong (coordinates T i) (T.commonMultiplier i) k
      (colourDifference (isolatedField T i σ) (tailField T i σ) a) ≠ 0

theorem mem_frequencies (i : ι) (k : ZMod (T.commonMultiplier i)) :
    k ∈ frequencies T i ↔ ∃ σ : Bool, ∃ a : α,
      projectAlong (coordinates T i) (T.commonMultiplier i) k
        (colourDifference (isolatedField T i σ) (tailField T i σ) a) ≠ 0 := by
  simp [frequencies]

theorem colour_periodic (i : ι) (σ : Bool) (a : α) :
    AlongPeriodic (coordinates T i) (T.commonMultiplier i)
      (colourDifference (isolatedField T i σ) (tailField T i σ) a) := by
  apply alongPeriodic_of_period T i
  intro z
  simp only [colourDifference, isolatedField_period T i σ z, tailField_period T i i σ z]

theorem encoded_periodic (i : ι) (σ : Bool) (w : α → ℤ) :
    AlongPeriodic (coordinates T i) (T.commonMultiplier i)
      (encodedDifference w (isolatedField T i σ) (tailField T i σ)) := by
  apply alongPeriodic_of_period T i
  intro z
  simp only [encodedDifference, isolatedField_period T i σ z, tailField_period T i i σ z]

theorem frequencies_nonempty (i : ι) : (frequencies T i).Nonempty := by
  have hne := isolatedField_ne_tailField T i true
  obtain ⟨z, hz⟩ : ∃ z, isolatedField T i true z ≠ tailField T i true z := by
    by_contra! h
    exact hne (funext h)
  let a := isolatedField T i true z
  have hcolour : colourDifference (isolatedField T i true) (tailField T i true) a ≠ 0 := by
    intro h
    have hzero := congrFun h z
    simp [colourDifference, a, Ne.symm hz] at hzero
  have hex : ∃ k : ZMod (T.commonMultiplier i),
      projectAlong (coordinates T i) (T.commonMultiplier i) k
        (colourDifference (isolatedField T i true) (tailField T i true) a) ≠ 0 := by
    by_contra! h
    apply hcolour
    rw [← sum_projectAlong (coordinates T i) _ (colour_periodic T i true a)]
    simp [h]
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, (mem_frequencies T i k).mpr ⟨true, a, hk⟩⟩

abbrev Index := (i : ι) × {k : ZMod (T.commonMultiplier i) // k ∈ frequencies T i}

def selectedSign (q : Index T) : Bool :=
  Classical.choose ((mem_frequencies T q.1 q.2).mp q.2.property)

theorem selected_occurs (q : Index T) : ∃ z : G, ∃ a : α,
    projectAlong (coordinates T q.1) (T.commonMultiplier q.1) q.2
      (colourDifference (isolatedField T q.1 (selectedSign T q))
        (tailField T q.1 (selectedSign T q)) a) z ≠ 0 := by
  obtain ⟨a, ha⟩ := Classical.choose_spec ((mem_frequencies T q.1 q.2).mp q.2.property)
  have hex : ∃ z, projectAlong (coordinates T q.1) (T.commonMultiplier q.1) q.2
      (colourDifference (isolatedField T q.1 (selectedSign T q))
        (tailField T q.1 (selectedSign T q)) a) z ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  obtain ⟨z, hz⟩ := hex
  exact ⟨z, a, hz⟩

theorem exists_encoding : ∃ w : α → ℤ, Function.Injective w ∧ ∀ q : Index T,
    projectAlong (coordinates T q.1) (T.commonMultiplier q.1) q.2
      (encodedDifference w (isolatedField T q.1 (selectedSign T q))
        (tailField T q.1 (selectedSign T q))) ≠ 0 := by
  exact exists_spectrum_preserving_encoding (fun q : Index T => T.commonMultiplier q.1)
    (fun q => coordinates T q.1) (fun q => q.2.val)
    (fun q => isolatedField T q.1 (selectedSign T q))
    (fun q => tailField T q.1 (selectedSign T q)) (selected_occurs T)

def encoding : α → ℤ := Classical.choose (exists_encoding T)

theorem encoding_injective : Function.Injective (encoding T) :=
  (Classical.choose_spec (exists_encoding T)).1

theorem encoding_occurs (q : Index T) :
    projectAlong (coordinates T q.1) (T.commonMultiplier q.1) q.2
      (encodedDifference (encoding T) (isolatedField T q.1 (selectedSign T q))
        (tailField T q.1 (selectedSign T q))) ≠ 0 :=
  (Classical.choose_spec (exists_encoding T)).2 q

def polynomial : Laurent :=
  ∏ q : Index T, binomial (T.direction q.1) (eigenvalue q.2.val : ℂ)

theorem polynomial_ne_zero : polynomial T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q _
  simpa only [coordinates_first] using
    (binomial_along_prime (coordinates T q.1) (eigenvalue q.2.val)).ne_zero

theorem polynomial_eq_prod : polynomial T =
    ∏ i, ∏ k ∈ frequencies T i, binomial (T.direction i) (eigenvalue k : ℂ) := by
  rw [polynomial, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  exact Finset.prod_coe_sort (frequencies T i) (fun k => binomial (T.direction i) (eigenvalue k : ℂ))

theorem polynomial_dvd_relation [Nontrivial ι] (f : Laurent) (c : ℂ)
    (hrelation : act f (fun z => (encoding T (T.total z) : ℂ)) = fun _ => c) :
    polynomial T ∣ f := by
  have h := lemma2_4_product (Finset.univ : Finset (Index T))
    (fun q => T.commonMultiplier q.1) (fun q => coordinates T q.1) (fun q => q.2.val)
    (fun q => encodedDifference (encoding T) (isolatedField T q.1 (selectedSign T q))
      (tailField T q.1 (selectedSign T q))) f
  simp only [coordinates_first] at h
  apply h
  · intro q _
    exact encoded_periodic T q.1 (selectedSign T q) (encoding T)
  · intro q _
    exact encoding_occurs T q
  · intro q _
    refine Or.inl ⟨T.upper q.1, ?_⟩
    intro z hz
    exact encodedDifference_zero_of_equal _ _ _ z
      (tailField_agreement T q.1 (selectedSign T q) z hz)
  · rintro ⟨i, k⟩ _ ⟨j, l⟩ _ hne
    by_cases hij : i = j
    · subst j
      right
      refine ⟨rfl, ?_⟩
      intro he
      apply hne
      congr 1
      exact Subtype.ext (eigenvalue_injective (Units.ext he))
    · left
      simpa only [coordinates_first, coordinates_transverse] using T.independent i j hij
  · intro q _
    exact annihilates_difference_of_localOrbitLimits f _ _ _ c
      (encode_mem_languageHull (fun a => (encoding T a : ℂ))
        (isolatedField_mem_languageHull T q.1 (selectedSign T q)))
      (encode_mem_languageHull (fun a => (encoding T a : ℂ))
        (tailField_mem_languageHull T q.1 (selectedSign T q))) hrelation

def directionPolynomial (i : ι) : Laurent :=
  ∏ k ∈ frequencies T i, binomial (T.direction i) (eigenvalue k : ℂ)

theorem directionPolynomial_eq_map (i : ι) : directionPolynomial T i =
    changeCoordinates (coordinates T i)
      (spectralAnnihilator (T.commonMultiplier i) (frequencies T i)) := by
  simp [directionPolynomial, spectralAnnihilator]

theorem directionPolynomial_dvd (i : ι) : directionPolynomial T i ∣ polynomial T := by
  rw [polynomial_eq_prod]
  exact Finset.dvd_prod_of_mem (fun j => directionPolynomial T j) (Finset.mem_univ i)

theorem project_encoded_eq_zero_of_not_mem (i : ι) (σ : Bool) (w : α → ℤ)
    (k : ZMod (T.commonMultiplier i)) (hk : k ∉ frequencies T i) :
    projectAlong (coordinates T i) (T.commonMultiplier i) k
      (encodedDifference w (isolatedField T i σ) (tailField T i σ)) = 0 := by
  funext z
  rw [projectAlong_encodedDifference]
  apply Finset.sum_eq_zero
  intro a _
  have hzero : projectAlong (coordinates T i) (T.commonMultiplier i) k
      (colourDifference (isolatedField T i σ) (tailField T i σ) a) = 0 := by
    by_contra h
    exact hk ((mem_frequencies T i k).mpr ⟨σ, a, h⟩)
  rw [hzero]
  simp

theorem directionPolynomial_annihilates (i : ι) (σ : Bool) (w : α → ℤ) :
    act (directionPolynomial T i)
      (encodedDifference w (isolatedField T i σ) (tailField T i σ)) = 0 := by
  let J := encodedDifference w (isolatedField T i σ) (tailField T i σ)
  have hzero := spectralAnnihilator_annihilates (frequencies T i)
    (inCoordinates (coordinates T i) J) (encoded_periodic T i σ w) (by
      intro k hk
      exact (projectAlong_eq_zero_iff (coordinates T i) k J).mp
        (project_encoded_eq_zero_of_not_mem T i σ w k hk))
  funext z
  rw [directionPolynomial_eq_map]
  have h := changeCoordinates_act (coordinates T i)
    (spectralAnnihilator (T.commonMultiplier i) (frequencies T i)) J
    ((coordinates T i).symm z)
  simpa only [AddEquiv.apply_symm_apply, Pi.zero_apply, J] using h.trans (congrFun hzero _)

theorem polynomial_annihilates_rightDefect (i : ι) (σ : Bool) (w : α → ℤ) :
    act (polynomial T) (rightDefect T.normalized i (ray T i σ)
      (fun a => (w a : ℂ))) = 0 := by
  exact act_eq_zero_of_dvd (directionPolynomial_dvd T i)
    (directionPolynomial_annihilates T i σ w)

def eigenvalues (i : ι) : Finset ℂˣ := (frequencies T i).image eigenvalue

theorem eigenvalues_nonempty (i : ι) : (eigenvalues T i).Nonempty :=
  (frequencies_nonempty T i).image eigenvalue

theorem eigenvalues_card (i : ι) : (eigenvalues T i).card = (frequencies T i).card := by
  exact Finset.card_image_of_injective _ eigenvalue_injective

theorem directionPolynomial_eq_eigenvalues (i : ι) : directionPolynomial T i =
    ∏ lam ∈ eigenvalues T i, binomial (T.direction i) (lam : ℂ) := by
  rw [eigenvalues, Finset.prod_image]
  · rfl
  · intro k _ l _ h
    exact eigenvalue_injective h

theorem polynomial_eq_eigenvalues : polynomial T =
    ∏ i, ∏ lam ∈ eigenvalues T i, binomial (T.direction i) (lam : ℂ) := by
  rw [polynomial_eq_prod]
  exact Finset.prod_congr rfl (fun i _ => directionPolynomial_eq_eigenvalues T i)

end

end NivatTrial.GlobalSpectrum
