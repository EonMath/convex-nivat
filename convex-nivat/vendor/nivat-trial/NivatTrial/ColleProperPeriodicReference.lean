import NivatTrial.CollePeriodicReferencePair
import NivatTrial.ColleReferenceSelection
import NivatTrial.ColleRationalDirections
import NivatTrial.ColleReferenceRigidity
import NivatTrial.ColleCoordinateTransport
import NivatTrial.ColleIntegerOpposite

/-! A genuine periodic interface supplies a proper periodic reference.
The reference is periodic in a positive multiple of an actual decomposition
direction, and has no doubly periodic extension across one oriented boundary. -/

namespace NivatTrial.ColleProperPeriodicReference

open NivatTrial.Geometry NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.Periodicity NivatTrial.ExternalInputs
open NivatTrial.CollePeriodicReferencePair
open NivatTrial.ColleReferenceSelection
open NivatTrial.ColleRationalDirections
open NivatTrial.ColleReferenceRigidity
open NivatTrial.ColleProperReferences
open NivatTrial.ColleCoordinateTransport
open NivatTrial.ColleDirectionalPropagation
open NivatTrial.LatticeCoordinates
open NivatTrial.ColleIntegerOpposite
open scoped Classical

noncomputable section

/-- The two actual periodic interface witnesses select a proper reference
on one of the two horizontal half-planes. -/
theorem low_complexity_has_proper_horizontal_reference {M m : ℕ}
    (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) m)
    (S : Finset Lattice) (hS : NivatTrial.LatticePolygon.IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card)
    (hpos : OneSidedNonexpansive θ (1,0))
    (hneg : OneSidedNonexpansive θ (-1,0)) :
    ∃ p ∈ languageHull θ,
      (∃ P : ℕ, 0 < P ∧ IsPeriod p (P • ((1,0) : Lattice))) ∧
      (¬HasDoublyPeriodicExtension p (halfPlane (1,0) 0) ∨
       ¬HasDoublyPeriodicExtension p (halfPlane (-1,0) 0)) := by
  obtain ⟨x,hx,y,hy,d,w,hw,hbad,hside,P,hP,hxP,hyP⟩ :=
    low_complexity_has_globally_periodic_interface_pair θ E S hS hlow hpos hneg
  have hxy : x ≠ y := by
    intro heq
    exact hbad (congrFun heq w)
  have hxperiod : ∃ q : ℕ, 0 < q ∧ IsPeriod x (q • ((1,0) : Lattice)) :=
    ⟨P,hP,hxP⟩
  have hyperiod : ∃ q : ℕ, 0 < q ∧ IsPeriod y (q • ((1,0) : Lattice)) :=
    ⟨P,hP,hyP⟩
  rcases hside with ⟨hupper,_⟩ | ⟨hlower,_⟩
  · have hagree : AgreeOn x y (halfPlane (1,0) 0) := by
      intro z hz
      apply hupper z
      have hs : (0 : ℝ) ≤ (z.2 : ℝ) := by simpa [halfPlane,score] using hz
      exact_mod_cast hs
    obtain ⟨p,hp,hperiod,hproper⟩ :=
      exists_proper_periodic_reference_of_interface θ x y hx hy
        (1,0) hxperiod hyperiod (1,0) (by simp) 0 hagree hxy
    exact ⟨p,hp,hperiod,Or.inl hproper⟩
  · have hagree : AgreeOn x y (halfPlane (-1,0) 0) := by
      intro z hz
      apply hlower z
      have hs : (z.2 : ℝ) ≤ 0 := by simpa [halfPlane,score] using hz
      exact_mod_cast hs
    obtain ⟨p,hp,hperiod,hproper⟩ :=
      exists_proper_periodic_reference_of_interface θ x y hx hy
        (1,0) hxperiod hyperiod (-1,0) (by simp) 0 hagree hxy
    exact ⟨p,hp,hperiod,Or.inr hproper⟩

/-- The selected nonexpansive horizontal direction is tangent to a genuine
factor of the integer decomposition. The proper reference has a positive
multiple of that factor direction as an actual global period. -/
theorem low_complexity_has_proper_component_reference {M m : ℕ}
    (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) m)
    (S : Finset Lattice) (hS : NivatTrial.LatticePolygon.IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card)
    (hpos : OneSidedNonexpansive θ (1,0))
    (hneg : OneSidedNonexpansive θ (-1,0)) :
    ∃ i : Fin m, ∃ p ∈ languageHull θ,
      (∃ K : ℕ, 0 < K ∧ IsPeriod p (K • E.period i)) ∧
      (¬HasDoublyPeriodicExtension p (halfPlane (1,0) 0) ∨
       ¬HasDoublyPeriodicExtension p (halfPlane (-1,0) 0)) := by
  obtain ⟨i,hi⟩ := tangent_factor_of_nonexpansive θ E (1,0) hpos
  obtain ⟨p,hp,⟨P,hP,hperiod⟩,hproper⟩ :=
    low_complexity_has_proper_horizontal_reference θ E S hS hlow hpos hneg
  have hhnz : P • ((1,0) : Lattice) ≠ 0 := by
    simp [Nat.ne_of_gt hP]
  have hpar : det (P • ((1,0) : Lattice)) (E.period i) = 0 := by
    have hi2 : (E.period i).2 = 0 := by
      have hs : ((E.period i).2 : ℝ) = 0 := by
        simpa [score] using hi
      exact_mod_cast hs
    simp [det,hi2]
  obtain ⟨K,hK,hKper⟩ :=
    parallel_period_of_arbitrary_alphabet hperiod hhnz (E.period i) hpar
  exact ⟨i,p,hp,⟨K,hK,hKper⟩,hproper⟩

/-- Proper half-plane references are invariant under integral changes of
coordinates, with the half-plane normal transformed by the dual map. -/
theorem extension_comp_equiv_iff {A : Type*}
    (e : Lattice ≃+ Lattice) (p : Lattice → A) (v : ℝ × ℝ) :
    HasDoublyPeriodicExtension (p ∘ e) (halfPlane (dualNormal e v) 0) ↔
      HasDoublyPeriodicExtension p (halfPlane v 0) := by
  constructor
  · rintro ⟨q,hq,hagree⟩
    let r := q ∘ e.symm
    have hr : IsDoublyPeriodic r := by
      obtain ⟨h,k,hdet,hh,hk⟩ := hq
      refine ⟨e h,e k,?_,?_,?_⟩
      · exact fun he => hdet ((det_equiv_zero_iff e h k).mp he)
      · exact (isPeriod_comp_iff e.symm q (e h)).mpr (by simpa using hh)
      · exact (isPeriod_comp_iff e.symm q (e k)).mpr (by simpa using hk)
    refine ⟨r,hr,?_⟩
    intro z hz
    have hz' : e.symm z ∈ halfPlane (dualNormal e v) 0 := by
      change (0 : ℝ) ≤ score (dualNormal e v) (e.symm z)
      rw [← score_mapWindow e v (e.symm z),e.apply_symm_apply]
      exact hz
    simpa [r,Function.comp_def] using hagree (e.symm z) hz'
  · rintro ⟨q,hq,hagree⟩
    let r := q ∘ e
    have hr : IsDoublyPeriodic r := by
      obtain ⟨h,k,hdet,hh,hk⟩ := hq
      refine ⟨e.symm h,e.symm k,?_,?_,?_⟩
      · exact fun he => hdet ((det_equiv_zero_iff e.symm h k).mp he)
      · exact (isPeriod_comp_iff e q (e.symm h)).mpr (by simpa using hh)
      · exact (isPeriod_comp_iff e q (e.symm k)).mpr (by simpa using hk)
    refine ⟨r,hr,?_⟩
    intro z hz
    have hz' : e z ∈ halfPlane v 0 := by
      change (0 : ℝ) ≤ score v (e z)
      rw [score_mapWindow e v z]
      exact hz
    exact hagree (e z) hz'

/-- Starting from an aperiodic low-complexity field and its genuine integer
decomposition, select a proper periodic reference in the original lattice.
The returned integral coordinates record which of the two half-planes is
proper, and the period remains a positive multiple of an actual factor. -/
theorem low_complexity_has_proper_reference {M m : ℕ}
    (hm : 2 ≤ m) (θ : Lattice → Fin M)
    (E : IntegerDecomposition (integerField θ) m)
    (S : Finset Lattice) (hS : NivatTrial.LatticePolygon.IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card)
    (hnot : ¬IsPeriodic θ) :
    ∃ e : Lattice ≃+ Lattice, ∃ i : Fin m, ∃ p ∈ languageHull θ,
      (∃ K : ℕ, 0 < K ∧ IsPeriod p (K • E.period i)) ∧
      (¬HasDoublyPeriodicExtension p
          (halfPlane (dualNormal e.symm (1,0)) 0) ∨
       ¬HasDoublyPeriodicExtension p
          (halfPlane (dualNormal e.symm (-1,0)) 0)) := by
  obtain ⟨j,k,c,e,hjk,hc,he,hvertical,hpos,hneg⟩ :=
    horizontal_opposite_of_low_complexity hm θ E S hlow hnot
  let S' := mapWindow e.symm S
  have hconv' : NivatTrial.LatticePolygon.IsLatticeConvex S' :=
    isLatticeConvex_mapWindow e.symm hS
  have hlow' : patternComplexity (θ ∘ e) S' ≤ S'.card := by
    calc
      patternComplexity (θ ∘ e) S' =
          patternComplexity ((θ ∘ e) ∘ e.symm) S := by
            exact patternComplexity_mapWindow e.symm (θ ∘ e) S
      _ = patternComplexity θ S := by
            congr 1
            funext z
            simp
      _ ≤ S.card := hlow
      _ = S'.card := (card_mapWindow e.symm S).symm
  let E' : IntegerDecomposition (integerField (θ ∘ e)) m :=
    reparametrize E e
  obtain ⟨i,p',hp',⟨K,hK,hper'⟩,hproper'⟩ :=
    low_complexity_has_proper_component_reference (θ ∘ e) E' S'
      hconv' hlow' hpos (by simpa using hneg)
  let p := p' ∘ e.symm
  have hp : p ∈ languageHull θ := by
    have hh := mem_languageHull_comp_equiv e.symm hp'
    simpa [p,Function.comp_def] using hh
  have hper : IsPeriod p (K • E.period i) := by
    apply (isPeriod_comp_iff e.symm p' (K • E.period i)).mpr
    have heq : e.symm (K • E.period i) = K • E'.period i := by
      change e.symm (K • E.period i) = K • e.symm (E.period i)
      rw [map_nsmul]
    rw [heq]
    exact hper'
  have hproper :
      ¬HasDoublyPeriodicExtension p
          (halfPlane (dualNormal e.symm (1,0)) 0) ∨
      ¬HasDoublyPeriodicExtension p
          (halfPlane (dualNormal e.symm (-1,0)) 0) := by
    rcases hproper' with hpplus | hpminus
    · exact Or.inl (fun hx => hpplus
        ((extension_comp_equiv_iff e.symm p' (1,0)).mp hx))
    · exact Or.inr (fun hx => hpminus
        ((extension_comp_equiv_iff e.symm p' (-1,0)).mp hx))
  exact ⟨e,i,p,hp,⟨K,hK,hper⟩,hproper⟩

end
end NivatTrial.ColleProperPeriodicReference
