import NivatTrial.KariMoutot
import NivatTrial.PeriodicNonexpansive
import NivatTrial.ColleRegions

/-! The opposite-direction theorem used in the convex Nivat reduction.
A symmetric minimal subsystem supplies a doubly periodic limit. A proper
half-plane interface with that limit is singly periodic, and therefore has
both orientations of its period line nonexpansive. -/

namespace NivatTrial.ColleOppositeDirections

open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.Periodicity
open NivatTrial.OneSidedRecurrence NivatTrial.PeriodicDifference
open NivatTrial.KariMoutot NivatTrial.RealHalfPlaneRecurrence
open NivatTrial.PeriodicInterface NivatTrial.ColleRegions
open NivatTrial.PeriodicNonexpansive NivatTrial.NonexpansiveExistence
open NivatTrial.LaurentAction NivatTrial.BinomialDirections
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

variable {A : Type*} [Fintype A]

/-- In a product-annihilated hull, a proper interface with a doubly periodic
point is globally periodic along the interface, though not doubly periodic. -/
theorem periodic_of_periodic_interface
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (hs : List Lattice) (hnonzero : ∀ h ∈ hs, h ≠ 0)
    (hpair : hs.Pairwise (fun h k => Geometry.det h k ≠ 0))
    (hann : iteratedIncrement hs (encode w θ) = 0)
    (v : Plane) (hv : v ≠ 0) (x y : Lattice → A)
    (hx : x ∈ languageHull θ) (hy : y ∈ languageHull θ)
    (hxDP : IsDoublyPeriodic x) (hne : x ≠ y)
    (hagree : AgreeOn x y (halfPlane v 0)) : IsPeriodic y := by
  have hneDirection : OneSidedNonexpansive θ v := ⟨x,hx,y,hy,hne,hagree⟩
  have htan : ∃ h, h ∈ hs ∧ score v h = 0 := by
    by_contra hnone
    have htrans : ∀ h ∈ hs, score v h ≠ 0 := by
      intro h hh hzero
      exact hnone ⟨h,hh,hzero⟩
    exact oneSidedExpansive_of_transverse_product θ w hw hs v htrans hann hneDirection
  obtain ⟨h,hh,hvh⟩ := htan
  have hi := tangent_increment_agrees θ w hs hann (-v) (neg_ne_zero.mpr hv)
    h hh (by rw [score_neg_direction,hvh,neg_zero]) hpair hx hy (by
      intro z hz
      apply hagree z
      change 0 ≤ score v z
      rw [score_neg_direction] at hz
      linarith)
  have hdiff : IsPeriod (encode w y - encode w x) h := by
    intro z
    have he := congrFun hi z
    simp only [increment] at he
    simp only [Pi.sub_apply]
    omega
  obtain ⟨Q,hQ,hxp⟩ := direction_period_of_finite_orbit x h
    (finite_orbit_of_doublyPeriodic x hxDP)
  have hyint : IsPeriod (encode w y) (Q•h) := by
    have hp := (hdiff.nsmul Q).add_config (hxp.encode w)
    simpa only [encode,sub_add_cancel] using hp
  refine ⟨Q•h,?_,(isPeriod_encode_iff hw y (Q•h)).mp hyint⟩
  intro he
  have hz := (hnonzero h hh)
  apply hz
  apply Prod.ext
  · have he1 := congrArg Prod.fst he
    simpa [nsmul_eq_mul, Nat.ne_of_gt hQ] using he1
  · have he2 := congrArg Prod.snd he
    simpa [nsmul_eq_mul, Nat.ne_of_gt hQ] using he2

theorem doublyPeriodic_of_no_opposite_nonexpansive_product
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (hs : List Lattice) (hnonzero : ∀ h ∈ hs, h ≠ 0)
    (hpair : hs.Pairwise (fun h k => Geometry.det h k ≠ 0))
    (hann : iteratedIncrement hs (encode w θ) = 0)
    (hno : ∀ v : Plane, v ≠ 0 →
      ¬(OneSidedNonexpansive θ v ∧ OneSidedNonexpansive θ (-v))) :
    IsDoublyPeriodic θ := by
  obtain ⟨p,hp,hsymm⟩ := directional_symmetry_of_product θ w hw hs hnonzero hpair hann
  have hpDP : IsDoublyPeriodic p := by
    apply doublyPeriodic_of_all_oneSidedExpansive p
    intro v hv hn
    have hnopp : OneSidedNonexpansive p (-v) := by
      by_contra he
      have he' := hsymm (-v) (neg_ne_zero.mpr hv) he
      exact he' (by simpa only [neg_neg] using hn)
    exact hno v hv ⟨oneSidedNonexpansive_of_hull hp hn,
      oneSidedNonexpansive_of_hull hp hnopp⟩
  by_contra hnot
  obtain ⟨v,hv,x,hxp,y,hy,hxy,hagree⟩ := exists_periodic_interface θ p hp hpDP hnot
  have hx : x ∈ languageHull θ :=
    languageHull_trans hp (orbit_subset_languageHull p hxp)
  have hxDP : IsDoublyPeriodic x := by
    obtain ⟨u,hu⟩ := hxp
    rw [← hu]
    exact hpDP.shift u
  have hyper := periodic_of_periodic_interface θ w hw hs hnonzero hpair hann
    v hv x y hx hy hxDP hxy hagree
  have hynot : ¬IsDoublyPeriodic y :=
    fun hdp => hxy (doublyPeriodic_eq_of_halfPlane_agreement hxDP hdp hv hagree)
  obtain ⟨u,hu,hu1,hu2⟩ := exists_opposite_nonexpansive_of_singlyPeriodic y hyper hynot
  exact hno u hu ⟨oneSidedNonexpansive_of_hull hy hu1,
    oneSidedNonexpansive_of_hull hy hu2⟩

/-- Colle's opposite-direction conclusion, with the integer annihilator
as the actual hypothesis rather than an imported theorem record. -/
theorem exists_opposite_nonexpansive_of_annihilator
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (f : RingLaurent ℤ) (hf : f ≠ 0) (hann : act f (encode w θ) = 0)
    (hnot : ¬IsDoublyPeriodic θ) :
    ∃ v : Plane, v ≠ 0 ∧ OneSidedNonexpansive θ v ∧ OneSidedNonexpansive θ (-v) := by
  have hfinite : (Set.range (encode w θ)).Finite := by
    apply (Set.finite_range w).subset
    rintro a ⟨z,rfl⟩
    exact ⟨θ z,rfl⟩
  obtain ⟨hs,hpair,hnonzero,hprod⟩ :=
    independent_difference_annihilator f (encode w θ) hf hfinite hann
  by_contra hnone
  apply hnot
  apply doublyPeriodic_of_no_opposite_nonexpansive_product θ w hw hs hnonzero hpair hprod
  intro v hv hp
  exact hnone ⟨v,hv,hp⟩

theorem exists_opposite_nonexpansive_of_low_complexity
    (θ : Lattice → A) (S : Finset Lattice)
    (hlow : patternComplexity θ S ≤ S.card) (hnot : ¬IsPeriodic θ) :
    ∃ v : Plane, v ≠ 0 ∧ OneSidedNonexpansive θ v ∧ OneSidedNonexpansive θ (-v) := by
  let w : A → ℤ := fun a => (Fintype.equivFin A a).val
  have hw : Function.Injective w := by
    intro a b hab
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    dsimp [w] at hab
    exact_mod_cast hab
  obtain ⟨f,hf,hann⟩ := NivatTrial.IntegerAnnihilator.exists_integer_annihilator θ S w hlow
  exact exists_opposite_nonexpansive_of_annihilator θ w hw f hf hann
    (fun hp => hnot hp.isPeriodic)

/-- The exact finite-range integer formulation of the cited theorem. -/
theorem exists_opposite_nonexpansive_of_finite_range
    (x : Lattice → ℤ) (hfinite : (Set.range x).Finite)
    (f : RingLaurent ℤ) (hf : f ≠ 0) (hann : act f x = 0)
    (hnot : ¬IsDoublyPeriodic x) :
    ∃ v : Plane, v ≠ 0 ∧ OneSidedNonexpansive x v ∧ OneSidedNonexpansive x (-v) := by
  let B := Set.range x
  let : Fintype B := hfinite.fintype
  let θ : Lattice → B := fun z => ⟨x z,⟨z,rfl⟩⟩
  have he : encode Subtype.val θ = x := rfl
  have hinj : Function.Injective (Subtype.val : B → ℤ) := Subtype.val_injective
  have hnθ : ¬IsDoublyPeriodic θ := fun hp => hnot (he ▸ hp.encode Subtype.val)
  obtain ⟨v,hv,hv1,hv2⟩ := exists_opposite_nonexpansive_of_annihilator θ Subtype.val hinj
    f hf (he ▸ hann) hnθ
  have htransfer (u : Plane) (hu : OneSidedNonexpansive θ u) :
      OneSidedNonexpansive x u := by
    rw [← he]
    by_contra hn
    exact (oneSidedExpansive_encode_iff θ Subtype.val hinj u).mp hn hu
  exact ⟨v,hv,htransfer v hv1,htransfer (-v) hv2⟩

end
end NivatTrial.ColleOppositeDirections
