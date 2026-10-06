import NivatTrial.ColleMaximalAgreementLimit

/-! A maximal agreement region formed from all finite long-faced windows.
The configuration is fixed throughout: no orbit limit is taken. Actual
annihilator coding makes the family directed and proves finite maximality. -/

namespace NivatTrial.ColleDirectedAgreement

open NivatTrial.Geometry NivatTrial.LatticePolygon NivatTrial.RegionGeometry
open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.OneSidedRecurrence
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleEnvelopeExpansion
open NivatTrial.ColleHullCoding NivatTrial.ColleMaximalSeedDefect
open NivatTrial.ColleMaximalAgreementLimit
open scoped Classical
noncomputable section

def windowUnion (C : Finset Lattice → Prop) : Set Lattice :=
  {z | ∃ T : Finset Lattice, C T ∧ z ∈ T}

theorem finite_subset_windowUnion (C : Finset Lattice → Prop)
    (hinh : ∃ T, C T)
    (hmerge : ∀ T S, C T → C S → ∃ U, C U ∧ T ⊆ U ∧ S ⊆ U)
    (F : Finset Lattice) (hF : (F : Set Lattice) ⊆ windowUnion C) :
    ∃ T, C T ∧ F ⊆ T := by
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨T,hT⟩ := hinh
    exact ⟨T,hT,Finset.empty_subset _⟩
  | @insert z F hz ih =>
    obtain ⟨T,hT,hFT⟩ := ih (fun w hw => hF (Finset.mem_insert_of_mem hw))
    obtain ⟨S,hS,hzS⟩ := hF (Finset.mem_insert_self z F)
    obtain ⟨U,hU,hTU,hSU⟩ := hmerge T S hT hS
    exact ⟨U,hU,Finset.insert_subset_iff.mpr ⟨hSU hzS,hFT.trans hTU⟩⟩

theorem windowUnion_isEnvelope (D : Finset Lattice) (C : Finset Lattice → Prop)
    (hinh : ∃ T, C T)
    (hmerge : ∀ T S, C T → C S → ∃ U, C U ∧ T ⊆ U ∧ S ⊆ U)
    (henv : ∀ T, C T → IsEnvelope D (T : Set Lattice)) :
    IsEnvelope D (windowUnion C) := by
  apply Set.Subset.antisymm _ (subset_supportHull D _)
  intro z hz
  have hw : ∀ d : D, ∃ w ∈ windowUnion C, det d w≤det d z :=
    fun d => (mem_supportHull_iff D (windowUnion C) z).mp hz d d.property
  let w : D → Lattice := fun d => Classical.choose (hw d)
  let F : Finset Lattice := Finset.univ.image w
  have hF : (F : Set Lattice) ⊆ windowUnion C := by
    intro a ha
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp ha
    exact (Classical.choose_spec (hw d)).1
  obtain ⟨T,hT,hFT⟩ := finite_subset_windowUnion C hinh hmerge F hF
  refine ⟨T,hT,?_⟩
  change z ∈ (T : Set Lattice)
  rw [← henv T hT]
  apply (mem_supportHull_iff D (T : Set Lattice) z).mpr
  intro d hd
  refine ⟨w ⟨d,hd⟩,hFT (Finset.mem_image.mpr ⟨⟨d,hd⟩,Finset.mem_univ _,rfl⟩),?_⟩
  exact (Classical.choose_spec (hw ⟨d,hd⟩)).2

theorem windowUnion_longFaces (D : Finset Lattice) (C : Finset Lattice → Prop)
    (hfaces : ∀ T, C T → LongFaces D (T : Set Lattice)) :
    LongFaces D (windowUnion C) := by
  intro d hd z hz hmin
  obtain ⟨T,hT,hzT⟩ := hz
  obtain ⟨w,hw,hwd,he⟩ := hfaces T hT d hd z hzT
    (fun s hs => hmin s ⟨T,hT,hs⟩)
  exact ⟨w,⟨T,hT,hw⟩,⟨T,hT,hwd⟩,he⟩

theorem finite_agreement_merge {A : Type*}
    (θ : Lattice → A) (code : A → ℤ) (hcode : Function.Injective code)
    (hs : List Lattice) (hne : ∀ d ∈ hs, d≠0)
    (hind : hs.Pairwise (fun d e => det d e≠0))
    (hann : iteratedIncrement hs (encode code θ)=0)
    (x p : Lattice → A) (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (D : Finset Lattice) (hdirs : ∀ d ∈ hs, d ∈ D ∧ -d ∈ D)
    (a b : Lattice) (hab : det a b≠0)
    (ha : a ∈ D) (hna : -a ∈ D) (hb : b ∈ D) (hnb : -b ∈ D)
    (Q : Set Lattice) (hQ : IsEnvelope D Q)
    (T S W : Finset Lattice) (hTc : IsLatticeConvex T) (hSc : IsLatticeConvex S)
    (hTf : LongFaces D (T : Set Lattice)) (hSf : LongFaces D (S : Set Lattice))
    (hTQ : (T : Set Lattice) ⊆ Q) (hSQ : (S : Set Lattice) ⊆ Q)
    (hTa : AgreeOn x p (T : Set Lattice)) (hSa : AgreeOn x p (S : Set Lattice))
    (hW : W.Nonempty) (hWc : IsLatticeConvex W) (hWf : LongFaces D (W : Set Lattice))
    (hWT : W ⊆ T) (hWS : W ⊆ S) :
    ∃ U : Finset Lattice, T ⊆ U ∧ S ⊆ U ∧ (U : Set Lattice) ⊆ Q ∧
      IsEnvelope D (U : Set Lattice) ∧ LongFaces D (U : Set Lattice) ∧
        AgreeOn x p (U : Set Lattice) := by
  let R := supportHull D ((T : Set Lattice) ∪ (S : Set Lattice))
  have hRQ : R ⊆ Q := by
    intro z hz
    rw [← hQ]
    exact supportHull_mono D (Set.union_subset hTQ hSQ) hz
  have hf : R.Finite := by
    change (supportHull D ((T : Set Lattice) ∪ (S : Set Lattice))).Finite
    rw [← Finset.coe_union,supportHull_finset D (T∪S)
      ((hW.mono hWT).mono Finset.subset_union_left)]
    exact envelope_finite D _ a b hab ha hna hb hnb
  let U := hf.toFinset
  have hU : (U : Set Lattice)=R := hf.coe_toFinset
  have hRf : LongFaces D R := (longFaces_union hTf hSf).supportHull
  have hRa : AgreeOn x p R := agreement_supportHull_union_of_common_window
    θ code hcode hs hne hind hann x p hx hp D T S W hdirs hTc hSc
      (factor_faces_of_directions hs D hdirs T hTf)
      (factor_faces_of_directions hs D hdirs S hSf) hW hWc
      (factor_faces_of_directions hs D hdirs W hWf) hWT hWS hTa hSa
  refine ⟨U,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    change z ∈ (U : Set Lattice)
    rw [hU]
    exact subset_supportHull D _ (Or.inl hz)
  · intro z hz
    change z ∈ (U : Set Lattice)
    rw [hU]
    exact subset_supportHull D _ (Or.inr hz)
  · rwa [hU]
  · rw [hU]
    exact supportHull_idempotent D _
  · rwa [hU]
  · rwa [hU]

def AgreementCandidate {A : Type*} (D : Finset Lattice) (x p : Lattice → A)
    (B : Finset Lattice) (Q : Set Lattice) (T : Finset Lattice) : Prop :=
  B ⊆ T ∧ (T : Set Lattice) ⊆ Q ∧ IsEnvelope D (T : Set Lattice) ∧
    LongFaces D (T : Set Lattice) ∧ AgreeOn x p (T : Set Lattice)

end
end NivatTrial.ColleDirectedAgreement
