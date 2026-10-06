import NivatTrial.ColleCaseTwoConclusion
import NivatTrial.ColleCoordinateTransport
import NivatTrial.LatticeCoordinates

/-! Reflection of the exact finite-normal envelope geometry. The normal
`d` becomes `-reflectX d`: this preserves its determinant support value,
including lower supports and exposed faces, even though the reflection
reverses orientation. -/

namespace NivatTrial.ColleCaseOneReflectionTransport

open NivatTrial.Geometry NivatTrial.LatticePolygon
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleMaximalAgreementLimit NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleCoordinateTransport NivatTrial.RegionGeometry
open NivatTrial.LatticeCoordinates
open NivatTrial.ColleDirectionalPropagation NivatTrial.ColleCaseTwoConclusion
open NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.ColleGenerating
open NivatTrial.Nonexpansive
open scoped Classical
noncomputable section

def reflectX : Lattice ≃+ Lattice where
  toFun z := (-z.1,z.2)
  invFun z := (-z.1,z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by ext <;> simp [add_comm]

@[simp] theorem reflectX_apply (z : Lattice) :
    reflectX z = (-z.1,z.2) := rfl

@[simp] theorem reflectX_symm_apply (z : Lattice) :
    reflectX.symm z = reflectX z := rfl

theorem reflectX_symm : reflectX.symm = reflectX := by
  ext z <;> simp [reflectX]

@[simp] theorem reflectX_involutive (z : Lattice) :
    reflectX (reflectX z) = z := by ext <;> simp [reflectX]

def dualNormal (d : Lattice) : Lattice := -reflectX d

@[simp] theorem dualNormal_involutive (d : Lattice) :
    dualNormal (dualNormal d) = d := by
  simp [dualNormal]

@[simp] theorem dualNormal_neg (d : Lattice) :
    dualNormal (-d) = -dualNormal d := by
  simp [dualNormal]

@[simp] theorem reflectX_dualNormal (d : Lattice) :
    reflectX (dualNormal d) = -d := by
  ext <;> simp [dualNormal,reflectX]

@[simp] theorem neg_dualNormal (d : Lattice) :
    -dualNormal d = reflectX d := by
  simp [dualNormal]

theorem det_reflected (d z : Lattice) :
    det (dualNormal d) (reflectX z) = det d z := by
  simp [dualNormal,reflectX,det]

theorem det_dual (d z : Lattice) :
    det (dualNormal d) z = det d (reflectX z) := by
  have h := det_reflected d (reflectX z)
  simpa using h

def reflectNormals (D : Finset Lattice) : Finset Lattice :=
  D.image dualNormal

@[simp] theorem mem_reflectNormals (D : Finset Lattice) (d : Lattice) :
    d ∈ reflectNormals D ↔ dualNormal d ∈ D := by
  simp only [reflectNormals,Finset.mem_image]
  constructor
  · rintro ⟨e,he,rfl⟩
    simpa using he
  · intro hd
    exact ⟨dualNormal d,hd,dualNormal_involutive d⟩

@[simp] theorem reflectNormals_involutive (D : Finset Lattice) :
    reflectNormals (reflectNormals D) = D := by
  ext d
  simp

def reflectSet (R : Set Lattice) : Set Lattice := reflectX ⁻¹' R

@[simp] theorem mem_reflectSet (R : Set Lattice) (z : Lattice) :
    z ∈ reflectSet R ↔ reflectX z ∈ R := Iff.rfl

@[simp] theorem reflectSet_involutive (R : Set Lattice) :
    reflectSet (reflectSet R) = R := by
  ext z
  simp [reflectSet]

theorem supportHull_reflect (D : Finset Lattice) (R : Set Lattice) :
    supportHull (reflectNormals D) (reflectSet R) =
      reflectSet (supportHull D R) := by
  ext z
  constructor
  · intro hz d hd b hb
    have hd' : dualNormal d ∈ reflectNormals D :=
      (mem_reflectNormals D _).2 (by simpa using hd)
    have hb' : ∀ w ∈ reflectSet R, b ≤ det (dualNormal d) w := by
      intro w hw
      rw [det_dual]
      exact hb (reflectX w) hw
    have h := hz (dualNormal d) hd' b hb'
    rwa [det_dual] at h
  · intro hz d hd b hb
    have hd' : dualNormal d ∈ D := (mem_reflectNormals D d).1 hd
    have hb' : ∀ w ∈ R, b ≤ det (dualNormal d) w := by
      intro w hw
      have hw' : reflectX w ∈ reflectSet R := by simpa using hw
      have hh := hb (reflectX w) hw'
      simpa [det_dual] using hh
    have h := hz (dualNormal d) hd' b hb'
    simpa [det_dual] using h

theorem isEnvelope_reflect {D : Finset Lattice} {R : Set Lattice}
    (hR : IsEnvelope D R) :
    IsEnvelope (reflectNormals D) (reflectSet R) := by
  rw [show IsEnvelope (reflectNormals D) (reflectSet R) =
      (supportHull (reflectNormals D) (reflectSet R) = reflectSet R) from rfl]
  rw [supportHull_reflect,hR]

def reflectWindow (T : Finset Lattice) : Finset Lattice :=
  T.image reflectX

@[simp] theorem mem_reflectWindow (T : Finset Lattice) (z : Lattice) :
    z ∈ reflectWindow T ↔ reflectX z ∈ T := by
  simp only [reflectWindow,Finset.mem_image]
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa using hw
  · intro hz
    exact ⟨reflectX z,hz,by simp⟩

@[simp] theorem reflectWindow_involutive (T : Finset Lattice) :
    reflectWindow (reflectWindow T) = T := by
  ext z
  simp

@[simp] theorem coe_reflectWindow (T : Finset Lattice) :
    (reflectWindow T : Set Lattice) = reflectSet (T : Set Lattice) := by
  ext z
  exact mem_reflectWindow T z

theorem isEnvelope_reflectWindow {D T : Finset Lattice}
    (hT : IsEnvelope D (T : Set Lattice)) :
    IsEnvelope (reflectNormals D) (reflectWindow T : Set Lattice) := by
  rw [coe_reflectWindow]
  exact isEnvelope_reflect hT

theorem longFaces_reflect {D : Finset Lattice} {R : Set Lattice}
    (hR : LongFaces D R) :
    LongFaces (reflectNormals D) (reflectSet R) := by
  intro d hd z hz hmin
  have he : dualNormal d ∈ D := (mem_reflectNormals D d).mp hd
  have hmin' : ∀ w ∈ R, det (dualNormal d) (reflectX z) ≤
      det (dualNormal d) w := by
    intro w hw
    have hw' : reflectX w ∈ reflectSet R := by simpa using hw
    have hh := hmin (reflectX w) hw'
    simpa only [det_dual,reflectX_involutive] using hh
  obtain ⟨w,hw,hwd,heq⟩ := hR (dualNormal d) he (reflectX z) hz hmin'
  refine ⟨reflectX (w + dualNormal d),?_,?_,?_⟩
  · change reflectX (reflectX (w + dualNormal d)) ∈ R
    rw [reflectX_involutive]
    exact hwd
  · have hstep : reflectX (w + dualNormal d) + d = reflectX w := by
      rw [map_add]
      have hdneg : reflectX (dualNormal d) = -d := by
        ext <;> simp [dualNormal,reflectX]
      rw [hdneg]
      abel
    rw [hstep]
    change reflectX (reflectX w) ∈ R
    simpa using hw
  · calc
      det d (reflectX (w + dualNormal d)) =
          det (dualNormal d) (w + dualNormal d) := (det_dual d _).symm
      _ = det (dualNormal d) w := by simp [det]; ring
      _ = det d z := by simpa [det_dual] using heq

theorem longFaces_reflectWindow {D T : Finset Lattice}
    (hT : LongFaces D (T : Set Lattice)) :
    LongFaces (reflectNormals D) (reflectWindow T : Set Lattice) := by
  rw [coe_reflectWindow]
  exact longFaces_reflect hT

theorem reflectSet_subset {R S : Set Lattice} (hRS : R ⊆ S) :
    reflectSet R ⊆ reflectSet S := by
  intro z hz
  exact hRS hz

theorem reflectWindow_subset {S T : Finset Lattice} (hST : S ⊆ T) :
    reflectWindow S ⊆ reflectWindow T := by
  intro z hz
  exact (mem_reflectWindow T z).mpr
    (hST ((mem_reflectWindow S z).mp hz))

theorem reflectWindow_nonempty {S : Finset Lattice} (hS : S.Nonempty) :
    (reflectWindow S).Nonempty := by
  obtain ⟨z,hz⟩ := hS
  exact ⟨reflectX z,by simpa using hz⟩

theorem isLatticeConvex_reflectWindow {S : Finset Lattice}
    (hS : IsLatticeConvex S) : IsLatticeConvex (reflectWindow S) := by
  have heq : reflectWindow S = mapWindow reflectX S := by
    ext z
    simp [mem_mapWindow,reflectX]
  rw [heq]
  exact isLatticeConvex_mapWindow reflectX hS

theorem agreeOn_reflect {A : Type*} {x p : Lattice → A} {R : Set Lattice}
    (hxp : AgreeOn x p R) :
    AgreeOn (x ∘ reflectX) (p ∘ reflectX) (reflectSet R) := by
  intro z hz
  exact hxp (reflectX z) hz

theorem finiteExtensionMaximal_reflect {A : Type*}
    {D : Finset Lattice} {x p : Lattice → A} {R Q : Set Lattice}
    (hmax : FiniteExtensionMaximal D x p R Q) :
    FiniteExtensionMaximal (reflectNormals D)
      (x ∘ reflectX) (p ∘ reflectX) (reflectSet R) (reflectSet Q) := by
  intro S W hSconv hSfaces hWne hWconv hWfaces hWS hWR hSQ hAgree
  have hSconv' : IsLatticeConvex (reflectWindow S) :=
    isLatticeConvex_reflectWindow hSconv
  have hSfaces' : LongFaces D (reflectWindow S : Set Lattice) := by
    simpa using longFaces_reflectWindow hSfaces
  have hWconv' : IsLatticeConvex (reflectWindow W) :=
    isLatticeConvex_reflectWindow hWconv
  have hWfaces' : LongFaces D (reflectWindow W : Set Lattice) := by
    simpa using longFaces_reflectWindow hWfaces
  have hWR' : (reflectWindow W : Set Lattice) ⊆ R := by
    rw [coe_reflectWindow,← reflectSet_involutive R]
    exact reflectSet_subset hWR
  have hSQ' : (reflectWindow S : Set Lattice) ⊆ Q := by
    rw [coe_reflectWindow,← reflectSet_involutive Q]
    exact reflectSet_subset hSQ
  have hAgree' : AgreeOn x p (reflectWindow S : Set Lattice) := by
    have h := agreeOn_reflect hAgree
    simpa [coe_reflectWindow,Function.comp_def] using h
  have hOld := hmax (reflectWindow S) (reflectWindow W)
    hSconv' hSfaces' (reflectWindow_nonempty hWne) hWconv' hWfaces'
    (reflectWindow_subset hWS) hWR' hSQ' hAgree'
  have hRef := reflectSet_subset hOld
  simpa [coe_reflectWindow] using hRef

theorem finiteExhaustion_reflect {D : Finset Lattice} {R : Set Lattice}
    (hexhaust : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
        IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice) ∧ 0 ∈ W) :
    ∀ F : Finset Lattice, (F : Set Lattice) ⊆ reflectSet R →
      ∃ W : Finset Lattice, F ⊆ W ∧
        (W : Set Lattice) ⊆ reflectSet R ∧
        IsEnvelope (reflectNormals D) (W : Set Lattice) ∧
        LongFaces (reflectNormals D) (W : Set Lattice) ∧ 0 ∈ W := by
  intro F hFR
  have hFR' : (reflectWindow F : Set Lattice) ⊆ R := by
    rw [coe_reflectWindow,← reflectSet_involutive R]
    exact reflectSet_subset hFR
  obtain ⟨W,hFW,hWR,hWE,hWF,hW0⟩ := hexhaust (reflectWindow F) hFR'
  refine ⟨reflectWindow W,?_,?_,isEnvelope_reflectWindow hWE,
    longFaces_reflectWindow hWF,?_⟩
  · have h := reflectWindow_subset hFW
    simpa using h
  · rw [coe_reflectWindow]
    exact reflectSet_subset hWR
  · rw [mem_reflectWindow]
    simpa only [map_zero] using hW0

theorem reflect_bottom_halfPlane (u : Lattice) :
    reflectSet {z : Lattice | 0 ≤ det u z} =
      {z : Lattice | 0 ≤ det (dualNormal u) z} := by
  ext z
  simp only [mem_reflectSet,Set.mem_ofPred_eq,det_dual]

theorem forwardInvariant_reflect {R : Set Lattice} {h : Lattice}
    (hR : ForwardInvariant R h) :
    ForwardInvariant (reflectSet R) (reflectX h) := by
  intro z hz
  change reflectX (z + reflectX h) ∈ R
  rw [map_add,reflectX_involutive]
  exact hR (reflectX z) hz

theorem reflect_zero_mem {R : Set Lattice} (hzero : 0 ∈ R) :
    0 ∈ reflectSet R := by
  change reflectX (0 : Lattice) ∈ R
  simpa only [map_zero] using hzero

theorem reflect_forward_ray {R : Set Lattice} {u : Lattice}
    (hray : ∀ n : ℕ, n • u ∈ R) :
    ∀ n : ℕ, -(n • dualNormal u) ∈ reflectSet R := by
  intro n
  change reflectX (-(n • dualNormal u)) ∈ R
  have h : reflectX (-(n • dualNormal u)) = n • u := by
    ext <;> simp [dualNormal,reflectX]
  rw [h]
  exact hray n

theorem height_unbounded_reflect {R : Set Lattice} {u : Lattice}
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z) :
    ∀ N : ℤ, ∃ z ∈ reflectSet R, N ≤ det (dualNormal u) z := by
  intro N
  obtain ⟨z,hz,hN⟩ := hheight N
  refine ⟨reflectX z,?_,?_⟩
  · simpa using hz
  · simpa only [det_dual,reflectX_involutive] using hN

/-- Reflection turns a first-boundary maximal agreement region into the
opposite-boundary situation. The conclusion is returned in the original
coordinates, with the original configuration and actual region. -/
theorem two_period_region_from_first_boundary {A : Type*} [Fintype A]
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (x p : Lattice → A) (hx : x ∈ languageHull θ)
    (hpHull : p ∈ languageHull θ) (hagree : AgreeOn x p R)
    (u : Lattice) (hu : u ∈ D) (hnu : -u ∈ D)
    (hzero : 0 ∈ R) (hout : -u ∉ R)
    (hray : ∀ n : ℕ, n • u ∈ R)
    (hforward : ForwardInvariant R u)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hp : IsPeriod p u)
    (hmax : FiniteExtensionMaximal D x p R {z | 0 ≤ det u z})
    (hexhaust : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
        IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice) ∧ 0 ∈ W) :
    ∃ K : Set Lattice, LatticeConvexRegion K ∧ K.Nonempty ∧ K ⊆ R ∧
      ∃ a b : Lattice, det a b ≠ 0 ∧
        PeriodicOn x K a ∧ PeriodicOn x K b := by
  let u' := dualNormal u
  let D' := reflectNormals D
  let R' := reflectSet R
  let θ' := θ ∘ reflectX
  let x' := x ∘ reflectX
  let p' := p ∘ reflectX
  let S' := mapWindow reflectX S
  have hS' : GeneratingWindow θ' S' := by
    simpa only [θ',S',reflectX_symm] using
      generatingWindow_mapWindow reflectX hS
  have hx' : x' ∈ languageHull θ' := mem_languageHull_comp_equiv reflectX hx
  have hpHull' : p' ∈ languageHull θ' := mem_languageHull_comp_equiv reflectX hpHull
  have hR' : IsEnvelope D' R' := isEnvelope_reflect hR
  have hagree' : AgreeOn x' p' R' := agreeOn_reflect hagree
  have hu' : u' ∈ D' := (mem_reflectNormals D u').mpr (by simpa [u'] using hu)
  have hnu' : -u' ∈ D' := (mem_reflectNormals D (-u')).mpr (by
    change dualNormal (-dualNormal u) ∈ D
    rw [dualNormal_neg,dualNormal_involutive]
    exact hnu)
  have hzero' : 0 ∈ R' := reflect_zero_mem hzero
  have hout' : u' ∉ R' := by
    intro hmem
    change reflectX (dualNormal u) ∈ R at hmem
    rw [reflectX_dualNormal] at hmem
    exact hout hmem
  have hray' : ∀ n : ℕ, -(n • u') ∈ R' := reflect_forward_ray hray
  have hforward' : ForwardInvariant R' (-u') := by
    simpa [u'] using forwardInvariant_reflect hforward
  have hheight' : ∀ N : ℤ, ∃ z ∈ R', N ≤ det u' z :=
    height_unbounded_reflect hheight
  have hp' : IsPeriod p' u' := by
    apply (isPeriod_comp_iff reflectX p u').mpr
    change IsPeriod p (reflectX (dualNormal u))
    rw [reflectX_dualNormal]
    exact hp.neg
  have hmax' : FiniteExtensionMaximal D' x' p' R'
      {z | 0 ≤ det u' z} := by
    simpa [D',x',p',R',u',reflect_bottom_halfPlane] using
      (finiteExtensionMaximal_reflect hmax)
  have hexhaust' : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R' →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R' ∧
        IsEnvelope D' (W : Set Lattice) ∧
        LongFaces D' (W : Set Lattice) ∧ 0 ∈ W :=
    finiteExhaustion_reflect hexhaust
  obtain ⟨K',hK',hKne',hKR',a,b,hab,ha,hb⟩ :=
    two_period_region_of_maximal_agreement θ' S' hS' D' R' hR'
      x' p' hx' hpHull' hagree' u' hu' hnu' hzero' hout'
      hray' hforward' hheight' hp' hmax' hexhaust'
  refine ⟨reflectSet K',?_,?_,?_,reflectX a,reflectX b,?_,?_,?_⟩
  · exact latticeConvex_preimage reflectX hK'
  · obtain ⟨z,hz⟩ := hKne'
    exact ⟨reflectX z,by simpa using hz⟩
  · have h := reflectSet_subset hKR'
    simpa [R',reflectSet_involutive] using h
  · exact fun he => hab ((det_equiv_zero_iff reflectX a b).mp he)
  · have hcomp : x' ∘ reflectX = x := by
      funext z
      exact congrArg x (reflectX_involutive z)
    simpa only [reflectSet,hcomp,reflectX_symm] using
      periodicOn_preimage reflectX ha
  · have hcomp : x' ∘ reflectX = x := by
      funext z
      exact congrArg x (reflectX_involutive z)
    simpa only [reflectSet,hcomp,reflectX_symm] using
      periodicOn_preimage reflectX hb

end
end NivatTrial.ColleCaseOneReflectionTransport
