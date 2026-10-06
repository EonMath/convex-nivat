import NivatTrial.ColleSecondBoundaryReference
import NivatTrial.ColleCoordinateTransport
import NivatTrial.CollePositiveCoordinates

/-! A positively oriented integer basis reduces only the reference-period
argument to horizontal coordinates. The actual maximal region, its normal
set and its finite-extension properties stay in the original coordinates. -/

namespace NivatTrial.ColleGeneralBoundaryReference

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Periodicity NivatTrial.ColleGenerating
open NivatTrial.ColleCoordinateTransport NivatTrial.ColleDirectionalPropagation
open NivatTrial.LatticeCoordinates NivatTrial.RowDetermination
open NivatTrial.ColleSecondBoundaryReference NivatTrial.CollePositiveCoordinates
open scoped Classical
noncomputable section

variable {A : Type*} [Fintype A]

/-- General first and second directions: the exact inner strips imply a
second period of the reference on a high determinant half-plane. -/
theorem reference_det_halfPlane_period_of_inner_strips
    (θ : Lattice → A) (S : Finset Lattice) (hS : GeneratingWindow θ S)
    (u : Lattice) (hu : u ≠ 0) {x p : Lattice → A}
    (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (hperiod : IsPeriod p u)
    (k : Lattice) (huk : 0 < det u k) (c : ℕ) (e : Lattice ≃+ Lattice)
    (hc : 0 < c) (hek : e (-(c : ℤ),0) = k)
    (hdet : ∀ z, det k (e z) = (c : ℤ)*z.2)
    (hstrips : ∀ height width : ℤ, ∃ v : Lattice, x (e v) ≠ p (e v) ∧
      ∀ z : Lattice, v.2 < z.2 → z.2 ≤ v.2+height → z.1 ≤ v.1+width →
        x (e z) = p (e z)) :
    ∃ M : ℕ, 0 < M ∧ ∃ b : ℤ, ∀ z : Lattice, b ≤ det u z →
      p (z+M•k) = p z := by
  obtain ⟨P,f,hP,hfu,hfd⟩ := exists_positive_horizontal_coordinates u hu
  let θ' := θ ∘ f
  let S' := mapWindow f.symm S
  let x' := x ∘ f
  let p' := p ∘ f
  let k' := f.symm k
  let e' := e.trans f.symm
  have hS' : GeneratingWindow θ' S' := by
    simpa only [θ',S',AddEquiv.symm_symm] using generatingWindow_mapWindow f.symm hS
  have hx' : x' ∈ languageHull θ' := mem_languageHull_comp_equiv f hx
  have hp' : p' ∈ languageHull θ' := mem_languageHull_comp_equiv f hp
  have hper' : IsPeriod p' (P•horizontal) :=
    (isPeriod_comp_iff f p (P•horizontal)).mpr (by simpa only [hfu] using hperiod)
  have hscore (z : Lattice) : det u (f z) = (P : ℤ)*z.2 := by
    rw [← hfu,hfd]
    simp [det,horizontal]
  have hk' : 0 < k'.2 := by
    have hh := hscore k'
    change det u (f (f.symm k)) = (P : ℤ)*k'.2 at hh
    rw [f.apply_symm_apply] at hh
    have hPi : (0 : ℤ) < P := by exact_mod_cast hP
    nlinarith
  have hek' : e' (-(c : ℤ),0) = k' := by
    change f.symm (e (-(c : ℤ),0)) = f.symm k
    rw [hek]
  have hdet' (z : Lattice) : det k' (e' z) = (c : ℤ)*z.2 := by
    have hh := hfd k' (e' z)
    have heq : det k (e z) = det k' (e' z) := by
      simpa only [k',e',AddEquiv.trans_apply,f.apply_symm_apply] using hh
    rw [← heq,hdet]
  have hstrips' : ∀ height width : ℤ, ∃ v : Lattice, x' (e' v) ≠ p' (e' v) ∧
      ∀ z : Lattice, v.2 < z.2 → z.2 ≤ v.2+height → z.1 ≤ v.1+width →
        x' (e' z) = p' (e' z) := by
    intro height width
    simpa only [x',p',e',Function.comp_apply,AddEquiv.trans_apply,f.apply_symm_apply]
      using hstrips height width
  obtain ⟨M,hM,lo,hhigh⟩ := reference_halfPlane_period_of_inner_strips θ' S' hS'
    P hP hx' hp' hper' k' hk' c e' hc hek' hdet' hstrips'
  refine ⟨M,hM,(P : ℤ)*lo,?_⟩
  intro z hz
  have hheight : lo ≤ (f.symm z).2 := by
    have hh := hscore (f.symm z)
    rw [f.apply_symm_apply] at hh
    have hPi : (0 : ℤ) < P := by exact_mod_cast hP
    nlinarith
  have hh := hhigh (f.symm z) hheight
  simpa only [p',Function.comp_apply,map_add,map_nsmul,k',f.apply_symm_apply] using hh

end
end NivatTrial.ColleGeneralBoundaryReference

