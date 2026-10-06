import NivatTrial.ColleSemiAmbiguityTransport
import NivatTrial.ColleSecondBoundaryStrip
import NivatTrial.ColleEnvelopeGeometry

/-! The actual bad-point/inner-strip output produces semi-ambiguity of a
translate of the periodic reference in the original lattice coordinates. -/

namespace NivatTrial.ColleActualSecondAmbiguity

open NivatTrial.Dynamics NivatTrial.Geometry NivatTrial.Zonotope
open NivatTrial.Nonexpansive NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleVertexGeometry
open NivatTrial.ColleDirectionalPropagation NivatTrial.LatticeCoordinates
open NivatTrial.ColleSecondBoundaryCoordinates NivatTrial.ColleSemiAmbiguity
open NivatTrial.ColleSemiAmbiguityTransport NivatTrial.ColleEnvelopeGeometry
open scoped Classical
noncomputable section
abbrev G := ℤ × ℤ

theorem primitive_second_axis (e : G ≃+ G) (k : G) (c : ℕ)
    (hc : 0 < c) (hek : e (-(c:ℤ),0)=k)
    (hdet : ∀ z, det k (e z)=(c:ℤ)*z.2) :
    k=(c:ℤ)•e (-1,0) ∧
    Int.gcd (e (-1,0)).1 (e (-1,0)).2=1 ∧
    dualNormal e (embed (e (-1,0)))=(1,0) := by
  have hec : e (-(c:ℤ),0)=(c:ℤ)•e (-1,0) := by
    rw [← map_zsmul]
    congr 1
    ext <;> simp
  have hk : k=(c:ℤ)•e (-1,0) := hek.symm.trans hec
  have hc0 : (c:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have hd : ∀ z, det (e (-1,0)) (e z)=z.2 := by
    intro z
    have hh := hdet z
    rw [hk,det_zsmul_left] at hh
    exact mul_left_cancel₀ hc0 hh
  refine ⟨hk,?_,?_⟩
  · let g := Int.gcd (e (-1,0)).1 (e (-1,0)).2
    have hg : (g:ℤ) ∣ det (e (-1,0)) (e (0,1)) := by
      apply dvd_sub
      · exact dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _
      · exact dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _
    rw [hd] at hg
    change (g:ℤ) ∣ (1:ℤ) at hg
    have hg' : g ∣ 1 := by exact_mod_cast hg
    exact Nat.dvd_one.mp hg'
  · unfold dualNormal
    change (linearScore (embed (e (-1,0))) (embed (e (0,1))),
      -linearScore (embed (e (-1,0))) (embed (e (1,0))))=(1,0)
    rw [linearScore_embed_det,linearScore_embed_det,hd,hd]
    norm_num

variable {A : Type*} [Fintype A]

theorem reference_semiAmbiguous_of_inner_strips
    (θ : G → A) (S : Finset G) (hS : GeneratingWindow θ S)
    (e : G ≃+ G) (k : G) (hek : e (-1,0)=k)
    (hdual : dualNormal e (embed k)=(1,0))
    {x p : G → A} (hx : x ∈ languageHull θ) (hp : p ∈ languageHull θ)
    (hstrips : ∀ height width : ℤ, ∃ v : G, x (e v)≠p (e v) ∧
      ∀ z : G, v.2<z.2 → z.2≤v.2+height → z.1≤v.1+width →
        x (e z)=p (e z)) :
    ∃ a : G, ∃ τ : ℤ,
      SemiAmbiguous θ S (embed k) k (shift a p) (shift_mem_languageHull hp a) τ := by
  let B := mapWindow e.symm S
  have hB : GeneratingWindow (θ ∘ e) B := by
    simpa only [B,AddEquiv.symm_symm] using generatingWindow_mapWindow e.symm hS
  obtain ⟨l,r,_,hr,_,_⟩ := bottom_interval_generated (θ ∘ e) B hB
  let H : ℤ := (B.image Prod.fst).max' (hB.nonempty.image _)
  have hH : ∀ s ∈ B, s.1≤H := by
    intro s hs
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
  obtain ⟨v,hbad,hstrip⟩ := hstrips (upper B-lower B) (H-r)
  have hsemi := (semi_ambiguous_pair_of_slanted_inner_strip e θ B hB hx hp
    v.2 (e v) (by simp) hbad H hH r ⟨l,hr⟩ (by
      intro z hlo hup hleft
      have hh := hstrip (e.symm z) hlo (by omega) (by
        simp only [e.symm_apply_apply] at hleft
        omega)
      simpa only [e.apply_symm_apply] using hh)).2
  let a := e (0,v.2-lower B)
  let q := shift (0,v.2-lower B) (p ∘ e)
  have hq : q ∈ languageHull (θ ∘ e) :=
    shift_mem_languageHull (mem_languageHull_comp_equiv e hp) _
  have hsemi' : SemiAmbiguous (θ ∘ e) B (dualNormal e (embed k)) (-1,0)
      q hq (r-v.1) := by simpa only [hdual,e.symm_apply_apply] using hsemi
  have hh := semiAmbiguous_mapWindow e (θ ∘ e) B (embed k) (-1,0) hq (r-v.1) hsemi'
  have hθ : (θ ∘ e) ∘ e.symm=θ := by funext z; simp
  have hqeq : q ∘ e.symm=shift a p := by
    funext z
    simp only [q,a,Function.comp_apply,shift_apply,map_add,e.apply_symm_apply]
  have hwin : mapWindow e B=S := by
    simpa only [B,AddEquiv.symm_symm] using mapWindow_symm_mapWindow e.symm S
  refine ⟨a,r-v.1,?_⟩
  simpa only [hθ,hqeq,hwin,hek] using hh

end
end NivatTrial.ColleActualSecondAmbiguity
