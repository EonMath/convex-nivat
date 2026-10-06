import NivatTrial.ColleSecondBoundaryDefects
import NivatTrial.ColleHighestBoundaryRow
import NivatTrial.ColleBoundaryStripGeometry
import NivatTrial.ColleLeftwardCoordinates

/-! Actual maximal-envelope geometry supplies a defect and the complete
finite-height left interior strip needed by one-sided ambiguity. -/

namespace NivatTrial.ColleSecondBoundaryStrip

open NivatTrial.Geometry NivatTrial.RegionGeometry NivatTrial.Nonexpansive
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleMaximalAgreementLimit NivatTrial.ColleSecondBoundaryDefects
open NivatTrial.ColleHighestBoundaryRow NivatTrial.ColleBoundaryStripGeometry
open NivatTrial.ColleLeftwardCoordinates Filter
open scoped Classical
noncomputable section

theorem inner_strip_from_boundary_defect_band {A : Type*}
    (R : Set Lattice) (x p : Lattice → A) (k w : Lattice)
    (hagree : AgreeOn x p R) (hforward : ForwardInvariant R k)
    (hevent : ∀ z, det k w ≤ det k z → ∀ᶠ n : ℕ in atTop, z+n•k ∈ R)
    (e : Lattice ≃+ Lattice) (c : ℤ) (hc : 0 < c)
    (hek : e (-c,0) = k) (hdet : ∀ z, det k (e z) = c*z.2)
    (S : Finset Lattice)
    (hbad : ∀ᶠ n : ℕ in atTop, ∃ z ∈ S,
      det k z < det k w ∧ x (z+n•k) ≠ p (z+n•k))
    (height width : ℤ) :
    ∃ v : Lattice, x (e v) ≠ p (e v) ∧
      ∀ z : Lattice, v.2 < z.2 → z.2 ≤ v.2+height →
        z.1 ≤ v.1+width → x (e z) = p (e z) := by
  have hS : S.Nonempty := by
    obtain ⟨_,z,hz,_,_⟩ := hbad.exists
    exact ⟨z,hz⟩
  have hlevels : (S.image (fun z => (e.symm z).2)).Nonempty := hS.image _
  let a : ℤ := (S.image (fun z => (e.symm z).2)).min' hlevels
  let b : ℤ := (e.symm w).2-1
  have hinvk : e.symm k = (-c,0) := by rw [← hek]; simp
  have hcoord (z : Lattice) (n : ℕ) :
      e.symm (z+n•k) = e.symm z+n•((-c,0):Lattice) := by
    rw [map_add,map_nsmul,hinvk]
  have hfirst (z : Lattice) (n : ℕ) :
      (e.symm (z+n•k)).1 = (e.symm z).1-(n:ℤ)*c := by
    rw [hcoord]
    simp [Prod.smul_mk]
    ring
  have hsecond (z : Lattice) (n : ℕ) :
      (e.symm (z+n•k)).2 = (e.symm z).2 := by
    rw [hcoord]
    simp
  have hscore (z : Lattice) : det k z = c*(e.symm z).2 := by
    simpa only [e.apply_symm_apply] using hdet (e.symm z)
  have harb : ∀ L : ℤ, ∃ z : Lattice,
      a ≤ z.2 ∧ z.2 ≤ b ∧ z.1 ≤ L ∧ (x ∘ e) z ≠ (p ∘ e) z := by
    intro L
    have hleft : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S,
        (e.symm (z+n•k)).1 ≤ L := by
      apply S.eventually_all.mpr
      intro z _
      obtain ⟨N,hN⟩ := exists_nat_gt ((e.symm z).1-L)
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [hfirst]
      have hnn : (N:ℤ) ≤ n := by exact_mod_cast hn
      have hn0 : (0:ℤ) ≤ n := by positivity
      nlinarith
    obtain ⟨n,⟨z,hz,hbelow,hneq⟩,hleftn⟩ := (hbad.and hleft).exists
    refine ⟨e.symm (z+n•k),?_,?_,hleftn z hz,?_⟩
    · rw [hsecond]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    · rw [hsecond]
      rw [hscore z,hscore w] at hbelow
      have hh : (e.symm z).2 < (e.symm w).2 := by nlinarith
      dsimp [b]
      omega
    · simpa only [Function.comp_apply,e.apply_symm_apply] using hneq
  have habove : ∀ H : ℤ, ∃ L : ℤ, ∀ z : Lattice,
      b < z.2 → z.2 ≤ H → z.1 ≤ L → (x ∘ e) z = (p ∘ e) z := by
    intro H
    have hentry : ∀ z : Lattice, (e.symm w).2 ≤ (e.symm z).2 →
        ∀ᶠ n : ℕ in atTop, z+n•e (-c,0) ∈ R := by
      intro z hz
      rw [hek]
      apply hevent z
      rw [hscore w,hscore z]
      exact mul_le_mul_of_nonneg_left hz hc.le
    have hfor : ForwardInvariant R (e (-c,0)) := by rwa [hek]
    obtain ⟨L,hL⟩ := eventual_entry_implies_left_band R e c hc (e.symm w).2
      hentry hfor (max (e.symm w).2 H) (le_max_left _ _)
    refine ⟨L,?_⟩
    intro z hbz hzH hzL
    exact hagree (e z) (hL z (by dsimp [b] at hbz; omega)
      (hzH.trans (le_max_right _ _)) hzL)
  obtain ⟨v,_,_,hbadV,hstrip⟩ := exists_bad_point_with_left_inner_strip
    (x ∘ e) (p ∘ e) a b harb habove height width
  exact ⟨v,hbadV,hstrip⟩

/-- All the interior-strip assumptions are consequences of the actual
maximal agreement region and its finite long-window exhaustion. -/
theorem exists_second_boundary_inner_strip {A : Type*}
    (D : Finset Lattice) (R : Set Lattice) (hR : IsEnvelope D R)
    (x p : Lattice → A) (hagree : AgreeOn x p R)
    (u : Lattice) (hu : u ∈ D) (hnu : -u ∈ D)
    (hzero : 0 ∈ R) (hout : u ∉ R)
    (hback : ∀ n : ℕ, -(n•u) ∈ R)
    (hheight : ∀ N : ℤ, ∃ z ∈ R, N ≤ det u z)
    (hmax : FiniteExtensionMaximal D x p R {z | 0 ≤ det u z})
    (hexhaust : ∀ F : Finset Lattice, (F : Set Lattice) ⊆ R →
      ∃ W : Finset Lattice, F ⊆ W ∧ (W : Set Lattice) ⊆ R ∧
        IsEnvelope D (W : Set Lattice) ∧ LongFaces D (W : Set Lattice) ∧ 0 ∈ W) :
    ∃ k ∈ D, 0 < det u k ∧ ∃ c : ℕ, ∃ e : Lattice ≃+ Lattice,
      0 < c ∧ e (-(c:ℤ),0) = k ∧
      (∀ z, det k (e z) = (c:ℤ)*z.2) ∧
      ∀ height width : ℤ, ∃ v : Lattice, x (e v) ≠ p (e v) ∧
        ∀ z : Lattice, v.2 < z.2 → z.2 ≤ v.2+height →
          z.1 ≤ v.1+width → x (e z) = p (e z) := by
  obtain ⟨k,hk,w,_,huk,_,hforward,hevent,S,_,hbad⟩ :=
    exists_second_boundary_defect_band D R hR x p hagree u hu hnu hzero hout
      hback hheight hmax hexhaust
  have hk0 : k ≠ 0 := by intro he; simp [he,det] at huk
  obtain ⟨c,e,hc,hek,hdet⟩ := exists_leftward_coordinates k hk0
  refine ⟨k,hk,huk,c,e,hc,hek,hdet,?_⟩
  intro height width
  exact inner_strip_from_boundary_defect_band R x p k w hagree hforward hevent
    e c (by exact_mod_cast hc) hek hdet S hbad height width

end
end NivatTrial.ColleSecondBoundaryStrip
