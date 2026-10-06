import NivatTrial.ColleMaximalAgreementLimit

/-! Finite windows translated along the second boundary force genuine
defects arbitrarily far along that boundary. Only a fixed finite band of
transverse heights is needed. -/

namespace NivatTrial.ColleSecondBoundaryDefects

open NivatTrial.Geometry NivatTrial.RegionGeometry NivatTrial.LatticePolygon
open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeTranslation NivatTrial.ColleEnvelopeExpansion
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleEnvelopeRays
open NivatTrial.ColleMaximalSeedDefect NivatTrial.ColleMaximalAgreementLimit
open NivatTrial.ColleEnvelopeRecession Filter
open scoped Classical
noncomputable section

theorem eventually_bottom_translate (u k z : Lattice) (huk : 0 < det u k) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ det u (z+n•k) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (-det u z)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [det_add_right,det_nsmul_right]
  have hnN : (N:ℤ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℤ) ≤ n := by positivity
  nlinarith

/-- A common finite long-faced window touches the actual supporting line.
Its one-step expansion has defects after every sufficiently far translation
along the second boundary. -/
theorem eventual_second_boundary_defects {A : Type*}
    (D : Finset Lattice) (R : Set Lattice) (x p : Lattice → A)
    (u k w : Lattice) (huk : 0 < det u k) (_hw : w ∈ R)
    (hmin : ∀ z ∈ R, det k w ≤ det k z)
    (hRforward : ForwardInvariant R k)
    (hevent : ∀ z, det k w ≤ det k z → ∀ᶠ n : ℕ in atTop, z+n•k ∈ R)
    (hagree : AgreeOn x p R)
    (hmax : FiniteExtensionMaximal D x p R {z | 0 ≤ det u z})
    (W : Finset Lattice) (hW : (W : Set Lattice) ⊆ R)
    (hWe : IsEnvelope D (W : Set Lattice)) (hWf : LongFaces D (W : Set Lattice))
    (hwW : w ∈ W) (hu : u ∈ D) (hnu : -u ∈ D) :
    (∀ z ∈ stepWindow W u, det k w+det k u ≤ det k z) ∧
    ∀ᶠ n : ℕ in atTop, ∃ z ∈ stepWindow W u,
      det k z < det k w ∧ x (z+n•k) ≠ p (z+n•k) := by
  have hku : det k u < 0 := by rw [det_swap]; omega
  have hu0 : u ≠ 0 := by intro he; simp [he,det] at huk
  let S := stepWindow W u
  have hSstep : (S : Set Lattice) = stepExpansion D (W : Set Lattice) u :=
    coe_stepWindow_eq_stepExpansion D W u ⟨w,hwW⟩ hWe hWf hu0 hu hnu
  have hSe : IsEnvelope D (S : Set Lattice) := by
    rw [hSstep]
    exact supportHull_idempotent D _
  have hSf : LongFaces D (S : Set Lattice) := by
    rw [hSstep]
    exact stepExpansion_longFaces hWf u
  have hWS : W ⊆ S := Finset.subset_union_left
  have hnew : w+u ∈ S := by
    apply Finset.mem_union_right
    simpa only [mem_recenterWindow,add_neg_cancel_right] using hwW
  constructor
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hh := hmin z (hW hz)
      omega
    · have hzW := (mem_recenterWindow W (-u) z).mp hz
      have hh := hmin (z+(-u)) (hW hzW)
      rw [det_add_right,det_neg_right] at hh
      omega
  · have hgood : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S,
        det k w ≤ det k z → z+n•k ∈ R := by
      apply S.eventually_all.mpr
      intro z _
      by_cases hz : det k w ≤ det k z
      · filter_upwards [hevent z hz] with n hn _
        exact hn
      · filter_upwards [] with n hn
        exact (hz hn).elim
    have hbottom : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, 0 ≤ det u (z+n•k) :=
      S.eventually_all.mpr (fun z _ => eventually_bottom_translate u k z huk)
    filter_upwards [hgood,hbottom] with n hgoodn hbottomn
    by_contra hnone
    push Not at hnone
    let Sn := recenterWindow S (-(n•k))
    let Wn := recenterWindow W (-(n•k))
    have hSne : IsEnvelope D (Sn : Set Lattice) := isEnvelope_recenterWindow hSe _
    have hWne : IsEnvelope D (Wn : Set Lattice) := isEnvelope_recenterWindow hWe _
    have hSnf : LongFaces D (Sn : Set Lattice) := longFaces_recenterWindow hSf _
    have hWnf : LongFaces D (Wn : Set Lattice) := longFaces_recenterWindow hWf _
    have hWn : Wn.Nonempty := ⟨w+n•k,by
      change w+n•k ∈ recenterWindow W (-(n•k))
      simpa only [mem_recenterWindow,add_neg_cancel_right] using hwW⟩
    have hWnSn : Wn ⊆ Sn := by
      intro z hz
      exact (mem_recenterWindow S (-(n•k)) z).mpr
        (hWS ((mem_recenterWindow W (-(n•k)) z).mp hz))
    have hWnR : (Wn : Set Lattice) ⊆ R := by
      intro z hz
      have hzW := (mem_recenterWindow W (-(n•k)) z).mp hz
      have hh := hRforward.nsmul n (z+(-(n•k))) (hW hzW)
      simpa only [neg_add_cancel_right] using hh
    have hSnBottom : (Sn : Set Lattice) ⊆ {z | 0 ≤ det u z} := by
      intro z hz
      change 0 ≤ det u z
      have hzS := (mem_recenterWindow S (-(n•k)) z).mp hz
      have hh := hbottomn (z+(-(n•k))) hzS
      simpa only [neg_add_cancel_right] using hh
    have hSnAgree : AgreeOn x p (Sn : Set Lattice) := by
      intro z hz
      have hzS := (mem_recenterWindow S (-(n•k)) z).mp hz
      by_cases hlow : det k (z+(-(n•k))) < det k w
      · have hh := hnone (z+(-(n•k))) hzS hlow
        simpa only [neg_add_cancel_right] using hh
      · have hh := hgoodn (z+(-(n•k))) hzS (le_of_not_gt hlow)
        have hzR : z ∈ R := by simpa only [neg_add_cancel_right] using hh
        exact hagree z hzR
    have hSnR := hmax Sn Wn (latticeConvex_finset_of_region _ hSne.latticeConvex) hSnf
      hWn (latticeConvex_finset_of_region _ hWne.latticeConvex) hWnf
      hWnSn hWnR hSnBottom hSnAgree
    have hnewn : w+u+n•k ∈ Sn := by
      change w+u+n•k ∈ recenterWindow S (-(n•k))
      simpa only [mem_recenterWindow,add_neg_cancel_right] using hnew
    have hh := hmin (w+u+n•k) (hSnR hnewn)
    rw [det_add_right,det_add_right,det_nsmul_right,det_self,mul_zero,add_zero] at hh
    omega

theorem exists_second_boundary_defect_band {A : Type*}
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
    ∃ k ∈ D, ∃ w ∈ R, 0 < det u k ∧
      (∀ z ∈ R, det k w ≤ det k z) ∧ ForwardInvariant R k ∧
      (∀ z, det k w ≤ det k z → ∀ᶠ n : ℕ in atTop, z+n•k ∈ R) ∧
      ∃ S : Finset Lattice, (∀ z ∈ S, det k w+det k u ≤ det k z) ∧
        ∀ᶠ n : ℕ in atTop, ∃ z ∈ S,
          det k z < det k w ∧ x (z+n•k) ≠ p (z+n•k) := by
  obtain ⟨k,hk,w,hw,huk,hmin,_,hforward,hevent⟩ :=
    exists_second_boundary_ray D R hR u hzero hout hback hheight
  obtain ⟨W,hFW,hWR,hWe,hWf,_⟩ := hexhaust {w} (by simpa using hw)
  have hwW : w ∈ W := hFW (by simp)
  obtain ⟨hlower,hbad⟩ := eventual_second_boundary_defects D R x p u k w huk hw
    hmin hforward hevent hagree hmax W hWR hWe hWf hwW hu hnu
  exact ⟨k,hk,w,hw,huk,hmin,hforward,hevent,stepWindow W u,hlower,hbad⟩

end
end NivatTrial.ColleSecondBoundaryDefects
