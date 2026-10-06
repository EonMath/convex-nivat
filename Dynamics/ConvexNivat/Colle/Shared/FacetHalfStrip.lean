import ConvexNivat.Colle.Shared.FacetShiftData
import ConvexNivat.Colle.Shared.CofinalExtensionRoute
import ConvexNivat.Colle.Shared.UniformCandidateConfinement
import ConvexNivat.Colle.Shared.FixedCandidateGeometrySupport

namespace ConvexNivat.Colle
noncomputable section

private theorem lattice_row_between_parallel_unit_edges
    (B : Finset Lattice) (hB : LatticeConvex B) (v : Lattice) (hv : Primitive v)
    (a b : Lattice) (ha : a ∈ B) (hav : a + v ∈ B)
    (hb : b ∈ B) (hbv : b + v ∈ B) (h : ℤ)
    (hlo : det v a ≤ h) (hhi : h ≤ det v b) :
    ∃ g ∈ B, det v g = h := by
  by_cases heq : det v a = det v b
  · exact ⟨a, ha, by omega⟩
  have hab : (det v a : ℝ) < (det v b : ℝ) := by exact_mod_cast (by omega : det v a < det v b)
  let t : ℝ := ((h : ℝ) - det v a) / ((det v b : ℝ) - det v a)
  have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast sub_nonneg.mpr hlo) (by linarith)
  have ht1 : t ≤ 1 := (div_le_one (by linarith)).mpr (by exact_mod_cast sub_le_sub_right hhi (det v a))
  let x : RealPlane := (1-t) • embed a + t • embed b
  have hx : x ∈ windowHull B := (windowHull_convex B)
    (window_mem_hull B ha) (window_mem_hull B hb) (by linarith) ht0 (by ring)
  have hxv : x + embed v ∈ windowHull B := by
    have hh := (windowHull_convex B) (window_mem_hull B hav)
      (window_mem_hull B hbv) (by linarith : 0 ≤ 1-t) ht0 (by ring : 1-t+t=1)
    convert hh using 1
    rw [embed_add,embed_add]
    dsimp [x]
    module
  have hxheight : realDet (embed v) x = (h : ℝ) := by
    have hd : realDet (embed v) x = (1-t)*(det v a : ℝ)+t*(det v b : ℝ) := by
      simp [x,realDet,embed,det];ring
    rw [hd]
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  obtain ⟨e, he, _⟩ := (primitive_row_coordinates v hv).1
  have heR : realDet (embed v) (embed e) = 1 := by
    change (v.1:ℝ)*(e.2:ℝ)-(v.2:ℝ)*(e.1:ℝ)=1
    exact_mod_cast he
  have hexpand : x = realDet x (embed e) • embed v +
      realDet (embed v) x • embed e := by
    apply Prod.ext <;> dsimp [realDet] at heR ⊢
    · linear_combination -x.1 * heR
    · linear_combination -x.2 * heR
  let k : ℤ := ⌈realDet x (embed e)⌉
  let g : Lattice := k • v + h • e
  let s : ℝ := (k : ℝ) - realDet x (embed e)
  have hs0 : 0 ≤ s := sub_nonneg.mpr (Int.le_ceil _)
  have hs1 : s ≤ 1 := by have hh := Int.ceil_lt_add_one (realDet x (embed e));dsimp [s,k];linarith
  have hgheight : det v g = h := by
    dsimp [g,det] at *
    linear_combination h*he
  have hgline : embed g = (1-s) • x + s • (x + embed v) := by
    calc
      embed g = (k:ℝ) • embed v + (h:ℝ) • embed e := by ext <;> simp [g,embed]
      _ = x + s • embed v := by
        conv_rhs => rw [hexpand,hxheight]
        dsimp [s]
        module
      _ = _ := by module
  refine ⟨g, (hB g).mp ?_, hgheight⟩
  rw [hgline]
  exact (windowHull_convex B) hx hxv (by linarith) hs0 (by ring)

local macro "paidAlignedMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.UniformCandidateConfinement).num 0 ++ `ConvexNivat.Colle.aligned_mem_support_iff))
local macro "paidRowMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.row_mem))

private theorem aligned_first_unit_step {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (D : AlignedBoundary C B) (r : ℤ) :
    D.vertex r + C.direction r ∈ B := by
  have he : D.vertex r + (D.length r : ℤ) • C.direction r = D.vertex (r+1) := by
    linear_combination (norm := module) -D.edge_eq r
  have hh := ((primitive_row_coordinates (C.direction r) (C.primitive r)).2.2
    (D.vertex r) 0 (D.length r) (by positivity) (D.vertex r + C.direction r)).mpr
    ⟨1, by norm_num, by exact_mod_cast D.length_positive r, by simp⟩
  simp only [zero_smul,add_zero,he] at hh
  exact (Finset.mem_filter.mp ((D.segment_eq r _).mpr hh)).1

private theorem aligned_preserved_supports_halfstrip {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (D : AlignedBoundary C B) (hB : LatticeConvex B)
    (i : ℤ) (z : Lattice)
    (hz : ∀ r : ℤ, 0 ≤ det (C.direction r) (C.direction i) →
      det (C.direction r) (D.vertex r) ≤ det (C.direction r) z) :
    z ∈ halfStrip B (C.direction i) := by
  let v := C.direction i
  let a := D.vertex i
  let b := D.vertex (i+(m:ℤ)) - v
  have ha : a ∈ B := (Finset.mem_filter.mp (D.initial i)).1
  have hav : a+v ∈ B := aligned_first_unit_step C D i
  have hb : b ∈ B := by
    simpa only [C.antipodal,sub_eq_add_neg,b,v] using aligned_first_unit_step C D (i+(m:ℤ))
  have hbv : b+v ∈ B := by
    simpa only [b,sub_add_cancel] using (Finset.mem_filter.mp (D.initial (i+(m:ℤ)))).1
  have hlo : det v a ≤ det v z := hz i (by dsimp [v,det];ring_nf;norm_num)
  have hhi : det v z ≤ det v b := by
    have hh := hz (i+(m:ℤ)) (by rw [C.antipodal];dsimp [det];ring_nf;norm_num)
    rw [C.antipodal] at hh
    dsimp [b,v,det] at hh ⊢
    nlinarith
  obtain ⟨g,hg,hrow⟩ := lattice_row_between_parallel_unit_edges B hB v (C.primitive i)
    a b ha hav hb hbv (det v z) hlo hhi
  obtain ⟨k,hk⟩ := ((primitive_row_coordinates v (C.primitive i)).2.1 g z).mp hrow
  by_cases hk0 : 0 ≤ k
  · refine ⟨g,hg,k.toNat,?_⟩
    rw [Int.toNat_of_nonneg hk0]
    exact hk
  · have hzB : z ∈ B := by
      apply (paidAlignedMem C hB D z).mpr
      intro r
      by_cases hr : 0 ≤ det (C.direction r) v
      · exact hz r hr
      · have hgr := (paidRowMem B (C.direction r) (D.vertex r)).mp (D.initial r)
        have hgmin := hgr.2 g hg
        have hdet : det (C.direction r) z = det (C.direction r) g +
            k*det (C.direction r) v := by rw [hk];dsimp [det];ring
        rw [hdet]
        exact hgmin.trans (le_add_of_nonneg_right (mul_nonneg_of_nonpos_of_nonpos
          (by omega) (by omega)))
    exact ⟨z,hzB,0,by simp⟩

local macro "facetU" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftLattice))
local macro "paidHalfOrder" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_half_order))

private theorem facet_halfstrip_each {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) :
    facetU W G L j ⊆ halfStrip
      (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) := by
  intro z hz
  let t := G.subsequence (L.index j)
  let v := C.direction i
  let n : ℤ := W.normalise t
  have hturn : 0 < det v (C.direction G.J) :=
    paidHalfOrder C i G.J (by have := G.lower;omega) (by have := G.upper;omega)
  have hback : det (C.direction G.J) v < 0 := by
    dsimp [det] at hturn ⊢
    nlinarith
  have hzA : z+n • v ∈ halfStrip (W.A t) v := by
    apply aligned_preserved_supports_halfstrip C (W.boundary t) (W.A_enveloped t).2.1 i
    intro r hr
    have hne : C.direction r ≠ C.direction G.J := by
      intro heq
      rw [heq] at hr
      exact (not_le_of_gt hback) hr
    have hh := hz r
    simp only [ite_eq_right hne,sub_zero] at hh
    change det (C.direction r) ((W.boundary t).vertex r - n • v) ≤
      det (C.direction r) z at hh
    dsimp [det] at hh ⊢
    nlinarith
  obtain ⟨g,hg,s,hzg⟩ := hzA
  obtain ⟨b,hb,u,hgb⟩ := (W.maximal t).2.2.1 hg
  refine ⟨b-n • v,?_,u+s,?_⟩
  · exact Finset.mem_image.mpr ⟨b,hb,by simp [sub_eq_add_neg,n,v,t]⟩
  · push_cast
    rw [add_smul]
    linear_combination (norm := module) hzg + hgb

private theorem independent_facet_halfstrip
(ξ xper : Configuration ℤ)
(alphabet : Finset ℤ) (halphabet : ∀ z, ξ z ∈ alphabet)
(S : Finset Lattice) (hS : GeneratingSet ξ S)
(m : ℕ) (C : AntipodalEdgeCycle S m) (i : ℤ)
(hxper : xper ∈ OrbitClosure ξ)
(hperiod : ∃ a : ℤ, a ≠ 0 ∧ HasPeriod xper (a • C.direction i))
(W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
(P : Region (C.direction i) (C.direction G.J))
(hP : P.lattice = normalisedUnion W G)
(hcarrier : P.carrier = closedRealHull (normalisedUnion W G))
(hweak : WeaklyEnveloped S P) (harc : RegionCompleteArc C i G.J P)
(hanchor : det (C.direction i) P.firstAnchor = -1)
(L : NormalisedWindowLimit W G)
(hall : ∀ r : ℕ, AgreesOn L.field
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r)) :
    ∃ jH : ℕ, ∀ j ≥ jH,
      facetU W G L j ⊆ halfStrip
        (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) := by
  exact ⟨0, fun j _ => facet_halfstrip_each W G L j⟩


end
end ConvexNivat.Colle
