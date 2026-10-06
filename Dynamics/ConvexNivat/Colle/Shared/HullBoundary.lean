import ConvexNivat.Colle.Shared.Enlargement
import ConvexNivat.Colle.Shared.BoundaryCycle

namespace ConvexNivat.Colle
noncomputable section

private theorem rj_real_det (u z : Lattice) :
    realDet (embed u) (embed z) = (det u z : ℝ) := by simp [realDet,embed,det]

private theorem rj_det_add (u z t : Lattice) : det u (z+t) = det u z+det u t := by
  dsimp [det];ring

private theorem rj_det_smul (u z : Lattice) (n : ℤ) : det u (n•z) = n*det u z := by
  dsimp [det];ring

private theorem rj_real_det_add (u x y : RealPlane) :
    realDet u (x+y) = realDet u x+realDet u y := by dsimp [realDet];ring

private theorem rj_real_det_sub (u x y : RealPlane) :
    realDet u (x-y) = realDet u x-realDet u y := by dsimp [realDet];ring

private theorem rj_real_det_smul (u x : RealPlane) (t : ℝ) :
    realDet u (t•x) = t*realDet u x := by dsimp [realDet];ring

private theorem rj_vertex_mem {v w : Lattice} (P : Region v w)
    (j : Fin (P.boundedCount+1)) : embed (P.vertex j) ∈ P.carrier := by
  rw [(region_halfplane_representation P).2.1]
  refine ⟨embed (P.vertex j),subset_convexHull ℝ _ ⟨j,rfl⟩,0,?_,by simp⟩
  exact ⟨0,0,le_rfl,le_rfl,by simp⟩

private theorem rj_predecessor_first_nonnegative {v w : Lattice} (P : Region v w) :
    0 ≤ det v P.predecessor := by
  unfold Region.predecessor
  split_ifs with h
  · let j : Fin P.boundedCount := ⟨P.boundedCount-1,Nat.sub_lt h Nat.zero_lt_one⟩
    have hz : P.vertex j.castSucc ∈ P.lattice := rj_vertex_mem P j.castSucc
    have hm := (region_halfplane_representation P).2.2.2.1 _ hz
    have hs := P.bounded_support j (embed (P.vertex j.castSucc+ -v)) hm
    have heq : embed (P.vertex j.castSucc+ -v)-embed (P.vertex j.castSucc) = embed (-v) := by
      rw [embed_add];abel
    rw [heq,rj_real_det] at hs
    have hdet : det (P.boundedDirection j) (-v) = det v (P.boundedDirection j) := by
      dsimp [det];ring
    rw [hdet] at hs
    exact_mod_cast hs
  · dsimp [det]
    nlinarith

private theorem rj_first_height_lower {v w : Lattice} (P : Region v w)
    (n : ℕ) (z : Lattice) (hz : z ∈ P.enlargement n) :
    det v P.firstAnchor ≤ det v z := by
  obtain ⟨g,hg,t,rfl,hrow⟩ := hz
  have h := P.first_support (embed g) hg
  change 0 ≤ realDet (embed v) (embed g-embed P.firstAnchor) at h
  rw [rj_real_det_sub,rj_real_det,rj_real_det] at h
  have hgheight : det v P.firstAnchor ≤ det v g := by exact_mod_cast (sub_nonneg.mp h)
  rw [rj_det_add,rj_det_smul]
  have hnon := mul_nonneg (Int.natCast_nonneg t) (rj_predecessor_first_nonnegative P)
  omega

private theorem rj_first_height_equal {v w : Lattice} (P Q : Region v w) (n : ℕ)
    (hQ : Q.lattice = P.enlargement n) : det v Q.firstAnchor = det v P.firstAnchor := by
  have hQmem : Q.firstAnchor ∈ P.enlargement n := by
    rw [← hQ]
    exact rj_vertex_mem Q ⟨0,Nat.zero_lt_succ _⟩
  have hlo := rj_first_height_lower P n Q.firstAnchor hQmem
  have hPmem : P.firstAnchor ∈ Q.lattice := by
    rw [hQ]
    exact ⟨P.firstAnchor,rj_vertex_mem P ⟨0,Nat.zero_lt_succ _⟩,0,by simp,
      Or.inl (rj_vertex_mem P ⟨0,Nat.zero_lt_succ _⟩)⟩
  have h := Q.first_support (embed P.firstAnchor) hPmem
  change 0 ≤ realDet (embed v) (embed P.firstAnchor-embed Q.firstAnchor) at h
  rw [rj_real_det_sub,rj_real_det,rj_real_det] at h
  have hhi : det v Q.firstAnchor ≤ det v P.firstAnchor := by exact_mod_cast (sub_nonneg.mp h)
  omega

private theorem rj_cone_convex (p q : Lattice) : Convex ℝ (twoRayCone p q) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨r,s,hr,hs,rfl⟩ := hx
  obtain ⟨t,u,ht,hu,rfl⟩ := hy
  exact ⟨a*r+b*t,a*s+b*u,add_nonneg (mul_nonneg ha hr) (mul_nonneg hb ht),
    add_nonneg (mul_nonneg ha hs) (mul_nonneg hb hu),by module⟩

private theorem rj_hull_convex (G : Finset Lattice) (p q : Lattice) :
    Convex ℝ (finiteRayHull G p q) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨r,hr,s,hs,rfl⟩ := hx
  obtain ⟨t,ht,u,hu,rfl⟩ := hy
  exact ⟨a•r+b•t,(windowHull_convex G) hr ht ha hb hab,
    a•s+b•u,(rj_cone_convex p q) hs hu ha hb hab,by module⟩

private theorem rj_hull_add_cone (G : Finset Lattice) (p q : Lattice)
    (x : RealPlane) (hx : x ∈ finiteRayHull G p q)
    (u : RealPlane) (hu : u ∈ twoRayCone p q) : x+u ∈ finiteRayHull G p q := by
  obtain ⟨y,hy,z,⟨a,b,ha,hb,rfl⟩,rfl⟩ := hx
  obtain ⟨r,s,hr,hs,rfl⟩ := hu
  refine ⟨y,hy,(a+r)•embed p+(b+s)•embed q,
    ⟨a+r,b+s,add_nonneg ha hr,add_nonneg hb hs,rfl⟩,?_⟩
  module

private theorem rj_hull_point (G : Finset Lattice) (p q : Lattice)
    (z : Lattice) (hz : z ∈ G) : embed z ∈ finiteRayHull G p q := by
  exact ⟨embed z,window_mem_hull G hz,0,⟨0,0,le_rfl,le_rfl,by simp⟩,by simp⟩

private theorem rj_region_subset_hull {v w : Lattice} (P : Region v w) (n : ℕ)
    (G : Finset Lattice) (hEq : P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w) :
    P.carrier ⊆ finiteRayHull G (-v) w := by
  have hvertices : regionVertexHull P ⊆ finiteRayHull G (-v) w := by
    apply convexHull_min _ (rj_hull_convex G (-v) w)
    rintro _ ⟨j,rfl⟩
    have hz : P.vertex j ∈ P.enlargement n :=
      ⟨P.vertex j,rj_vertex_mem P j,0,by simp,Or.inl (rj_vertex_mem P j)⟩
    rw [hEq] at hz
    exact hz
  intro x hx
  rw [(region_halfplane_representation P).2.1] at hx
  obtain ⟨y,hy,u,hu,rfl⟩ := hx
  exact rj_hull_add_cone G (-v) w y (hvertices hy) u hu

private theorem rj_hull_area {v w : Lattice} (P : Region v w) (n : ℕ)
    (G : Finset Lattice) (hEq : P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w) :
    (interior (finiteRayHull G (-v) w)).Nonempty :=
  P.interior_nonempty.mono (interior_mono (rj_region_subset_hull P n G hEq))

private theorem rj_hull_support (G : Finset Lattice) (p q d g : Lattice)
    (_hg : g ∈ G) (hmin : ∀ z ∈ G, det d g ≤ det d z)
    (hp : 0 ≤ det d p) (hq : 0 ≤ det d q) :
    ∀ x ∈ finiteRayHull G p q, (det d g:ℝ) ≤ realDet (embed d) x := by
  have hconv : Convex ℝ {x : RealPlane | (det d g:ℝ) ≤ realDet (embed d) x} := by
    intro x hx y hy a b ha hb hab
    change (det d g:ℝ) ≤ realDet (embed d) (a•x+b•y)
    rw [rj_real_det_add,rj_real_det_smul,rj_real_det_smul]
    calc
      _ = a*(det d g:ℝ)+b*(det d g:ℝ) := by rw [← add_mul,hab,one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  have hpoints : embed '' (G:Set Lattice) ⊆ {x | (det d g:ℝ) ≤ realDet (embed d) x} := by
    rintro _ ⟨z,hz,rfl⟩
    change (det d g:ℝ) ≤ realDet (embed d) (embed z)
    rw [rj_real_det]
    exact_mod_cast hmin z hz
  have hH := convexHull_min hpoints hconv
  intro x hx
  obtain ⟨y,hy,z,⟨a,b,ha,hb,rfl⟩,rfl⟩ := hx
  have hymin := hH hy
  change (det d g:ℝ) ≤ realDet (embed d) y at hymin
  rw [rj_real_det_add,rj_real_det_add,rj_real_det_smul,rj_real_det_smul,rj_real_det,rj_real_det]
  have hpR : (0:ℝ) ≤ det d p := by exact_mod_cast hp
  have hqR : (0:ℝ) ≤ det d q := by exact_mod_cast hq
  linarith [mul_nonneg ha hpR,mul_nonneg hb hqR]

private theorem rj_hull_recession (G : Finset Lattice) (hG : G.Nonempty)
    (v w : Lattice) (hturn : 0 < det v w) :
    recessionCone (finiteRayHull G (-v) w) = twoRayCone (-v) w := by
  apply Set.Subset.antisymm
  · intro d hd
    have hv0 : det v (-v) = 0 := by dsimp [det];ring
    have hw0 : det w w = 0 := by dsimp [det];ring
    have hwv : det w (-v) = det v w := by dsimp [det];ring
    obtain ⟨gv,hgv,hminv⟩ := G.exists_min_image (det v) hG
    obtain ⟨gw,hgw,hminw⟩ := G.exists_min_image (det w) hG
    have hv := rj_hull_support G (-v) w v gv hgv hminv (by rw [hv0]) hturn.le
      _ (hd _ (rj_hull_point G (-v) w gv hgv))
    have hw := rj_hull_support G (-v) w w gw hgw hminw (by rw [hwv];exact hturn.le) (by rw [hw0])
      _ (hd _ (rj_hull_point G (-v) w gw hgw))
    rw [rj_real_det_add,rj_real_det] at hv hw
    have hvd : 0 ≤ realDet (embed v) d := by linarith
    have hwd : 0 ≤ realDet (embed w) d := by linarith
    let D : ℝ := realDet (embed v) (embed w)
    have hD : 0 < D := by dsimp [D];rw [rj_real_det];exact_mod_cast hturn
    refine ⟨realDet (embed w) d/D,realDet (embed v) d/D,
      div_nonneg hwd hD.le,div_nonneg hvd hD.le,?_⟩
    have hneg : embed (-v) = -embed v := by simp [embed]
    rw [hneg,smul_neg]
    have hbase : D•d = -(realDet (embed w) d • embed v)+realDet (embed v) d • embed w := by
      ext <;> dsimp [D,realDet] <;> ring
    have h := congrArg (fun x : RealPlane => D⁻¹•x) hbase
    simpa only [smul_add,smul_neg,smul_smul,inv_mul_cancel₀ (ne_of_gt hD),one_smul,
      ← div_eq_inv_mul] using h
  · intro d hd x hx
    exact rj_hull_add_cone G (-v) w x hx d hd

private theorem rj_collar_hull_nonempty {v w : Lattice} (P : Region v w) (n : ℕ)
    (G : Finset Lattice) (hEq : P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w) : G.Nonempty := by
  by_contra h
  have hG : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hm := rj_region_subset_hull P n G hEq (rj_vertex_mem P ⟨0,Nat.zero_lt_succ _⟩)
  obtain ⟨y,hy,z,hz,heq⟩ := hm
  simp [hG,windowHull] at hy

private theorem rj_collar_hull_recession {v w : Lattice} (P : Region v w) (n : ℕ)
    (G : Finset Lattice) (hEq : P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w) :
    recessionCone (finiteRayHull G (-v) w) = twoRayCone (-v) w :=
  rj_hull_recession G (rj_collar_hull_nonempty P n G hEq) v w P.turn_positive

private theorem hb_cone_halfplanes (v w : Lattice) (hturn : 0 < det v w) :
    twoRayCone (-v) w = {x | 0 ≤ realDet (embed v) x ∧ 0 ≤ realDet (embed w) x} := by
  have hneg : embed (-v) = -embed v := by simp [embed]
  have hv0 : realDet (embed v) (embed (-v)) = 0 := by rw [rj_real_det];simp [det];ring
  have hw0 : realDet (embed w) (embed w) = 0 := by rw [rj_real_det];simp [det];ring
  have hwv : realDet (embed w) (embed (-v)) = (det v w:ℝ) := by rw [rj_real_det];dsimp [det];ring
  have hD : (0:ℝ) < det v w := by exact_mod_cast hturn
  ext x
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    simp only [Set.mem_ofPred_eq,rj_real_det_add,rj_real_det_smul,hv0,hw0,hwv,
      rj_real_det,mul_zero,zero_add,add_zero]
    exact ⟨mul_nonneg hb hD.le,mul_nonneg ha hD.le⟩
  · rintro ⟨hvx,hwx⟩
    refine ⟨realDet (embed w) x/(det v w:ℝ),realDet (embed v) x/(det v w:ℝ),
      div_nonneg hwx hD.le,div_nonneg hvx hD.le,?_⟩
    rw [hneg,smul_neg]
    have hbase : (det v w:ℝ)•x =
        -(realDet (embed w) x • embed v)+realDet (embed v) x • embed w := by
      ext <;> simp [det,realDet,embed] <;> ring
    have h := congrArg (fun z : RealPlane => (det v w:ℝ)⁻¹•z) hbase
    simpa only [smul_add,smul_neg,smul_smul,inv_mul_cancel₀ (ne_of_gt hD),one_smul,
      ← div_eq_inv_mul] using h

private theorem hb_cone_closed (v w : Lattice) (hturn : 0 < det v w) :
    IsClosed (twoRayCone (-v) w) := by
  rw [hb_cone_halfplanes v w hturn]
  have hv : Continuous (fun x : RealPlane => realDet (embed v) x) := by unfold realDet;fun_prop
  have hw : Continuous (fun x : RealPlane => realDet (embed w) x) := by unfold realDet;fun_prop
  exact (isClosed_le continuous_const hv).inter (isClosed_le continuous_const hw)

private theorem hb_hull_closed (G : Finset Lattice) (v w : Lattice)
    (hturn : 0 < det v w) : IsClosed (finiteRayHull G (-v) w) := by
  have hcompact : IsCompact (windowHull G) :=
    (G.finite_toSet.image embed).isCompact_convexHull ℝ
  have h := (hb_cone_closed v w hturn).add_left_of_isCompact hcompact
  convert h using 1
  ext x
  simp only [finiteRayHull,realMinkowski,Set.mem_ofPred_eq,Set.mem_add]
  constructor <;> rintro ⟨y,hy,z,hz,hEq⟩ <;> exact ⟨y,hy,z,hz,hEq.symm⟩

private theorem hb_window_subset_hull (G : Finset Lattice) (p q : Lattice) :
    windowHull G ⊆ finiteRayHull G p q := by
  intro x hx
  exact ⟨x,hx,0,⟨0,0,le_rfl,le_rfl,by simp⟩,by simp⟩

private theorem hb_extreme_subset_anchors (G : Finset Lattice) (p q : Lattice) :
    (finiteRayHull G p q).extremePoints ℝ ⊆ embed '' (G : Set Lattice) := by
  intro x hx
  obtain ⟨y,hy,u,hu,hEq⟩ := hx.1
  have hyH := hb_window_subset_hull G p q hy
  have hx2 := rj_hull_add_cone G p q x hx.1 u hu
  have hm : x ∈ openSegment ℝ y (x+u) := by
    have h := mem_openSegment_sub_add (𝕜 := ℝ) x u
    have hyEq : x-u=y := by rw [hEq];abel
    rwa [hyEq] at h
  have hyx : y=x := hx.2 hyH hx2 hm
  have hxW : x ∈ windowHull G := hyx ▸ hy
  have hex : x ∈ (windowHull G).extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (hb_window_subset_hull G p q) ⟨hxW,hx⟩
  exact extremePoints_convexHull_subset hex

private theorem hb_extreme_finite (G : Finset Lattice) (p q : Lattice) :
    ((finiteRayHull G p q).extremePoints ℝ).Finite :=
  (G.finite_toSet.image embed).subset (hb_extreme_subset_anchors G p q)

private theorem hb_lex_anchor (G : Finset Lattice) (hG : G.Nonempty) (u d : Lattice) :
    ∃ g ∈ G, (∀ z ∈ G, det u g ≤ det u z) ∧
      (∀ z ∈ G, det u z = det u g → det d g ≤ det d z) := by
  obtain ⟨a,ha,hmin⟩ := G.exists_min_image (det u) hG
  let F := G.filter (fun z => det u z=det u a)
  have hF : F.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
  obtain ⟨g,hg,hming⟩ := F.exists_min_image (det d) hF
  have hga := (Finset.mem_filter.mp hg).2
  refine ⟨g,(Finset.mem_filter.mp hg).1,?_,?_⟩
  · intro z hz
    rw [hga]
    exact hmin z hz
  · intro z hz hzu
    exact hming z (Finset.mem_filter.mpr ⟨hz,hzu.trans hga⟩)

private theorem hb_lex_convex (u d : RealPlane) (c k : ℝ) :
    Convex ℝ {x | c ≤ realDet u x ∧ (realDet u x=c → k ≤ realDet d x)} := by
  apply convex_iff_forall_pos.mpr
  intro x hx y hy a b ha hb hab
  have hlow : c ≤ realDet u (a•x+b•y) := by
    rw [rj_real_det_add,rj_real_det_smul,rj_real_det_smul]
    calc
      _ = a*c+b*c := by rw [← add_mul,hab,one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha.le)
        (mul_le_mul_of_nonneg_left hy.1 hb.le)
  refine ⟨hlow,?_⟩
  intro heq
  rw [rj_real_det_add,rj_real_det_smul,rj_real_det_smul] at heq
  have hslack : a*(realDet u x-c)+b*(realDet u y-c)=0 := by
    calc
      _ = a*realDet u x+b*realDet u y-(a+b)*c := by ring
      _ = 0 := by rw [heq,hab];ring
  have he := (add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hx.1))
    (mul_nonneg hb.le (sub_nonneg.mpr hy.1))).mp hslack
  have hxEq : realDet u x=c := sub_eq_zero.mp ((mul_eq_zero.mp he.1).resolve_left ha.ne')
  have hyEq : realDet u y=c := sub_eq_zero.mp ((mul_eq_zero.mp he.2).resolve_left hb.ne')
  change k ≤ realDet d (a•x+b•y)
  rw [rj_real_det_add,rj_real_det_smul,rj_real_det_smul]
  calc
    _ = a*k+b*k := by rw [← add_mul,hab,one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2 hxEq) ha.le)
      (mul_le_mul_of_nonneg_left (hy.2 hyEq) hb.le)

private theorem hb_hull_lex_support (G : Finset Lattice) (p q u d g : Lattice)
    (hmin : ∀ z ∈ G, det u g ≤ det u z)
    (hlex : ∀ z ∈ G, det u z=det u g → det d g ≤ det d z)
    (hup : det u p=0) (huq : 0 < det u q) (hdp : 0 ≤ det d p) :
    ∀ x ∈ finiteRayHull G p q,
      (det u g:ℝ) ≤ realDet (embed u) x ∧
      (realDet (embed u) x=(det u g:ℝ) → (det d g:ℝ) ≤ realDet (embed d) x) := by
  have hW : ∀ x ∈ windowHull G,
      (det u g:ℝ) ≤ realDet (embed u) x ∧
      (realDet (embed u) x=(det u g:ℝ) → (det d g:ℝ) ≤ realDet (embed d) x) := by
    apply convexHull_min ?_ (hb_lex_convex _ _ _ _)
    rintro _ ⟨z,hz,rfl⟩
    change (det u g:ℝ) ≤ realDet (embed u) (embed z) ∧ _
    rw [rj_real_det]
    refine ⟨by exact_mod_cast hmin z hz,?_⟩
    intro hEq
    rw [rj_real_det]
    exact_mod_cast hlex z hz (by exact_mod_cast hEq)
  intro x hx
  obtain ⟨y,hy,t,⟨a,b,ha,hb,rfl⟩,rfl⟩ := hx
  have hymin := hW y hy
  have hupR : (det u p:ℝ)=0 := by exact_mod_cast hup
  have huqR : (0:ℝ)<det u q := by exact_mod_cast huq
  have hdpR : (0:ℝ)≤det d p := by exact_mod_cast hdp
  simp only [rj_real_det_add,rj_real_det_smul,rj_real_det,hupR,mul_zero,zero_add]
  refine ⟨by linarith [mul_nonneg hb huqR.le],?_⟩
  intro hEq
  have hb0 : b=0 := by nlinarith [hymin.1]
  have hyEq : realDet (embed u) y=(det u g:ℝ) := by simpa [hb0] using hEq
  have hyd := hymin.2 hyEq
  rw [hb0,zero_mul,add_zero]
  linarith [mul_nonneg ha hdpR]

private theorem hb_first_anchor_ray (G : Finset Lattice) (hG : G.Nonempty)
    (v w : Lattice) (hturn : 0 < det v w) :
    ∃ g ∈ G,
      (∀ x ∈ finiteRayHull G (-v) w, 0 ≤ realDet (embed v) (x-embed g)) ∧
      {x ∈ finiteRayHull G (-v) w | realDet (embed v) (x-embed g)=0} =
        {x | ∃ t : ℝ, 0 ≤ t ∧ x=embed g-t•embed v} := by
  obtain ⟨g,hg,hmin,hlex⟩ := hb_lex_anchor G hG v w
  have hvv : det v (-v)=0 := by dsimp [det];ring
  have hwv : det w (-v)=det v w := by dsimp [det];ring
  have hs := hb_hull_lex_support G (-v) w v w g hmin hlex hvv hturn
    (by rw [hwv];exact hturn.le)
  refine ⟨g,hg,?_,?_⟩
  · intro x hx
    rw [rj_real_det_sub,rj_real_det]
    exact sub_nonneg.mpr (hs x hx).1
  · ext x
    constructor
    · rintro ⟨hx,hzero⟩
      have hvEq : realDet (embed v) x=(det v g:ℝ) := by
        rw [rj_real_det_sub,rj_real_det] at hzero
        exact sub_eq_zero.mp hzero
      have hdw : 0 ≤ realDet (embed w) (x-embed g) := by
        rw [rj_real_det_sub,rj_real_det]
        exact sub_nonneg.mpr ((hs x hx).2 hvEq)
      have hc : x-embed g ∈ twoRayCone (-v) w := by
        rw [hb_cone_halfplanes v w hturn]
        exact ⟨hzero.ge,hdw⟩
      obtain ⟨a,b,ha,hb,heq⟩ := hc
      have hD : (0:ℝ)<det v w := by exact_mod_cast hturn
      have hb0 : b=0 := by
        have hh := congrArg (realDet (embed v)) heq
        rw [hzero,rj_real_det_add,rj_real_det_smul,rj_real_det_smul,rj_real_det,
          rj_real_det,hvv] at hh
        simp only [Int.cast_zero,mul_zero,zero_add] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_right hD.ne'
      refine ⟨a,ha,?_⟩
      have hneg : embed (-v) = -embed v := by simp [embed]
      rw [hb0,zero_smul,add_zero,hneg,smul_neg] at heq
      linear_combination (norm := module) heq
    · rintro ⟨t,ht,rfl⟩
      have hneg : embed (-v) = -embed v := by simp [embed]
      constructor
      · have hm := rj_hull_add_cone G (-v) w (embed g) (rj_hull_point G (-v) w g hg)
          (-t•embed v) ⟨t,0,ht,le_rfl,by rw [hneg];module⟩
        simpa [sub_eq_add_neg,neg_smul] using hm
      · have he : embed g-t•embed v-embed g = (-t)•embed v := by module
        have hv0 : det v v=0 := by dsimp [det];ring
        rw [he,rj_real_det_smul,rj_real_det,hv0]
        simp

private theorem hb_second_anchor_ray (G : Finset Lattice) (hG : G.Nonempty)
    (v w : Lattice) (hturn : 0 < det v w) :
    ∃ g ∈ G,
      (∀ x ∈ finiteRayHull G (-v) w, 0 ≤ realDet (embed w) (x-embed g)) ∧
      {x ∈ finiteRayHull G (-v) w | realDet (embed w) (x-embed g)=0} =
        {x | ∃ t : ℝ, 0 ≤ t ∧ x=embed g+t•embed w} := by
  obtain ⟨g,hg,hmin,hlex⟩ := hb_lex_anchor G hG w v
  have hww : det w w=0 := by dsimp [det];ring
  have hwv : det w (-v)=det v w := by dsimp [det];ring
  have hswap : finiteRayHull G w (-v) = finiteRayHull G (-v) w := by
    unfold finiteRayHull
    congr 1
    ext x
    constructor <;> rintro ⟨a,b,ha,hb,he⟩ <;>
      exact ⟨b,a,hb,ha,by rw [he];abel⟩
  have hs := hb_hull_lex_support G w (-v) w v g hmin hlex hww
    (by rw [hwv];exact hturn) hturn.le
  rw [hswap] at hs
  refine ⟨g,hg,?_,?_⟩
  · intro x hx
    rw [rj_real_det_sub,rj_real_det]
    exact sub_nonneg.mpr (hs x hx).1
  · ext x
    constructor
    · rintro ⟨hx,hzero⟩
      have hwEq : realDet (embed w) x=(det w g:ℝ) := by
        rw [rj_real_det_sub,rj_real_det] at hzero
        exact sub_eq_zero.mp hzero
      have hdv : 0 ≤ realDet (embed v) (x-embed g) := by
        rw [rj_real_det_sub,rj_real_det]
        exact sub_nonneg.mpr ((hs x hx).2 hwEq)
      have hc : x-embed g ∈ twoRayCone (-v) w := by
        rw [hb_cone_halfplanes v w hturn]
        exact ⟨hdv,hzero.ge⟩
      obtain ⟨a,b,ha,hb,heq⟩ := hc
      have hD : (0:ℝ)<det v w := by exact_mod_cast hturn
      have ha0 : a=0 := by
        have hh := congrArg (realDet (embed w)) heq
        rw [hzero,rj_real_det_add,rj_real_det_smul,rj_real_det_smul,rj_real_det,
          rj_real_det,hwv,hww] at hh
        simp only [Int.cast_zero,mul_zero,add_zero] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_right hD.ne'
      refine ⟨b,hb,?_⟩
      rw [ha0,zero_smul,zero_add] at heq
      linear_combination (norm := module) heq
    · rintro ⟨t,ht,rfl⟩
      constructor
      · exact rj_hull_add_cone G (-v) w (embed g) (rj_hull_point G (-v) w g hg)
          (t•embed w) ⟨0,t,le_rfl,ht,by simp⟩
      · rw [add_sub_cancel_left,rj_real_det_smul,rj_real_det,hww]
        simp

private theorem hb_weighted_values_eq (a b c r s : ℝ)
    (ha : 0<a) (hb : 0<b) (hab : a+b=1) (hr : c ≤ r) (hs : c ≤ s)
    (hEq : a*r+b*s=c) : r=c ∧ s=c := by
  have hslack : a*(r-c)+b*(s-c)=0 := by
    calc
      _ = a*r+b*s-(a+b)*c := by ring
      _ = 0 := by rw [hEq,hab];ring
  have he := (add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hr))
    (mul_nonneg hb.le (sub_nonneg.mpr hs))).mp hslack
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp he.1).resolve_left ha.ne'),
    sub_eq_zero.mp ((mul_eq_zero.mp he.2).resolve_left hb.ne')⟩

private theorem hb_extreme_of_lex_support (S : Set RealPlane) (g u d : RealPlane)
    (hg : g ∈ S) (hdet : realDet u d ≠ 0)
    (hs : ∀ x ∈ S, realDet u g ≤ realDet u x ∧
      (realDet u x=realDet u g → realDet d g ≤ realDet d x)) :
    g ∈ S.extremePoints ℝ := by
  refine ⟨hg,?_⟩
  intro x hx y hy hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have huEq : a*realDet u x+b*realDet u y=realDet u g := by
    rw [← rj_real_det_smul,← rj_real_det_smul,← rj_real_det_add,heq]
  have hdEq : a*realDet d x+b*realDet d y=realDet d g := by
    rw [← rj_real_det_smul,← rj_real_det_smul,← rj_real_det_add,heq]
  have heu := hb_weighted_values_eq a b _ _ _ ha hb hab (hs x hx).1 (hs y hy).1 huEq
  have hed := hb_weighted_values_eq a b _ _ _ ha hb hab
    ((hs x hx).2 heu.1) ((hs y hy).2 heu.2) hdEq
  have hu0 : realDet u (x-g)=0 := by rw [rj_real_det_sub,heu.1];ring
  have hd0 : realDet d (x-g)=0 := by rw [rj_real_det_sub,hed.1];ring
  have hbase : realDet u d • (x-g) =
      -(realDet d (x-g) • u)+realDet u (x-g) • d := by
    ext <;> dsimp [realDet] <;> ring
  rw [hu0,hd0,zero_smul,zero_smul,neg_zero,add_zero] at hbase
  exact sub_eq_zero.mp ((smul_eq_zero.mp hbase).resolve_left hdet)

private theorem hb_extreme_nonempty (G : Finset Lattice) (hG : G.Nonempty)
    (v w : Lattice) (hturn : 0<det v w) :
    ((finiteRayHull G (-v) w).extremePoints ℝ).Nonempty := by
  obtain ⟨g,hg,hmin,hlex⟩ := hb_lex_anchor G hG v w
  have hvv : det v (-v)=0 := by dsimp [det];ring
  have hwv : det w (-v)=det v w := by dsimp [det];ring
  have hs := hb_hull_lex_support G (-v) w v w g hmin hlex hvv hturn
    (by rw [hwv];exact hturn.le)
  refine ⟨embed g,hb_extreme_of_lex_support _ _ (embed v) (embed w)
    (rj_hull_point G (-v) w g hg) ?_ ?_⟩
  · rw [rj_real_det]
    exact_mod_cast hturn.ne'
  · simpa only [rj_real_det] using hs

private theorem hb_region_endpoint_support {v w : Lattice} (P : Region v w)
    (i : Fin P.boundedCount) :
    ∀ x ∈ P.carrier, 0 ≤ realDet (embed (P.boundedDirection i)) (x-embed (P.vertex i.succ)) := by
  intro x hx
  have hs := P.bounded_support i x hx
  obtain ⟨k,hk,he⟩ := P.bounded_length i
  have heR : embed (P.vertex i.succ)-embed (P.vertex i.castSucc) =
      (k:ℝ)•embed (P.boundedDirection i) := by
    rw [← embed_sub,he]
    ext <;> simp [embed]
  have hzero : realDet (embed (P.boundedDirection i))
      (embed (P.vertex i.succ)-embed (P.vertex i.castSucc))=0 := by
    rw [heR,rj_real_det_smul,rj_real_det]
    have hd : det (P.boundedDirection i) (P.boundedDirection i)=0 := by dsimp [det];ring
    rw [hd];simp
  rw [rj_real_det_sub] at hs hzero ⊢
  linarith

private theorem hb_region_vertex_supports {v w : Lattice} (P : Region v w)
    (j : Fin (P.boundedCount+1)) :
    ∃ u d : Lattice, 0 < det u d ∧
      (∀ x ∈ P.carrier, 0 ≤ realDet (embed u) (x-embed (P.vertex j))) ∧
      (∀ x ∈ P.carrier, 0 ≤ realDet (embed d) (x-embed (P.vertex j))) := by
  by_cases hj0 : j.val=0
  · have hj : j=⟨0,Nat.zero_lt_succ _⟩ := Fin.ext hj0
    subst j
    by_cases hN : P.boundedCount=0
    · refine ⟨v,w,P.turn_positive,P.first_support,?_⟩
      have he : (⟨P.boundedCount,Nat.lt_succ_self _⟩ : Fin (P.boundedCount+1))=
          ⟨0,Nat.zero_lt_succ _⟩ := Fin.ext hN
      simpa only [he] using P.second_support
    · let i : Fin P.boundedCount := ⟨0,Nat.pos_of_ne_zero hN⟩
      exact ⟨v,P.boundedDirection i,P.first_turn i rfl,P.first_support,P.bounded_support i⟩
  · let i : Fin P.boundedCount := ⟨j.val-1,by omega⟩
    have hij : i.succ=j := Fin.ext (by dsimp [i];omega)
    have hiS : ∀ x ∈ P.carrier,
        0 ≤ realDet (embed (P.boundedDirection i)) (x-embed (P.vertex j)) := by
      simpa only [hij] using hb_region_endpoint_support P i
    by_cases hjN : j.val=P.boundedCount
    · refine ⟨P.boundedDirection i,w,P.second_turn i (by dsimp [i];omega),hiS,?_⟩
      have he : j=⟨P.boundedCount,Nat.lt_succ_self _⟩ := Fin.ext hjN
      simpa only [he] using P.second_support
    · let k : Fin P.boundedCount := ⟨j.val,by omega⟩
      have hkj : k.castSucc=j := Fin.ext rfl
      refine ⟨P.boundedDirection i,P.boundedDirection k,
        P.bounded_turn i k (by dsimp [i,k];omega),hiS,?_⟩
      simpa only [hkj] using P.bounded_support k

private theorem hb_region_vertices_extreme {v w : Lattice} (P : Region v w)
    (j : Fin (P.boundedCount+1)) : embed (P.vertex j) ∈ P.carrier.extremePoints ℝ := by
  obtain ⟨u,d,hud,hu,hd⟩ := hb_region_vertex_supports P j
  apply hb_extreme_of_lex_support _ _ (embed u) (embed d) (rj_vertex_mem P j)
  · rw [rj_real_det];exact_mod_cast hud.ne'
  · intro x hx
    have hu' := hu x hx
    have hd' := hd x hx
    rw [rj_real_det_sub] at hu' hd'
    exact ⟨sub_nonneg.mp hu',fun _ => sub_nonneg.mp hd'⟩

private theorem hb_region_extreme_points {v w : Lattice} (P : Region v w) :
    P.carrier.extremePoints ℝ = Set.range (fun j => embed (P.vertex j)) := by
  let V : Finset Lattice := Finset.univ.image P.vertex
  have hpoints : embed '' (V:Set Lattice)=Set.range (fun j => embed (P.vertex j)) := by
    ext x
    simp [V]
  have hH : windowHull V=regionVertexHull P := by
    unfold windowHull regionVertexHull
    rw [hpoints]
  have hcarrier : P.carrier=finiteRayHull V (-v) w := by
    rw [(region_halfplane_representation P).2.1]
    exact congrArg (fun H => realMinkowski H (twoRayCone (-v) w)) hH.symm
  apply Set.Subset.antisymm
  · intro x hx
    rw [hcarrier] at hx
    have hm := hb_extreme_subset_anchors V (-v) w hx
    rwa [hpoints] at hm
  · rintro x ⟨j,rfl⟩
    exact hb_region_vertices_extreme P j

private theorem rj_join_finish {v w : Lattice} (P : Region v w) (n : ℕ)
    (G : Finset Lattice) (hEq : P.enlargement n = embed ⁻¹' finiteRayHull G (-v) w)
    (Q : Region v w) (hQ : Q.carrier=finiteRayHull G (-v) w) :
    Q.lattice=P.enlargement n ∧ det v Q.firstAnchor=det v P.firstAnchor ∧
      recessionCone Q.carrier=twoRayCone (-v) w := by
  have hlattice : Q.lattice=P.enlargement n := by
    rw [hEq,Region.lattice,hQ]
  exact ⟨hlattice,rj_first_height_equal P Q n hlattice,
    (region_halfplane_representation Q).2.2.1⟩

private theorem hb_hull_nonempty_anchors (G : Finset Lattice) (p q : Lattice)
    (hH : (finiteRayHull G p q).Nonempty) : G.Nonempty := by
  by_contra h
  have hG : G=∅ := Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨x,y,hy,z,hz,heq⟩ := hH
  simp [hG,windowHull] at hy

private theorem hb_boundary_finish (G : Finset Lattice) (v w : Lattice)
    (P : Region v w) (hP : P.carrier=finiteRayHull G (-v) w) :
    ∃ P : Region v w, P.carrier=finiteRayHull G (-v) w ∧
      P.carrier.extremePoints ℝ=Set.range (fun j => embed (P.vertex j)) :=
  ⟨P,hP,hb_region_extreme_points P⟩

private theorem hb_unit_segment_edge (B : Finset Lattice) (d g : Lattice) (t : ℤ)
    (hd : Primitive d) (ht : t≠0) (harea : (interior (windowHull B)).Nonempty)
    (hg : g ∈ B) (hgt : g+t•d ∈ B)
    (hs : ∀ x ∈ windowHull B, 0 ≤ realDet (embed d) (x-embed g)) :
    d ∈ edgeDirections B := by
  have hdot : ∀ z : Lattice, realDot (embed z) (normal d)=(det d z:ℝ) := by
    intro z;simp [realDot,embed,normal,det];ring
  have hsame : det d (g+t•d)=det d g := by dsimp [det];ring
  have hrow : ∀ z ∈ B, det d z=det d g → z ∈ supportRow B d := by
    intro z hz he
    refine Finset.mem_filter.mpr ⟨hz,?_⟩
    intro q hq
    rw [hdot,hdot,he]
    have h := hs (embed q) (window_mem_hull B hq)
    rw [rj_real_det_sub,rj_real_det,rj_real_det] at h
    exact sub_nonneg.mp h
  refine ⟨hd,harea,?_⟩
  apply Finset.one_lt_card.mpr
  refine ⟨g,hrow g hg rfl,g+t•d,hrow _ hgt hsame,?_⟩
  intro he
  have ht0 : t•d=0 := by linear_combination (norm := module) -he
  exact (smul_eq_zero.mp ht0).elim ht (primitive_ne_zero d hd)

private theorem hb_augmented_polygon (G : Finset Lattice) (hG : G.Nonempty)
    (v w : Lattice) (hv : Primitive v) (hw : Primitive w) (hturn : 0<det v w) :
    ∃ B : Finset Lattice, LatticeConvex B ∧ Nonempty (WindowBoundary B) ∧
      v ∈ edgeDirections B ∧ w ∈ edgeDirections B ∧
      (G:Set Lattice) ⊆ B ∧ finiteRayHull B (-v) w=finiteRayHull G (-v) w := by
  let T := G ∪ G.image (fun g => g-v) ∪ G.image (fun g => g+w)
  have hGT : G ⊆ T := by intro g hg;exact Finset.mem_union_left _ (Finset.mem_union_left _ hg)
  have hleft : ∀ g ∈ G, g-v ∈ T := by
    intro g hg;exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩))
  have hright : ∀ g ∈ G, g+w ∈ T := by
    intro g hg;exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)
  have hTH : windowHull T ⊆ finiteRayHull G (-v) w := by
    apply convexHull_min ?_ (rj_hull_convex G (-v) w)
    rintro _ ⟨z,hz,rfl⟩
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hg | hg
      · exact rj_hull_point G (-v) w z hg
      · obtain ⟨g,hgg,rfl⟩ := Finset.mem_image.mp hg
        rw [embed_sub]
        have hneg : embed (-v) = -embed v := by simp [embed]
        have hm := rj_hull_add_cone G (-v) w (embed g) (rj_hull_point G (-v) w g hgg)
          (embed (-v)) ⟨1,0,by norm_num,le_rfl,by simp⟩
        simpa [hneg,sub_eq_add_neg] using hm
    · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hz
      rw [embed_add]
      exact rj_hull_add_cone G (-v) w (embed g) (rj_hull_point G (-v) w g hg)
        (embed w) ⟨0,1,le_rfl,by norm_num,by simp⟩
  obtain ⟨g,hg⟩ := hG
  let D : ℝ := det v w
  have hD : 0<D := by dsimp [D];exact_mod_cast hturn
  let A : RealPlane → ℝ := fun x => realDet (embed w) (x-embed g)/D
  let Bc : RealPlane → ℝ := fun x => realDet (embed v) (x-embed g)/D
  let U : Set RealPlane := {x | 0<A x ∧ 0<Bc x ∧ A x+Bc x<1}
  have hA : Continuous A := by dsimp [A,realDet];fun_prop
  have hBc : Continuous Bc := by dsimp [Bc,realDet];fun_prop
  have hUopen : IsOpen U := (isOpen_lt continuous_const hA).inter
    ((isOpen_lt continuous_const hBc).inter (isOpen_lt (hA.add hBc) continuous_const))
  have hU : U ⊆ windowHull T := by
    intro x hx
    have hrep : x-embed g = -(A x)•embed v+Bc x•embed w := by
      have hbase : D•(x-embed g) = -(realDet (embed w) (x-embed g)•embed v)+
          realDet (embed v) (x-embed g)•embed w := by
        ext <;> simp [D,det,realDet,embed] <;> ring
      have h := congrArg (fun z : RealPlane => D⁻¹•z) hbase
      simpa only [smul_add,smul_smul,smul_neg,inv_mul_cancel₀ hD.ne',one_smul,
        ← div_eq_inv_mul,neg_smul] using h
    let weights : Fin 3 → ℝ := ![1-A x-Bc x,A x,Bc x]
    let pts : Fin 3 → RealPlane := ![embed g,embed (g-v),embed (g+w)]
    have hw : ∀ j : Fin 3, 0≤weights j := by
      intro j;fin_cases j <;> dsimp [weights]
      · linarith [hx.2.2]
      · exact hx.1.le
      · exact hx.2.1.le
    have hp : ∀ j : Fin 3, pts j ∈ windowHull T := by
      intro j;fin_cases j
      · exact window_mem_hull T (hGT hg)
      · exact window_mem_hull T (hleft g hg)
      · exact window_mem_hull T (hright g hg)
    have hm := (windowHull_convex T).sum_mem (t := Finset.univ) (w := weights) (z := pts)
      (fun j _ => hw j) (by simp [weights,Fin.sum_univ_succ]) (fun j _ => hp j)
    convert hm using 1
    simp [Fin.sum_univ_succ,weights,pts,embed_sub,embed_add]
    linear_combination (norm := module) hrep
  let x : RealPlane := embed g-(1/3:ℝ)•embed v+(1/3:ℝ)•embed w
  have hxA : A x=1/3 := by
    change realDet (embed w) (x-embed g)/D=1/3
    have hn : realDet (embed w) (x-embed g)=D/3 := by
      simp [x,D,realDet,det,embed]
      ring
    rw [hn]
    field_simp
  have hxB : Bc x=1/3 := by
    change realDet (embed v) (x-embed g)/D=1/3
    have hn : realDet (embed v) (x-embed g)=D/3 := by
      simp [x,D,realDet,det,embed]
      ring
    rw [hn]
    field_simp
  have hxU : x ∈ U := by change 0<A x ∧ 0<Bc x ∧ A x+Bc x<1;rw [hxA,hxB];norm_num
  have harea : (interior (windowHull T)).Nonempty :=
    ⟨x,interior_mono hU (by rwa [hUopen.interior_eq])⟩
  let B := convexLatticeWindow T
  have hBmem : ∀ z, z ∈ B ↔ embed z ∈ windowHull T := fun z =>
    (lattice_windowHull_finite T).mem_toFinset
  have hHull : windowHull B=windowHull T := by
    apply Set.Subset.antisymm
    · apply convexHull_min ?_ (windowHull_convex T)
      rintro _ ⟨z,hz,rfl⟩;exact (hBmem z).mp hz
    · apply convexHull_mono
      rintro _ ⟨z,hz,rfl⟩
      exact ⟨z,(hBmem z).mpr (window_mem_hull T hz),rfl⟩
  have hBconv : LatticeConvex B := by intro z;rw [hHull];exact (hBmem z).symm
  have hareaB := hHull.symm ▸ harea
  have hGB : G ⊆ B := by intro z hz;exact (hBmem z).mpr (window_mem_hull T (hGT hz))
  have hleftB : ∀ g ∈ G, g-v ∈ B := by
    intro g hg;exact (hBmem _).mpr (window_mem_hull T (hleft g hg))
  have hrightB : ∀ g ∈ G, g+w ∈ B := by
    intro g hg;exact (hBmem _).mpr (window_mem_hull T (hright g hg))
  have hBH : windowHull B ⊆ finiteRayHull G (-v) w := by rwa [hHull]
  obtain ⟨gv,hgv,hvs,heqv⟩ := hb_first_anchor_ray G ⟨g,hg⟩ v w hturn
  obtain ⟨gw,hgw,hws,heqw⟩ := hb_second_anchor_ray G ⟨g,hg⟩ v w hturn
  have hvB : v ∈ edgeDirections B := hb_unit_segment_edge B v gv (-1) hv (by norm_num)
    hareaB (hGB hgv) (by simpa [sub_eq_add_neg] using hleftB gv hgv) (fun x hx => hvs x (hBH hx))
  have hwB : w ∈ edgeDirections B := hb_unit_segment_edge B w gw 1 hw (by norm_num)
    hareaB (hGB hgw) (by simpa using hrightB gw hgw) (fun x hx => hws x (hBH hx))
  refine ⟨B,hBconv,finite_window_support_polygon B hBconv hareaB,hvB,hwB,hGB,?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,z,hz,rfl⟩
    rw [hHull] at hy
    exact rj_hull_add_cone G (-v) w y (hTH hy) z hz
  · rintro x ⟨y,hy,z,hz,rfl⟩
    refine ⟨y,?_,z,hz,rfl⟩
    rw [hHull]
    exact convexHull_mono (Set.image_mono hGT) hy

private theorem hb_normal_height (z d : Lattice) :
    realDot (embed z) (normal d)=(det d z:ℝ) := by
  simp [realDot,embed,normal,det];ring

private theorem hb_row_mem (S : Finset Lattice) (u a : Lattice) :
    a ∈ supportRow S u ↔ a ∈ S ∧ ∀ z ∈ S, det u a ≤ det u z := by
  simp only [supportRow,supportFace,Finset.mem_filter,hb_normal_height]
  constructor
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz

private theorem hb_support_det_nonneg {S : Finset Lattice} {u a z : Lattice}
    (ha : a ∈ supportRow S u) (hz : z ∈ S) : 0 ≤ det u (z-a) := by
  have hh := ((hb_row_mem S u a).mp ha).2 z hz
  have he : det u (z-a)=det u z-det u a := by simp [det]; ring
  rw [he]
  omega

private theorem hb_support_pair_forbids_middle {S : Finset Lattice} {u v w a : Lattice}
    (hu : a ∈ supportRow S u) (hv : a ∈ supportRow S v)
    (huv : 0 < det u v) (huw : 0 < det u w) (hwv : 0 < det w v) :
    w ∉ edgeDirections S := by
  intro hw
  have hz_eq : ∀ z ∈ supportRow S w, z=a := by
    intro z hz
    have hzS := ((hb_row_mem S w z).mp hz).1
    have hu0 := hb_support_det_nonneg hu hzS
    have hv0 := hb_support_det_nonneg hv hzS
    have hw0 : det w (z-a) ≤ 0 := by
      have hh := ((hb_row_mem S w z).mp hz).2 a ((hb_row_mem S u a).mp hu).1
      have he : det w (z-a)=det w z-det w a := by simp [det]; ring
      rw [he]
      omega
    have hid : det u v * det w (z-a) =
        det w v * det u (z-a)+det u w * det v (z-a) := by simp [det]; ring
    have huz : det u (z-a)=0 := by nlinarith [mul_nonneg huw.le hv0]
    have hvz : det v (z-a)=0 := by nlinarith [mul_nonneg hwv.le hu0]
    have hcoord1 : det u v * (z-a).1 =
        v.1 * det u (z-a)-u.1 * det v (z-a) := by simp [det]; ring
    have hcoord2 : det u v * (z-a).2 =
        v.2 * det u (z-a)-u.2 * det v (z-a) := by simp [det]; ring
    rw [huz,hvz,mul_zero,mul_zero,sub_self] at hcoord1 hcoord2
    have h1 := (mul_eq_zero.mp hcoord1).resolve_left huv.ne'
    have h2 := (mul_eq_zero.mp hcoord2).resolve_left huv.ne'
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  have hcard : (supportRow S w).card ≤ 1 := Finset.card_le_one.mpr
    (fun z hz q hq => (hz_eq z hz).trans (hz_eq q hq).symm)
  have hh := hw.2.2
  omega

private theorem hb_primitive_parallel_eq_or_neg (u v : Lattice)
    (hu : Primitive u) (hv : Primitive v) (hdet : det u v=0) : v=u ∨ v= -u := by
  have hz : det u 0=det u v := by simp [det] at hdet ⊢; exact hdet.symm
  obtain ⟨k,hk⟩ := (primitive_row_coordinates u hu).2.1 0 v |>.mp hz
  simp only [zero_add] at hk
  have hg : k.natAbs=1 := by
    have h := hv
    rw [hk] at h
    change Int.gcd (k*u.1) (k*u.2)=1 at h
    rw [Int.gcd_mul_left,show Int.gcd u.1 u.2=1 from hu,mul_one] at h
    exact h
  have hkpm : k=1 ∨ k= -1 := by omega
  rcases hkpm with h | h
  · left; simpa [h] using hk
  · right; simpa [h] using hk

private theorem hb_direction_next_positive {B : Finset Lattice}
    (W : WindowBoundary B) (j : ℤ) (w : Lattice) (hw : w ∈ edgeDirections B)
    (hprev : 0<det (W.direction j) w) (hne : w≠W.direction (j+1)) :
    0<det (W.direction (j+1)) w := by
  have hturn := W.turns j
  by_contra! hnon
  have hneg : det (W.direction (j+1)) w < 0 := by
    apply lt_of_le_of_ne hnon
    intro hzero
    rcases hb_primitive_parallel_eq_or_neg _ _ (W.primitive (j+1)) hw.1 hzero with he | he
    · exact hne he
    · rw [he] at hprev
      have hd : det (W.direction j) (-W.direction (j+1)) =
          -det (W.direction j) (W.direction (j+1)) := by dsimp [det];ring
      rw [hd] at hprev
      omega
  have hlast : 0<det w (W.direction (j+1)) := by
    have hd : det w (W.direction (j+1)) = -det (W.direction (j+1)) w := by dsimp [det];ring
    rw [hd];omega
  have hj := (W.support_segment j (W.vertex (j+1))).mpr (right_mem_segment _ _ _)
  have hj1 := (W.support_segment (j+1) (W.vertex (j+1))).mpr (left_mem_segment _ _ _)
  exact hb_support_pair_forbids_middle hj hj1 hturn hprev hlast hw

private theorem hb_positive_chain {B : Finset Lattice} (W : WindowBoundary B)
    (v w : Lattice) (hv : v ∈ edgeDirections B) (hw : w ∈ edgeDirections B)
    (hturn : 0<det v w) :
    ∃ i : ℤ, ∃ n : ℕ, 0<n ∧ W.direction i=v ∧ W.direction (i+n)=w ∧
      (∀ k : ℕ, k<n → 0<det (W.direction (i+k)) w) ∧
      (∀ k : ℕ, 0<k → k≤n → 0<det v (W.direction (i+k))) := by
  obtain ⟨iv,hiv⟩ := W.covers ▸ hv
  obtain ⟨iw,hiw⟩ := W.covers ▸ hw
  let i : ℤ := iv.val
  have hex : ∃ n : ℕ, 0<n ∧ W.direction (i+n)=w := by
    let n := iw.val+W.count-iv.val
    have hn : 0<n := by dsimp [n];omega
    have he : i+(n:ℤ)=(iw.val:ℤ)+W.count := by dsimp [i,n];omega
    exact ⟨n,hn,by rw [he,W.direction_periodic];exact hiw⟩
  let n := Nat.find hex
  have hn : 0<n := (Nat.find_spec hex).1
  have hnw : W.direction (i+n)=w := (Nat.find_spec hex).2
  have hbefore : ∀ k : ℕ, k<n → 0<det (W.direction (i+k)) w := by
    intro k
    induction k with
    | zero => intro hk;simpa [i,hiv] using hturn
    | succ k ih =>
      intro hk
      have hne : w≠W.direction (i+k+1) := by
        intro he
        apply Nat.find_min hex hk
        exact ⟨Nat.succ_pos _,by simpa [Nat.cast_add,add_assoc] using he.symm⟩
      have hh := hb_direction_next_positive W (i+k) w hw (ih (by omega)) hne
      simpa [Nat.cast_add,add_assoc] using hh
  have hvdirs : ∀ k : ℕ, 0<k → k≤n → 0<det v (W.direction (i+k)) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk hkn
      by_cases hk0 : k=0
      · subst k
        simpa [i,hiv] using W.turns i
      have hvprev := ih (by omega) (by omega)
      have hprev := hbefore k (by omega)
      have hnext : 0≤det (W.direction (i+(k+1:ℕ))) w := by
        by_cases he : k+1=n
        · rw [he,hnw];simp [det,mul_comm]
        · exact (hbefore (k+1) (by omega)).le
      have hadj : 0<det (W.direction (i+k)) (W.direction (i+(k+1:ℕ))) := by
        simpa [Nat.cast_add,add_assoc] using W.turns (i+k)
      have halg : det v w * det (W.direction (i+k)) (W.direction (i+(k+1:ℕ))) =
          det v (W.direction (i+(k+1:ℕ))) * det (W.direction (i+k)) w -
          det v (W.direction (i+k)) * det (W.direction (i+(k+1:ℕ))) w := by
        dsimp [det];ring
      nlinarith [mul_pos hturn hadj,mul_nonneg hvprev.le hnext]
  exact ⟨i,n,hn,hiv,hnw,hbefore,hvdirs⟩

private theorem hb_height_bracket (n : ℕ) (f : Fin (n+1) → ℝ) (r : ℝ)
    (hn : 0<n) (hlo : f 0≤r) (hhi : r≤f (Fin.last n)) :
    ∃ j : Fin n, f j.castSucc≤r ∧ r≤f j.succ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hr : r≤f ⟨1,by omega⟩
    · exact ⟨0,hlo,hr⟩
    · by_cases hn0 : n=0
      · subst n;exact False.elim (hr hhi)
      obtain ⟨j,hj⟩ := ih (fun k => f k.succ) (by omega) (le_of_lt (lt_of_not_ge hr)) hhi
      exact ⟨j.succ,hj⟩

private theorem hb_chain_cover (v w : Lattice) (hturn : 0<det v w)
    (n : ℕ) (a : Fin (n+1) → Lattice) (d : Fin n → Lattice)
    (hlen : ∀ j : Fin n, ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j)
    (hv : ∀ j, 0<det v (d j))
    (x : RealPlane)
    (hfirst : 0≤realDet (embed v) (x-embed (a 0)))
    (hlast : 0≤realDet (embed w) (x-embed (a (Fin.last n))))
    (hsupport : ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc))) :
    x ∈ realMinkowski (convexHull ℝ (Set.range (fun j => embed (a j)))) (twoRayCone (-v) w) := by
  by_cases hhigh : realDet (embed v) (embed (a (Fin.last n)))≤realDet (embed v) x
  · refine ⟨embed (a (Fin.last n)),subset_convexHull ℝ _ ⟨Fin.last n,rfl⟩,
      x-embed (a (Fin.last n)),?_,by abel⟩
    rw [hb_cone_halfplanes v w hturn]
    refine ⟨?_,hlast⟩
    rw [rj_real_det_sub]
    exact sub_nonneg.mpr hhigh
  · have hn : 0<n := by
      by_contra! hn
      have hn0 : n=0 := Nat.eq_zero_of_le_zero hn
      have he : (Fin.last n : Fin (n+1))=0 := Fin.ext hn0
      rw [he] at hhigh
      rw [rj_real_det_sub] at hfirst
      exact hhigh (sub_nonneg.mp hfirst)
    obtain ⟨j,hlo,hhi⟩ := hb_height_bracket n (fun j => realDet (embed v) (embed (a j)))
      (realDet (embed v) x) hn (by rw [rj_real_det_sub] at hfirst;exact sub_nonneg.mp hfirst) (le_of_lt (lt_of_not_ge hhigh))
    obtain ⟨k,hk,hedge⟩ := hlen j
    have hedgeR : embed (a j.succ)-embed (a j.castSucc)=(k:ℝ)•embed (d j) := by
      rw [← embed_sub,hedge];ext <;> simp [embed]
    let D : ℝ := realDet (embed v) (embed (a j.succ)-embed (a j.castSucc))
    have hD : 0<D := by
      dsimp [D]
      rw [hedgeR,rj_real_det_smul,rj_real_det]
      exact mul_pos (by exact_mod_cast (show 0<k by omega)) (by exact_mod_cast hv j)
    let t : ℝ := realDet (embed v) (x-embed (a j.castSucc))/D
    have ht0 : 0≤t := by
      apply div_nonneg ?_ hD.le
      rw [rj_real_det_sub];exact sub_nonneg.mpr hlo
    have ht1 : t≤1 := by
      apply (div_le_one hD).mpr
      dsimp [D]
      rw [rj_real_det_sub,rj_real_det_sub]
      linarith
    let y := (1-t)•embed (a j.castSucc)+t•embed (a j.succ)
    have hy : y ∈ convexHull ℝ (Set.range (fun j => embed (a j))) :=
      (convex_convexHull ℝ (Set.range (fun j => embed (a j))))
        (subset_convexHull ℝ (Set.range (fun j => embed (a j))) ⟨j.castSucc,rfl⟩)
        (subset_convexHull ℝ (Set.range (fun j => embed (a j))) ⟨j.succ,rfl⟩) (sub_nonneg.mpr ht1) ht0 (by ring)
    have hzero : realDet (embed v) (x-y)=0 := by
      have he : realDet (embed v) (x-y)=
          realDet (embed v) (x-embed (a j.castSucc))-t*D := by dsimp [y,D,realDet];ring
      rw [he];dsimp [t];rw [div_mul_cancel₀ _ hD.ne'];ring
    have hs : 0≤realDet (embed (d j)) (x-y) := by
      have he : realDet (embed (d j)) (x-y)=realDet (embed (d j)) (x-embed (a j.castSucc)) := by
        have hz : realDet (embed (d j)) (embed (a j.succ)-embed (a j.castSucc))=0 := by
          rw [hedgeR,rj_real_det_smul,rj_real_det]
          have hd0 : det (d j) (d j)=0 := by dsimp [det];ring
          rw [hd0];simp
        have heq : realDet (embed (d j)) (x-y)=
            realDet (embed (d j)) (x-embed (a j.castSucc))-
            t*realDet (embed (d j)) (embed (a j.succ)-embed (a j.castSucc)) := by
          dsimp [y,realDet];ring
        rw [heq,hz,mul_zero,sub_zero]
      rw [he];exact hsupport j
    have hDw : (0:ℝ)<det v w := by exact_mod_cast hturn
    have hdv : (0:ℝ)<det v (d j) := by exact_mod_cast hv j
    have hid : (det v w:ℝ)*realDet (embed (d j)) (x-y)=
        (det v (d j):ℝ)*realDet (embed w) (x-y)-
        (det w (d j):ℝ)*realDet (embed v) (x-y) := by
      simp [det,embed,realDet];ring
    have hwxy : 0≤realDet (embed w) (x-y) := by
      rw [hzero,mul_zero,sub_zero] at hid
      nlinarith [mul_nonneg hDw.le hs]
    refine ⟨y,hy,x-y,?_,by abel⟩
    rw [hb_cone_halfplanes v w hturn]
    exact ⟨hzero.ge,hwxy⟩

private theorem hb_parallel_coeff (u d z : RealPlane) (hD : realDet u d≠0)
    (hz : realDet d z=0) : z=(realDet u z/realDet u d)•d := by
  have hb : realDet u d • z= -(realDet d z • u)+realDet u z • d := by
    ext <;> dsimp [realDet] <;> ring
  rw [hz,zero_smul,neg_zero,zero_add] at hb
  have h := congrArg (fun x : RealPlane => (realDet u d)⁻¹•x) hb
  simpa only [smul_smul,inv_mul_cancel₀ hD,one_smul,← div_eq_inv_mul] using h

private theorem hb_segment_face (a u d e x : RealPlane) (k : ℝ)
    (hk : 0<k) (hu : 0<realDet u d) (he : 0<realDet d e)
    (hlo : 0≤realDet u (x-a)) (hhi : 0≤realDet e (x-(a+k•d)))
    (hz : realDet d (x-a)=0) : x ∈ segment ℝ a (a+k•d) := by
  let t := realDet u (x-a)/realDet u d
  have hrep : x-a=t•d := hb_parallel_coeff u d (x-a) hu.ne' hz
  have ht0 : 0≤t := div_nonneg hlo hu.le
  have hhi' : 0≤(k-t)*realDet d e := by
    have hid : realDet e (x-(a+k•d))=(k-t)*realDet d e := by
      have hx : x-(a+k•d)=(t-k)•d := by linear_combination (norm := module) hrep
      rw [hx,rj_real_det_smul];dsimp [realDet];ring
    rwa [hid] at hhi
  have htk : t≤k := by nlinarith
  refine ⟨1-t/k,t/k,sub_nonneg.mpr ((div_le_one hk).mpr htk),div_nonneg ht0 hk.le,
    by ring,?_⟩
  have heq : (1-t/k)•a+(t/k)•(a+k•d)=a+t•d := by
    calc
      _ = ((1-t/k)+t/k)•a+(t/k*k)•d := by module
      _ = a+t•d := by rw [div_mul_cancel₀ _ hk.ne'];module
  rw [heq]
  linear_combination (norm := module) -hrep

private theorem hb_first_ray_face (a v d x : RealPlane)
    (hvd : 0<realDet v d) (hd : 0≤realDet d (x-a))
    (hz : realDet v (x-a)=0) : ∃t : ℝ, 0≤t ∧ x=a-t•v := by
  have hdv : realDet d v = -realDet v d := by dsimp [realDet];ring
  have hD : realDet d v≠0 := by rw [hdv];exact neg_ne_zero.mpr hvd.ne'
  have hrep := hb_parallel_coeff d v (x-a) hD hz
  have ht : realDet d (x-a)/realDet d v≤0 :=
    div_nonpos_of_nonneg_of_nonpos hd (by rw [hdv];linarith)
  refine ⟨-(realDet d (x-a)/realDet d v),neg_nonneg.mpr ht,?_⟩
  linear_combination (norm := module) hrep

private theorem hb_last_ray_face (a d w x : RealPlane)
    (hdw : 0<realDet d w) (hd : 0≤realDet d (x-a))
    (hz : realDet w (x-a)=0) : ∃t : ℝ, 0≤t ∧ x=a+t•w := by
  have hrep := hb_parallel_coeff d w (x-a) hdw.ne' hz
  exact ⟨realDet d (x-a)/realDet d w,div_nonneg hd hdw.le,
    by linear_combination (norm := module) hrep⟩

private theorem hb_support_zero_not_interior (S : Set RealPlane) (u a x : RealPlane)
    (hu : u ≠ 0) (hsupp : ∀ y ∈ S, 0 ≤ realDet u (y-a))
    (hx : realDet u (x-a)=0) : x ∉ interior S := by
  let f : RealPlane →L[ℝ] ℝ :=
    u.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - u.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hf : ∀ y, f y = realDet u y := by intro y; rfl
  have hsurj : Function.Surjective f := by
    intro t
    by_cases h1 : u.1=0
    · have h2 : u.2 ≠ 0 := by
        intro h2
        exact hu (Prod.ext h1 h2)
      refine ⟨(-t/u.2,0),?_⟩
      rw [hf]
      simp [realDet,h1,h2,mul_div_cancel₀]
    · refine ⟨(0,t/u.1),?_⟩
      rw [hf]
      simp [realDet,h1,mul_div_cancel₀]
  have ho : IsOpenMap (fun y => realDet u (y-a)) := by
    exact (f.isOpenMap hsurj).comp (Homeomorph.subRight a).isOpenMap
  intro hxi
  have hhalf : S ⊆ (fun y => realDet u (y-a)) ⁻¹' Set.Ici 0 := hsupp
  have hh := ho.interior_preimage_subset_preimage_interior (interior_mono hhalf hxi)
  simp [hx] at hh

private theorem hb_chain_endpoint_support (n : ℕ) (a : Fin (n+1) → Lattice)
    (d : Fin n → Lattice) (j : Fin n)
    (hlen : ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j) (x : RealPlane)
    (hs : 0≤realDet (embed (d j)) (x-embed (a j.castSucc))) :
    0≤realDet (embed (d j)) (x-embed (a j.succ)) := by
  obtain ⟨k,hk,he⟩ := hlen
  have heR : embed (a j.succ)-embed (a j.castSucc)=(k:ℝ)•embed (d j) := by
    rw [← embed_sub,he];ext <;> simp [embed]
  have hz : realDet (embed (d j)) (embed (a j.succ)-embed (a j.castSucc))=0 := by
    rw [heR,rj_real_det_smul,rj_real_det]
    have hd : det (d j) (d j)=0 := by dsimp [det];ring
    rw [hd];simp
  rw [rj_real_det_sub] at hs hz ⊢
  linarith

private theorem hb_chain_adjacent_support (v w : Lattice)
    (n : ℕ) (a : Fin (n+1) → Lattice) (d : Fin n → Lattice)
    (hlen : ∀ j : Fin n, ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j)
    (hfirst : ∀ j : Fin n, j.val=0 → 0<det v (d j))
    (hturn : ∀ j k : Fin n, k.val=j.val+1 → 0<det (d j) (d k))
    (hlast : ∀ j : Fin n, j.val+1=n → 0<det (d j) w)
    (x : RealPlane) (hv : 0≤realDet (embed v) (x-embed (a 0)))
    (hw : 0≤realDet (embed w) (x-embed (a (Fin.last n))))
    (hs : ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc))) (j : Fin n) :
    ∃ u e : Lattice, 0<det u (d j) ∧ 0<det (d j) e ∧
      0≤realDet (embed u) (x-embed (a j.castSucc)) ∧
      0≤realDet (embed e) (x-embed (a j.succ)) := by
  have hlo : ∃ u : Lattice, 0<det u (d j) ∧
      0≤realDet (embed u) (x-embed (a j.castSucc)) := by
    by_cases hj0 : j.val=0
    · refine ⟨v,hfirst j hj0,?_⟩
      have he : j.castSucc=0 := Fin.ext hj0
      simpa only [he] using hv
    · let k : Fin n := ⟨j.val-1,by omega⟩
      have he : k.succ=j.castSucc := Fin.ext (by dsimp [k];omega)
      refine ⟨d k,hturn k j (by dsimp [k];omega),?_⟩
      simpa only [he] using hb_chain_endpoint_support n a d k (hlen k) x (hs k)
  have hhi : ∃ e : Lattice, 0<det (d j) e ∧
      0≤realDet (embed e) (x-embed (a j.succ)) := by
    by_cases hjN : j.val+1=n
    · refine ⟨w,hlast j hjN,?_⟩
      have he : j.succ=Fin.last n := Fin.ext hjN
      simpa only [he] using hw
    · let k : Fin n := ⟨j.val+1,by omega⟩
      have he : k.castSucc=j.succ := Fin.ext rfl
      exact ⟨d k,hturn j k rfl,by simpa only [he] using hs k⟩
  obtain ⟨u,hu,hux⟩ := hlo
  obtain ⟨e,he,hex⟩ := hhi
  exact ⟨u,e,hu,he,hux,hex⟩

private theorem hb_active_chain_face (v w : Lattice) (hvw : 0<det v w)
    (n : ℕ) (a : Fin (n+1) → Lattice) (d : Fin n → Lattice)
    (hlen : ∀ j : Fin n, ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j)
    (hfirst : ∀ j : Fin n, j.val=0 → 0<det v (d j))
    (hturn : ∀ j k : Fin n, k.val=j.val+1 → 0<det (d j) (d k))
    (hlast : ∀ j : Fin n, j.val+1=n → 0<det (d j) w)
    (x : RealPlane) (hv : 0≤realDet (embed v) (x-embed (a 0)))
    (hw : 0≤realDet (embed w) (x-embed (a (Fin.last n))))
    (hs : ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc)))
    (hactive : realDet (embed v) (x-embed (a 0))=0 ∨
      realDet (embed w) (x-embed (a (Fin.last n)))=0 ∨
      ∃ j, realDet (embed (d j)) (x-embed (a j.castSucc))=0) :
    (∃ t : ℝ, 0≤t ∧ x=embed (a 0)-t•embed v) ∨
      (∃ t : ℝ, 0≤t ∧ x=embed (a (Fin.last n))+t•embed w) ∨
      ∃ j : Fin n, x ∈ segment ℝ (embed (a j.castSucc)) (embed (a j.succ)) := by
  rcases hactive with hz | hz | ⟨j,hz⟩
  · left
    by_cases hn : n=0
    · have he : (Fin.last n : Fin (n+1))=0 := Fin.ext hn
      rw [he] at hw
      exact hb_first_ray_face _ _ _ _ (by rw [rj_real_det];exact_mod_cast hvw) hw hz
    · let j : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
      exact hb_first_ray_face _ _ _ _ (by rw [rj_real_det];exact_mod_cast hfirst j rfl) (hs j) hz
  · right;left
    by_cases hn : n=0
    · have he : (Fin.last n : Fin (n+1))=0 := Fin.ext hn
      rw [he] at hz ⊢
      exact hb_last_ray_face _ _ _ _ (by rw [rj_real_det];exact_mod_cast hvw) hv hz
    · let j : Fin n := ⟨n-1,by omega⟩
      have he : j.succ=Fin.last n := Fin.ext (by dsimp [j];omega)
      have hj := hb_chain_endpoint_support n a d j (hlen j) x (hs j)
      rw [he] at hj
      exact hb_last_ray_face _ _ _ _
        (by rw [rj_real_det];exact_mod_cast hlast j (by dsimp [j];omega)) hj hz
  · right;right
    obtain ⟨u,e,hu,he,hux,hex⟩ := hb_chain_adjacent_support v w n a d hlen hfirst hturn hlast x hv hw hs j
    obtain ⟨k,hk,hkeq⟩ := hlen j
    have heq : embed (a j.succ)=embed (a j.castSucc)+(k:ℝ)•embed (d j) := by
      have heR := congrArg embed hkeq
      rw [embed_sub] at heR
      have hem : embed (k•d j)=(k:ℝ)•embed (d j) := by ext <;> simp [embed]
      rw [hem] at heR
      linear_combination (norm := module) heR
    refine ⟨j,?_⟩
    rw [heq] at hex ⊢
    exact hb_segment_face _ _ _ _ _ _ (by exact_mod_cast (show 0<k by omega))
      (by rw [rj_real_det];exact_mod_cast hu) (by rw [rj_real_det];exact_mod_cast he) hux hex hz

private theorem hb_region_from_chain (v w : Lattice) (hv : Primitive v) (hw : Primitive w)
    (hvw : 0<det v w) (C : Set RealPlane) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (harea : (interior C).Nonempty) (n : ℕ) (a : Fin (n+1) → Lattice) (d : Fin n → Lattice)
    (hprimitive : ∀ j, Primitive (d j))
    (hlen : ∀ j : Fin n, ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j)
    (hfirst : ∀ j : Fin n, j.val=0 → 0<det v (d j))
    (hturn : ∀ j k : Fin n, k.val=j.val+1 → 0<det (d j) (d k))
    (hlast : ∀ j : Fin n, j.val+1=n → 0<det (d j) w)
    (hvertices : ∀ j, embed (a j) ∈ C)
    (hcone : ∀ x ∈ C, ∀ u ∈ twoRayCone (-v) w, x+u ∈ C)
    (hC : C={x | 0≤realDet (embed v) (x-embed (a 0)) ∧
      0≤realDet (embed w) (x-embed (a (Fin.last n))) ∧
      ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc))}) :
    ∃ P : Region v w, P.carrier=C := by
  have hs : ∀ x ∈ C, 0≤realDet (embed v) (x-embed (a 0)) ∧
      0≤realDet (embed w) (x-embed (a (Fin.last n))) ∧
      ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc)) := by rw [hC];exact fun _ h => h
  have hne : ∀ u : Lattice, Primitive u → embed u≠0 := by
    intro u hu he
    apply primitive_ne_zero u hu
    have he1 : (u.1:ℝ)=0 := congrArg Prod.fst he
    have he2 : (u.2:ℝ)=0 := congrArg Prod.snd he
    apply Prod.ext <;> change _=0
    · exact_mod_cast he1
    · exact_mod_cast he2
  have hfront : frontier C=
      {x | ∃t : ℝ, 0≤t ∧ x=embed (a 0)-t•embed v} ∪
      {x | ∃t : ℝ, 0≤t ∧ x=embed (a (Fin.last n))+t•embed w} ∪
      {x | ∃j : Fin n, x ∈ segment ℝ (embed (a j.castSucc)) (embed (a j.succ))} := by
    rw [hclosed.frontier_eq]
    ext x
    constructor
    · rintro ⟨hx,hni⟩
      have hsx := hs x hx
      have ha : realDet (embed v) (x-embed (a 0))=0 ∨
          realDet (embed w) (x-embed (a (Fin.last n)))=0 ∨
          ∃ j, realDet (embed (d j)) (x-embed (a j.castSucc))=0 := by
        by_contra! hno
        let U : Set RealPlane := {y | 0<realDet (embed v) (y-embed (a 0))} ∩
          {y | 0<realDet (embed w) (y-embed (a (Fin.last n)))} ∩
          ⋂ j : Fin n, {y | 0<realDet (embed (d j)) (y-embed (a j.castSucc))}
        have hopen (u z : RealPlane) : IsOpen {y | 0<realDet u (y-z)} := by
          apply isOpen_lt continuous_const
          dsimp [realDet];fun_prop
        have hUopen : IsOpen U := ((hopen _ _).inter (hopen _ _)).inter
          (isOpen_iInter_of_finite (fun j => hopen _ _))
        have hxU : x ∈ U := ⟨⟨lt_of_le_of_ne hsx.1 (Ne.symm hno.1),
          lt_of_le_of_ne hsx.2.1 (Ne.symm hno.2.1)⟩,
          Set.mem_iInter.mpr (fun j => lt_of_le_of_ne (hsx.2.2 j) (Ne.symm (hno.2.2 j)))⟩
        have hUC : U ⊆ C := by
          intro y hy
          rw [hC]
          exact ⟨hy.1.1.le,hy.1.2.le,fun j => (Set.mem_iInter.mp hy.2 j).le⟩
        exact hni (interior_mono hUC (by rwa [hUopen.interior_eq]))
      have hh := hb_active_chain_face v w hvw n a d hlen hfirst hturn hlast x hsx.1 hsx.2.1 hsx.2.2 ha
      rcases hh with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((hx | hx) | hx)
      · obtain ⟨t,ht,rfl⟩ := hx
        have hc : -t•embed v ∈ twoRayCone (-v) w :=
          ⟨t,0,ht,le_rfl,by simp [embed]⟩
        have hm : embed (a 0)-t•embed v ∈ C := by
          simpa [sub_eq_add_neg,neg_smul] using hcone _ (hvertices 0) _ hc
        refine ⟨hm,hb_support_zero_not_interior C (embed v) (embed (a 0)) _
          (hne v hv) (fun y hy => (hs y hy).1) ?_⟩
        dsimp [realDet];ring
      · obtain ⟨t,ht,rfl⟩ := hx
        have hc : t•embed w ∈ twoRayCone (-v) w := ⟨0,t,le_rfl,ht,by simp⟩
        have hm := hcone _ (hvertices (Fin.last n)) _ hc
        refine ⟨hm,hb_support_zero_not_interior C (embed w) (embed (a (Fin.last n))) _
          (hne w hw) (fun y hy => (hs y hy).2.1) ?_⟩
        dsimp [realDet];ring
      · obtain ⟨j,hj⟩ := hx
        have hm := hconvex.segment_subset (hvertices j.castSucc) (hvertices j.succ) hj
        refine ⟨hm,hb_support_zero_not_interior C (embed (d j)) (embed (a j.castSucc)) _
          (hne (d j) (hprimitive j)) (fun y hy => (hs y hy).2.2 j) ?_⟩
        obtain ⟨r,t,hr,ht,hrt,rfl⟩ := hj
        obtain ⟨k,hk,hedge⟩ := hlen j
        have heR : embed (a j.succ)-embed (a j.castSucc)=(k:ℝ)•embed (d j) := by
          rw [← embed_sub,hedge];ext <;> simp [embed]
        have heq : r•embed (a j.castSucc)+t•embed (a j.succ)-embed (a j.castSucc)=
            t•(embed (a j.succ)-embed (a j.castSucc)) := by
          have h := congrArg (fun z : ℝ => z•embed (a j.castSucc)) hrt
          linear_combination (norm := module) h
        rw [heq,heR,rj_real_det_smul,rj_real_det_smul]
        dsimp [realDet];ring
  let P : Region v w := {
    carrier := C
    closed := hclosed
    convex := hconvex
    interior_nonempty := harea
    first_primitive := hv
    second_primitive := hw
    turn_positive := hvw
    boundedCount := n
    vertex := a
    boundedDirection := d
    bounded_primitive := hprimitive
    bounded_length := hlen
    first_turn := hfirst
    bounded_turn := hturn
    second_turn := hlast
    first_support := fun x hx => (hs x hx).1
    second_support := fun x hx => (hs x hx).2.1
    bounded_support := fun j x hx => (hs x hx).2.2 j
    boundary_eq := hfront }
  exact ⟨P,rfl⟩

private theorem hb_extend_support (B : Finset Lattice) (v w d g : Lattice)
    (hs : ∀ x ∈ windowHull B, 0≤realDet (embed d) (x-embed g))
    (hdv : 0≤det v d) (hdw : 0≤det d w) :
    ∀ x ∈ finiteRayHull B (-v) w, 0≤realDet (embed d) (x-embed g) := by
  rintro x ⟨y,hy,z,⟨a,b,ha,hb,rfl⟩,rfl⟩
  have he : y+(a•embed (-v)+b•embed w)-embed g =
      (y-embed g)+(a•embed (-v)+b•embed w) := by abel
  rw [he,rj_real_det_add,rj_real_det_add,rj_real_det_smul,rj_real_det_smul,
    rj_real_det,rj_real_det]
  have hdv' : det d (-v)=det v d := by dsimp [det];ring
  rw [hdv']
  exact add_nonneg (hs y hy) (add_nonneg
    (mul_nonneg ha (by exact_mod_cast hdv)) (mul_nonneg hb (by exact_mod_cast hdw)))

private theorem hb_window_region (B : Finset Lattice) (W : WindowBoundary B)
    (v w : Lattice) (hv : Primitive v) (hw : Primitive w) (hvw : 0<det v w)
    (hvB : v ∈ edgeDirections B) (hwB : w ∈ edgeDirections B)
    (harea : (interior (finiteRayHull B (-v) w)).Nonempty) :
    ∃ P : Region v w, P.carrier=finiteRayHull B (-v) w := by
  obtain ⟨i,N,hN,hiv,hiw,hbefore,hafter⟩ := hb_positive_chain W v w hvB hwB hvw
  let n := N-1
  have hn : n+1=N := by dsimp [n];omega
  let a : Fin (n+1) → Lattice := fun j => W.vertex (i+1+j.val)
  let d : Fin n → Lattice := fun j => W.direction (i+1+j.val)
  have ha0 : a 0=W.vertex (i+1) := by simp [a]
  have halast : a (Fin.last n)=W.vertex (i+N) := by
    dsimp [a];congr 1;exact_mod_cast (show i+1+(n:ℤ)=i+(N:ℤ) by omega)
  have hlen : ∀ j : Fin n, ∃ k : ℤ, 1≤k ∧ a j.succ-a j.castSucc=k•d j := by
    intro j
    refine ⟨W.length (i+1+j.val),by exact_mod_cast W.length_positive _,?_⟩
    simpa [a,d,add_assoc,add_left_comm,add_comm] using W.edge_eq (i+1+j.val)
  have hprim : ∀ j, Primitive (d j) := fun j => W.primitive _
  have hdv : ∀ j, 0<det v (d j) := by
    intro j
    have h := hafter (j.val+1) (by omega) (by omega)
    simpa [d,Nat.cast_add,add_assoc,add_left_comm,add_comm] using h
  have hdw : ∀ j, 0<det (d j) w := by
    intro j
    have h := hbefore (j.val+1) (by omega)
    simpa [d,Nat.cast_add,add_assoc,add_left_comm,add_comm] using h
  have ht : ∀ j k : Fin n, k.val=j.val+1 → 0<det (d j) (d k) := by
    intro j k he
    simpa [d,he,Nat.cast_add,add_assoc] using W.turns (i+1+j.val)
  have hfirst : ∀ x ∈ finiteRayHull B (-v) w,
      0≤realDet (embed v) (x-embed (a 0)) := by
    apply hb_extend_support B v w v (a 0) ?_ (by simp [det,mul_comm]) hvw.le
    intro x hx
    have hs := W.supports i x hx
    have he : realDet (embed v) (embed (W.vertex (i+1))-embed (W.vertex i))=0 := by
      have hedge := congrArg embed (W.edge_eq i)
      rw [embed_sub] at hedge
      rw [hiv] at hedge
      have hem : embed ((W.length i:ℤ)•v)=(W.length i:ℝ)•embed v := by ext <;> simp [embed]
      rw [hem] at hedge
      rw [hedge,rj_real_det_smul]
      dsimp [realDet];ring
    rw [hiv,rj_real_det_sub] at hs
    rw [rj_real_det_sub] at he
    rw [ha0,rj_real_det_sub]
    linarith
  have hlast : ∀ x ∈ finiteRayHull B (-v) w,
      0≤realDet (embed w) (x-embed (a (Fin.last n))) := by
    apply hb_extend_support B v w w (a (Fin.last n)) ?_ hvw.le (by simp [det,mul_comm])
    intro x hx
    simpa [halast,hiw] using W.supports (i+N) x hx
  have hs : ∀ j, ∀ x ∈ finiteRayHull B (-v) w,
      0≤realDet (embed (d j)) (x-embed (a j.castSucc)) := by
    intro j
    exact hb_extend_support B v w (d j) (a j.castSucc) (W.supports _) (hdv j).le (hdw j).le
  have hav : ∀ j, embed (a j) ∈ finiteRayHull B (-v) w := by
    intro j;exact rj_hull_point B (-v) w (a j) (W.vertex_mem _)
  have hcarrier : finiteRayHull B (-v) w={x | 0≤realDet (embed v) (x-embed (a 0)) ∧
      0≤realDet (embed w) (x-embed (a (Fin.last n))) ∧
      ∀ j, 0≤realDet (embed (d j)) (x-embed (a j.castSucc))} := by
    ext x
    constructor
    · intro hx;exact ⟨hfirst x hx,hlast x hx,fun j => hs j x hx⟩
    · rintro ⟨hvx,hwx,hsx⟩
      obtain ⟨y,hy,z,hz,rfl⟩ := hb_chain_cover v w hvw n a d hlen hdv x hvx hwx hsx
      have hsubset : convexHull ℝ (Set.range (fun j => embed (a j))) ⊆ finiteRayHull B (-v) w := by
        apply convexHull_min ?_ (rj_hull_convex B (-v) w)
        rintro _ ⟨j,rfl⟩;exact hav j
      exact rj_hull_add_cone B (-v) w y (hsubset hy) z hz
  exact hb_region_from_chain v w hv hw hvw _ (hb_hull_closed B v w hvw)
    (rj_hull_convex B (-v) w) harea n a d hprim hlen (fun j _ => hdv j) ht
    (fun j _ => hdw j) hav (rj_hull_add_cone B (-v) w) hcarrier

theorem finite_anchor_two_ray_boundary (G : Finset Lattice) (v w : Lattice)
    (hv : Primitive v) (hw : Primitive w) (hturn : 0 < det v w)
    (harea : (interior (finiteRayHull G (-v) w)).Nonempty)
    (hrecession : recessionCone (finiteRayHull G (-v) w) = twoRayCone (-v) w) :
    ∃ P : Region v w, P.carrier = finiteRayHull G (-v) w ∧
      (P.carrier).extremePoints ℝ = Set.range (fun j => embed (P.vertex j)) := by
  clear hrecession
  have hG := hb_hull_nonempty_anchors G (-v) w (harea.mono interior_subset)
  obtain ⟨B,hB,⟨W⟩,hvB,hwB,hGB,hH⟩ := hb_augmented_polygon G hG v w hv hw hturn
  have hareaB : (interior (finiteRayHull B (-v) w)).Nonempty := hH.symm ▸ harea
  obtain ⟨P,hP⟩ := hb_window_region B W v w hv hw hturn hvB hwB hareaB
  exact hb_boundary_finish G v w P (hP.trans hH)

theorem region_enlargement_geometry_join {v w : Lattice} (P : Region v w) (n : ℕ) :
    ∃ Q : Region v w, Q.lattice = P.enlargement n ∧
      det v Q.firstAnchor = det v P.firstAnchor ∧
      recessionCone Q.carrier = twoRayCone (-v) w := by
  obtain ⟨G,hG,hEq⟩ := (enlargement_integer_collar P n).2
  obtain ⟨Q,hQ,hvertices⟩ := finite_anchor_two_ray_boundary G v w P.first_primitive
    P.second_primitive P.turn_positive (rj_hull_area P n G hEq)
    (rj_collar_hull_recession P n G hEq)
  exact ⟨Q,rj_join_finish P n G hEq Q hQ⟩

end
end ConvexNivat.Colle
