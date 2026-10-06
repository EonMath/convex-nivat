import ConvexNivat.Colle.Shared.Definitions

namespace ConvexNivat.Colle
open Set Filter Topology
noncomputable section

private theorem closed_convex_ray_add (C : Set RealPlane) (hc : IsClosed C)
    (hv : Convex ℝ C) (p u x : RealPlane) (hx : x ∈ C)
    (hray : ∀ t : ℝ, 0 ≤ t → p + t • u ∈ C) (t : ℝ) (ht : 0 ≤ t) :
    x + t • u ∈ C := by
  let f : ℕ → RealPlane := fun n =>
    x + t • u + (1 / ((n : ℝ) + 1)) • (p - x)
  have hmem : ∀ n, f n ∈ C := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have ha : (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_one hden).mpr
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      linarith
    have h := hv hx (hray (((n : ℝ) + 1) * t) (mul_nonneg hden.le ht)) ha hb
      (by ring : 1 - 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) = 1)
    convert h using 1
    ext <;> simp only [f, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;>
      field_simp <;> ring
  have hlim : Tendsto f atTop (𝓝 (x + t • u)) := by
    have hzero := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (p - x)
    simpa [f] using tendsto_const_nhds.add hzero
  exact hc.mem_of_tendsto hlim (Eventually.of_forall hmem)

private theorem first_ray_mem {v w : Lattice} (P : Region v w) (t : ℝ)
    (ht : 0 ≤ t) : embed P.firstAnchor - t • embed v ∈ P.carrier := by
  apply P.closed.closure_eq ▸ (frontier_subset_closure (s := P.carrier) ?_)
  rw [P.boundary_eq]
  exact Or.inl (Or.inl ⟨t, ht, rfl⟩)

private theorem second_ray_mem {v w : Lattice} (P : Region v w) (t : ℝ)
    (ht : 0 ≤ t) : embed P.secondAnchor + t • embed w ∈ P.carrier := by
  apply P.closed.closure_eq ▸ (frontier_subset_closure (s := P.carrier) ?_)
  rw [P.boundary_eq]
  exact Or.inl (Or.inr ⟨t, ht, rfl⟩)

private theorem lattice_forward_first {v w : Lattice} (P : Region v w) (a : ℕ) :
    ForwardInvariant P.lattice ((-(a : ℤ)) • v) := by
  intro z hz
  have h := closed_convex_ray_add P.carrier P.closed P.convex
    (embed P.firstAnchor) (-embed v) (embed z) hz
    (fun t ht => by simpa [smul_neg, sub_eq_add_neg] using first_ray_mem P t ht)
    (a : ℝ) (Nat.cast_nonneg a)
  simpa [Region.lattice, embed, smul_eq_mul] using h

private theorem lattice_forward_second {v w : Lattice} (P : Region v w) (a : ℕ) :
    ForwardInvariant P.lattice ((a : ℤ) • w) := by
  intro z hz
  have h := closed_convex_ray_add P.carrier P.closed P.convex
    (embed P.secondAnchor) (embed w) (embed z) hz
    (second_ray_mem P) (a : ℝ) (Nat.cast_nonneg a)
  simpa [Region.lattice, embed, smul_eq_mul] using h

private theorem strict_support_mem {v w : Lattice} (P : Region v w) (x : RealPlane)
    (hxv : 0 < realDet (embed v) (x - embed P.firstAnchor))
    (hxw : 0 < realDet (embed w) (x - embed P.secondAnchor))
    (hxb : ∀ i : Fin P.boundedCount,
      0 < realDet (embed (P.boundedDirection i)) (x - embed (P.vertex i.castSucc))) :
    x ∈ P.carrier := by
  let U : Set RealPlane := {x |
    0 < realDet (embed v) (x - embed P.firstAnchor) ∧
    0 < realDet (embed w) (x - embed P.secondAnchor) ∧
    ∀ i : Fin P.boundedCount,
      0 < realDet (embed (P.boundedDirection i)) (x - embed (P.vertex i.castSucc))}
  have hcv : Convex ℝ U := by
    intro a ha b hb r s hr hs hrs
    rcases ha with ⟨hav, haw, hab⟩
    rcases hb with ⟨hbv, hbw, hbb⟩
    have hlin : ∀ u q : RealPlane,
        realDet u (r • a + s • b - q) =
          r * realDet u (a - q) + s * realDet u (b - q) := by
      intro u q
      dsimp [realDet]
      linear_combination -u.2 * q.1 * hrs + u.1 * q.2 * hrs
    have hpos : ∀ α β : ℝ, 0 < α → 0 < β → 0 < r * α + s * β := by
      intro α β hα hβ
      by_cases hzero : r = 0
      · have hs1 : s = 1 := by linarith
        simpa [hzero, hs1] using hβ
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hr (Ne.symm hzero)) hα)
          (mul_nonneg hs hβ.le)
    dsimp [U]
    simp only [hlin]
    exact ⟨hpos _ _ hav hbv, hpos _ _ haw hbw, fun i => hpos _ _ (hab i) (hbb i)⟩
  have hfront : Disjoint U (frontier P.carrier) := by
    apply Set.disjoint_left.mpr
    intro y hy hboundary
    rw [P.boundary_eq] at hboundary
    rcases hy with ⟨hyv, hyw, hyb⟩
    rcases hboundary with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨i, hi⟩
    · have heq : realDet (embed v)
          (embed P.firstAnchor - t • embed v - embed P.firstAnchor) = 0 := by
        dsimp [realDet]
        ring
      exact (ne_of_gt hyv) heq
    · have heq : realDet (embed w)
          (embed P.secondAnchor + t • embed w - embed P.secondAnchor) = 0 := by
        dsimp [realDet]
        ring
      exact (ne_of_gt hyw) heq
    · obtain ⟨r, s, hr, hs, hrs, rfl⟩ := hi
      obtain ⟨k, hk, heq⟩ := P.bounded_length i
      have heq' : embed (P.vertex i.succ) =
          embed (P.vertex i.castSucc) + (k : ℝ) • embed (P.boundedDirection i) := by
        have hh := sub_eq_iff_eq_add.mp heq
        simpa [embed, smul_eq_mul, add_comm] using congrArg embed hh
      have hdet : realDet (embed (P.boundedDirection i))
          (r • embed (P.vertex i.castSucc) + s • embed (P.vertex i.succ) -
            embed (P.vertex i.castSucc)) = 0 := by
        rw [heq']
        dsimp [realDet]
        linear_combination (-(embed (P.boundedDirection i)).2 *
          (embed (P.vertex i.castSucc)).1 + (embed (P.boundedDirection i)).1 *
          (embed (P.vertex i.castSucc)).2) * hrs
      exact (ne_of_gt (hyb i)) hdet
  have hcover : U ⊆ interior P.carrier ∪ interior P.carrierᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact Set.disjoint_left.mp hfront
  have hp : ∃ p ∈ U, p ∈ interior P.carrier := by
    obtain ⟨p, hp⟩ := P.interior_nonempty
    have hpos : ∀ u q : RealPlane, u ≠ 0 →
        (∀ y ∈ P.carrier, 0 ≤ realDet u (y - q)) → 0 < realDet u (p - q) := by
      intro u q hu hsupport
      have hge := hsupport p (interior_subset hp)
      by_contra h
      have heq : realDet u (p - q) = 0 := by linarith
      have hn : 0 < u.1 ^ 2 + u.2 ^ 2 := by
        have hu' : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
          by_contra hh
          push Not at hh
          exact hu (Prod.ext hh.1 hh.2)
        rcases hu' with hu' | hu' <;> nlinarith [sq_pos_of_ne_zero hu']
      let f : ℕ → RealPlane := fun n => p + (1 / ((n : ℝ) + 1)) • (u.2, -u.1)
      have hf : Tendsto f atTop (𝓝 p) := by
        have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (u.2, -u.1)
        simpa [f] using tendsto_const_nhds.add ht
      have hev := hf.eventually (isOpen_interior.mem_nhds hp)
      obtain ⟨n, htf⟩ := hev.exists
      have hnegative := hsupport (f n) (interior_subset htf)
      dsimp [f, realDet] at heq hnegative
      have hsmall : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hprod := mul_pos hsmall hn
      nlinarith
    have hne : ∀ d : Lattice, Primitive d → embed d ≠ 0 := by
      intro d hd hdz
      have hx : d.1 = 0 := by
        have hh : (d.1 : ℝ) = 0 := congrArg Prod.fst hdz
        exact_mod_cast hh
      have hy : d.2 = 0 := by
        have hh : (d.2 : ℝ) = 0 := congrArg Prod.snd hdz
        exact_mod_cast hh
      simpa [Primitive, hx, hy] using hd
    refine ⟨p, ?_, hp⟩
    exact ⟨hpos _ _ (hne v P.first_primitive) P.first_support,
      hpos _ _ (hne w P.second_primitive) P.second_support,
      fun i => hpos _ _ (hne _ (P.bounded_primitive i)) (P.bounded_support i)⟩
  obtain hinside | houtside := (hcv.isPreconnected).subset_or_subset
    isOpen_interior isOpen_interior
    (Set.disjoint_left.mpr (fun y hy hyc =>
      (show y ∉ P.carrier from interior_subset hyc)
        (show y ∈ P.carrier from interior_subset hy))) hcover
  · exact interior_subset (hinside ⟨hxv, hxw, hxb⟩)
  · obtain ⟨p, hpU, hpC⟩ := hp
    exact False.elim ((interior_subset (houtside hpU)) (interior_subset hpC))


private theorem vertex_mem_carrier {v w : Lattice} (P : Region v w)
    (j : Fin (P.boundedCount + 1)) : embed (P.vertex j) ∈ P.carrier := by
  apply P.closed.closure_eq ▸ (frontier_subset_closure (s := P.carrier) ?_)
  rw [P.boundary_eq]
  by_cases h : j.val < P.boundedCount
  · let i : Fin P.boundedCount := ⟨j.val, h⟩
    have heq : i.castSucc = j := Fin.ext rfl
    exact Or.inr ⟨i, heq ▸ left_mem_segment ℝ (embed (P.vertex i.castSucc))
      (embed (P.vertex i.succ))⟩
  · have heq : j = ⟨P.boundedCount, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
    exact Or.inl (Or.inr ⟨0, le_rfl, by simp [heq]⟩)

private theorem vertex_hull_subset {v w : Lattice} (P : Region v w) :
    regionVertexHull P ⊆ P.carrier := by
  apply convexHull_min ?_ P.convex
  rintro x ⟨j, rfl⟩
  exact vertex_mem_carrier P j

private theorem vertex_in_hull {v w : Lattice} (P : Region v w)
    (j : Fin (P.boundedCount + 1)) : embed (P.vertex j) ∈ regionVertexHull P :=
  subset_convexHull ℝ _ ⟨j, rfl⟩

private theorem cone_add_mem {v w : Lattice} (P : Region v w)
    {x d : RealPlane} (hx : x ∈ P.carrier) (hd : d ∈ twoRayCone (-v) w) :
    x + d ∈ P.carrier := by
  rcases hd with ⟨a, b, ha, hb, rfl⟩
  have hfirst := closed_convex_ray_add P.carrier P.closed P.convex
    (embed P.firstAnchor) (-embed v) x hx
    (fun t ht => by simpa [smul_neg, sub_eq_add_neg] using first_ray_mem P t ht) a ha
  have hsecond := closed_convex_ray_add P.carrier P.closed P.convex
    (embed P.secondAnchor) (embed w) (x + a • (-embed v)) hfirst
    (second_ray_mem P) b hb
  simpa [embed, add_assoc] using hsecond

private theorem frontier_decomp {v w : Lattice} (P : Region v w)
    {x : RealPlane} (hx : x ∈ frontier P.carrier) :
    x ∈ realMinkowski (regionVertexHull P) (twoRayCone (-v) w) := by
  rw [P.boundary_eq] at hx
  rcases hx with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨i, hi⟩
  · refine ⟨embed P.firstAnchor, vertex_in_hull P _, -t • embed v, ?_, ?_⟩
    · exact ⟨t, 0, ht, le_rfl, by simp [embed, neg_smul]⟩
    · change embed P.firstAnchor - t • embed v = embed P.firstAnchor + -t • embed v
      module
  · refine ⟨embed P.secondAnchor, vertex_in_hull P _, t • embed w, ?_, rfl⟩
    exact ⟨0, t, le_rfl, ht, by simp⟩
  · refine ⟨x, (convex_convexHull ℝ _).segment_subset
      (vertex_in_hull P i.castSucc) (vertex_in_hull P i.succ) hi, 0, ?_, by simp⟩
    exact ⟨0, 0, le_rfl, le_rfl, by simp⟩

private theorem segment_meets_frontier (C : Set RealPlane) {x y : RealPlane}
    (hx : x ∈ C) (hy : y ∉ C) :
    ∃ z ∈ segment ℝ x y, z ∈ frontier C := by
  by_contra h
  have hd : Disjoint (segment ℝ x y) (frontier C) := by
    apply Set.disjoint_left.mpr
    intro z hz hzf
    exact h ⟨z, hz, hzf⟩
  have hcover : segment ℝ x y ⊆ interior C ∪ interior Cᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact Set.disjoint_left.mp hd
  obtain hleft | hright := (convex_segment x y).isPreconnected.subset_or_subset
    isOpen_interior isOpen_interior
    (Set.disjoint_left.mpr (fun z hz hzc =>
      (show z ∉ C from interior_subset hzc) (show z ∈ C from interior_subset hz))) hcover
  · exact hy (interior_subset (hleft (right_mem_segment ℝ x y)))
  · exact interior_subset (hright (left_mem_segment ℝ x y)) hx

private theorem carrier_minkowski {v w : Lattice} (P : Region v w) :
    P.carrier = realMinkowski (regionVertexHull P) (twoRayCone (-v) w) := by
  apply Set.Subset.antisymm
  · intro x hx
    let D : ℝ := realDet (embed v) (embed w)
    have hD : 0 < D := by
      have h := P.turn_positive
      dsimp [D, realDet, embed]
      exact_mod_cast h
    let T : ℝ := realDet (embed v) (x - embed P.firstAnchor) / D + 1
    have hT : 0 ≤ T := by
      have hh : 0 ≤ realDet (embed v) (x - embed P.firstAnchor) := P.first_support x hx
      have := div_nonneg hh hD.le
      dsimp [T]
      linarith
    let d : RealPlane := -embed v + embed w
    have hout : x - T • d ∉ P.carrier := by
      intro hout
      have h : 0 ≤ realDet (embed v) (x - T • d - embed P.firstAnchor) := P.first_support _ hout
      have heq : realDet (embed v) (x - T • d - embed P.firstAnchor) = -D := by
        calc
          _ = realDet (embed v) (x - embed P.firstAnchor) - T * D := by
            dsimp [d, D, realDet]
            ring
          _ = -D := by dsimp [T]; field_simp [ne_of_gt hD]; ring
      rw [heq] at h
      linarith
    obtain ⟨z, hzseg, hzfront⟩ := segment_meets_frontier P.carrier hx hout
    obtain ⟨r, s, hr, hs, hrs, rfl⟩ := hzseg
    obtain ⟨a, ha, c, ⟨u, t, hu, ht, hc⟩, hz⟩ := frontier_decomp P hzfront
    refine ⟨a, ha, (u + s * T) • embed (-v) + (t + s * T) • embed w,
      ⟨u + s * T, t + s * T, add_nonneg hu (mul_nonneg hs hT),
        add_nonneg ht (mul_nonneg hs hT), rfl⟩, ?_⟩
    rw [hc] at hz
    have hembed : embed (-v) = -embed v := by simp [embed]
    rw [hembed] at hz ⊢
    dsimp [d] at hz
    have hcalc : r • x + s • (x - T • (-embed v + embed w)) =
        x - (s * T) • (-embed v + embed w) := by
      calc
        _ = (r + s) • x - (s * T) • (-embed v + embed w) := by module
        _ = _ := by rw [hrs]; simp
    rw [hcalc] at hz
    calc
      x = a + (u • (-embed v) + t • embed w) +
          (s * T) • (-embed v + embed w) := by rw [← hz]; module
      _ = _ := by module
  · rintro x ⟨y, hy, d, hd, rfl⟩
    exact cone_add_mem P (vertex_hull_subset P hy) hd

private theorem exists_strict_point {v w : Lattice} (P : Region v w) :
    ∃ p : RealPlane,
      0 < realDet (embed v) (p - embed P.firstAnchor) ∧
      0 < realDet (embed w) (p - embed P.secondAnchor) ∧
      ∀ i, 0 < realDet (embed (P.boundedDirection i)) (p - embed (P.vertex i.castSucc)) := by
  obtain ⟨p, hp⟩ := P.interior_nonempty
  have hpos : ∀ u q : RealPlane, u ≠ 0 →
      (∀ y ∈ P.carrier, 0 ≤ realDet u (y - q)) → 0 < realDet u (p - q) := by
    intro u q hu hsupport
    have hge := hsupport p (interior_subset hp)
    by_contra h
    have heq : realDet u (p - q) = 0 := by linarith
    have hn : 0 < u.1 ^ 2 + u.2 ^ 2 := by
      have hu' : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hu (Prod.ext hh.1 hh.2)
      rcases hu' with hu' | hu' <;> nlinarith [sq_pos_of_ne_zero hu']
    let f : ℕ → RealPlane := fun n => p + (1 / ((n : ℝ) + 1)) • (u.2, -u.1)
    have hf : Tendsto f atTop (𝓝 p) := by
      have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (u.2, -u.1)
      simpa [f] using tendsto_const_nhds.add ht
    have hev := hf.eventually (isOpen_interior.mem_nhds hp)
    obtain ⟨n, htf⟩ := hev.exists
    have hnegative := hsupport (f n) (interior_subset htf)
    dsimp [f, realDet] at heq hnegative
    have hsmall : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hprod := mul_pos hsmall hn
    nlinarith
  have hne : ∀ d : Lattice, Primitive d → embed d ≠ 0 := by
    intro d hd hdz
    have hx : d.1 = 0 := by
      have hh : (d.1 : ℝ) = 0 := congrArg Prod.fst hdz
      exact_mod_cast hh
    have hy : d.2 = 0 := by
      have hh : (d.2 : ℝ) = 0 := congrArg Prod.snd hdz
      exact_mod_cast hh
    simpa [Primitive, hx, hy] using hd
  refine ⟨p, ?_⟩
  exact ⟨hpos _ _ (hne v P.first_primitive) P.first_support,
    hpos _ _ (hne w P.second_primitive) P.second_support,
    fun i => hpos _ _ (hne _ (P.bounded_primitive i)) (P.bounded_support i)⟩

private theorem carrier_support {v w : Lattice} (P : Region v w) :
    P.carrier = regionSupportIntersection P := by
  apply Set.Subset.antisymm
  · exact fun x hx => ⟨P.first_support x hx, P.second_support x hx,
      fun i => P.bounded_support i x hx⟩
  · intro x hx
    rcases hx with ⟨hxv, hxw, hxb⟩
    obtain ⟨p, hpv, hpw, hpb⟩ := exists_strict_point P
    let f : ℕ → RealPlane := fun n => x + (1 / ((n : ℝ) + 1)) • (p - x)
    have hmem : ∀ n, f n ∈ P.carrier := by
      intro n
      have ht : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have ht1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hstrict : ∀ u q : RealPlane, 0 ≤ realDet u (x - q) →
          0 < realDet u (p - q) → 0 < realDet u (f n - q) := by
        intro u q hxu hpu
        have heq : realDet u (f n - q) =
            (1 - 1 / ((n : ℝ) + 1)) * realDet u (x - q) +
              (1 / ((n : ℝ) + 1)) * realDet u (p - q) := by
          dsimp [f, realDet]
          ring
        rw [heq]
        exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hxu)
          (mul_pos ht hpu)
      exact strict_support_mem P _ (hstrict _ _ hxv hpv) (hstrict _ _ hxw hpw)
        (fun i => hstrict _ _ (hxb i) (hpb i))
    apply P.closed.mem_of_tendsto (f := f) (b := atTop) ?_ (Eventually.of_forall hmem)
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (p - x)
    simpa [f] using tendsto_const_nhds.add ht

private theorem carrier_recession {v w : Lattice} (P : Region v w) :
    recessionCone P.carrier = twoRayCone (-v) w := by
  apply Set.Subset.antisymm
  · intro d hd
    have hv := P.first_support _ (hd (embed P.firstAnchor)
      (by simpa using first_ray_mem P 0 le_rfl))
    have hw := P.second_support _ (hd (embed P.secondAnchor)
      (by simpa using second_ray_mem P 0 le_rfl))
    have hv' : 0 ≤ realDet (embed v) d := by simpa [Region.firstAnchor] using hv
    have hw' : 0 ≤ realDet (embed w) d := by simpa [Region.secondAnchor] using hw
    let D : ℝ := realDet (embed v) (embed w)
    have hD : 0 < D := by
      have h := P.turn_positive
      dsimp [D, realDet, embed]
      exact_mod_cast h
    refine ⟨realDet (embed w) d / D, realDet (embed v) d / D,
      div_nonneg hw' hD.le, div_nonneg hv' hD.le, ?_⟩
    have hneg : embed (-v) = -embed v := by simp [embed]
    rw [hneg]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul]
    all_goals
      field_simp [ne_of_gt hD]
      dsimp [D, realDet]
      ring
  · intro d hd x hx
    exact cone_add_mem P hx hd

/-- RC03: all supporting inequalities suffice because the complete frontier is known. -/
theorem region_halfplane_representation {v w : Lattice} (P : Region v w) :
    P.carrier = regionSupportIntersection P ∧
    P.carrier = realMinkowski (regionVertexHull P) (twoRayCone (-v) w) ∧
    recessionCone P.carrier = twoRayCone (-v) w ∧
    ForwardInvariant P.lattice (-v) ∧ ForwardInvariant P.lattice w := by
  refine ⟨carrier_support P, carrier_minkowski P, carrier_recession P, ?_, ?_⟩
  · simpa using lattice_forward_first P 1
  · simpa using lattice_forward_second P 1

end
end ConvexNivat.Colle
