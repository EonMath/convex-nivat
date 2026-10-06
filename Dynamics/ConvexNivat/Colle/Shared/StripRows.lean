import ConvexNivat.Colle.Shared.RowCoordinates

namespace ConvexNivat.Colle
noncomputable section

private theorem embed_int_smul_local (n : ℤ) (v : Lattice) :
    embed (n • v) = (n : ℝ) • embed v := by
  ext <;> simp [embed, smul_eq_mul]

private theorem supportRow_det {B : Finset Lattice} {v p : Lattice}
    (hp : p ∈ supportRow B v) : p ∈ B ∧ ∀ q ∈ B, det v p ≤ det v q := by
  obtain ⟨hpB, hh⟩ := Finset.mem_filter.mp hp
  refine ⟨hpB, ?_⟩
  intro q hq
  have h := hh q hq
  rw [normal_height, normal_height] at h
  exact_mod_cast h

private theorem support_unit_segment (B : Finset Lattice) (hB : LatticeConvex B)
    (v : Lattice) (hv : Primitive v) (hc : 2 ≤ (supportRow B v).card) :
    ∃ p : Lattice, p ∈ B ∧ p + v ∈ B ∧ ∀ q ∈ B, det v p ≤ det v q := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
  have hamin := supportRow_det ha
  have hbmin := supportRow_det hb
  have hh : det v a = det v b := le_antisymm (hamin.2 b hbmin.1) (hbmin.2 a hamin.1)
  obtain ⟨k, hk⟩ := ((primitive_row_coordinates v hv).2.1 a b).mp hh
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, zero_smul, add_zero] at hk
    exact hab hk.symm
  have hbetween : ∀ p : Lattice, ∀ n : ℤ, 1 ≤ n → p ∈ B → p + n • v ∈ B → p + v ∈ B := by
    intro p n hn hp hpn
    apply (hB _).mp
    apply (convex_convexHull ℝ (embed '' (B : Set Lattice))).segment_subset
      (subset_convexHull ℝ _ ⟨p, hp, rfl⟩)
      (subset_convexHull ℝ _ ⟨p+n•v, hpn, rfl⟩)
    have hseg := ((primitive_row_coordinates v hv).2.2 p 0 n (by omega) (p+v)).mpr
      ⟨1, by omega, hn, by simp⟩
    simpa using hseg
  rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
  · refine ⟨b, hbmin.1, hbetween b (-k) (by omega) hbmin.1 ?_, hbmin.2⟩
    have he : b + (-k) • v = a := by rw [hk]; module
    exact he ▸ hamin.1
  · exact ⟨a, hamin.1, hbetween a k (by omega) hamin.1 (hk ▸ hbmin.1), hamin.2⟩

private theorem real_unit_row_point (B : Finset Lattice) (hB : LatticeConvex B)
    (v : Lattice) (hv : Primitive v) (x : RealPlane) (t : ℤ)
    (hx : x ∈ windowHull B) (hxv : x + embed v ∈ windowHull B)
    (ht : realDet (embed v) x = (t : ℝ)) :
    ∃ z ∈ B, det v z = t := by
  obtain ⟨e, he, _⟩ := (primitive_row_coordinates v hv).1
  let a : ℝ := realDet x (embed e)
  let n : ℤ := ⌈a⌉
  let z : Lattice := n • v + t • e
  have heR : realDet (embed v) (embed e) = 1 := by
    dsimp [realDet, embed, det] at *
    exact_mod_cast he
  have hbasis : x = a • embed v + (t : ℝ) • embed e := by
    dsimp [a, realDet] at *
    apply Prod.ext
    · change x.1 = _
      dsimp
      nlinarith [congrArg (fun s : ℝ => x.1 * s) heR,
        congrArg (fun s : ℝ => (embed e).1 * s) ht]
    · change x.2 = _
      dsimp
      nlinarith [congrArg (fun s : ℝ => x.2 * s) heR,
        congrArg (fun s : ℝ => (embed e).2 * s) ht]
  have hnlo : 0 ≤ (n : ℝ) - a := sub_nonneg.mpr (Int.le_ceil a)
  have hnhi : (n : ℝ) - a ≤ 1 := by
    have h := Int.ceil_lt_add_one a
    dsimp [n]
    linarith
  have hzemb : embed z = x + ((n : ℝ) - a) • embed v := by
    rw [hbasis]
    dsimp [z]
    rw [embed_add, embed_int_smul_local, embed_int_smul_local]
    module
  have hzB : z ∈ B := by
    apply (hB z).mp
    rw [hzemb]
    have h := (convex_convexHull ℝ (embed '' (B : Set Lattice))) hx hxv
      (sub_nonneg.mpr hnhi) hnlo (by ring : 1 - ((n : ℝ)-a) + ((n : ℝ)-a) = 1)
    convert h using 1 <;> first | rfl | module
  refine ⟨z, hzB, ?_⟩
  dsimp [z, det] at *
  nlinarith [congrArg (fun s : ℤ => t * s) he]

private theorem rows_between_unit_edges (B : Finset Lattice) (hB : LatticeConvex B)
    (v : Lattice) (hv : Primitive v) (p q : Lattice)
    (hp : p ∈ B) (hpv : p + v ∈ B) (hq : q ∈ B) (hqv : q + v ∈ B)
    (t : ℤ) (hpt : det v p ≤ t) (htq : t ≤ det v q) :
    ∃ z ∈ B, det v z = t := by
  by_cases he : det v p = det v q
  · exact ⟨p, hp, by omega⟩
  have hden : (0 : ℝ) < (det v q : ℝ) - (det v p : ℝ) := by exact_mod_cast (by omega : 0 < det v q - det v p)
  let a : ℝ := ((t : ℝ) - (det v p : ℝ)) / ((det v q : ℝ) - (det v p : ℝ))
  have ha : 0 ≤ a := div_nonneg (by exact_mod_cast (sub_nonneg.mpr hpt)) hden.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hden).mpr
    exact_mod_cast (by omega : t - det v p ≤ det v q - det v p)
  let x := (1-a) • embed p + a • embed q
  have hvertex : ∀ z ∈ B, embed z ∈ windowHull B := fun z hz => subset_convexHull ℝ _ ⟨z,hz,rfl⟩
  have hx : x ∈ windowHull B := (convex_convexHull ℝ _) (hvertex p hp) (hvertex q hq)
    (sub_nonneg.mpr ha1) ha (by ring)
  have hxv : x + embed v ∈ windowHull B := by
    have h := (convex_convexHull ℝ _) (hvertex (p+v) hpv) (hvertex (q+v) hqv)
      (sub_nonneg.mpr ha1) ha (by ring : 1-a+a=1)
    have heq : x + embed v = (1-a) • embed (p+v) + a • embed (q+v) := by
      rw [embed_add, embed_add]
      dsimp [x]
      module
    exact heq.symm ▸ h
  apply real_unit_row_point B hB v hv x t hx hxv
  have hdet : realDet (embed v) x =
      (1-a) * (det v p : ℝ) + a * (det v q : ℝ) := by
    dsimp [x, realDet, embed, det]
    push_cast
    ring
  rw [hdet]
  dsimp [a]
  field_simp [ne_of_gt hden]
  ring

private theorem periodic_mod {α : Type*} (f : ℤ → α) (n : ℕ)
    (hn : 0 < n) (hf : ∀ j, f (j+(n : ℤ))=f j) (j : ℤ) : f (j % n)=f j := by
  have hp : Function.Periodic f (n : ℤ) := hf
  have h := hp.int_mul (j/(n : ℤ)) (j % (n : ℤ))
  simpa only [Int.cast_id,Int.emod_add_ediv_mul] using h.symm


private theorem cycle_direction_mem {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) : C.direction j ∈ edgeDirections S := by
  have hm := C.at_least_two
  have hj0 : 0 ≤ j % (2*m : ℕ) := Int.emod_nonneg _ (by omega)
  have hjlt : j % (2*m : ℕ) < (2*m : ℕ) := Int.emod_lt_of_pos _ (by omega)
  let k : Fin (2*m) := ⟨(j % (2*m : ℕ)).toNat,(Int.toNat_lt hj0).mpr hjlt⟩
  apply (C.covers _).mpr
  refine ⟨k,?_⟩
  change C.direction ((j % (2*m : ℕ)).toNat : ℤ)=C.direction j
  rw [Int.toNat_of_nonneg hj0]
  exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) j

private theorem enveloped_edgeDirections_eq {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hB : EnvelopedWindow S B) :
    edgeDirections B = edgeDirections S := by
  have hfinite : (edgeDirections S).Finite := by
    have he : edgeDirections S = Set.range (fun i : Fin (2 * m) => C.direction (i.val : ℤ)) := by
      ext v
      exact C.covers v
    rw [he]
    exact Set.finite_range _
  exact Set.eq_of_subset_of_ncard_le (fun v hv => (hB.2.2.2.1 v hv).1)
    (le_of_eq hB.2.2.2.2.symm) hfinite

theorem enveloped_two_sided_strip_row_complete {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (hB : EnvelopedWindow S B) :
    rowMinimum (C.direction i) B hB.1 ≤ rowMaximum (C.direction i) B hB.1 ∧
    halfStrip B (C.direction i) ∪ halfStrip B (-C.direction i) =
      latticeStrip (C.direction i) (rowMinimum (C.direction i) B hB.1)
        (rowMaximum (C.direction i) B hB.1) := by
  classical
  let v := C.direction i
  have hv : Primitive v := C.primitive i
  have hedge : edgeDirections B = edgeDirections S := enveloped_edgeDirections_eq C hB
  have hvB : v ∈ edgeDirections B := hedge ▸ cycle_direction_mem C i
  have hnvB : -v ∈ edgeDirections B := by
    rw [hedge]
    have h := cycle_direction_mem C (i + (m : ℤ))
    simpa [C.antipodal, v] using h
  obtain ⟨p, hp, hpv, hmin⟩ := support_unit_segment B hB.2.1 v hv hvB.2.2
  obtain ⟨q, hq, hqv, hmax⟩ := support_unit_segment B hB.2.1 (-v) hnvB.1 hnvB.2.2
  have hneg : ∀ z : Lattice, det (-v) z = -det v z := by intro z; dsimp [det]; ring
  have hqmax : ∀ z ∈ B, det v z ≤ det v q := by
    intro z hz
    have h := hmax z hz
    rw [hneg, hneg] at h
    omega
  have hlo : rowMinimum v B hB.1 = det v p := le_antisymm
    (Finset.inf'_le _ hp) ((Finset.le_inf'_iff _ _).mpr hmin)
  have hhi : rowMaximum v B hB.1 = det v q := le_antisymm
    ((Finset.sup'_le_iff _ _).mpr hqmax) (Finset.le_sup' _ hq)
  have hordered : rowMinimum v B hB.1 ≤ rowMaximum v B hB.1 := by
    rw [hlo, hhi]
    exact hmin q hq
  refine ⟨hordered, ?_⟩
  change halfStrip B v ∪ halfStrip B (-v) = latticeStrip v _ _
  ext z
  constructor
  · intro hz
    rcases hz with ⟨g, hg, n, rfl⟩ | ⟨g, hg, n, rfl⟩
    all_goals
      have hh1 : rowMinimum v B hB.1 ≤ det v g := Finset.inf'_le (det v) hg
      have hh2 : det v g ≤ rowMaximum v B hB.1 := Finset.le_sup' (det v) hg
      have heq : det v (g + (n : ℤ) • v) = det v g := by dsimp [det]; ring
      have hneq : det v (g + (n : ℤ) • (-v)) = det v g := by dsimp [det]; ring
      constructor <;> change _ ≤ _
      all_goals first | simpa only [heq, hneq] using hh1 | simpa only [heq, hneq] using hh2
  · intro hz
    obtain ⟨hzlo, hzhi⟩ := hz
    rw [hlo] at hzlo
    rw [hhi] at hzhi
    have hqminus : det v (q + -v) = det v q := by dsimp [det]; ring
    obtain ⟨g, hg, hgheight⟩ := rows_between_unit_edges B hB.2.1 v hv
      p (q + -v) hp hpv hqv (by simpa using hq) (det v z) hzlo (by rwa [hqminus])
    obtain ⟨k, hk⟩ := ((primitive_row_coordinates v hv).2.1 g z).mp hgheight
    by_cases hk0 : 0 ≤ k
    · exact Or.inl ⟨g, hg, k.toNat, by simpa [Int.toNat_of_nonneg hk0] using hk⟩
    · apply Or.inr
      refine ⟨g, hg, (-k).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -k)]
      simpa only [neg_smul, smul_neg, neg_neg] using hk


end
end ConvexNivat.Colle
