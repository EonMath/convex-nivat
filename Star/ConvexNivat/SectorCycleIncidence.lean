import ConvexNivat.SectorCycleCodes
import ConvexNivat.SectorCycleClosure

namespace ConvexNivat
noncomputable section

def sectorOppositeOrientation : RayOrientation → RayOrientation
  | .positive => .negative
  | .negative => .positive

def sectorPositiveRayOrientation {p : ℕ} (star : StarData p) (j : SectorRest star) :
    RayOrientation :=
  if 0 < det (sectorBaseDirection star) (star.component j.val).direction
  then .positive else .negative

def sectorPositiveRayPoint {p : ℕ} (star : StarData p) (j : SectorRest star) :
    RealPlane :=
  embed ((sectorPositiveRayOrientation star j).sign • (star.component j.val).direction)

theorem sector_nonbase_ray_incidence {p : ℕ} (star : StarData p) :
    ∀ r : Fin (star.m - 1),
      0 < realHeight (sectorBaseDirection star)
        (sectorPositiveRayPoint star (sectorLabel star r)) ∧
      (∀ l : Fin star.m,
        sectorPositiveRayPoint star (sectorLabel star r) ∈
            closure (sectorCone star (sectorPositiveCode star l)) ↔
          l.val = r.val ∨ l.val = r.val + 1) ∧
      (∀ l : Fin star.m,
        sectorPositiveRayPoint star (sectorLabel star r) ∉
          closure (sectorCone star (sectorNegativeCode star l))) ∧
      (∀ l : Fin star.m,
        -sectorPositiveRayPoint star (sectorLabel star r) ∈
            closure (sectorCone star (sectorNegativeCode star l)) ↔
          l.val = r.val ∨ l.val = r.val + 1) ∧
      (∀ l : Fin star.m,
        -sectorPositiveRayPoint star (sectorLabel star r) ∉
          closure (sectorCone star (sectorPositiveCode star l))) ∧
      embed ((sectorOppositeOrientation
          (sectorPositiveRayOrientation star (sectorLabel star r))).sign •
        (star.component (sectorLabel star r).val).direction) =
          -sectorPositiveRayPoint star (sectorLabel star r) ∧
      (∀ σ : RayOrientation,
        embed (σ.sign • (star.component (sectorLabel star r).val).direction) =
          sectorPositiveRayPoint star (sectorLabel star r) ∨
        embed (σ.sign • (star.component (sectorLabel star r).val).direction) =
          -sectorPositiveRayPoint star (sectorLabel star r)) := by
  have ha := sector_height_algebra
  have hpositive := sector_positive_codes star
  have hnegative := (sector_signed_bijection star).2.1
  have hsorted : StrictMono (sectorOrderedBreakpoint star) :=
    (Classical.choose_spec (sector_sorted_labelled_breakpoints star)).1
  have hside (B T : ℝ) (hB : B ≠ 0) :
      ((sectorSignSide B = .left → B * T ≤ 0) ∧
        (sectorSignSide B = .right → 0 ≤ B * T)) ↔ 0 ≤ T := by
    by_cases hp : 0 < B
    · simp only [sectorSignSide, ite_eq_left hp]
      simp
      exact mul_nonneg_iff_of_pos_left hp
    · have hn : B < 0 := lt_of_le_of_ne (le_of_not_gt hp) hB
      simp only [sectorSignSide, ite_eq_right hp]
      simp
      constructor
      · intro h
        by_contra ht
        have : T < 0 := lt_of_not_ge ht
        have := mul_pos_of_neg_of_neg hn this
        linarith
      · exact fun h => mul_nonpos_of_nonpos_of_nonneg hn.le h
  have hopside (B T : ℝ) (hB : B ≠ 0) :
      ((sectorOppositeSide (sectorSignSide B) = .left → B * T ≤ 0) ∧
        (sectorOppositeSide (sectorSignSide B) = .right → 0 ≤ B * T)) ↔ T ≤ 0 := by
    by_cases hp : 0 < B
    · simp only [sectorSignSide, ite_eq_left hp, sectorOppositeSide]
      simp
      constructor
      · intro h
        by_contra ht
        have := mul_pos hp (lt_of_not_ge ht)
        linarith
      · exact fun h => mul_nonpos_of_nonneg_of_nonpos hp.le h
    · have hn : B < 0 := lt_of_le_of_ne (le_of_not_gt hp) hB
      simp only [sectorSignSide, ite_eq_right hp, sectorOppositeSide]
      simp
      constructor
      · intro h
        by_contra ht
        have := mul_neg_of_neg_of_pos hn (lt_of_not_ge ht)
        linarith
      · exact fun h => mul_nonneg_of_nonpos_of_nonpos hn.le h
  have hweak (l : Fin star.m) (t : ℝ) :
      sectorSlice star t ∈ closure (sectorCone star (sectorPositiveCode star l)) ↔
        t ∈ realWeakCut (sectorOrderedBreakpoint star) l.val := by
    rw [sector_closure_weak_signs star _ (hpositive l).2]
    have hrank (r : Fin (star.m - 1)) :
        sectorRank star ⟨(sectorLabel star r).val, (sectorLabel star r).property⟩ = r := by
      change (sectorLabel star).symm (sectorLabel star r) = r
      exact (sectorLabel star).symm_apply_apply r
    constructor
    · intro hx
      constructor
      · intro r hr
        have h := hx (sectorLabel star r).val
        rw [sectorPositiveCode, dite_eq_right (sectorLabel star r).property] at h
        rw [hrank] at h
        rw [ite_eq_left hr, (sector_slice_factors star (sectorLabel star r)).2.1 t |>.2] at h
        have ht := (hside _ _ (sector_slice_factors star (sectorLabel star r)).1).mp h
        exact sub_nonneg.mp ht
      · intro r hr
        have h := hx (sectorLabel star r).val
        rw [sectorPositiveCode, dite_eq_right (sectorLabel star r).property] at h
        rw [hrank] at h
        rw [ite_eq_right (not_lt.mpr hr),
          (sector_slice_factors star (sectorLabel star r)).2.1 t |>.2] at h
        have ht := (hopside _ _ (sector_slice_factors star (sectorLabel star r)).1).mp h
        exact sub_nonpos.mp ht
    · intro ht j
      by_cases hj : j = sectorBaseIndex star
      · subst j
        simp only [sectorPositiveCode]
        simp
        change 0 ≤ realHeight (sectorBaseDirection star) (sectorSlice star t)
        rw [(sector_slice_complement star).2]
        norm_num
      · let J : SectorRest star := ⟨j, hj⟩
        let r := sectorRank star J
        have hr : sectorOrderedBreakpoint star r = sectorBreakpoint star J := by
          simp [sectorOrderedBreakpoint, r, sectorRank]
        rw [sectorPositiveCode, dite_eq_right hj,
          (sector_slice_factors star J).2.1 t |>.2]
        by_cases hl : r.val < l.val
        · rw [ite_eq_left hl, hside _ _ (sector_slice_factors star J).1]
          exact sub_nonneg.mpr (by simpa only [hr] using ht.1 r hl)
        · rw [ite_eq_right hl, hopside _ _ (sector_slice_factors star J).1]
          exact sub_nonpos.mpr (by simpa only [hr] using ht.2 r (le_of_not_gt hl))
  have hscale (l : Fin star.m) (x : RealPlane) (c : ℝ) (hc : 0 < c) :
      c • x ∈ closure (sectorCone star (sectorPositiveCode star l)) ↔
        x ∈ closure (sectorCone star (sectorPositiveCode star l)) := by
    rw [sector_closure_weak_signs star _ (hpositive l).2,
      sector_closure_weak_signs star _ (hpositive l).2]
    simp only [ha.2.1]
    constructor <;> intro h j
    · constructor
      · intro hj
        have hh := (h j).1 hj
        nlinarith
      · intro hj
        have hh := (h j).2 hj
        nlinarith
    · constructor
      · intro hj
        exact mul_nonpos_of_nonneg_of_nonpos hc.le ((h j).1 hj)
      · intro hj
        exact mul_nonneg hc.le ((h j).2 hj)
  have hneg (l : Fin star.m) (x : RealPlane) :
      -x ∈ closure (sectorCone star (sectorNegativeCode star l)) ↔
        x ∈ closure (sectorCone star (sectorPositiveCode star l)) := by
    rw [sector_closure_weak_signs star _ (hnegative l),
      sector_closure_weak_signs star _ (hpositive l).2]
    have hn (v : Lattice) : realHeight v (-x) = -realHeight v x := by
      simp [realHeight]
      ring
    simp only [hn, sectorNegativeCode]
    constructor <;> intro h j <;> have hj := h j <;>
      cases hs : sectorPositiveCode star l j <;>
      simp [hs, sectorOppositeSide] at hj ⊢ <;> linarith
  intro r
  let j := sectorLabel star r
  let D : ℤ := det (sectorBaseDirection star) (star.component j.val).direction
  have hD : D ≠ 0 := star.pairwise_nonparallel _ _ j.property.symm
  let H : ℝ := ((sectorPositiveRayOrientation star j).sign : ℝ) * (D : ℝ)
  have htau : sectorPositiveRayOrientation star j =
      if 0 < D then .positive else .negative := rfl
  have hH : 0 < H := by
    by_cases hp : 0 < D
    · simp only [H, htau, ite_eq_left hp, RayOrientation.sign,
        Int.cast_one, one_mul]
      exact_mod_cast hp
    · have hn : D < 0 := lt_of_le_of_ne (le_of_not_gt hp) hD
      simp only [H, htau, ite_eq_right hp, RayOrientation.sign,
        Int.cast_neg, Int.cast_one, neg_one_mul]
      exact neg_pos.mpr (by exact_mod_cast hn)
  have hq : sectorPositiveRayPoint star j = H • sectorSlice star (sectorBreakpoint star j) := by
    rw [(sector_slice_factors star j).2.2]
    have hc : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    simp only [sectorPositiveRayPoint, H]
    have he : embed ((sectorPositiveRayOrientation star j).sign • (star.component j.val).direction) =
        ((sectorPositiveRayOrientation star j).sign : ℝ) • embed (star.component j.val).direction := by
      ext <;> simp [embed]
    rw [he, smul_smul]
    congr 1
    change ((sectorPositiveRayOrientation star j).sign : ℝ) =
      (((sectorPositiveRayOrientation star j).sign : ℝ) * (D : ℝ)) * (1 / (D : ℝ))
    field_simp
  have hheight : realHeight (sectorBaseDirection star) (sectorPositiveRayPoint star j) = H := by
    rw [hq, ha.2.1, (sector_slice_complement star).2, mul_one]
  have hinc (l : Fin star.m) :
      sectorPositiveRayPoint star j ∈ closure (sectorCone star (sectorPositiveCode star l)) ↔
        l.val = r.val ∨ l.val = r.val + 1 := by
    rw [hq, hscale _ _ _ hH, hweak]
    let L : Fin (star.m - 1 + 1) := ⟨l.val, by have := l.isLt; have := star.two_le; omega⟩
    exact (sector_interval_partition (sectorOrderedBreakpoint star) hsorted).2.2.2 r L
  have hnotneg (l : Fin star.m) :
      sectorPositiveRayPoint star j ∉ closure (sectorCone star (sectorNegativeCode star l)) := by
    intro hm
    have hh := (sector_closure_weak_signs star _ (hnegative l) _).mp hm (sectorBaseIndex star)
    have hs : sectorNegativeCode star l (sectorBaseIndex star) = .left := by
      simp [sectorNegativeCode, sectorPositiveCode, sectorOppositeSide]
    have hh' := hh.1 hs
    change realHeight (sectorBaseDirection star) _ ≤ 0 at hh'
    rw [hheight] at hh'
    linarith
  change 0 < realHeight (sectorBaseDirection star) (sectorPositiveRayPoint star j) ∧ _
  refine ⟨by rw [hheight]; exact hH, hinc, hnotneg, ?_, ?_, ?_, ?_⟩
  · intro l
    exact (hneg l _).trans (hinc l)
  · intro l hm
    have hn := (hneg l (-sectorPositiveRayPoint star j)).mpr hm
    rw [neg_neg] at hn
    exact hnotneg l hn
  · change embed ((sectorOppositeOrientation (sectorPositiveRayOrientation star j)).sign •
        (star.component j.val).direction) = -sectorPositiveRayPoint star j
    cases hs : sectorPositiveRayOrientation star j <;>
      ext <;> simp [sectorPositiveRayPoint, sectorOppositeOrientation, hs,
        RayOrientation.sign, embed]
  · intro σ
    change embed (σ.sign • (star.component j.val).direction) = sectorPositiveRayPoint star j ∨
      embed (σ.sign • (star.component j.val).direction) = -sectorPositiveRayPoint star j
    cases hs : sectorPositiveRayOrientation star j <;> cases σ
    · exact Or.inl (by simp [sectorPositiveRayPoint, hs])
    · exact Or.inr (by ext <;> simp [sectorPositiveRayPoint, hs, RayOrientation.sign, embed])
    · exact Or.inr (by ext <;> simp [sectorPositiveRayPoint, hs, RayOrientation.sign, embed])
    · exact Or.inl (by simp [sectorPositiveRayPoint, hs])

theorem sector_base_ray_incidence {p : ℕ} (star : StarData p) :
    ∀ l : Fin star.m,
      (embed (sectorBaseDirection star) ∈
          closure (sectorCone star (sectorPositiveCode star l)) ↔ l.val = star.m - 1) ∧
      (embed (sectorBaseDirection star) ∈
          closure (sectorCone star (sectorNegativeCode star l)) ↔ l.val = 0) ∧
      (-embed (sectorBaseDirection star) ∈
          closure (sectorCone star (sectorPositiveCode star l)) ↔ l.val = 0) ∧
      (-embed (sectorBaseDirection star) ∈
          closure (sectorCone star (sectorNegativeCode star l)) ↔ l.val = star.m - 1) := by
  have hp := sector_positive_codes star
  have hn := (sector_signed_bijection star).2.1
  have hneg (l : Fin star.m) (x : RealPlane) :
      -x ∈ closure (sectorCone star (sectorNegativeCode star l)) ↔
        x ∈ closure (sectorCone star (sectorPositiveCode star l)) := by
    rw [sector_closure_weak_signs star _ (hn l),
      sector_closure_weak_signs star _ (hp l).2]
    have hh (v : Lattice) : realHeight v (-x) = -realHeight v x := by
      simp [realHeight]; ring
    simp only [hh, sectorNegativeCode]
    constructor <;> intro h j <;> have hj := h j <;>
      cases hs : sectorPositiveCode star l j <;>
      simp [hs, sectorOppositeSide] at hj ⊢ <;> linarith
  have hw (B : ℝ) (hB : B ≠ 0) (P : Prop) [Decidable P] :
      (((if P then sectorSignSide B else sectorOppositeSide (sectorSignSide B)) = .left →
          B ≤ 0) ∧
        ((if P then sectorSignSide B else sectorOppositeSide (sectorSignSide B)) = .right →
          0 ≤ B)) ↔ P := by
    by_cases h : 0 < B
    · have h' : ¬ B ≤ 0 := not_le.mpr h
      by_cases hP : P <;> simp [hP, sectorSignSide, h, sectorOppositeSide, h.le, h']
    · have h' : B < 0 := lt_of_le_of_ne (le_of_not_gt h) hB
      by_cases hP : P <;>
        simp [hP, sectorSignSide, h, sectorOppositeSide, h'.le, not_le.mpr h']
  have hwm (B : ℝ) (hB : B ≠ 0) (P : Prop) [Decidable P] :
      (((if P then sectorSignSide B else sectorOppositeSide (sectorSignSide B)) = .left →
          -B ≤ 0) ∧
        ((if P then sectorSignSide B else sectorOppositeSide (sectorSignSide B)) = .right →
          0 ≤ -B)) ↔ ¬ P := by
    by_cases h : 0 < B
    · have h' : ¬ -B ≥ 0 := by linarith
      have h'' : -B ≤ 0 := by linarith
      by_cases hP : P <;> simp [hP, sectorSignSide, h, sectorOppositeSide, h', h'']
    · have h' : B < 0 := lt_of_le_of_ne (le_of_not_gt h) hB
      have h'' : ¬ -B ≤ 0 := by linarith
      have h''' : 0 ≤ -B := by linarith
      by_cases hP : P <;> simp [hP, sectorSignSide, h, sectorOppositeSide, h'', h''']
  have hB (j : SectorRest star) : sectorSliceB star j.val ≠ 0 :=
    (sector_slice_factors star j).1
  have hrank (r : Fin (star.m - 1)) :
      sectorRank star ⟨(sectorLabel star r).val, (sectorLabel star r).property⟩ = r := by
    change (sectorLabel star).symm (sectorLabel star r) = r
    exact (sectorLabel star).symm_apply_apply r
  have hheight (j : Fin star.m) :
      realHeight (star.component j).direction (embed (sectorBaseDirection star)) =
        sectorSliceB star j := (sector_height_algebra).2.2.1 _ _
  have hheightm (j : Fin star.m) :
      realHeight (star.component j).direction (-embed (sectorBaseDirection star)) =
        -sectorSliceB star j := by
    have hh (v : Lattice) (x : RealPlane) : realHeight v (-x) = -realHeight v x := by
      simp [realHeight]; ring
    rw [hh, hheight]
  have hpos (l : Fin star.m) :
      embed (sectorBaseDirection star) ∈ closure (sectorCone star (sectorPositiveCode star l)) ↔
        l.val = star.m - 1 := by
    rw [sector_closure_weak_signs star _ (hp l).2]
    constructor
    · intro h
      let r : Fin (star.m - 1) := ⟨star.m - 2, by have := star.two_le; omega⟩
      have hj := h (sectorLabel star r).val
      rw [sectorPositiveCode, dite_eq_right (sectorLabel star r).property, hrank, hheight,
        hw _ (hB (sectorLabel star r))] at hj
      have := l.isLt
      have := star.two_le
      change star.m - 2 < l.val at hj
      omega
    · intro hl j
      by_cases hj : j = sectorBaseIndex star
      · subst j
        simp only [sectorPositiveCode]
        change (TailSide.right = TailSide.left → realHeight (sectorBaseDirection star) _ ≤ 0) ∧
          (TailSide.right = TailSide.right → 0 ≤ realHeight (sectorBaseDirection star) _)
        rw [(sector_height_algebra).2.2.1]
        simp [det, mul_comm]
      · rw [sectorPositiveCode, dite_eq_right hj, hheight, hw _ (hB ⟨j,hj⟩)]
        have := (sectorRank star ⟨j,hj⟩).isLt
        omega
  have hminus (l : Fin star.m) :
      -embed (sectorBaseDirection star) ∈ closure (sectorCone star (sectorPositiveCode star l)) ↔
        l.val = 0 := by
    rw [sector_closure_weak_signs star _ (hp l).2]
    constructor
    · intro h
      let r : Fin (star.m - 1) := ⟨0, by have := star.two_le; omega⟩
      have hj := h (sectorLabel star r).val
      rw [sectorPositiveCode, dite_eq_right (sectorLabel star r).property, hrank, hheightm,
        hwm _ (hB (sectorLabel star r))] at hj
      change ¬ 0 < l.val at hj
      omega
    · intro hl j
      by_cases hj : j = sectorBaseIndex star
      · subst j
        simp only [sectorPositiveCode]
        rw [hheightm]
        change (TailSide.right = TailSide.left → -(det (sectorBaseDirection star) (sectorBaseDirection star) : ℝ) ≤ 0) ∧
          (TailSide.right = TailSide.right → 0 ≤ -(det (sectorBaseDirection star) (sectorBaseDirection star) : ℝ))
        simp [det, mul_comm]
      · rw [sectorPositiveCode, dite_eq_right hj, hheightm, hwm _ (hB ⟨j,hj⟩)]
        omega
  intro l
  refine ⟨hpos l, ?_, hminus l, (hneg l _).trans (hpos l)⟩
  have hh := (hneg l (-embed (sectorBaseDirection star))).trans (hminus l)
  simpa only [neg_neg] using hh

theorem sector_adjacency_blocks {p : ℕ} (star : StarData p) :
    (∀ a b : Fin star.m,
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorPositiveCode star a) (sectorPositiveCode star b)) ↔
        (a.val + 1 = b.val ∨ b.val + 1 = a.val)) ∧
    (∀ a b : Fin star.m,
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorNegativeCode star a) (sectorNegativeCode star b)) ↔
        (a.val + 1 = b.val ∨ b.val + 1 = a.val)) ∧
    (∀ a b : Fin star.m,
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorPositiveCode star a) (sectorNegativeCode star b)) ↔
        ((a.val = star.m - 1 ∧ b.val = 0) ∨
          (a.val = 0 ∧ b.val = star.m - 1))) ∧
    (∀ a b : Fin star.m,
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorNegativeCode star a) (sectorPositiveCode star b)) ↔
        ((a.val = star.m - 1 ∧ b.val = 0) ∨
          (a.val = 0 ∧ b.val = star.m - 1))) := by
  have hp := sector_positive_codes star
  have hn := (sector_signed_bijection star).2.1
  have hE :
      (∀ l : Fin star.m, (sectorSignedEquiv star (.inl l)).val = sectorPositiveCode star l) ∧
      (∀ l : Fin star.m, (sectorSignedEquiv star (.inr l)).val = sectorNegativeCode star l) :=
    Classical.choose_spec (sector_signed_bijection star).2.2
  have hinjp : Function.Injective (sectorPositiveCode star) := by
    intro a b h
    have he : sectorSignedEquiv star (.inl a) = sectorSignedEquiv star (.inl b) :=
      Subtype.ext (by rw [hE.1, hE.1, h])
    exact Sum.inl.inj ((sectorSignedEquiv star).injective he)
  have hinjn : Function.Injective (sectorNegativeCode star) := by
    intro a b h
    have he : sectorSignedEquiv star (.inr a) = sectorSignedEquiv star (.inr b) :=
      Subtype.ext (by rw [hE.2, hE.2, h])
    exact Sum.inr.inj ((sectorSignedEquiv star).injective he)
  have hpnne (a b : Fin star.m) : sectorPositiveCode star a ≠ sectorNegativeCode star b := by
    intro h
    have hh := congrFun h (sectorBaseIndex star)
    simp [sectorPositiveCode, sectorNegativeCode, sectorOppositeSide] at hh
  have hneg (l : Fin star.m) (x : RealPlane) :
      -x ∈ closure (sectorCone star (sectorNegativeCode star l)) ↔
        x ∈ closure (sectorCone star (sectorPositiveCode star l)) := by
    rw [sector_closure_weak_signs star _ (hn l),
      sector_closure_weak_signs star _ (hp l).2]
    have hh (v : Lattice) : realHeight v (-x) = -realHeight v x := by
      simp [realHeight]; ring
    simp only [hh, sectorNegativeCode]
    constructor <;> intro h j <;> have hj := h j <;>
      cases hs : sectorPositiveCode star l j <;>
      simp [hs, sectorOppositeSide] at hj ⊢ <;> linarith
  have hop (i : Fin star.m) (σ : RayOrientation) :
      embed ((sectorOppositeOrientation σ).sign • (star.component i).direction) =
        -embed (σ.sign • (star.component i).direction) := by
    cases σ <;> ext <;> simp [sectorOppositeOrientation, RayOrientation.sign, embed]
  have hbpos : embed (RayOrientation.positive.sign •
      (star.component (sectorBaseIndex star)).direction) = embed (sectorBaseDirection star) := by
    simp [RayOrientation.sign, sectorBaseDirection]
  have hbneg : embed (RayOrientation.negative.sign •
      (star.component (sectorBaseIndex star)).direction) = -embed (sectorBaseDirection star) := by
    ext <;> simp [RayOrientation.sign, sectorBaseDirection, embed]
  have hpp (a b : Fin star.m) :
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorPositiveCode star a) (sectorPositiveCode star b)) ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
    constructor
    · rintro ⟨i, σ, _, _, hne, ha, hb⟩
      have hab : a ≠ b := fun h => hne (congrArg (sectorPositiveCode star) h)
      have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      by_cases hi : i = sectorBaseIndex star
      · subst i
        cases σ
        · rw [hbpos] at ha hb
          have := (sector_base_ray_incidence star a).1.mp ha
          have := (sector_base_ray_incidence star b).1.mp hb
          omega
        · rw [hbneg] at ha hb
          have := (sector_base_ray_incidence star a).2.2.1.mp ha
          have := (sector_base_ray_incidence star b).2.2.1.mp hb
          omega
      · let J : SectorRest star := ⟨i, hi⟩
        let r := sectorRank star J
        have hj : sectorLabel star r = J := by simp [r, sectorRank]
        have ht := sector_nonbase_ray_incidence star r
        have hall := ht.2.2.2.2.2.2 σ
        simp only [hj] at hall
        rcases hall with hq | hq
        · rw [hq] at ha hb
          have haa := ht.2.1 a
          have hbb := ht.2.1 b
          simp only [hj] at haa hbb
          have := haa.mp ha
          have := hbb.mp hb
          omega
        · rw [hq] at ha
          have hnot := ht.2.2.2.2.1 a
          simp only [hj] at hnot
          exact (hnot ha).elim
    · intro hab
      have hne : sectorPositiveCode star a ≠ sectorPositiveCode star b := by
        intro h
        have hv := congrArg Fin.val (hinjp h)
        omega
      rcases hab with hab | hba
      · let r : Fin (star.m - 1) := ⟨a.val, by have := b.isLt; omega⟩
        have ht := sector_nonbase_ray_incidence star r
        refine ⟨(sectorLabel star r).val, sectorPositiveRayOrientation star (sectorLabel star r),
          (hp a).2, (hp b).2, hne, ?_, ?_⟩
        · exact (ht.2.1 a).mpr (Or.inl rfl)
        · exact (ht.2.1 b).mpr (Or.inr hab.symm)
      · let r : Fin (star.m - 1) := ⟨b.val, by have := a.isLt; omega⟩
        have ht := sector_nonbase_ray_incidence star r
        refine ⟨(sectorLabel star r).val, sectorPositiveRayOrientation star (sectorLabel star r),
          (hp a).2, (hp b).2, hne, ?_, ?_⟩
        · exact (ht.2.1 a).mpr (Or.inr hba.symm)
        · exact (ht.2.1 b).mpr (Or.inl rfl)
  have hnn (a b : Fin star.m) :
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorNegativeCode star a) (sectorNegativeCode star b)) ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by
    have ht :
        (∃ i σ, SectorsAdjacentAtRay star i σ
          (sectorNegativeCode star a) (sectorNegativeCode star b)) ↔
        (∃ i σ, SectorsAdjacentAtRay star i σ
          (sectorPositiveCode star a) (sectorPositiveCode star b)) := by
      constructor
      · rintro ⟨i, σ, _, _, hne, ha, hb⟩
        have hne' : sectorPositiveCode star a ≠ sectorPositiveCode star b := by
          intro h
          exact hne (congrArg (sectorNegativeCode star) (hinjp h))
        refine ⟨i, sectorOppositeOrientation σ, (hp a).2, (hp b).2, hne', ?_, ?_⟩
        · rw [hop]
          exact (hneg a _).mp (by simpa only [neg_neg] using ha)
        · rw [hop]
          exact (hneg b _).mp (by simpa only [neg_neg] using hb)
      · rintro ⟨i, σ, _, _, hne, ha, hb⟩
        have hne' : sectorNegativeCode star a ≠ sectorNegativeCode star b := by
          intro h
          exact hne (congrArg (sectorPositiveCode star) (hinjn h))
        refine ⟨i, sectorOppositeOrientation σ, hn a, hn b, hne', ?_, ?_⟩
        · rw [hop]
          exact (hneg a _).mpr ha
        · rw [hop]
          exact (hneg b _).mpr hb
    exact ht.trans (hpp a b)
  have hpn (a b : Fin star.m) :
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorPositiveCode star a) (sectorNegativeCode star b)) ↔
      ((a.val = star.m - 1 ∧ b.val = 0) ∨
        (a.val = 0 ∧ b.val = star.m - 1)) := by
    constructor
    · rintro ⟨i, σ, _, _, _, ha, hb⟩
      by_cases hi : i = sectorBaseIndex star
      · subst i
        cases σ
        · rw [hbpos] at ha hb
          exact Or.inl ⟨(sector_base_ray_incidence star a).1.mp ha,
            (sector_base_ray_incidence star b).2.1.mp hb⟩
        · rw [hbneg] at ha hb
          exact Or.inr ⟨(sector_base_ray_incidence star a).2.2.1.mp ha,
            (sector_base_ray_incidence star b).2.2.2.mp hb⟩
      · let J : SectorRest star := ⟨i, hi⟩
        let r := sectorRank star J
        have hj : sectorLabel star r = J := by simp [r, sectorRank]
        have ht := sector_nonbase_ray_incidence star r
        have hall := ht.2.2.2.2.2.2 σ
        simp only [hj] at hall
        rcases hall with hq | hq
        · rw [hq] at hb
          have hnot := ht.2.2.1 b
          simp only [hj] at hnot
          exact (hnot hb).elim
        · rw [hq] at ha
          have hnot := ht.2.2.2.2.1 a
          simp only [hj] at hnot
          exact (hnot ha).elim
    · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
      · refine ⟨sectorBaseIndex star, .positive, (hp a).2, hn b, hpnne a b, ?_, ?_⟩
        · rw [hbpos]
          exact (sector_base_ray_incidence star a).1.mpr ha
        · rw [hbpos]
          exact (sector_base_ray_incidence star b).2.1.mpr hb
      · refine ⟨sectorBaseIndex star, .negative, (hp a).2, hn b, hpnne a b, ?_, ?_⟩
        · rw [hbneg]
          exact (sector_base_ray_incidence star a).2.2.1.mpr ha
        · rw [hbneg]
          exact (sector_base_ray_incidence star b).2.2.2.mpr hb
  refine ⟨hpp, hnn, hpn, ?_⟩
  intro a b
  have hsym :
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorNegativeCode star a) (sectorPositiveCode star b)) ↔
      (∃ i σ, SectorsAdjacentAtRay star i σ
        (sectorPositiveCode star b) (sectorNegativeCode star a)) := by
    constructor <;> rintro ⟨i, σ, h1, h2, hne, h3, h4⟩ <;>
      exact ⟨i, σ, h2, h1, Ne.symm hne, h4, h3⟩
  rw [hsym, hpn]
  tauto

end
end ConvexNivat
