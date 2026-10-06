import ConvexNivat.SectorCycleOrder
import ConvexNivat.SectorCycleIntervals

namespace ConvexNivat
noncomputable section

def sectorOppositeSide : TailSide → TailSide
  | .left => .right
  | .right => .left

def sectorSignSide (c : ℝ) : TailSide :=
  if 0 < c then .right else .left

def sectorPositiveCode {p : ℕ} (star : StarData p) (l : Fin star.m) :
    SectorSigns star := fun j =>
  if hj : j = sectorBaseIndex star then .right
  else if (sectorRank star ⟨j, hj⟩).val < l.val
    then sectorSignSide (sectorSliceB star j)
    else sectorOppositeSide (sectorSignSide (sectorSliceB star j))

def sectorNegativeCode {p : ℕ} (star : StarData p) (l : Fin star.m) :
    SectorSigns star := fun j => sectorOppositeSide (sectorPositiveCode star l j)

def sectorCut {p : ℕ} (star : StarData p) (l : Fin star.m) : Set ℝ :=
  realOpenCut (sectorOrderedBreakpoint star) l.val

def sectorNormalisationParameter {p : ℕ} (star : StarData p) (x : RealPlane) : ℝ :=
  -realHeight (sectorComplement star) x / realHeight (sectorBaseDirection star) x

private theorem sector_code_base {p : ℕ} (star : StarData p) (l : Fin star.m) :
    sectorPositiveCode star l (sectorBaseIndex star) = .right := by
  simp [sectorPositiveCode]

private theorem sector_order_strict {p : ℕ} (star : StarData p) :
    StrictMono (sectorOrderedBreakpoint star) := by
  exact (Classical.choose_spec (sector_sorted_labelled_breakpoints star)).1

private theorem sector_code_slice_sign {p : ℕ} (star : StarData p)
    (l : Fin star.m) (j : SectorRest star) (t : ℝ) :
    (match sectorPositiveCode star l j.val with
      | .left => realHeight (star.component j.val).direction (sectorSlice star t) < 0
      | .right => 0 < realHeight (star.component j.val).direction (sectorSlice star t)) ↔
    if (sectorRank star j).val < l.val then sectorBreakpoint star j < t
      else t < sectorBreakpoint star j := by
  have hb := (sector_slice_factors star j).1
  have hf := (sector_slice_factors star j).2.1 t |>.2
  simp only [sectorPositiveCode, dite_eq_right j.property]
  by_cases hr : (sectorRank star j).val < l.val
  · simp only [ite_eq_left hr]
    by_cases hs : 0 < sectorSliceB star j.val
    · simp only [sectorSignSide, ite_eq_left hs]
      rw [hf]
      constructor <;> intro h <;> nlinarith
    · have hs' : sectorSliceB star j.val < 0 := lt_of_le_of_ne (le_of_not_gt hs) hb
      simp only [sectorSignSide, ite_eq_right hs]
      rw [hf]
      constructor <;> intro h <;> nlinarith
  · simp only [ite_eq_right hr]
    by_cases hs : 0 < sectorSliceB star j.val
    · simp only [sectorSignSide, ite_eq_left hs, sectorOppositeSide]
      rw [hf]
      constructor <;> intro h <;> nlinarith
    · have hs' : sectorSliceB star j.val < 0 := lt_of_le_of_ne (le_of_not_gt hs) hb
      simp only [sectorSignSide, ite_eq_right hs, sectorOppositeSide]
      rw [hf]
      constructor <;> intro h <;> nlinarith

theorem sector_positive_codes {p : ℕ} (star : StarData p) :
    ∀ l : Fin star.m,
      (∀ t : ℝ, sectorSlice star t ∈ sectorCone star (sectorPositiveCode star l) ↔
        t ∈ sectorCut star l) ∧
      RealisedSector star (sectorPositiveCode star l) := by
  classical
  have hm : star.m - 1 + 1 = star.m := by have := star.two_le; omega
  intro l
  have hc : ∀ t : ℝ, sectorSlice star t ∈ sectorCone star (sectorPositiveCode star l) ↔
      t ∈ sectorCut star l := by
    intro t
    constructor
    · intro ht
      constructor
      · intro r hr
        have hs := (sector_code_slice_sign star l (sectorLabel star r) t).1
          (ht (sectorLabel star r).val)
        simpa [sectorRank, sectorOrderedBreakpoint, hr] using hs
      · intro r hr
        have hs := (sector_code_slice_sign star l (sectorLabel star r) t).1
          (ht (sectorLabel star r).val)
        have hn : ¬r.val < l.val := by omega
        simpa [sectorRank, sectorOrderedBreakpoint, hn] using hs
    · intro ht j
      by_cases hj : j = sectorBaseIndex star
      · subst j
        rw [sector_code_base]
        change 0 < realHeight (sectorBaseDirection star) (sectorSlice star t)
        rw [(sector_slice_complement star).2 t]
        norm_num
      · let k : SectorRest star := ⟨j, hj⟩
        apply (sector_code_slice_sign star l k t).2
        have hl : sectorOrderedBreakpoint star (sectorRank star k) = sectorBreakpoint star k := by
          simp [sectorOrderedBreakpoint, sectorRank]
        by_cases hr : (sectorRank star k).val < l.val
        · simpa [hr, hl] using ht.1 (sectorRank star k) hr
        · have hn : l.val ≤ (sectorRank star k).val := by omega
          simpa [hr, hl] using ht.2 (sectorRank star k) hn
  refine ⟨hc, ?_⟩
  have hn := (sector_interval_partition (sectorOrderedBreakpoint star)
    (sector_order_strict star)).1
  have hl : l.val < star.m - 1 + 1 := by omega
  obtain ⟨t, ht⟩ := hn ⟨l.val, hl⟩
  exact ⟨sectorSlice star t, (hc t).2 ht⟩

private theorem sector_cone_scale {p : ℕ} (star : StarData p)
    (ε : SectorSigns star) (h : ℝ) (hh : 0 < h) (x : RealPlane) :
    h • x ∈ sectorCone star ε ↔ x ∈ sectorCone star ε := by
  constructor <;> intro hx j <;> have hj := hx j <;>
    simp only [sector_height_algebra.2.1] at hj ⊢ <;>
    cases he : ε j <;> simp only [he] at hj ⊢ <;> nlinarith

private theorem sector_cone_unique {p : ℕ} (star : StarData p)
    (ε δ : SectorSigns star) (x : RealPlane)
    (hε : x ∈ sectorCone star ε) (hδ : x ∈ sectorCone star δ) : ε = δ := by
  funext j
  have hj := hε j
  have hk := hδ j
  cases he : ε j <;> cases hd : δ j <;> simp only [he, hd] at hj hk ⊢ <;>
    first | rfl | linarith

private theorem sector_cone_height_ne {p : ℕ} (star : StarData p)
    (ε : SectorSigns star) (x : RealPlane) (hx : x ∈ sectorCone star ε)
    (j : Fin star.m) : realHeight (star.component j).direction x ≠ 0 := by
  have hj := hx j
  cases he : ε j <;> simp only [he] at hj
  · exact ne_of_lt hj
  · exact ne_of_gt hj

private theorem sector_normalise_eq {p : ℕ} (star : StarData p)
    (x : RealPlane) (hh : realHeight (sectorBaseDirection star) x ≠ 0) :
    x = realHeight (sectorBaseDirection star) x •
      sectorSlice star (sectorNormalisationParameter star x) := by
  have hd := sector_height_algebra.2.2.2 (sectorBaseDirection star)
    (sectorComplement star) (sector_slice_complement star).1 x
  rw [sectorSlice, smul_add, smul_smul, sectorNormalisationParameter]
  have hc : realHeight (sectorBaseDirection star) x *
      (-realHeight (sectorComplement star) x / realHeight (sectorBaseDirection star) x) =
      -realHeight (sectorComplement star) x := by field_simp
  rw [hc, add_comm]
  exact hd

theorem sector_positive_normalisation {p : ℕ} (star : StarData p) :
    (∀ (ε : SectorSigns star) (x : RealPlane),
      ε (sectorBaseIndex star) = .right → x ∈ sectorCone star ε →
      0 < realHeight (sectorBaseDirection star) x ∧
      x = realHeight (sectorBaseDirection star) x •
        sectorSlice star (sectorNormalisationParameter star x) ∧
      (∀ j : SectorRest star,
        sectorNormalisationParameter star x ≠ sectorBreakpoint star j) ∧
      ∃! l : Fin star.m,
        sectorNormalisationParameter star x ∈ sectorCut star l ∧
        ε = sectorPositiveCode star l) ∧
    (∀ (l : Fin star.m) (x : RealPlane),
      x ∈ sectorCone star (sectorPositiveCode star l) ↔
        ∃ h : ℝ, 0 < h ∧ ∃ t : ℝ, t ∈ sectorCut star l ∧
          x = h • sectorSlice star t) := by
  classical
  have hm : star.m - 1 + 1 = star.m := by have := star.two_le; omega
  have first : ∀ (ε : SectorSigns star) (x : RealPlane),
      ε (sectorBaseIndex star) = .right → x ∈ sectorCone star ε →
      0 < realHeight (sectorBaseDirection star) x ∧
      x = realHeight (sectorBaseDirection star) x •
        sectorSlice star (sectorNormalisationParameter star x) ∧
      (∀ j : SectorRest star,
        sectorNormalisationParameter star x ≠ sectorBreakpoint star j) ∧
      ∃! l : Fin star.m,
        sectorNormalisationParameter star x ∈ sectorCut star l ∧
        ε = sectorPositiveCode star l := by
    intro ε x he hx
    have hh : 0 < realHeight (sectorBaseDirection star) x := by
      simpa [sectorBaseDirection, he] using hx (sectorBaseIndex star)
    have hn := sector_normalise_eq star x (ne_of_gt hh)
    have hs : sectorSlice star (sectorNormalisationParameter star x) ∈ sectorCone star ε := by
      apply (sector_cone_scale star ε _ hh _).1
      rwa [← hn]
    have hoff : ∀ j : SectorRest star,
        sectorNormalisationParameter star x ≠ sectorBreakpoint star j := by
      intro j hj
      have hf := (sector_slice_factors star j).2.1 (sectorNormalisationParameter star x) |>.2
      have hz := sector_cone_height_ne star ε _ hs j.val
      apply hz
      rw [hf, hj, sub_self, mul_zero]
    have ho : ∀ r : Fin (star.m - 1),
        sectorNormalisationParameter star x ≠ sectorOrderedBreakpoint star r := by
      intro r
      exact hoff (sectorLabel star r)
    obtain ⟨l, hl, hu⟩ := (sector_interval_partition (sectorOrderedBreakpoint star)
      (sector_order_strict star)).2.2.1 _ ho
    let k : Fin star.m := ⟨l.val, by omega⟩
    have hk : sectorNormalisationParameter star x ∈ sectorCut star k := hl.1
    have heq : ε = sectorPositiveCode star k :=
      sector_cone_unique star ε _ _ hs ((sector_positive_codes star k).1 _ |>.2 hk)
    refine ⟨hh, hn, hoff, k, ⟨hk, heq⟩, ?_⟩
    intro a ha
    apply Fin.ext
    have hdis := (sector_interval_partition (sectorOrderedBreakpoint star)
      (sector_order_strict star)).2.1
    by_contra hv
    have hneq : (⟨a.val, by omega⟩ : Fin (star.m - 1 + 1)) ≠ l := by
      intro hh'
      exact hv (congrArg (fun q : Fin (star.m - 1 + 1) => q.val) hh')
    have hd := hdis ⟨a.val, by omega⟩ l hneq
    exact Set.disjoint_left.1 hd ha.1 hl.1
  refine ⟨first, ?_⟩
  intro l x
  constructor
  · intro hx
    obtain ⟨hh, hn, hoff, k, hk, hu⟩ := first _ x (sector_code_base star l) hx
    have hs : sectorSlice star (sectorNormalisationParameter star x) ∈
        sectorCone star (sectorPositiveCode star l) := by
      apply (sector_cone_scale star _ _ hh _).1
      rwa [← hn]
    have hl := (sector_positive_codes star l).1 _ |>.1 hs
    exact ⟨realHeight (sectorBaseDirection star) x, hh,
      sectorNormalisationParameter star x, hl, hn⟩
  · rintro ⟨h, hh, t, ht, rfl⟩
    exact (sector_cone_scale star _ h hh _).2 ((sector_positive_codes star l).1 t |>.2 ht)

private theorem sector_opposite_involutive (s : TailSide) :
    sectorOppositeSide (sectorOppositeSide s) = s := by
  cases s <;> rfl

private theorem sector_cone_opposite {p : ℕ} (star : StarData p)
    (ε : SectorSigns star) (x : RealPlane) :
    x ∈ sectorCone star (fun j => sectorOppositeSide (ε j)) ↔
      -x ∈ sectorCone star ε := by
  have hn : ∀ v : Lattice, realHeight v (-x) = -realHeight v x := by
    intro v
    simp [realHeight]
    ring
  constructor <;> intro hx j <;> have hj := hx j <;>
    cases he : ε j <;> simp only [he, sectorOppositeSide, hn] at hj ⊢ <;> linarith

private theorem sector_positive_code_injective {p : ℕ} (star : StarData p) :
    Function.Injective (sectorPositiveCode star) := by
  intro l k he
  have hm : star.m - 1 + 1 = star.m := by have := star.two_le; omega
  obtain ⟨x, hx⟩ := (sector_positive_codes star l).2
  have hn := (sector_positive_normalisation star).1 _ x (sector_code_base star l) hx
  have hkx : x ∈ sectorCone star (sectorPositiveCode star k) := by rwa [← he]
  have ht := sector_normalise_eq star x (ne_of_gt hn.1)
  have hl : sectorNormalisationParameter star x ∈ sectorCut star l := by
    apply (sector_positive_codes star l).1 _ |>.1
    apply (sector_cone_scale star _ _ hn.1 _).1
    rwa [← ht]
  have hk : sectorNormalisationParameter star x ∈ sectorCut star k := by
    apply (sector_positive_codes star k).1 _ |>.1
    apply (sector_cone_scale star _ _ hn.1 _).1
    rwa [← ht]
  by_contra hne
  have hneq : (⟨l.val, by omega⟩ : Fin (star.m - 1 + 1)) ≠ ⟨k.val, by omega⟩ := by
    intro h
    exact hne (Fin.ext (congrArg (fun q : Fin (star.m - 1 + 1) => q.val) h))
  have hd := (sector_interval_partition (sectorOrderedBreakpoint star)
    (sector_order_strict star)).2.1 _ _ hneq
  exact Set.disjoint_left.1 hd hl hk

theorem sector_signed_bijection {p : ℕ} (star : StarData p) :
    (∀ (l : Fin star.m) (x : RealPlane),
      x ∈ sectorCone star (sectorNegativeCode star l) ↔
        -x ∈ sectorCone star (sectorPositiveCode star l)) ∧
    (∀ l : Fin star.m, RealisedSector star (sectorNegativeCode star l)) ∧
    ∃ E : Fin star.m ⊕ Fin star.m ≃
        {ε : SectorSigns star // RealisedSector star ε},
      (∀ l : Fin star.m, (E (.inl l)).val = sectorPositiveCode star l) ∧
      (∀ l : Fin star.m, (E (.inr l)).val = sectorNegativeCode star l) := by
  classical
  have hneg : ∀ (l : Fin star.m) (x : RealPlane),
      x ∈ sectorCone star (sectorNegativeCode star l) ↔
        -x ∈ sectorCone star (sectorPositiveCode star l) := by
    intro l x
    exact sector_cone_opposite star (sectorPositiveCode star l) x
  have hr : ∀ l : Fin star.m, RealisedSector star (sectorNegativeCode star l) := by
    intro l
    obtain ⟨x, hx⟩ := (sector_positive_codes star l).2
    exact ⟨-x, (hneg l (-x)).2 (by simpa using hx)⟩
  refine ⟨hneg, hr, ?_⟩
  let f : Fin star.m ⊕ Fin star.m → {ε : SectorSigns star // RealisedSector star ε} :=
    Sum.elim (fun l => ⟨sectorPositiveCode star l, (sector_positive_codes star l).2⟩)
      (fun l => ⟨sectorNegativeCode star l, hr l⟩)
  have hi : Function.Injective f := by
    intro a b hab
    have hv := congrArg Subtype.val hab
    cases a with
    | inl l =>
      cases b with
      | inl k =>
        exact congrArg Sum.inl (sector_positive_code_injective star hv)
      | inr k =>
        have hb := congrFun hv (sectorBaseIndex star)
        simp [f, sectorNegativeCode, sector_code_base, sectorOppositeSide] at hb
    | inr l =>
      cases b with
      | inl k =>
        have hb := congrFun hv (sectorBaseIndex star)
        simp [f, sectorNegativeCode, sector_code_base, sectorOppositeSide] at hb
      | inr k =>
        apply congrArg Sum.inr
        apply sector_positive_code_injective star
        funext j
        have hj := congrFun hv j
        have hh := congrArg sectorOppositeSide hj
        simpa [f, sectorNegativeCode, sector_opposite_involutive] using hh
  have hs : Function.Surjective f := by
    intro ε
    obtain ⟨x, hx⟩ := ε.property
    cases he : ε.val (sectorBaseIndex star) with
    | right =>
      obtain ⟨hh, hn, hoff, l, hl, hu⟩ := (sector_positive_normalisation star).1 _ x he hx
      exact ⟨.inl l, Subtype.ext hl.2.symm⟩
    | left =>
      let δ : SectorSigns star := fun j => sectorOppositeSide (ε.val j)
      have hd : δ (sectorBaseIndex star) = .right := by
        simp [δ, he, sectorOppositeSide]
      have hδ : -x ∈ sectorCone star δ := by
        apply (sector_cone_opposite star ε.val (-x)).2
        simpa using hx
      obtain ⟨hh, hn, hoff, l, hl, hu⟩ := (sector_positive_normalisation star).1 δ (-x) hd hδ
      refine ⟨.inr l, Subtype.ext ?_⟩
      funext j
      have hj := congrFun hl.2 j
      have ho := congrArg sectorOppositeSide hj
      simpa [f, δ, sectorNegativeCode, sector_opposite_involutive] using ho.symm
  refine ⟨Equiv.ofBijective f ⟨hi, hs⟩, ?_, ?_⟩ <;> intro l <;> rfl

def sectorSignedEquiv {p : ℕ} (star : StarData p) :
    Fin star.m ⊕ Fin star.m ≃ {ε : SectorSigns star // RealisedSector star ε} :=
  Classical.choose (sector_signed_bijection star).2.2

end
end ConvexNivat
