import ConvexNivat.Colle.GeneratingHalfPlane

namespace ConvexNivat.Colle
open scoped BigOperators

private theorem offFace_convex (S : Finset Lattice) (hc : LatticeConvex S)
    (hs : S.Nonempty) (n : RealPlane) : LatticeConvex (offFace S n) := by
  classical
  let H : RealPlane → ℝ := fun x => realDot x n
  let a : ℝ := S.inf' hs (fun z => H (embed z))
  have hlinear : IsLinearMap ℝ H := by
    constructor
    · intro x y; simp [H, realDot]; ring
    · intro c x; simp [H, realDot]; ring
  have hface : ∀ z ∈ S, z ∈ supportFace S n ↔ H (embed z) = a := by
    intro z hz
    constructor
    · intro hzf
      have hb := (Finset.mem_filter.mp hzf).2
      apply le_antisymm
      · exact (Finset.le_inf'_iff hs (fun z => H (embed z))).mpr hb
      · exact Finset.inf'_le _ hz
    · intro he
      refine Finset.mem_filter.mpr ⟨hz, ?_⟩
      intro q hq
      change H (embed z) ≤ H (embed q)
      rw [he]
      exact Finset.inf'_le _ hq
  have hhalf : windowHull (offFace S n) ⊆ {x | a < H x} := by
    apply convexHull_min _ (convex_halfSpace_gt hlinear _)
    rintro _ ⟨w, hw, rfl⟩
    have hw' := Finset.mem_sdiff.mp hw
    change a < H (embed w)
    apply lt_of_le_of_ne (Finset.inf'_le (fun z => H (embed z)) hw'.1)
    intro he
    exact hw'.2 ((hface w hw'.1).mpr he.symm)
  have hhull : windowHull (offFace S n) ⊆ windowHull S := by
    apply convexHull_mono
    exact Set.image_mono (by exact_mod_cast (Finset.sdiff_subset : offFace S n ⊆ S))
  intro z
  constructor
  · intro hz
    have hzS := (hc z).mp (hhull hz)
    refine Finset.mem_sdiff.mpr ⟨hzS, ?_⟩
    intro hzf
    have he := (hface z hzS).mp hzf
    have hlt := hhalf hz
    change a < H (embed z) at hlt
    rw [he] at hlt
    exact lt_irrefl _ hlt
  · intro hz
    exact subset_convexHull ℝ _ (Set.mem_image_of_mem embed hz)

/-- Colle Lemma 2.6, with the extension bound for every real oriented line,
including irrational slopes, not just the rational directions used later. -/
theorem colle_2_6 (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (hlow : LowConvexComplexity ξ) :
    ∃ S : Finset Lattice, GeneratingSet ξ S ∧
      ∀ n : RealPlane, n ≠ 0 → SmallExtensionCount ξ S n := by
  classical
  let P : ℕ → Prop := fun k => ∃ S : Finset Lattice,
    S.card = k ∧ S.Nonempty ∧ LatticeConvex S ∧ complexity ξ S ≤ S.card
  have hex : ∃ k, P k := by
    obtain ⟨S, hs, hc, hl⟩ := hlow
    exact ⟨S.card, S, rfl, hs, hc, hl⟩
  obtain ⟨S, hcard, hs, hc, hl⟩ := Nat.find_spec hex
  have hminimal (T : Finset Lattice) (ht : T.Nonempty) (hct : LatticeConvex T)
      (hsmall : T.card < S.card) : T.card < complexity ξ T := by
    by_contra hgrowth
    have hlowT : complexity ξ T ≤ T.card := by omega
    have he := Nat.find_min' hex ⟨T, rfl, ht, hct, hlowT⟩
    rw [← hcard] at he
    omega
  refine ⟨S, ⟨hs, hc, ?_⟩, ?_⟩
  · intro z hz
    have hzS := hz.1
    have hcards := Finset.card_erase_of_mem hzS
    have hproper : (S.erase z).card < S.card := Finset.card_erase_lt_of_mem hzS
    have hmono : complexity ξ (S.erase z) ≤ complexity ξ S := by
      let r : Pattern ℤ S → Pattern ℤ (S.erase z) :=
        fun p q => p ⟨q.val, (Finset.mem_erase.mp q.property).2⟩
      have hr : r '' patternSet ξ S = patternSet ξ (S.erase z) := by
        ext p
        constructor
        · rintro ⟨q, ⟨u, rfl⟩, rfl⟩; exact ⟨u, rfl⟩
        · rintro ⟨u, rfl⟩; exact ⟨pattern ξ S u, ⟨u, rfl⟩, rfl⟩
      rw [complexity, ← hr]
      exact Set.ncard_image_le (finiteRange_patternSet_finite ξ A hA S)
    apply (generating_point_iff_complexity ξ A hA S z hzS).mpr
    by_cases hTne : (S.erase z).Nonempty
    · have hTgrowth := hminimal (S.erase z) hTne hz.2 hproper
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp hTne
      have hSpos := Finset.card_pos.mpr hs
      rw [he, Finset.card_empty] at hcards
      rw [he, complexity_empty] at hmono ⊢
      omega
  · intro n hn
    have hfacesub : supportFace S n ⊆ S := Finset.filter_subset _ _
    have hfacene : (supportFace S n).Nonempty := by
      obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_inf' hs (fun z => realDot (embed z) n)
      refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩⟩
      intro q hq
      rw [← he]
      exact Finset.inf'_le _ hq
    have hcards := Finset.card_sdiff_add_card_eq_card hfacesub
    have hproper : (offFace S n).card < S.card := by
      have hf := Finset.card_pos.mpr hfacene
      change (offFace S n).card + (supportFace S n).card = S.card at hcards
      omega
    by_cases hTne : (offFace S n).Nonempty
    · have hg := hminimal (offFace S n) hTne (offFace_convex S hc hs n) hproper
      unfold SmallExtensionCount
      change (offFace S n).card + (supportFace S n).card = S.card at hcards
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp hTne
      unfold SmallExtensionCount
      rw [he, complexity_empty]
      change (offFace S n).card + (supportFace S n).card = S.card at hcards
      rw [he, Finset.card_empty] at hcards
      omega

end ConvexNivat.Colle
