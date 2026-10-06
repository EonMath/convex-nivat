import ConvexNivat.Colle.Shared.FacetShiftData
import ConvexNivat.Colle.Shared.CofinalExtensionRoute

namespace ConvexNivat.Colle
noncomputable section

local macro "facetU" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftLattice))
local macro "facetDepth" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FacetShiftData).num 0 ++ `ConvexNivat.Colle.facetShiftDepth))
local macro "paidTurn" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.cycle_turn_positive))
local macro "paidRow" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.row_mem))
local macro "paidDirectionMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.cycle_direction_mem))
local macro "paidNoMiddle" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CycleAlignment).num 0 ++ `ConvexNivat.Colle.support_pair_forbids_middle))
local macro "paidParallel" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.primitive_parallel_eq_or_neg))

private theorem cycle_halfplanes_finite {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (c : ℤ → ℤ) :
    {z : Lattice | ∀ r : ℤ, c r ≤ det (C.direction r) z}.Finite := by
  let f : Lattice → ℤ × ℤ := fun z => (det (C.direction 0) z,det (C.direction 1) z)
  let T : Set (ℤ × ℤ) := Set.Icc (c 0) (-c m) ×ˢ Set.Icc (c 1) (-c (1+m))
  have hfinite : T.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  apply hfinite.of_injOn (f := f)
  · intro z hz
    refine ⟨⟨hz 0,?_⟩,⟨hz 1,?_⟩⟩
    · have h := hz m
      have hd : C.direction (m : ℤ) = -C.direction 0 := by simpa using C.antipodal 0
      rw [hd] at h
      dsimp [f,det] at h ⊢
      linarith
    · have h := hz (1+m)
      rw [C.antipodal 1] at h
      dsimp [f,det] at h ⊢
      linarith
  · intro x hx y hy he
    have h1 : det (C.direction 0) x = det (C.direction 0) y := congrArg Prod.fst he
    have h2 : det (C.direction 1) x = det (C.direction 1) y := congrArg Prod.snd he
    have hd := paidTurn C 0
    change 0 < det (C.direction 0) (C.direction 1) at hd
    have hx1 : det (C.direction 0) (C.direction 1)*(x.1-y.1)=0 := by
      have hid : det (C.direction 0) (C.direction 1)*(x.1-y.1) =
          (C.direction 1).1*(det (C.direction 0) x-det (C.direction 0) y)-
          (C.direction 0).1*(det (C.direction 1) x-det (C.direction 1) y) := by
        simp [det];ring
      rw [hid,h1,h2];ring
    have hx2 : det (C.direction 0) (C.direction 1)*(x.2-y.2)=0 := by
      have hid : det (C.direction 0) (C.direction 1)*(x.2-y.2) =
          (C.direction 1).2*(det (C.direction 0) x-det (C.direction 0) y)-
          (C.direction 0).2*(det (C.direction 1) x-det (C.direction 1) y) := by
        simp [det];ring
      rw [hid,h1,h2];ring
    apply Prod.ext
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hx1).resolve_left hd.ne')
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hx2).resolve_left hd.ne')

private theorem facet_depth_positive {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) : 0 < facetDepth C J := by
  exact mul_pos (by simpa using paidTurn C (J-1)) (paidTurn C J)

private theorem facet_old_subset {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) :
    (W.normalised (G.subsequence (L.index j)) : Set Lattice) ⊆ facetU W G L j := by
  intro z hz r
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  have hs := ((paidRow _ _ _).mp ((W.boundary (G.subsequence (L.index j))).initial r)).2 q hq
  have hdepth := facet_depth_positive C G.J
  change det (C.direction r)
    ((W.boundary (G.subsequence (L.index j))).vertex r-
      (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i)-
    (if C.direction r=C.direction G.J then facetDepth C G.J else 0) ≤ _
  split_ifs <;> dsimp [det] at hs ⊢ <;> nlinarith

private theorem facet_finite_family {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) :
    ∃ E : ℕ → Finset Lattice, (∀ j, (E j : Set Lattice)=facetU W G L j) ∧
      ∀ j, W.normalised (G.subsequence (L.index j)) ⊆ E j := by
  classical
  have hf (j : ℕ) : (facetU W G L j).Finite := cycle_halfplanes_finite C _
  refine ⟨fun j => (hf j).toFinset,fun j => Set.Finite.coe_toFinset (hf j),?_⟩
  intro j z hz
  exact (hf j).mem_toFinset.mpr (facet_old_subset W G L j hz)

private theorem facet_lattice_convex {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice)=facetU W G L j) : LatticeConvex E := by
  intro z
  constructor
  · intro hz
    change z ∈ (E : Set Lattice)
    rw [hE]
    intro r
    let c : ℤ := det (C.direction r)
      ((W.boundary (G.subsequence (L.index j))).vertex r-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i)-
      (if C.direction r=C.direction G.J then facetDepth C G.J else 0)
    have hhalf : windowHull E ⊆ {x : RealPlane | (c : ℝ) ≤ realDet (embed (C.direction r)) x} := by
      apply convexHull_min
      · rintro _ ⟨q,hq,rfl⟩
        have hq' : q ∈ facetU W G L j := by rw [← hE];exact hq
        have hh := hq' r
        change c ≤ det (C.direction r) q at hh
        simpa [realDet,embed,det] using (show (c : ℝ) ≤ (det (C.direction r) q : ℝ) by exact_mod_cast hh)
      · intro x hx y hy a b ha hb hab
        change (c : ℝ) ≤ realDet (embed (C.direction r)) (a • x+b • y)
        have he : realDet (embed (C.direction r)) (a • x+b • y) =
            a*realDet (embed (C.direction r)) x+b*realDet (embed (C.direction r)) y := by
          simp [realDet];ring
        rw [he]
        change (c : ℝ) ≤ _ at hx hy
        have hc : a*(c : ℝ)+b*c=c := by rw [← add_mul,hab,one_mul]
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hx),mul_nonneg hb (sub_nonneg.mpr hy)]
    have hh := hhalf hz
    change (c : ℝ) ≤ realDet (embed (C.direction r)) (embed z) at hh
    have he : realDet (embed (C.direction r)) (embed z) = (det (C.direction r) z : ℝ) := by
      simp [realDet,embed,det]
    rw [he] at hh
    exact_mod_cast hh
  · intro hz
    exact subset_convexHull ℝ _ ⟨z,hz,rfl⟩

private theorem left_shift_lowered_direction {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) (delta : Lattice)
    (hd : delta ∈ edgeDirections S) (hne : delta ≠ C.direction J)
    (hlow : det delta (C.direction (J-1)) < 0) : det delta (C.direction J) < 0 := by
  have hturn : 0 < det (C.direction (J-1)) (C.direction J) := by simpa using paidTurn C (J-1)
  have hzero : det delta (C.direction J) ≠ 0 := by
    intro hz
    have hz' : det (C.direction J) delta=0 := by dsimp [det] at hz ⊢;linarith
    rcases paidParallel _ _ (C.primitive J) hd.1 hz' with he | he
    · exact hne he
    · rw [he] at hlow
      dsimp [det] at hlow hturn
      linarith
  by_contra! hnon
  have hpos : 0 < det delta (C.direction J) := lt_of_le_of_ne hnon (Ne.symm hzero)
  have hprev : C.vertex J ∈ supportRow S (C.direction (J-1)) := by
    simpa using C.terminal_mem (J-1)
  apply paidNoMiddle hprev (C.initial_mem J) hturn _ hpos hd
  dsimp [det] at hlow ⊢
  linarith

private theorem right_shift_lowered_direction {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) (delta : Lattice)
    (hd : delta ∈ edgeDirections S) (hne : delta ≠ C.direction J)
    (hlow : 0 < det delta (C.direction (J+1))) : 0 < det delta (C.direction J) := by
  have hturn := paidTurn C J
  have hzero : det delta (C.direction J) ≠ 0 := by
    intro hz
    have hz' : det (C.direction J) delta=0 := by dsimp [det] at hz ⊢;linarith
    rcases paidParallel _ _ (C.primitive J) hd.1 hz' with he | he
    · exact hne he
    · rw [he] at hlow
      dsimp [det] at hlow hturn
      linarith
  by_contra! hnon
  have hneg : det delta (C.direction J) < 0 := lt_of_le_of_ne hnon hzero
  apply paidNoMiddle (C.terminal_mem J) (C.initial_mem (J+1)) hturn _ hlow hd
  dsimp [det] at hneg ⊢
  linarith

private theorem facet_uniform_endpoint_bound {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) :
    ∃ N : ℕ, ∀ r : ℤ,
      -(det (C.direction J) (C.direction (J+1))*det (C.direction r) (C.direction (J-1))) ≤ N ∧
      det (C.direction (J-1)) (C.direction J)*det (C.direction r) (C.direction (J+1)) ≤ N := by
  classical
  let f (k : Fin (2*m)) : ℕ := max
    (-(det (C.direction J) (C.direction (J+1))*det (C.direction k.val) (C.direction (J-1)))).toNat
    (det (C.direction (J-1)) (C.direction J)*det (C.direction k.val) (C.direction (J+1))).toNat
  obtain ⟨N,hN⟩ := (Finset.univ.image f).exists_le
  refine ⟨N,?_⟩
  intro r
  obtain ⟨k,hk⟩ := (C.covers _).mp (paidDirectionMem C r)
  have hNk := hN (f k) (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  dsimp [f] at hNk
  rw [hk] at hNk
  constructor <;> omega

private theorem facet_shifted_endpoints_support {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) (J : ℤ)
    (N : ℕ) (hN : ∀ r : ℤ,
      -(det (C.direction J) (C.direction (J+1))*det (C.direction r) (C.direction (J-1))) ≤ N ∧
      det (C.direction (J-1)) (C.direction J)*det (C.direction r) (C.direction (J+1)) ≤ N)
    (hlen : N ≤ b.length J) :
    ∀ r : ℤ,
      det (C.direction r) (b.vertex r-u)-
        (if C.direction r=C.direction J then facetDepth C J else 0) ≤
          det (C.direction r) (b.vertex J-u+
            det (C.direction J) (C.direction (J+1)) • C.direction (J-1)) ∧
      det (C.direction r) (b.vertex r-u)-
        (if C.direction r=C.direction J then facetDepth C J else 0) ≤
          det (C.direction r) (b.vertex (J+1)-u-
            det (C.direction (J-1)) (C.direction J) • C.direction (J+1)) := by
  intro r
  have hs (s : ℤ) : det (C.direction r) (b.vertex r-u) ≤ det (C.direction r) (b.vertex s-u) := by
    have hh := ((paidRow _ _ _).mp (b.initial r)).2 _ ((paidRow _ _ _).mp (b.initial s)).1
    dsimp [det] at hh ⊢
    linarith
  have hedge := b.edge_eq J
  have hstart := hs J
  have hend := hs (J+1)
  have hstep : det (C.direction r) (b.vertex (J+1)-u) =
      det (C.direction r) (b.vertex J-u)+(b.length J : ℤ)*det (C.direction r) (C.direction J) := by
    have he := congrArg (det (C.direction r)) hedge
    dsimp [det] at he ⊢
    nlinarith
  by_cases heq : C.direction r=C.direction J
  · have hsrev := ((paidRow _ _ _).mp (b.initial J)).2 _ ((paidRow _ _ _).mp (b.initial r)).1
    rw [ite_eq_left heq]
    have hh : det (C.direction r) (b.vertex r-u) = det (C.direction J) (b.vertex J-u) := by
      rw [heq] at hstart ⊢
      dsimp [det] at hsrev hstart ⊢
      linarith
    rw [hh,heq]
    constructor
    · change det (C.direction J) (b.vertex J-u)-
        det (C.direction (J-1)) (C.direction J)*det (C.direction J) (C.direction (J+1)) ≤ _
      dsimp [det]
      ring_nf
      rfl
    · have he : det (C.direction J) (b.vertex (J+1)-u) = det (C.direction J) (b.vertex J-u) := by
        rw [heq] at hstep
        have hz : det (C.direction J) (C.direction J)=0 := by dsimp [det];ring
        simpa [hz] using hstep
      have hcalc : det (C.direction J) (b.vertex (J+1)-u-
          det (C.direction (J-1)) (C.direction J) • C.direction (J+1)) =
          det (C.direction J) (b.vertex (J+1)-u)-facetDepth C J := by
        change _ = det (C.direction J) (b.vertex (J+1)-u)-
          det (C.direction (J-1)) (C.direction J)*det (C.direction J) (C.direction (J+1))
        dsimp [det];ring
      rw [hcalc,he]
  · rw [ite_eq_right heq,sub_zero]
    have hleft : det (C.direction r) (b.vertex J-u+
        det (C.direction J) (C.direction (J+1)) • C.direction (J-1)) =
        det (C.direction r) (b.vertex J-u)+
          det (C.direction J) (C.direction (J+1))*det (C.direction r) (C.direction (J-1)) := by
      simp [det];ring
    have hright : det (C.direction r) (b.vertex (J+1)-u-
        det (C.direction (J-1)) (C.direction J) • C.direction (J+1)) =
        det (C.direction r) (b.vertex (J+1)-u)-
          det (C.direction (J-1)) (C.direction J)*det (C.direction r) (C.direction (J+1)) := by
      simp [det];ring
    rw [hleft,hright]
    have hN' : (N : ℤ) ≤ b.length J := by exact_mod_cast hlen
    have hlen0 : (0 : ℤ) ≤ b.length J := by positivity
    constructor
    · by_cases hp : 0 ≤ det (C.direction r) (C.direction (J-1))
      · exact hstart.trans (le_add_of_nonneg_right (mul_nonneg (paidTurn C J).le hp))
      · have hw := left_shift_lowered_direction C J _ (paidDirectionMem C r) heq (lt_of_not_ge hp)
        have hh := (hN r).1
        have hprod : (b.length J : ℤ) ≤ -(b.length J : ℤ)*det (C.direction r) (C.direction J) := by
          nlinarith
        linarith
    · by_cases hd : det (C.direction r) (C.direction (J+1)) ≤ 0
      · have hturn : 0 ≤ det (C.direction (J-1)) (C.direction J) := by
          exact (show 0 < det (C.direction (J-1)) (C.direction J) by simpa using paidTurn C (J-1)).le
        have hp := mul_nonpos_of_nonneg_of_nonpos hturn hd
        linarith
      · have hw := right_shift_lowered_direction C J _ (paidDirectionMem C r) heq (lt_of_not_ge hd)
        have hh := (hN r).2
        have hprod : (b.length J : ℤ) ≤ (b.length J : ℤ)*det (C.direction r) (C.direction J) := by
          nlinarith
        linarith

private theorem facet_late_endpoints {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) :
    ∃ jG : ℕ, ∀ j ≥ jG,
      (W.boundary (G.subsequence (L.index j))).vertex G.J-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
          det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1) ∈ facetU W G L j ∧
      (W.boundary (G.subsequence (L.index j))).vertex (G.J+1)-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i-
          det (C.direction (G.J-1)) (C.direction G.J) • C.direction (G.J+1) ∈ facetU W G L j := by
  obtain ⟨N,hN⟩ := facet_uniform_endpoint_bound C G.J
  refine ⟨N,?_⟩
  intro j hj
  have hlen : N ≤ (W.boundary (G.subsequence (L.index j))).length G.J :=
    hj.trans ((L.strict.id_le j).trans (G.growing.id_le (L.index j)))
  have hh := facet_shifted_endpoints_support C (W.boundary (G.subsequence (L.index j)))
    ((W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i) G.J N hN hlen
  exact ⟨fun r => (hh r).1,fun r => (hh r).2⟩

private theorem facet_late_strict {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (E : ℕ → Finset Lattice)
    (hE : ∀ j, (E j : Set Lattice)=facetU W G L j) :
    ∃ jG : ℕ, ∀ j ≥ jG, W.normalised (G.subsequence (L.index j)) ⊂ E j := by
  obtain ⟨jG,hjG⟩ := facet_late_endpoints W G L
  refine ⟨jG,?_⟩
  intro j hj
  apply Finset.ssubset_iff_subset_ne.mpr
  have hAE : W.normalised (G.subsequence (L.index j)) ⊆ E j := by
    intro z hz
    change z ∈ (E j : Set Lattice)
    rw [hE j]
    exact facet_old_subset W G L j hz
  refine ⟨hAE,?_⟩
  intro heq
  have he := (hjG j hj).1
  rw [← hE j] at he
  have he' : (W.boundary (G.subsequence (L.index j))).vertex G.J-
      (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
        det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1) ∈
      W.normalised (G.subsequence (L.index j)) := by rw [heq];exact he
  obtain ⟨q,hq,hqeq⟩ := Finset.mem_image.mp he'
  have hs := ((paidRow _ _ _).mp ((W.boundary (G.subsequence (L.index j))).initial G.J)).2 q hq
  have hd := facet_depth_positive C G.J
  change 0 < det (C.direction (G.J-1)) (C.direction G.J)*
    det (C.direction G.J) (C.direction (G.J+1)) at hd
  have hh := congrArg (det (C.direction G.J)) hqeq
  dsimp [det] at hs hh hd
  nlinarith

private theorem facet_unchanged_rows {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice)=facetU W G L j) (r : ℤ)
    (hne : C.direction r ≠ C.direction G.J) :
    supportRow (W.normalised (G.subsequence (L.index j))) (C.direction r) ⊆
      supportRow E (C.direction r) := by
  intro a ha
  obtain ⟨haA,hmin⟩ := (paidRow _ _ _).mp ha
  have hAE : W.normalised (G.subsequence (L.index j)) ⊆ E := by
    intro z hz
    change z ∈ (E : Set Lattice)
    rw [hE]
    exact facet_old_subset W G L j hz
  apply (paidRow _ _ _).mpr
  refine ⟨hAE haA,?_⟩
  intro z hz
  have hz' : z ∈ facetU W G L j := by rw [← hE];exact hz
  have hb := hz' r
  rw [ite_eq_right hne,sub_zero] at hb
  have hv : (W.boundary (G.subsequence (L.index j))).vertex r-
      (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i ∈
      W.normalised (G.subsequence (L.index j)) := by
    refine Finset.mem_image.mpr ⟨_,((paidRow _ _ _).mp
      ((W.boundary (G.subsequence (L.index j))).initial r)).1,?_⟩
    simp [sub_eq_add_neg]
  exact (hmin _ hv).trans hb

local macro "paidSegmentFace" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.HullBoundary).num 0 ++ `ConvexNivat.Colle.hb_segment_face))

private theorem parallel_strip_in_hull (Q : Set RealPlane) (hQ : Convex ℝ Q)
    (a b c e p w d x : RealPlane) (l k : ℝ)
    (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (he : e ∈ Q)
    (hab : b-a=l • w) (hce : e-c=k • w) (hl : 0 < l) (hk : 0 < k)
    (hpw : 0 < realDet p w) (hwd : 0 < realDet w d)
    (hpc : realDet p (c-a)=0) (hde : realDet d (e-b)=0)
    (hdepth : 0 < realDet w (a-c))
    (hlo : 0 ≤ realDet w (x-c)) (hhi : realDet w (x-a) ≤ 0)
    (hleft : 0 ≤ realDet p (x-a)) (hright : 0 ≤ realDet d (x-b)) : x ∈ Q := by
  let t : ℝ := realDet w (a-x)/realDet w (a-c)
  have hnum : realDet w (a-x) = -realDet w (x-a) := by dsimp [realDet];ring
  have ht0 : 0 ≤ t := div_nonneg (by rw [hnum];linarith) hdepth.le
  have ht1 : t ≤ 1 := by
    apply (div_le_one hdepth).mpr
    have heq : realDet w (a-x)+realDet w (x-c)=realDet w (a-c) := by dsimp [realDet];ring
    linarith
  have htD : t*realDet w (a-c)=realDet w (a-x) := div_mul_cancel₀ _ hdepth.ne'
  let xa : RealPlane := (1-t) • a+t • c
  let bt : RealPlane := (1-t) • b+t • e
  let kt : ℝ := (1-t)*l+t*k
  have hat : xa ∈ Q := hQ.segment_subset ha hc ⟨1-t,t,by linarith,ht0,by ring,rfl⟩
  have hbt : bt ∈ Q := hQ.segment_subset hb he ⟨1-t,t,by linarith,ht0,by ring,rfl⟩
  have hkt : 0 < kt := by
    by_cases ht : t=1
    · simpa [kt,ht] using hk
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hl) (mul_nonneg ht0 hk.le)
  have hstep : bt=xa+kt • w := by
    dsimp [xa,bt,kt]
    linear_combination (norm := module) (1-t) • hab+t • hce
  have hleft' : 0 ≤ realDet p (x-xa) := by
    have hid : realDet p (x-xa)=realDet p (x-a)-t*realDet p (c-a) := by
      dsimp [xa,realDet];ring
    rw [hid,hpc,mul_zero,sub_zero]
    exact hleft
  have hright' : 0 ≤ realDet d (x-(xa+kt • w)) := by
    rw [← hstep]
    have hid : realDet d (x-bt)=realDet d (x-b)-t*realDet d (e-b) := by
      dsimp [bt,realDet];ring
    rw [hid,hde,mul_zero,sub_zero]
    exact hright
  have hzero : realDet w (x-xa)=0 := by
    have hid : realDet w (x-xa)=realDet w (x-a)+t*realDet w (a-c) := by
      dsimp [xa,realDet];ring
    rw [hid,htD,hnum]
    ring
  have hseg := paidSegmentFace xa p w d x kt hkt hpw hwd hleft' hright' hzero
  rw [← hstep] at hseg
  exact hQ.segment_subset hat hbt hseg

local macro "paidTranslateHull" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_translate_hull))

private theorem aligned_same_support_height {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice)
    (r s : ℤ) (he : C.direction r=C.direction s) :
    det (C.direction r) (b.vertex r-u)=det (C.direction s) (b.vertex s-u) := by
  have h1 := ((paidRow _ _ _).mp (b.initial r)).2 _ ((paidRow _ _ _).mp (b.initial s)).1
  have h2 := ((paidRow _ _ _).mp (b.initial s)).2 _ ((paidRow _ _ _).mp (b.initial r)).1
  rw [he] at h1 ⊢
  dsimp [det] at h1 h2 ⊢
  linarith

private theorem translated_aligned_hull {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) :
    windowHull (windowTranslate B (-u)) =
      {x : RealPlane | ∀ r : ℤ,
        (det (C.direction r) (b.vertex r-u) : ℝ) ≤ realDet (embed (C.direction r)) x} := by
  ext x
  rw [paidTranslateHull B (-u) x,b.hull_eq]
  constructor <;> intro h r
  · have hh := h r
    dsimp [realDet,embed] at hh
    simp only [Int.cast_neg] at hh
    simp only [realDet,embed,det,Prod.fst_sub,Prod.snd_sub,Int.cast_sub,Int.cast_mul]
    linarith
  · have hh := h r
    simp only [realDet,embed,det,Prod.fst_sub,Prod.snd_sub,Int.cast_sub,Int.cast_mul] at hh
    dsimp [realDet,embed]
    simp only [Int.cast_neg]
    linarith

private def facetRealSet {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) (J : ℤ) : Set RealPlane :=
  {x | ∀ r : ℤ,
    ((det (C.direction r) (b.vertex r-u)-
      (if C.direction r=C.direction J then facetDepth C J else 0) : ℤ) : ℝ) ≤
      realDet (embed (C.direction r)) x}

private theorem facet_real_convex {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) (J : ℤ) :
    Convex ℝ (facetRealSet C b u J) := by
  intro x hx y hy a d ha hd had r
  let c : ℤ := det (C.direction r) (b.vertex r-u)-
    (if C.direction r=C.direction J then facetDepth C J else 0)
  have hx' := hx r
  have hy' := hy r
  change (c : ℝ) ≤ _ at hx' hy' ⊢
  have he : realDet (embed (C.direction r)) (a • x+d • y) =
      a*realDet (embed (C.direction r)) x+d*realDet (embed (C.direction r)) y := by
    simp [realDet];ring
  rw [he]
  have hc : a*(c : ℝ)+d*c=c := by rw [← add_mul,had,one_mul]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'),mul_nonneg hd (sub_nonneg.mpr hy')]

private theorem facet_hull_subset_real {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice)=facetU W G L j) :
    windowHull E ⊆ facetRealSet C (W.boundary (G.subsequence (L.index j)))
      ((W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i) G.J := by
  apply convexHull_min _ (facet_real_convex _ _ _ _)
  rintro _ ⟨z,hz,rfl⟩ r
  have hz' : z ∈ facetU W G L j := by rw [← hE];exact hz
  have hh := hz' r
  have hc := (show ((det (C.direction r)
      ((W.boundary (G.subsequence (L.index j))).vertex r-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i)-
      (if C.direction r=C.direction G.J then facetDepth C G.J else 0) : ℤ) : ℝ) ≤
      (det (C.direction r) z : ℝ) by exact_mod_cast hh)
  simpa [realDet,embed,det] using hc

private theorem facet_real_subset_hull {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice)=facetU W G L j)
    (hc : (W.boundary (G.subsequence (L.index j))).vertex G.J-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
          det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1) ∈ E)
    (he : (W.boundary (G.subsequence (L.index j))).vertex (G.J+1)-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i-
          det (C.direction (G.J-1)) (C.direction G.J) • C.direction (G.J+1) ∈ E)
    (k : ℤ) (hk : 0 < k)
    (hce : ((W.boundary (G.subsequence (L.index j))).vertex (G.J+1)-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i-
          det (C.direction (G.J-1)) (C.direction G.J) • C.direction (G.J+1))-
      ((W.boundary (G.subsequence (L.index j))).vertex G.J-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
          det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1)) =
        k • C.direction G.J) :
    facetRealSet C (W.boundary (G.subsequence (L.index j)))
      ((W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i) G.J ⊆ windowHull E := by
  let b := W.boundary (G.subsequence (L.index j))
  let u : Lattice := (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i
  let p := C.direction (G.J-1)
  let w := C.direction G.J
  let d := C.direction (G.J+1)
  let a := b.vertex G.J-u
  let q := b.vertex (G.J+1)-u
  let c := a+det w d • p
  let e := q-det p w • d
  have hpw : 0 < det p w := by simpa [p,w] using paidTurn C (G.J-1)
  have hwd : 0 < det w d := paidTurn C G.J
  have hpne : p ≠ w := by intro hh;rw [hh] at hpw;dsimp [det] at hpw;nlinarith
  have hdne : d ≠ w := by intro hh;rw [hh] at hwd;dsimp [det] at hwd;nlinarith
  have hAE : W.normalised (G.subsequence (L.index j)) ⊆ E := by
    intro z hz
    change z ∈ (E : Set Lattice)
    rw [hE]
    exact facet_old_subset W G L j hz
  have hvertex (r : ℤ) : b.vertex r-u ∈ E := by
    apply hAE
    refine Finset.mem_image.mpr ⟨_,((paidRow _ _ _).mp (b.initial r)).1,?_⟩
    simp [u,sub_eq_add_neg]
  have hab : q-a=(b.length G.J : ℤ) • w := by
    dsimp [q,a]
    simpa using b.edge_eq G.J
  have hcast (q a v : Lattice) (s : ℤ) (hs : q-a=s • v) :
      embed q-embed a=(s : ℝ) • embed v := by
    rw [← embed_sub,hs]
    ext <;> simp [embed]
  have hdif (v z : Lattice) (x : RealPlane) :
      realDet (embed v) (x-embed z)=realDet (embed v) x-(det v z : ℝ) := by
    simp [realDet,embed,det];ring
  intro x hx
  by_cases hold : 0 ≤ realDet (embed w) (x-embed a)
  · apply (convexHull_mono (Set.image_mono hAE))
    change x ∈ windowHull (windowTranslate _ (-u))
    rw [translated_aligned_hull C b u]
    intro r
    by_cases hr : C.direction r=w
    · have hh := aligned_same_support_height C b u r G.J hr
      rw [hh,hr]
      change (det w a : ℝ) ≤ realDet (embed w) x
      rw [hdif] at hold
      linarith
    · have hh := hx r
      change ((det (C.direction r) (b.vertex r-u)-
        (if C.direction r=w then facetDepth C G.J else 0) : ℤ) : ℝ) ≤ _ at hh
      simpa [hr] using hh
  · apply parallel_strip_in_hull (windowHull E) (windowHull_convex E)
      (embed a) (embed q) (embed c) (embed e) (embed p) (embed w) (embed d) x
      (b.length G.J : ℝ) (k : ℝ)
      (window_mem_hull _ (hvertex G.J)) (window_mem_hull _ (hvertex (G.J+1)))
      (window_mem_hull _ hc) (window_mem_hull _ he)
    · exact_mod_cast hcast q a w (b.length G.J) hab
    · exact hcast e c w k hce
    · exact_mod_cast b.length_positive G.J
    · exact_mod_cast hk
    · have hh : realDet (embed p) (embed w)=(det p w : ℝ) := by simp [realDet,embed,det]
      rw [hh];exact_mod_cast hpw
    · have hh : realDet (embed w) (embed d)=(det w d : ℝ) := by simp [realDet,embed,det]
      rw [hh];exact_mod_cast hwd
    · dsimp [c,realDet,embed]
      simp only [Int.cast_add,Int.cast_mul]
      ring
    · dsimp [e,realDet,embed]
      simp only [Int.cast_sub,Int.cast_mul]
      ring
    · have hh : realDet (embed w) (embed a-embed c)=(det p w*det w d : ℤ) := by
        dsimp [c,realDet,embed,det]
        push_cast
        ring
      rw [hh];exact_mod_cast mul_pos hpw hwd
    · have hh := hx G.J
      simp only [ite_true] at hh
      change ((det w a-facetDepth C G.J : ℤ) : ℝ) ≤ realDet (embed w) x at hh
      have hcd : det w c=det w a-facetDepth C G.J := by
        change det w (a+det w d • p)=det w a-det p w*det w d
        dsimp [det];ring
      rw [hdif,hcd]
      exact sub_nonneg.mpr hh
    · exact (lt_of_not_ge hold).le
    · have hh := hx (G.J-1)
      change ((det p (b.vertex (G.J-1)-u)-
        (if p=w then facetDepth C G.J else 0) : ℤ) : ℝ) ≤ _ at hh
      rw [ite_eq_right hpne,sub_zero] at hh
      have hpa : det p (b.vertex (G.J-1)-u)=det p a := by
        have hed := b.edge_eq (G.J-1)
        have hd := congrArg (det p) hed
        simp only [sub_add_cancel] at hd
        dsimp [a,det] at hd ⊢
        nlinarith
      rw [hpa] at hh
      rw [hdif]
      exact sub_nonneg.mpr hh
    · have hh := hx (G.J+1)
      change ((det d q-(if d=w then facetDepth C G.J else 0) : ℤ) : ℝ) ≤ _ at hh
      rw [ite_eq_right hdne,sub_zero] at hh
      rw [hdif]
      exact sub_nonneg.mpr hh

local macro "paidSupportNotInterior" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_support_not_interior))

private theorem facet_finite_halfplanes {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) (J : ℤ)
    (x : RealPlane) : x ∈ facetRealSet C b u J ↔
    ∀ k : Fin (2*m),
      ((det (C.direction k.val) (b.vertex k.val-u)-
        (if C.direction k.val=C.direction J then facetDepth C J else 0) : ℤ) : ℝ) ≤
        realDet (embed (C.direction k.val)) x := by
  constructor
  · intro h k;exact h k.val
  · intro h r
    obtain ⟨k,hk⟩ := (C.covers _).mp (paidDirectionMem C r)
    have hs := aligned_same_support_height C b u k.val r hk
    have hh := h k
    rw [hs,hk] at hh
    exact hh

private theorem facet_active_halfplane {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) (J : ℤ)
    (x : RealPlane) (hx : x ∈ facetRealSet C b u J)
    (hni : x ∉ interior (facetRealSet C b u J)) :
    ∃ r : ℤ, ((det (C.direction r) (b.vertex r-u)-
      (if C.direction r=C.direction J then facetDepth C J else 0) : ℤ) : ℝ) =
      realDet (embed (C.direction r)) x := by
  by_contra! hne
  let V : Set RealPlane := ⋂ k : Fin (2*m),
    {y | ((det (C.direction k.val) (b.vertex k.val-u)-
      (if C.direction k.val=C.direction J then facetDepth C J else 0) : ℤ) : ℝ) <
      realDet (embed (C.direction k.val)) y}
  have hopen : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_lt continuous_const
    change Continuous (fun y : RealPlane =>
      (embed (C.direction k.val)).1*y.2-(embed (C.direction k.val)).2*y.1)
    fun_prop
  have hsub : V ⊆ facetRealSet C b u J := by
    intro y hy
    apply (facet_finite_halfplanes C b u J y).mpr
    intro k
    exact (Set.mem_iInter.mp hy k).le
  apply hni
  apply interior_maximal hsub hopen
  apply Set.mem_iInter.mpr
  intro k
  exact lt_of_le_of_ne (hx k.val) (hne k.val)

private theorem facet_no_new_directions {S B E : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (b : AlignedBoundary C B) (u : Lattice) (J : ℤ)
    (hEC : LatticeConvex E) (harea : (interior (windowHull E)).Nonempty)
    (hhull : windowHull E=facetRealSet C b u J) : edgeDirections E ⊆ edgeDirections S := by
  obtain ⟨F⟩ := finite_window_support_polygon E hEC harea
  intro delta hd
  rw [F.covers] at hd
  obtain ⟨k,rfl⟩ := hd
  let a := F.vertex k.val
  let q := F.vertex (k.val+1)
  let delta := F.direction k.val
  let x : RealPlane := (1/2 : ℝ) • embed a+(1/2 : ℝ) • embed q
  have ha : embed a ∈ windowHull E := window_mem_hull E (F.vertex_mem _)
  have hq : embed q ∈ windowHull E := window_mem_hull E (F.vertex_mem _)
  have hx : x ∈ windowHull E := (windowHull_convex E).segment_subset ha hq
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  have heq : embed q-embed a=(F.length k.val : ℝ) • embed delta := by
    rw [← embed_sub,F.edge_eq]
    ext <;> simp [embed,delta]
  have hzero : realDet (embed delta) (x-embed a)=0 := by
    have hid : realDet (embed delta) (x-embed a)=
        (1/2 : ℝ)*realDet (embed delta) (embed q-embed a) := by dsimp [x,realDet];ring
    rw [hid,heq]
    dsimp [realDet]
    ring
  have hni : x ∉ interior (windowHull E) :=
    paidSupportNotInterior _ delta a (F.primitive _) (F.supports _) x hzero
  obtain ⟨r,hr⟩ := facet_active_halfplane C b u J x (hhull ▸ hx) (hhull ▸ hni)
  let gamma := C.direction r
  let c : ℝ := ((det gamma (b.vertex r-u)-
    (if gamma=C.direction J then facetDepth C J else 0) : ℤ) : ℝ)
  have haG : c ≤ realDet (embed gamma) (embed a) := (hhull ▸ ha) r
  have hqG : c ≤ realDet (embed gamma) (embed q) := (hhull ▸ hq) r
  have hmid : c=(1/2 : ℝ)*realDet (embed gamma) (embed a)+
      (1/2 : ℝ)*realDet (embed gamma) (embed q) := by
    calc
      c = realDet (embed gamma) x := hr
      _ = _ := by dsimp [x,realDet];ring
  have hga : realDet (embed gamma) (embed a)=c := by linarith
  have hgq : realDet (embed gamma) (embed q)=c := by linarith
  have hgzero : realDet (embed gamma) (embed q-embed a)=0 := by
    have hid : realDet (embed gamma) (embed q-embed a)=
        realDet (embed gamma) (embed q)-realDet (embed gamma) (embed a) := by dsimp [realDet];ring
    rw [hid,hga,hgq];ring
  rw [heq] at hgzero
  have hdetR : realDet (embed gamma) (embed delta)=0 := by
    have hid : realDet (embed gamma) ((F.length k.val : ℝ) • embed delta)=
        (F.length k.val : ℝ)*realDet (embed gamma) (embed delta) := by dsimp [realDet];ring
    rw [hid] at hgzero
    exact (mul_eq_zero.mp hgzero).resolve_left (by exact_mod_cast (F.length_positive _).ne')
  have hdet : det delta gamma=0 := by
    have hh : realDet (embed gamma) (embed delta)=(det gamma delta : ℝ) := by simp [realDet,embed,det]
    rw [hh] at hdetR
    have hz : det gamma delta=0 := by exact_mod_cast hdetR
    dsimp [det] at hz ⊢
    linarith
  rcases paidParallel delta gamma (F.primitive _) (C.primitive r) hdet with hsame | hopp
  · change delta ∈ edgeDirections S
    rw [← hsame]
    exact paidDirectionMem C r
  · obtain ⟨y,hy⟩ := harea
    have hyE := interior_subset hy
    have hpos := F.supports (k.val : ℤ) y hyE
    have hg : c ≤ realDet (embed gamma) y := (hhull ▸ hyE) r
    have hz : realDet (embed delta) (y-embed a)=0 := by
      rw [← hga,hopp] at hg
      dsimp [realDet,embed] at hg hpos ⊢
      push_cast at hg
      linarith
    exact False.elim (paidSupportNotInterior _ delta a (F.primitive _) (F.supports _) y hz hy)

private theorem lattice_segment_support_card (E : Finset Lattice) (w c e : Lattice)
    (hw : Primitive w) (hEC : LatticeConvex E) (hc : c ∈ E) (he : e ∈ E)
    (k : ℤ) (hk : 0 ≤ k) (hce : e-c=k • w)
    (hmin : ∀ z ∈ E, det w c ≤ det w z) :
    k.toNat+1 ≤ (supportRow E w).card := by
  classical
  let f : ℕ → Lattice := fun t => c+(t : ℤ) • w
  have hinj : Function.Injective f := by
    intro a b hab
    have heq : (a : ℤ) • w=(b : ℤ) • w := add_left_cancel hab
    exact_mod_cast (smul_left_injective ℤ (primitive_ne_zero w hw) heq)
  have hsub : (Finset.range (k.toNat+1)).image f ⊆ supportRow E w := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
    have htk : (t : ℤ) ≤ k := by have h := Finset.mem_range.mp ht;omega
    have heq : e=c+k • w := by linear_combination (norm := module) hce
    have hseg : embed (f t) ∈ segment ℝ (embed c) (embed e) := by
      rw [heq]
      have hh := ((primitive_row_coordinates w hw).2.2 c 0 k hk (f t)).mpr
        ⟨t,by positivity,htk,rfl⟩
      simpa using hh
    have htE : f t ∈ E := (hEC _).mp
      ((windowHull_convex E).segment_subset (window_mem_hull E hc) (window_mem_hull E he) hseg)
    apply (paidRow E w (f t)).mpr
    refine ⟨htE,?_⟩
    intro z hz
    have hh : det w (f t)=det w c := by dsimp [f,det];ring
    rw [hh]
    exact hmin z hz
  have hh := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj,Finset.card_range] at hh

local macro "paidEndpointData" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.CofinalExtensionRoute).num 0 ++ `ConvexNivat.Colle.cofinal_parallel_facet_endpoint_data))
local macro "paidTranslatedEnvelope" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_translate_enveloped))

private theorem facet_envelope_from_endpoints {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (L : NormalisedWindowLimit W G) (j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice)=facetU W G L j)
    (hc : (W.boundary (G.subsequence (L.index j))).vertex G.J-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
          det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1) ∈ E)
    (he : (W.boundary (G.subsequence (L.index j))).vertex (G.J+1)-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i-
          det (C.direction (G.J-1)) (C.direction G.J) • C.direction (G.J+1) ∈ E)
    (k : ℤ) (hk : 0 < k)
    (hce : ((W.boundary (G.subsequence (L.index j))).vertex (G.J+1)-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i-
          det (C.direction (G.J-1)) (C.direction G.J) • C.direction (G.J+1))-
      ((W.boundary (G.subsequence (L.index j))).vertex G.J-
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
          det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1)) =
        k • C.direction G.J)
    (hcard : ((supportRow S (C.direction G.J)).card : ℤ) ≤ k+1) : EnvelopedWindow S E := by
  have hA : EnvelopedWindow S (W.normalised (G.subsequence (L.index j))) :=
    paidTranslatedEnvelope S _ (W.A_enveloped _) _
  have hAE : W.normalised (G.subsequence (L.index j)) ⊆ E := by
    intro z hz
    change z ∈ (E : Set Lattice)
    rw [hE]
    exact facet_old_subset W G L j hz
  have hEC := facet_lattice_convex W G L j E hE
  have harea : (interior (windowHull E)).Nonempty := hA.2.2.1.mono
    (interior_mono (convexHull_mono (Set.image_mono hAE)))
  have hhull : windowHull E=facetRealSet C (W.boundary (G.subsequence (L.index j)))
      ((W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i) G.J :=
    Set.Subset.antisymm (facet_hull_subset_real W G L j E hE)
      (facet_real_subset_hull W G L j E hE hc he k hk hce)
  have hnew := facet_no_new_directions C _ _ G.J hEC harea hhull
  have hfinite : (edgeDirections S).Finite := by
    have heq : edgeDirections S=Set.range (fun r : Fin (2*m) => C.direction r.val) := by
      ext v;exact C.covers v
    rw [heq]
    exact Set.finite_range _
  have hAedges : edgeDirections (W.normalised (G.subsequence (L.index j)))=edgeDirections S :=
    Set.eq_of_subset_of_ncard_le (fun d hd => (hA.2.2.2.1 d hd).1) hA.2.2.2.2.ge hfinite
  have hsupp (delta : Lattice) (hd : delta ∈ edgeDirections S) :
      (supportRow S delta).card ≤ (supportRow E delta).card := by
    by_cases heq : delta=C.direction G.J
    · subst delta
      apply (show (supportRow S (C.direction G.J)).card ≤ k.toNat+1 by omega).trans
      apply lattice_segment_support_card E (C.direction G.J) _ _ (C.primitive _) hEC hc he k hk.le hce
      intro z hz
      have hz' : z ∈ facetU W G L j := by rw [← hE];exact hz
      have hh := hz' G.J
      simp only [ite_true] at hh
      have hcalc : det (C.direction G.J)
          ((W.boundary (G.subsequence (L.index j))).vertex G.J-
            (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i+
              det (C.direction G.J) (C.direction (G.J+1)) • C.direction (G.J-1)) =
          det (C.direction G.J)
            ((W.boundary (G.subsequence (L.index j))).vertex G.J-
              (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i)-facetDepth C G.J := by
        change _ = _-det (C.direction (G.J-1)) (C.direction G.J)*det (C.direction G.J) (C.direction (G.J+1))
        simp [det];ring
      rw [hcalc]
      exact hh
    · obtain ⟨r,hr⟩ := (C.covers delta).mp hd
      have hda : delta ∈ edgeDirections (W.normalised (G.subsequence (L.index j))) := hAedges.symm ▸ hd
      apply ((hA.2.2.2.1 delta hda).2).trans
      rw [← hr]
      exact Finset.card_le_card (facet_unchanged_rows W G L j E hE r.val (by rw [hr];exact heq))
  have heq : edgeDirections E=edgeDirections S := by
    apply Set.Subset.antisymm hnew
    intro delta hd
    exact ⟨hd.1,harea,hd.2.2.trans (hsupp delta hd)⟩
  refine ⟨hA.1.mono hAE,hEC,harea,?_,?_⟩
  · intro delta hd
    exact ⟨hnew hd,hsupp delta (hnew hd)⟩
  · rw [heq]

private theorem independent_facet_geometry
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
    ∃ E : ℕ → Finset Lattice,
      (∀ j : ℕ, (E j : Set Lattice) = facetU W G L j) ∧
      ∃ jG : ℕ, ∀ j ≥ jG, EnvelopedWindow S (E j) ∧
        W.normalised (G.subsequence (L.index j)) ⊂ E j := by
  obtain ⟨E,hE,_⟩ := facet_finite_family W G L
  obtain ⟨a,κ,hfix,hend,_,jL,hjL⟩ := paidEndpointData ξ xper alphabet halphabet S hS
    m C i hxper hperiod W G P hP hcarrier hweak harc hanchor L hall
  obtain ⟨jV,hjV⟩ := facet_late_endpoints W G L
  obtain ⟨jS,hjS⟩ := facet_late_strict W G L E hE
  refine ⟨E,hE,max jL (max jV jS),?_⟩
  intro j hj
  have hjL' : jL ≤ j := (le_max_left _ _).trans hj
  have hjV' : jV ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hjS' : jS ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  refine ⟨?_,hjS j hjS'⟩
  obtain ⟨hc,he⟩ := hjV j hjV'
  rw [← hE j] at hc he
  have hcard := hjL j hjL'
  have htwo := (paidDirectionMem C G.J).2.2
  have hk : 0 < ((W.boundary (G.subsequence (L.index j))).length G.J : ℤ)+κ := by
    have hh : (2 : ℤ) ≤ (supportRow S (C.direction G.J)).card := by exact_mod_cast htwo
    omega
  have hedge := hend j
  rw [← hfix j] at hedge
  exact facet_envelope_from_endpoints W G L j (E j) (hE j) hc he
    (((W.boundary (G.subsequence (L.index j))).length G.J : ℤ)+κ) hk hedge hcard

end
end ConvexNivat.Colle
