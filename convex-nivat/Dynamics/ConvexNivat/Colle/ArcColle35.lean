import ConvexNivat.Colle.ArcUnion

namespace ConvexNivat.Colle
noncomputable section

local macro "paidEnlargementAbove" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.Enlargement).num 0 ++ `ConvexNivat.Colle.eg_enlargement_above))
local macro "paidEnlargementLower" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.Enlargement).num 0 ++ `ConvexNivat.Colle.eg_enlargement_lower))

private theorem colle35_enlargement_zero {v w : Lattice} (P : Region v w) :
    P.enlargement 0 = P.lattice := by
  apply Set.Subset.antisymm
  · intro z hz
    exact paidEnlargementAbove P 0 z hz (by simpa using paidEnlargementLower P 0 z hz)
  · intro z hz
    exact ⟨z,hz,0,by simp,Or.inl hz⟩

private theorem colle35_normalised_agreement {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) (j : ℕ) :
    AgreesOn (W.shiftedField (G.subsequence j))
      (translate ((G.phase:ℤ) • C.direction i) xper)
      (W.normalised (G.subsequence j) : Set Lattice) := by
  intro z hz
  obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp hz
  have heq : z + (W.normalise (G.subsequence j):ℤ) • C.direction i = q := by
    linear_combination (norm := module) -hqz
  have ha := (W.maximal (G.subsequence j)).2.2.2.1 q hq
  have hp := congrFun (G.same_phase j) z
  calc
    W.shiftedField (G.subsequence j) z = translate (W.shift (G.subsequence j)) ξ q := by
      dsimp [AlternatingWindows.shiftedField,translate]
      congr 1
      linear_combination (norm := module) heq
    _ = xper q := ha
    _ = translate ((W.normalise (G.subsequence j):ℤ) • C.direction i) xper z := by
      simp only [translate,heq]
    _ = translate ((G.phase:ℤ) • C.direction i) xper z := hp

private theorem colle35_limit_agrees {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (s : ℕ → ℕ) (hs : StrictMono s) (ϑ : Configuration ℤ)
    (hlim : PointwiseLimit (fun j => W.shiftedField (G.subsequence (s j))) ϑ) :
    AgreesOn ϑ (translate ((G.phase:ℤ) • C.direction i) xper) (normalisedUnion W G) := by
  intro z hz
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
  obtain ⟨N,hN⟩ := hlim z
  let k := max N j
  have hmono : Monotone (fun t => W.normalised (G.subsequence t)) := monotone_nat_of_le_succ G.nested
  have hjk : j ≤ s k := (le_max_right N j).trans (hs.id_le k)
  have hag := colle35_normalised_agreement W G (s k) z (hmono hjk hj)
  exact (hN k (le_max_left N j)).symm.trans hag

private theorem colle35_limit_selection (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) {xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ ϑ ∈ OrbitClosure ξ,
      PointwiseLimit (fun j => W.shiftedField (G.subsequence (s j))) ϑ ∧
      AgreesOn ϑ (translate ((G.phase:ℤ) • C.direction i) xper) (normalisedUnion W G) := by
  obtain ⟨s,hs,ϑ,hϑ,hlim⟩ := orbitClosure_pointwise_subsequence ξ A hA
    (fun j => W.shiftedField (G.subsequence j))
    (fun j => orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _)
  exact ⟨s,hs,ϑ,hϑ,hlim,colle35_limit_agrees W G s hs ϑ hlim⟩

private theorem colle35_first_failure {v w : Lattice} (P : Region v w)
    (ϑ y : Configuration ℤ) (hzero : AgreesOn ϑ y P.lattice)
    (hfail : ∃ n, ¬ AgreesOn ϑ y (P.enlargement n)) :
    ∃ n, AgreesOn ϑ y (P.enlargement n) ∧ ¬ AgreesOn ϑ y (P.enlargement (n+1)) := by
  classical
  let K := Nat.find hfail
  have hK : ¬ AgreesOn ϑ y (P.enlargement K) := Nat.find_spec hfail
  have hKpos : 0 < K := by
    by_contra! h
    have he : K=0 := by omega
    rw [he,colle35_enlargement_zero] at hK
    exact hK hzero
  refine ⟨K-1,?_,?_⟩
  · by_contra h
    exact Nat.find_min hfail (by omega : K-1<K) h
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ K)] using hK

local macro "paidColle35HullImage" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.PositionedWindows).num 0 ++ `ConvexNivat.Colle.sg_hull_image))

private theorem colle35_translate_hull (T : Finset Lattice) (u : Lattice) (x : RealPlane) :
    x ∈ windowHull (windowTranslate T u) ↔ x-embed u ∈ windowHull T := by
  have he : windowTranslate T u = T.image (fun z => u+(1:ℤ)•z) := by
    simp only [windowTranslate,one_smul,add_comm]
  rw [he,paidColle35HullImage T u 1]
  simp only [Int.cast_one,one_smul,Set.mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x-embed u,hx,by abel⟩


local macro "paidColle35RowMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.AlternatingAssembly).num 0 ++ `ConvexNivat.Colle.row_membership))

private theorem colle35_translate_row (T : Finset Lattice) (u d : Lattice) :
    supportRow (windowTranslate T u) d = windowTranslate (supportRow T d) u := by
  have he : ∀ p q : Lattice, det d (p+u) ≤ det d (q+u) ↔ det d p ≤ det d q := by
    intro p q
    have hp : det d (p+u)=det d p+det d u := by simp [det];ring
    have hq : det d (q+u)=det d q+det d u := by simp [det];ring
    rw [hp,hq,add_le_add_iff_right]
  ext z
  constructor
  · intro hz
    obtain ⟨hzT,hmin⟩ := (paidColle35RowMem _ d z).mp hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hzT
    refine Finset.mem_image.mpr ⟨q,(paidColle35RowMem _ d q).mpr ⟨hq,?_⟩,rfl⟩
    intro p hp
    exact (he q p).mp (hmin (p+u) (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
  · intro hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hqT,hmin⟩ := (paidColle35RowMem _ d q).mp hq
    apply (paidColle35RowMem _ d (q+u)).mpr
    refine ⟨Finset.mem_image.mpr ⟨q,hqT,rfl⟩,?_⟩
    intro p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    exact (he q r).mpr (hmin r hr)

private theorem colle35_translate_enveloped (S T : Finset Lattice) (hT : EnvelopedWindow S T)
    (u : Lattice) : EnvelopedWindow S (windowTranslate T u) := by
  have hmem (z : Lattice) : z ∈ windowTranslate T u ↔ z-u ∈ T := by
    constructor
    · intro hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      simpa using hq
    · intro hz
      exact Finset.mem_image.mpr ⟨z-u,hz,by simp⟩
  have hconv : LatticeConvex (windowTranslate T u) := by
    intro z
    rw [colle35_translate_hull,← embed_sub,hT.2.1,hmem]
  have harea : (interior (windowHull (windowTranslate T u))).Nonempty := by
    obtain ⟨x,hx⟩ := hT.2.2.1
    have hhull : windowHull (windowTranslate T u) =
        (Homeomorph.addRight (-embed u)) ⁻¹' windowHull T := by
      ext y
      change (y ∈ windowHull (windowTranslate T u)) ↔ y + -embed u ∈ windowHull T
      simpa only [sub_eq_add_neg] using colle35_translate_hull T u y
    refine ⟨x+embed u,?_⟩
    rw [hhull,← (Homeomorph.addRight (-embed u)).preimage_interior]
    change x+embed u+-embed u ∈ interior (windowHull T)
    simpa using hx
  have hc (d : Lattice) : (supportRow (windowTranslate T u) d).card = (supportRow T d).card := by
    rw [colle35_translate_row,windowTranslate,Finset.card_image_of_injective _ (add_left_injective u)]
  have he : edgeDirections (windowTranslate T u) = edgeDirections T := by
    ext d
    simp only [edgeDirections,Set.mem_ofPred_eq,hc]
    exact ⟨fun h => ⟨h.1,hT.2.2.1,h.2.2⟩,fun h => ⟨h.1,harea,h.2.2⟩⟩
  refine ⟨hT.1.image _,hconv,harea,?_,?_⟩
  · intro d hd
    rw [he] at hd
    rw [hc]
    exact hT.2.2.2.1 d hd
  · rw [he]
    exact hT.2.2.2.2

private theorem colle35_maximality_contradiction {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W) (j : ℕ)
    (E : Finset Lattice) (hE : EnvelopedWindow S E)
    (hstrict : W.normalised (G.subsequence j) ⊂ E)
    (hstrip : (E : Set Lattice) ⊆ halfStrip (W.normalisedBase (G.subsequence j)) (C.direction i))
    (hagrees : AgreesOn (W.shiftedField (G.subsequence j))
      (translate ((G.phase:ℤ) • C.direction i) xper) (E : Set Lattice)) : False := by
  let t := G.subsequence j
  let u := (W.normalise t : ℤ) • C.direction i
  let T := windowTranslate E u
  have hAT : W.A t ⊆ T := by
    intro z hz
    have hn : z-u ∈ W.normalised t := Finset.mem_image.mpr ⟨z,hz,by simp [u,sub_eq_add_neg]⟩
    exact Finset.mem_image.mpr ⟨z-u,hstrict.le hn,by simp⟩
  have hTstrip : (T : Set Lattice) ⊆ halfStrip (W.B t) (C.direction i) := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b,hb,n,hqn⟩ := hstrip hq
    obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp hb
    refine ⟨c,hc,n,?_⟩
    dsimp [u,t] at *
    linear_combination (norm := module) hqn - hcb
  have hTagree : AgreesOn (translate (W.shift t) ξ) xper (T : Set Lattice) := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    have h := hagrees q hq
    have hp := congrFun (G.same_phase j) q
    rw [← hp] at h
    dsimp [AlternatingWindows.shiftedField,translate,t,u] at h ⊢
    convert h using 1
    congr 1
    abel
  have heq : T = W.A t := (W.maximal t).2.2.2.2 T
    (colle35_translate_enveloped S E hE u) hAT hTstrip hTagree
  have hEA : E ⊆ W.normalised t := by
    intro z hz
    have hzT : z+u ∈ T := Finset.mem_image.mpr ⟨z,hz,rfl⟩
    rw [heq] at hzT
    exact Finset.mem_image.mpr ⟨z+u,hzT,by simp [u]⟩
  exact hstrict.not_ge hEA

private theorem colle35_same_union {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (s : ℕ → ℕ) (hs : StrictMono s) :
    (⋃ j, (W.normalised (G.subsequence (s j)) : Set Lattice)) = normalisedUnion W G := by
  have hm : Monotone (fun j => W.normalised (G.subsequence j)) := monotone_nat_of_le_succ G.nested
  apply Set.Subset.antisymm
  · rintro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨s j,hj⟩
  · rintro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨j,hm (hs.id_le j) hj⟩

private theorem colle35_actual_start (ξ : Configuration ℤ) (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) (m : ℕ)
    (C : AntipodalEdgeCycle S m) (i : ℤ)
    (xper : Configuration ℤ) (hxper : xper ∈ OrbitClosure ξ)
    (hperiod : ∃ k : ℤ, k ≠ 0 ∧ HasPeriod xper (k • C.direction i))
    (hmismatch : UnboundedHalfStripMismatch ξ xper S (C.direction i)) :
    ∃ W : AlternatingWindows ξ xper C i, ∃ G : GrowingSubsequence W,
      ∃ P : Region (C.direction i) (C.direction G.J),
        P.lattice = normalisedUnion W G ∧
        P.carrier = closedRealHull (normalisedUnion W G) ∧
        WeaklyEnveloped S P ∧ RegionCompleteArc C i G.J P ∧
        det (C.direction i) P.firstAnchor = -1 ∧
        ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ ϑ ∈ OrbitClosure ξ,
          PointwiseLimit (fun j => W.shiftedField (G.subsequence (s j))) ϑ ∧
          AgreesOn ϑ (translate ((G.phase : ℤ) • C.direction i) xper) P.lattice ∧
          (⋃ j, (W.normalised (G.subsequence (s j)) : Set Lattice)) = normalisedUnion W G := by
  obtain ⟨W⟩ := alternating_windows_terminal_normalisation ξ xper A hA S hS m C i hxper hperiod hmismatch
  obtain ⟨a,ha,hp⟩ := hperiod
  obtain ⟨G⟩ := residue_and_first_growing_edge_subsequence W a ha hp
  obtain ⟨P,hP,hcarrier,hweak,harc,hanchor,_⟩ := normalised_union_actual_region_with_arc W G
  obtain ⟨s,hs,ϑ,hϑ,hlim,hagrees⟩ := colle35_limit_selection ξ A hA W G
  exact ⟨W,G,P,hP,hcarrier,hweak,harc,hanchor,s,hs,ϑ,hϑ,hlim,hP.symm ▸ hagrees,colle35_same_union W G s hs⟩

end
end ConvexNivat.Colle
