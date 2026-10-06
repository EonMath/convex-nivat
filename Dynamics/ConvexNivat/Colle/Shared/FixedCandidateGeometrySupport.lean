import ConvexNivat.Colle.Shared.FixedPatchConvex

namespace ConvexNivat.Colle
noncomputable section

local macro "paidRowMem" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.row_mem))
local macro "paidExteriorSeed" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_exterior_seed))
local macro "paidCycleTurn" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.cycle_turn_positive))
local macro "paidEnlargementMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_enlargement_mono))
local macro "paidLatticeInEnlargement" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_lattice_subset_enlargement))
local macro "paidNormalisedMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_normalised_mono))
local macro "paidTranslatedEnvelope" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_translate_enveloped))
local macro "paidCandidateConvex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchConvex).num 0 ++ `ConvexNivat.Colle.normalised_candidate_lattice_convex))
local macro "paidCandidateArea" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchConvex).num 0 ++ `ConvexNivat.Colle.candidate_nonempty_and_area))

private theorem retained_support_rows (A E : Finset Lattice) (d delta : Lattice)
    (hAE : A ⊆ E)
    (hsub : (E : Set Lattice) ⊆ saturateRay (A : Set Lattice) (-d))
    (hdet : 0 ≤ det delta (-d)) : supportRow A delta ⊆ supportRow E delta := by
  intro a ha
  obtain ⟨haA,hmin⟩ := (paidRowMem A delta a).mp ha
  apply (paidRowMem E delta a).mpr
  refine ⟨hAE haA,?_⟩
  intro z hz
  obtain ⟨g,hg,t,rfl⟩ := hsub hz
  have he : det delta (g+(t : ℤ) • (-d)) = det delta g+(t : ℤ)*det delta (-d) := by
    simp [det]; ring
  rw [he]
  exact (hmin g hg).trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hdet))

private theorem retained_support_card (A E : Finset Lattice) (d delta : Lattice)
    (hAE : A ⊆ E)
    (hsub : (E : Set Lattice) ⊆ saturateRay (A : Set Lattice) (-d))
    (hdet : 0 ≤ det delta (-d)) :
    (supportRow A delta).card ≤ (supportRow E delta).card :=
  Finset.card_le_card (retained_support_rows A E d delta hAE hsub hdet)

private theorem primitive_forward_coordinate (v : Lattice) (hv : Primitive v) :
    ∃ a c : ℤ, a*v.1+c*v.2=1 := by
  obtain ⟨e,he,_⟩ := (primitive_row_coordinates v hv).1
  refine ⟨e.2,-e.1,?_⟩
  dsimp [det] at he
  linear_combination he

private theorem halfstrip_row_coordinate (B : Finset Lattice) (v z : Lattice)
    (hv : Primitive v) (a c : ℤ) (hcoord : a*v.1+c*v.2=1) :
    z ∈ halfStrip B v ↔ ∃ g ∈ B, det v g=det v z ∧
      a*g.1+c*g.2 ≤ a*z.1+c*z.2 := by
  have hshift (g : Lattice) (k : ℤ) :
      a*(g+k • v).1+c*(g+k • v).2 = a*g.1+c*g.2+k := by
    change a*(g.1+k*v.1)+c*(g.2+k*v.2) = a*g.1+c*g.2+k
    linear_combination k*hcoord
  constructor
  · rintro ⟨g,hg,t,rfl⟩
    refine ⟨g,hg,?_,?_⟩
    · simp [det]; ring
    · rw [hshift]
      exact le_add_of_nonneg_right (by positivity)
  · rintro ⟨g,hg,hrow,hforward⟩
    obtain ⟨k,hk⟩ := ((primitive_row_coordinates v hv).2.1 g z).mp hrow
    have hk0 : 0 ≤ k := by rw [hk,hshift] at hforward; omega
    refine ⟨g,hg,k.toNat,?_⟩
    rw [Int.toNat_of_nonneg hk0]
    exact hk

private theorem literal_strictness_tail {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (L : NormalisedWindowLimit W G) :
    ∃ N jS : ℕ, ∀ n : ℕ, N ≤ n → ∀ E : ℕ → Finset Lattice,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index j))) (C.direction (G.J+1))
        (P.enlargement n)) →
      ∀ j ≥ jS, W.normalised (G.subsequence (L.index j)) ⊂ E j := by
  obtain ⟨N,g,z,hg,hz,hzN,t,hzt⟩ :=
    paidExteriorSeed P (C.direction (G.J+1)) (paidCycleTurn C G.J)
  have hgunion : g ∈ ⋃ j, (W.normalised (G.subsequence (L.index j)) : Set Lattice) := by
    rw [L.same_union,← hP]
    exact hg
  obtain ⟨jS,hgjS⟩ := Set.mem_iUnion.mp hgunion
  refine ⟨N,jS,?_⟩
  intro n hn E hE j hj
  have hAE : W.normalised (G.subsequence (L.index j)) ⊆ E j := by
    intro q hq
    have hqP : q ∈ P.lattice := by
      rw [hP]
      exact Set.mem_iUnion.mpr ⟨L.index j,hq⟩
    change q ∈ (E j : Set Lattice)
    rw [hE j]
    exact ⟨⟨q,hq,0,by simp⟩,paidLatticeInEnlargement P n hqP⟩
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hAE,?_⟩
  intro heq
  have hgj := paidNormalisedMono G (L.strict.monotone hj) hgjS
  have hzE : z ∈ (E j : Set Lattice) := by
    rw [hE j]
    exact ⟨⟨g,hgj,t,hzt⟩,paidEnlargementMono P hn hzN⟩
  have hzA : z ∈ W.normalised (G.subsequence (L.index j)) := by rw [heq]; exact hzE
  apply hz
  rw [hP]
  exact Set.mem_iUnion.mpr ⟨L.index j,hzA⟩

private theorem literal_envelope_from_recovery {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J)) (L : NormalisedWindowLimit W G)
    (n j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J+1)) (P.enlargement n))
    (hAE : W.normalised (G.subsequence (L.index j)) ⊆ E)
    (hnew : edgeDirections E ⊆ edgeDirections S)
    (hbad : ∀ delta ∈ edgeDirections S, det delta (-C.direction (G.J+1)) < 0 →
      (supportRow S delta).card ≤ (supportRow E delta).card) : EnvelopedWindow S E := by
  have hA : EnvelopedWindow S (W.normalised (G.subsequence (L.index j))) :=
    paidTranslatedEnvelope S _ (W.A_enveloped _) _
  have hfinite : (edgeDirections S).Finite := by
    have he : edgeDirections S = Set.range (fun k : Fin (2*m) => C.direction (k.val : ℤ)) := by
      ext v
      exact C.covers v
    rw [he]
    exact Set.finite_range _
  have hAedges : edgeDirections (W.normalised (G.subsequence (L.index j))) = edgeDirections S :=
    Set.eq_of_subset_of_ncard_le (fun delta hdelta => (hA.2.2.2.1 delta hdelta).1)
      hA.2.2.2.2.ge hfinite
  have hsub : (E : Set Lattice) ⊆ saturateRay
      (W.normalised (G.subsequence (L.index j)) : Set Lattice) (-C.direction (G.J+1)) := by
    rw [hE]
    exact Set.inter_subset_left
  have hsupp (delta : Lattice) (hd : delta ∈ edgeDirections S) :
      (supportRow S delta).card ≤ (supportRow E delta).card := by
    by_cases hnonneg : 0 ≤ det delta (-C.direction (G.J+1))
    · have hda : delta ∈ edgeDirections (W.normalised (G.subsequence (L.index j))) :=
        hAedges.symm ▸ hd
      exact ((hA.2.2.2.1 delta hda).2).trans
        (retained_support_card _ E _ delta hAE hsub hnonneg)
    · exact hbad delta hd (lt_of_not_ge hnonneg)
  obtain ⟨hne,harea⟩ := paidCandidateArea hA.1 hA.2.2.1 hAE
  have heq : edgeDirections E = edgeDirections S := by
    apply Set.Subset.antisymm hnew
    intro delta hd
    exact ⟨hd.1,harea,hd.2.2.trans (hsupp delta hd)⟩
  refine ⟨hne,paidCandidateConvex W G P L n j E hE,harea,?_,?_⟩
  · intro delta hd
    have hds := hnew hd
    exact ⟨hds,hsupp delta hds⟩
  · rw [heq]

private theorem geometry_family_from_recovery {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J)) (L : NormalisedWindowLimit W G)
    (hbridge : ∃ n : ℕ, ∃ E : ℕ → Finset Lattice, ∃ jG : ℕ, ∃ a c : ℤ,
      a*(C.direction i).1+c*(C.direction i).2=1 ∧
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index j))) (C.direction (G.J+1))
        (P.enlargement n)) ∧
      ∀ j ≥ jG,
        W.normalised (G.subsequence (L.index j)) ⊂ E j ∧
        (∀ delta ∈ edgeDirections (E j), delta ∈ edgeDirections S) ∧
        (∀ delta ∈ edgeDirections S, det delta (-C.direction (G.J+1)) < 0 →
          (supportRow S delta).card ≤ (supportRow (E j) delta).card) ∧
        (∀ z ∈ E j, ∃ g ∈ W.normalisedBase (G.subsequence (L.index j)),
          det (C.direction i) g=det (C.direction i) z ∧
          a*g.1+c*g.2 ≤ a*z.1+c*z.2)) :
    ∃ n' : ℕ, ∃ E : ℕ → Finset Lattice, ∃ j₀ : ℕ,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index j))) (C.direction (G.J+1))
        (P.enlargement n')) ∧
      ∀ j ≥ j₀, EnvelopedWindow S (E j) ∧
        W.normalised (G.subsequence (L.index j)) ⊂ E j ∧
        (E j : Set Lattice) ⊆ halfStrip
          (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) := by
  obtain ⟨n,E,jG,a,c,hcoord,hE,hall⟩ := hbridge
  refine ⟨n,E,jG,hE,?_⟩
  intro j hj
  obtain ⟨hstrict,hnew,hbad,hrow⟩ := hall j hj
  refine ⟨literal_envelope_from_recovery W G P L n j (E j) (hE j)
    (Finset.ssubset_iff_subset_ne.mp hstrict).1 hnew hbad,hstrict,?_⟩
  intro z hz
  exact (halfstrip_row_coordinate _ _ z (C.primitive i) a c hcoord).mpr (hrow z hz)

end
end ConvexNivat.Colle
