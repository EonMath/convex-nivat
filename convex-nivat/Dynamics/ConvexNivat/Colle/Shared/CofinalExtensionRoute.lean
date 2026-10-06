import ConvexNivat.Colle.Shared.FiniteSweepLocalisation
import ConvexNivat.Colle.Shared.Sweeps

namespace ConvexNivat.Colle
noncomputable section

local macro "paidNormalisedMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_normalised_mono))
local macro "paidRegionFiniteSeed" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FiniteSweepLocalisation).num 0 ++ `ConvexNivat.Colle.region_finite_seed_eventual_windows))
local macro "paidNormalisedAgreement" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_normalised_agreement))
local macro "paidMaximalityContradiction" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_maximality_contradiction))

private theorem cofinal_fixed_targets_eventually_swept
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
    ∀ n : ℕ, ∃ K : Finset Lattice, (K : Set Lattice) ⊆ P.enlargement n ∧
      ∀ F : Finset Lattice, (F : Set Lattice) ⊆ P.enlargement n →
        ∃ k : ℕ, ∀ j ≥ k, HasFiniteSweep S
          ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
            (K : Set Lattice)) F := by
  intro n
  exact paidRegionFiniteSeed ξ S hS P hweak (region_complete_arc_compatible harc) n
    (fun j => W.normalised (G.subsequence (L.index j)))
    ((paidNormalisedMono G).comp L.strict.monotone) (hP.trans L.same_union.symm)

private theorem cofinal_eventually_no_enveloped_extension
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
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r))
    (N : ℕ) (K : Finset Lattice) (hK : (K : Set Lattice) ⊆ P.enlargement N) :
    ∃ I : ℕ, ∀ j ≥ I, ∀ T : Finset Lattice,
      EnvelopedWindow S T → W.normalised (G.subsequence (L.index j)) ⊂ T →
      (T : Set Lattice) ⊆ halfStrip
        (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) →
      ¬ HasFiniteSweep S
        ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
          (K : Set Lattice)) T := by
  classical
  choose time htime using L.converges
  obtain ⟨I, hI⟩ := (K.image time).exists_le
  refine ⟨I, ?_⟩
  intro j hj T henv hstrict hstrip hsweep
  have hagree : AgreesOn (W.shiftedField (G.subsequence (L.index j)))
      (translate ((G.phase : ℤ) • C.direction i) xper)
      ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (K : Set Lattice)) := by
    intro z hz
    rcases hz with hz | hz
    · exact paidNormalisedAgreement W G (L.index j) z hz
    · exact (htime z j ((hI (time z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)).trans hj)).trans
        (hall N z (hK hz))
  obtain ⟨steps, hvalid, hT⟩ := hsweep
  have hprop := generating_one_point_and_finite_sweep ξ
    (W.shiftedField (G.subsequence (L.index j)))
    (translate ((G.phase : ℤ) • C.direction i) xper) S hS
    (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _)
    (orbitClosure_translate_member ξ xper hxper _) _ steps hvalid hagree
  exact paidMaximalityContradiction W G (L.index j) T henv hstrict hstrip
    (fun z hz => hprop z (hT hz))

private theorem cofinal_extension_implies_false
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
  (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r))
    (hX1 : ∃ N : ℕ, ∃ K : Finset Lattice,
      (K : Set Lattice) ⊆ P.enlargement N ∧
      ∀ I : ℕ, ∃ j : ℕ, I ≤ j ∧ ∃ T : Finset Lattice,
        EnvelopedWindow S T ∧ W.normalised (G.subsequence (L.index j)) ⊂ T ∧
        (T : Set Lattice) ⊆ halfStrip
          (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) ∧
        HasFiniteSweep S
          ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
            (K : Set Lattice)) T) : False := by
  obtain ⟨N, K, hK, hcofinal⟩ := hX1
  obtain ⟨I, hI⟩ := cofinal_eventually_no_enveloped_extension ξ xper alphabet halphabet
    S hS m C i hxper hperiod W G P hP hcarrier hweak harc hanchor L hall N K hK
  obtain ⟨j, hj, T, henv, hstrict, hstrip, hsweep⟩ := hcofinal I
  exact hI j hj T henv hstrict hstrip hsweep

local macro "paidFixedVertex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcUnion).num 0 ++ `ConvexNivat.Colle.arc_fixed_vertex))

private theorem cofinal_parallel_facet_endpoint_data
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
    let p := C.direction (G.J - 1)
    let w := C.direction G.J
    let d := C.direction (G.J + 1)
    let α := det w d
    let β := det p w
    ∃ a : Lattice, ∃ κ : ℤ,
      (∀ j : ℕ, (W.boundary (G.subsequence (L.index j))).vertex G.J -
        (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i = a) ∧
      (∀ j : ℕ,
        ((W.boundary (G.subsequence (L.index j))).vertex (G.J + 1) -
          (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i - β • d) -
            (a + α • p) =
        (((W.boundary (G.subsequence (L.index j))).length G.J : ℤ) + κ) • w) ∧
      det w (a + α • p) = det w a - β * α ∧
      ∃ j₀ : ℕ, ∀ j ≥ j₀,
        ((supportRow S w).card : ℤ) ≤
          ((W.boundary (G.subsequence (L.index j))).length G.J : ℤ) + κ + 1 := by
  dsimp only
  let p := C.direction (G.J - 1)
  let w := C.direction G.J
  let d := C.direction (G.J + 1)
  let α := det w d
  let β := det p w
  let a := (W.boundary (G.subsequence 0)).vertex G.J -
    (W.normalise (G.subsequence 0) : ℤ) • C.direction i
  have hfix (j : ℕ) : (W.boundary (G.subsequence (L.index j))).vertex G.J -
      (W.normalise (G.subsequence (L.index j)) : ℤ) • C.direction i = a :=
    paidFixedVertex W G G.J G.lower le_rfl (L.index j)
  have hzero : det w (0 : Lattice) = det w (-β • d - α • p) := by
    dsimp [α, β, det]
    ring
  obtain ⟨κ, hκ⟩ := ((primitive_row_coordinates w (C.primitive G.J)).2.1
    0 (-β • d - α • p)).mp hzero
  have hκ' : -β • d - α • p = κ • w := by simpa using hκ
  refine ⟨a, κ, hfix, ?_, ?_, ?_⟩
  · intro j
    have he := (W.boundary (G.subsequence (L.index j))).edge_eq G.J
    change _ = (_ : ℤ) • w at he
    have ha := hfix j
    rw [add_smul]
    linear_combination (norm := module) he + hκ' + ha
  · change det w (a + α • p) = det w a - β * α
    dsimp [β, det]
    ring
  · obtain ⟨N, hN⟩ := exists_nat_gt (((supportRow S w).card : ℤ) - κ)
    refine ⟨N, ?_⟩
    intro j hj
    have hlen := (L.strict.id_le j).trans (G.growing.id_le (L.index j))
    have hlen' : (j : ℤ) ≤
        (W.boundary (G.subsequence (L.index j))).length G.J := by exact_mod_cast hlen
    have hj' : (N : ℤ) ≤ j := by exact_mod_cast hj
    change ((supportRow S w).card : ℤ) ≤ _
    omega

end
end ConvexNivat.Colle
