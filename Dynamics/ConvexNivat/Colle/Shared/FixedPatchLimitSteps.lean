import ConvexNivat.Colle.Shared.NormalisedLimitExists
import ConvexNivat.Colle.Shared.FixedPatchSteps
import ConvexNivat.Colle.Shared.Sweeps

namespace ConvexNivat.Colle
noncomputable section

local macro "paidNormalisedAgreement" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_normalised_agreement))
local macro "paidFirstFailure" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_first_failure))
local macro "paidMaximalityContradiction" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_maximality_contradiction))
local macro "paidFiniteCandidates" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_all_literal_candidates))

local macro "paidStrictCandidates" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_eventual_strict_candidates))

private theorem limit_fixed_patch {ξ xper : Configuration ℤ} {S : Finset Lattice}
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    {W : AlternatingWindows ξ xper C i} {G : GrowingSubsequence W}
    (L : NormalisedWindowLimit W G) (F : Finset Lattice) :
    ∃ I₀ : ℕ, ∀ j ≥ I₀, AgreesOn L.field
      (W.shiftedField (G.subsequence (L.index j))) (F : Set Lattice) := by
  classical
  choose N hN using L.converges
  obtain ⟨I₀, hI₀⟩ := (F.image N).exists_le
  refine ⟨I₀, ?_⟩
  intro j hj z hz
  exact (hN z j ((hI₀ (N z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)).trans hj)).symm

private theorem limit_literal_candidates {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G)
    (L : NormalisedWindowLimit W G) (n : ℕ) :
    ∃ E : ℕ → Finset Lattice,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
        (P.enlargement n)) ∧ Monotone E ∧
      ∀ j, W.normalised (G.subsequence (L.index j)) ⊆ E j := by
  obtain ⟨E, he, hm, hA⟩ := paidFiniteCandidates W G P hP n
  exact ⟨fun j => E (L.index j), fun j => he (L.index j), hm.comp L.strict.monotone,
    fun j => hA (L.index j)⟩

private theorem fixed_patch_sweep_agreement {ξ xper : Configuration ℤ}
    {S : Finset Lattice} (hS : GeneratingSet ξ S)
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (hxper : xper ∈ OrbitClosure ξ)
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (L : NormalisedWindowLimit W G) (n : ℕ)
    (hall : AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
      (P.enlargement n)) (E : ℕ → Finset Lattice) (j₀ j : ℕ)
    (hseed : (E j₀ : Set Lattice) ⊆ P.enlargement n)
    (hclose : AgreesOn L.field (W.shiftedField (G.subsequence (L.index j)))
      (E j₀ : Set Lattice))
    (hsweep : HasFiniteSweep S
      ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (E j₀ : Set Lattice)) (E j)) :
    AgreesOn (W.shiftedField (G.subsequence (L.index j)))
      (translate ((G.phase : ℤ) • C.direction i) xper) (E j : Set Lattice) := by
  obtain ⟨steps, hvalid, hE⟩ := hsweep
  have hagree : AgreesOn (W.shiftedField (G.subsequence (L.index j)))
      (translate ((G.phase : ℤ) • C.direction i) xper)
      ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (E j₀ : Set Lattice)) := by
    intro z hz
    rcases hz with hz | hz
    · exact paidNormalisedAgreement W G (L.index j) z hz
    · exact (hclose z hz).symm.trans (hall z (hseed hz))
  have hf := generating_one_point_and_finite_sweep ξ
    (W.shiftedField (G.subsequence (L.index j)))
    (translate ((G.phase : ℤ) • C.direction i) xper) S hS
    (orbitClosure_translate_member ξ ξ (orbitClosure_contains_self ξ) _)
    (orbitClosure_translate_member ξ xper hxper _) _ steps hvalid hagree
  exact fun z hz => hf z (hE hz)

private theorem no_source_geometry_and_sweep {ξ xper : Configuration ℤ}
    {S : Finset Lattice} (hS : GeneratingSet ξ S)
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (hxper : xper ∈ OrbitClosure ξ)
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (L : NormalisedWindowLimit W G) (n : ℕ)
    (hall : AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
      (P.enlargement n)) (E : ℕ → Finset Lattice) (j₀ : ℕ)
    (hseed : (E j₀ : Set Lattice) ⊆ P.enlargement n)
    (hgeom : ∀ j ≥ j₀, EnvelopedWindow S (E j) ∧
      W.normalised (G.subsequence (L.index j)) ⊂ E j ∧
      (E j : Set Lattice) ⊆ halfStrip
        (W.normalisedBase (G.subsequence (L.index j))) (C.direction i) ∧
      HasFiniteSweep S ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (E j₀ : Set Lattice)) (E j)) : False := by
  obtain ⟨I₀, hI⟩ := limit_fixed_patch L (E j₀)
  let j := max j₀ I₀
  obtain ⟨hE, hs, hstrip, hsweep⟩ := hgeom j (le_max_left _ _)
  have ha := fixed_patch_sweep_agreement hS hxper W G P L n hall E j₀ j hseed
    (hI j (le_max_right _ _)) hsweep
  exact paidMaximalityContradiction W G (L.index j) (E j) hE hs hstrip ha

private theorem limit_first_failure_iff_not_all {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (L : NormalisedWindowLimit W G) :
    (∃ n : ℕ, AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
      (P.enlargement n) ∧
      ¬ AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
        (P.enlargement (n + 1))) ↔
    ¬ ∀ r : ℕ, AgreesOn L.field (translate ((G.phase : ℤ) • C.direction i) xper)
      (P.enlargement r) := by
  constructor
  · rintro ⟨n, _, hn⟩ hall
    exact hn (hall (n + 1))
  · intro hnot
    have hfail : ∃ r : ℕ, ¬ AgreesOn L.field
        (translate ((G.phase : ℤ) • C.direction i) xper) (P.enlargement r) := by
      simpa only [not_forall] using hnot
    apply paidFirstFailure P L.field (translate ((G.phase : ℤ) • C.direction i) xper)
      _ hfail
    rw [hP]
    exact L.agrees_union

private theorem limit_strict_family_and_fixed_convergence {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (L : NormalisedWindowLimit W G) (n : ℕ) :
    ∃ n' : ℕ, n ≤ n' ∧ ∃ E : ℕ → Finset Lattice, ∃ j₀ I₀ : ℕ,
      (∀ j, (E j : Set Lattice) = backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
        (P.enlargement n')) ∧ Monotone E ∧
      (∀ j ≥ j₀, W.normalised (G.subsequence (L.index j)) ⊂ E j) ∧
      ∀ j ≥ I₀, AgreesOn L.field (W.shiftedField (G.subsequence (L.index j)))
        (E j₀ : Set Lattice) := by
  obtain ⟨n', hnn', E, j₀, he, hm, hs⟩ := paidStrictCandidates W G P hP n
  obtain ⟨I₀, hI⟩ := limit_fixed_patch L (E (L.index j₀))
  refine ⟨n', hnn', fun j => E (L.index j), j₀, I₀,
    fun j => he (L.index j), hm.comp L.strict.monotone, ?_, hI⟩
  intro j hj
  exact hs (L.index j) (hj.trans (L.strict.id_le j))

end
end ConvexNivat.Colle
