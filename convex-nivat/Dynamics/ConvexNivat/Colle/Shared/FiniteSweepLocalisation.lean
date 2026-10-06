import ConvexNivat.Colle.Shared.NormalisedLimitExists
import ConvexNivat.Colle.Shared.FixedPatchSteps
import ConvexNivat.Colle.RegionArcSweeps
import ConvexNivat.Colle.Shared.SaturationSteps

namespace ConvexNivat.Colle
noncomputable section

local macro "paidValidMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_valid_sweep_mono))
local macro "paidDomainMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_sweep_domain_mono))
local macro "paidSweepMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_finite_sweep_mono))

private theorem finite_sweep_localisation {S F : Finset Lattice} {U : Set Lattice}
    (h : HasFiniteSweep S U F) :
    ∃ K : Finset Lattice, (K : Set Lattice) ⊆ U ∧ HasFiniteSweep S (K : Set Lattice) F := by
  classical
  obtain ⟨steps, hs, hF⟩ := h
  induction hs with
  | nil U => exact ⟨F, hF, [], .nil _, Set.Subset.rfl⟩
  | cons U u z steps hz he hs ih =>
    obtain ⟨K, hKU, tail, ht, hFt⟩ := ih hF
    let Q := (S.erase z).image (u + ·)
    let K' := (K.erase (u + z)) ∪ Q
    have hQ : (Q : Set Lattice) ⊆ U := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact he q hq
    have hK' : (K' : Set Lattice) ⊆ U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases hKU (Finset.mem_of_mem_erase hx) with hh | hh
        · exact hh
        · exact False.elim ((Finset.mem_erase.mp hx).1 (Set.mem_singleton_iff.mp hh))
      · exact hQ hx
    have hK : (K : Set Lattice) ⊆ (K' : Set Lattice) ∪ {u + z} := by
      intro x hx
      by_cases heq : x = u + z
      · exact Or.inr heq
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hx⟩))
    refine ⟨K', hK', (u, z) :: tail, .cons _ u z tail hz ?_ (paidValidMono hK ht), ?_⟩
    · intro q hq
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    · exact hFt.trans (paidDomainMono hK tail)

private theorem finite_sweep_localisation_union {S F : Finset Lattice}
    {U V : Set Lattice} (h : HasFiniteSweep S (U ∪ V) F) :
    ∃ K : Finset Lattice, (K : Set Lattice) ⊆ U ∧
      HasFiniteSweep S ((K : Set Lattice) ∪ V) F := by
  classical
  obtain ⟨K, hK, hs⟩ := finite_sweep_localisation h
  refine ⟨K.filter (· ∈ U), ?_, paidSweepMono ?_ hs⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro z hz
    rcases hK hz with hU | hV
    · exact Or.inl (Finset.mem_filter.mpr ⟨hz, hU⟩)
    · exact Or.inr hV

private theorem finite_sweep_eventual_capture {S F : Finset Lattice}
    {A : ℕ → Finset Lattice} (hA : Monotone A) {V : Set Lattice}
    (h : HasFiniteSweep S ((⋃ j, (A j : Set Lattice)) ∪ V) F) :
    ∃ k : ℕ, ∀ j ≥ k, HasFiniteSweep S ((A j : Set Lattice) ∪ V) F := by
  classical
  obtain ⟨K, hK, hs⟩ := finite_sweep_localisation_union h
  have hc : ∀ z ∈ K, ∃ j, z ∈ A j := by
    intro z hz
    exact Set.mem_iUnion.mp (hK hz)
  choose index hindex using hc
  let k := K.sup fun z => if hz : z ∈ K then index z hz else 0
  refine ⟨k, ?_⟩
  intro j hj
  apply paidSweepMono _ hs
  apply Set.union_subset_union _ (Set.Subset.refl V)
  intro z hz
  change z ∈ K at hz
  have hi : index z hz ≤ k := by
    have hh := Finset.le_sup (f := fun z => if hz : z ∈ K then index z hz else 0) hz
    simpa only [dite_eq_left hz] using hh
  exact hA (hi.trans hj) (hindex z hz)


local macro "paidValidAppend" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.valid_append))
local macro "paidDomainAppend" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.domain_append))
local macro "paidDomainContains" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.domain_contains))
local macro "paidEnlargementZero" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_enlargement_zero))
local macro "paidEnlargementMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_enlargement_mono))

private theorem finite_sweep_trans {S F K : Finset Lattice} {U : Set Lattice}
    (hK : HasFiniteSweep S U K) (hF : HasFiniteSweep S ((K : Set Lattice) ∪ U) F) :
    HasFiniteSweep S U F := by
  obtain ⟨s, hs, hKs⟩ := hK
  obtain ⟨t, ht, hFt⟩ := hF
  have hseed : (K : Set Lattice) ∪ U ⊆ sweepDomain U s :=
    Set.union_subset hKs (paidDomainContains U s)
  refine ⟨s ++ t, paidValidAppend hs (paidValidMono hseed ht), ?_⟩
  rw [paidDomainAppend]
  exact hFt.trans (paidDomainMono hseed t)

private theorem finite_sweep_transfer {S F : Finset Lattice} {U V : Set Lattice}
    (h : HasFiniteSweep S U F)
    (hU : ∀ K : Finset Lattice, (K : Set Lattice) ⊆ U → HasFiniteSweep S V K) :
    HasFiniteSweep S V F := by
  obtain ⟨K, hK, hs⟩ := finite_sweep_localisation h
  exact finite_sweep_trans (hU K hK) (paidSweepMono Set.subset_union_left hs)

private theorem region_finite_seed_all_layers (ξ : Configuration ℤ)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (hcompat : RegionCompatibleArc S P) (n : ℕ) :
    ∃ K : Finset Lattice, (K : Set Lattice) ⊆ P.enlargement n ∧
      ∀ F : Finset Lattice, (F : Set Lattice) ⊆ P.enlargement n →
        HasFiniteSweep S (P.lattice ∪ (K : Set Lattice)) F := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    intro F hF
    refine ⟨[], .nil _, ?_⟩
    intro z hz
    exact Or.inl (paidEnlargementZero P ▸ hF hz)
  | succ n ih =>
    obtain ⟨K, hK, hgen⟩ := ih
    obtain ⟨R, T, hsweep⟩ := enlarged_region_finite_seed_sweep ξ S hS P hweak hcompat n
    let Q := (windowTranslate (integerSquare R) ((T : ℤ) • w)).filter
      (· ∈ P.enlargement (n + 1))
    have hQ : (Q : Set Lattice) ⊆ P.enlargement (n + 1) := by
      intro z hz
      exact (Finset.mem_filter.mp hz).2
    have hseed : regionalSeed P n R T = P.enlargement n ∪ (Q : Set Lattice) := by
      ext z
      simp only [regionalSeed, Set.mem_union, Set.mem_inter_iff, Finset.mem_coe,
        Q, Finset.mem_filter]
      tauto
    refine ⟨K ∪ Q, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact paidEnlargementMono P (Nat.le_succ n) (hK hz)
      · exact hQ hz
    · intro F hF
      have hs := hsweep T le_rfl F hF
      rw [hseed] at hs
      obtain ⟨H, hH, hHs⟩ := finite_sweep_localisation_union hs
      have hHgen : HasFiniteSweep S (P.lattice ∪ ((K ∪ Q : Finset Lattice) : Set Lattice)) H :=
        paidSweepMono (Set.union_subset_union (Set.Subset.refl _) (by
          intro z hz; exact Finset.mem_union_left _ hz)) (hgen H hH)
      apply finite_sweep_trans hHgen
      apply paidSweepMono _ hHs
      intro z hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inr (Finset.mem_union_right _ hz))

private theorem region_finite_seed_eventual_windows (ξ : Configuration ℤ)
    (S : Finset Lattice) (hS : GeneratingSet ξ S) {v w : Lattice}
    (P : Region v w) (hweak : WeaklyEnveloped S P)
    (hcompat : RegionCompatibleArc S P) (n : ℕ)
    (A : ℕ → Finset Lattice) (hA : Monotone A)
    (hP : P.lattice = ⋃ j, (A j : Set Lattice)) :
    ∃ K : Finset Lattice, (K : Set Lattice) ⊆ P.enlargement n ∧
      ∀ F : Finset Lattice, (F : Set Lattice) ⊆ P.enlargement n →
        ∃ k : ℕ, ∀ j ≥ k, HasFiniteSweep S ((A j : Set Lattice) ∪ (K : Set Lattice)) F := by
  obtain ⟨K, hK, hs⟩ := region_finite_seed_all_layers ξ S hS P hweak hcompat n
  refine ⟨K, hK, ?_⟩
  intro F hF
  have hf := hs F hF
  rw [hP] at hf
  exact finite_sweep_eventual_capture hA hf


local macro "paidSweepPoints" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.sweep_of_points))
local macro "paidSweepStep" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.sweep_one_step))
local macro "paidSweepKnown" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.sweep_known_point))

private theorem finite_sweep_of_decreasing_placements {S F : Finset Lattice}
    {U : Set Lattice} (rank : Lattice → ℕ)
    (hplacement : ∀ z ∈ F, z ∉ U → ∃ p : Lattice, WindowVertex S p ∧
      ∀ q ∈ S.erase p, z + (q - p) ∈ U ∨
        (z + (q - p) ∈ F ∧ rank (z + (q - p)) < rank z)) :
    HasFiniteSweep S U F := by
  have hpoint : ∀ r : ℕ, ∀ z ∈ F, rank z = r → HasFiniteSweep S U {z} := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro z hz hr
      by_cases hzU : z ∈ U
      · exact paidSweepKnown hzU
      · obtain ⟨p, hp, hq⟩ := hplacement z hz hzU
        have h : HasFiniteSweep S U {(z - p) + p} := paidSweepStep (z - p) p hp (by
          intro q hqS
          have he : z - p + q = z + (q - p) := by abel
          rw [he]
          rcases hq q hqS with hU | ⟨hF, hlt⟩
          · exact paidSweepKnown hU
          · exact ih _ (by omega) _ hF rfl)
        simpa using h
  exact paidSweepPoints (fun z hz => hpoint (rank z) z hz rfl)


local macro "paidNewRowOffset" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.new_row_offset_old))
local macro "paidSecondRay" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_second_ray_mem))
local macro "paidConeMember" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_cone_mem_of_clockwise_dets))
local macro "paidCycleOrder" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_cycle_order))
local macro "paidDetNonneg" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_ordered_det_nonneg))
local macro "paidCycleTurn" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.cycle_turn_positive))
local macro "paidConeAdd" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.RegionCore).num 0 ++ `ConvexNivat.Colle.cone_add_mem))
local macro "paidNormalisedMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_normalised_mono))
local macro "paidCandidateMono" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.fp_candidate_mono))

private theorem enlargement_shift_to_region {v w : Lattice} (P : Region v w)
    (d : Lattice) (hd : 0 < det w d)
    (hforward : ∀ z ∈ P.lattice, z + d ∈ P.lattice) (n : ℕ)
    (z : Lattice) (hz : z ∈ P.enlargement n) :
    z + (n : ℤ) • d ∈ P.lattice := by
  have ha : P.secondAnchor ∈ P.lattice := by
    simpa using paidSecondRay P 0 le_rfl
  have hfit := hforward P.secondAnchor ha
  induction n generalizing z with
  | zero => simpa using (paidEnlargementZero P ▸ hz)
  | succ n ih =>
    by_cases ho : z ∈ P.enlargement n
    · have hh := hforward _ (ih z ho)
      simpa [Nat.cast_add, add_smul, add_assoc] using hh
    · have hh := ih (z + d) (paidNewRowOffset P n z d ⟨hz, ho⟩ hfit hd)
      convert hh using 1 <;> simp [Nat.cast_add, add_smul] <;> abel

private theorem cycle_successor_forward {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i J : ℤ)
    (P : Region (C.direction i) (C.direction J))
    (harc : RegionCompleteArc C i J P) :
    ∀ z ∈ P.lattice, z + C.direction (J + 1) ∈ P.lattice := by
  have h0 := paidDetNonneg C (paidCycleOrder C) i (J + 1)
    (by have := harc.lower; omega) (by have := harc.upper; omega)
  have h1 := paidCycleTurn C J
  have hcone : embed (C.direction (J + 1)) ∈ twoRayCone (-(C.direction i)) (C.direction J) := by
    apply paidConeMember
    · have h := P.turn_positive
      have he : det (-(C.direction i)) (C.direction J) =
          -det (C.direction i) (C.direction J) := by simp [det]; ring
      rw [he]
      omega
    · have he : det (C.direction (J + 1)) (C.direction J) =
          -det (C.direction J) (C.direction (J + 1)) := by simp [det]; ring
      rw [he]
      omega
    · have he : det (-(C.direction i)) (C.direction (J + 1)) =
          -det (C.direction i) (C.direction (J + 1)) := by simp [det]; ring
      rw [he]
      omega
  intro z hz
  have hh : embed z + embed (C.direction (J + 1)) ∈ P.carrier := paidConeAdd P hz hcone
  simpa only [Region.lattice, Set.mem_preimage, ← embed_add] using hh

private theorem literal_candidates_union {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G)
    (harc : RegionCompleteArc C i G.J P) (L : NormalisedWindowLimit W G)
    (n : ℕ) (E : ℕ → Finset Lattice)
    (hE : ∀ j, (E j : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
      (P.enlargement n)) :
    Monotone E ∧ (⋃ j, (E j : Set Lattice)) = P.enlargement n := by
  constructor
  · intro a b hab z hz
    have hA := paidNormalisedMono G (L.strict.monotone hab)
    have hh : backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index a))) (C.direction (G.J + 1)) (P.enlargement n) ⊆
        backwardSaturationCandidate
        (W.normalised (G.subsequence (L.index b))) (C.direction (G.J + 1)) (P.enlargement n) :=
      paidCandidateMono hA (Set.Subset.refl (P.enlargement n))
    have hza : z ∈ (E a : Set Lattice) := hz
    rw [hE a] at hza
    have hzb := hh hza
    rw [← hE b] at hzb
    exact hzb
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      rw [hE j] at hj
      exact hj.2
    · intro z hz
      let d := C.direction (G.J + 1)
      have hg := enlargement_shift_to_region P d (paidCycleTurn C G.J)
        (cycle_successor_forward C i G.J P harc) n z hz
      have hgU : z + (n : ℤ) • d ∈ ⋃ j,
          (W.normalised (G.subsequence (L.index j)) : Set Lattice) := by
        rw [L.same_union, ← hP]
        exact hg
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hgU
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      rw [hE j]
      refine ⟨⟨z + (n : ℤ) • d, hj, n, ?_⟩, hz⟩
      change z = z + (n : ℤ) • d + (n : ℤ) • (-d)
      simp


private theorem finite_subset_eventual_capture {A : ℕ → Finset Lattice}
    (hA : Monotone A) (K : Finset Lattice)
    (hK : (K : Set Lattice) ⊆ ⋃ j, (A j : Set Lattice)) :
    ∃ k : ℕ, ∀ j ≥ k, K ⊆ A j := by
  classical
  have hc : ∀ z ∈ K, ∃ j, z ∈ A j := by
    intro z hz
    exact Set.mem_iUnion.mp (hK hz)
  choose index hindex using hc
  let k := K.sup fun z => if hz : z ∈ K then index z hz else 0
  refine ⟨k, ?_⟩
  intro j hj z hz
  have hi : index z hz ≤ k := by
    have hh := Finset.le_sup (f := fun z => if hz : z ∈ K then index z hz else 0) hz
    simpa only [dite_eq_left hz] using hh
  exact hA (hi.trans hj) (hindex z hz)

private theorem literal_fixed_seed_global_sweep {ξ xper : Configuration ℤ}
    {S : Finset Lattice} (hS : GeneratingSet ξ S)
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (hweak : WeaklyEnveloped S P)
    (harc : RegionCompleteArc C i G.J P) (L : NormalisedWindowLimit W G)
    (n : ℕ) (E : ℕ → Finset Lattice) (j₀ : ℕ)
    (hE : ∀ j, (E j : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
      (P.enlargement n)) :
    ∃ k : ℕ, j₀ ≤ k ∧ ∀ F : Finset Lattice,
      (F : Set Lattice) ⊆ P.enlargement n →
      HasFiniteSweep S (P.lattice ∪ (E k : Set Lattice)) F := by
  obtain ⟨K, hK, hs⟩ := region_finite_seed_all_layers ξ S hS P hweak
    (region_complete_arc_compatible harc) n
  obtain ⟨hmono, hUnion⟩ := literal_candidates_union W G P hP harc L n E hE
  obtain ⟨k, hk⟩ := finite_subset_eventual_capture hmono K (by rw [hUnion]; exact hK)
  refine ⟨max j₀ k, le_max_left _ _, ?_⟩
  intro F hF
  apply paidSweepMono _ (hs F hF)
  exact Set.union_subset_union (Set.Subset.refl _) (hk _ (le_max_right _ _))

private theorem literal_fixed_seed_eventual_targets {ξ xper : Configuration ℤ}
    {S : Finset Lattice} (hS : GeneratingSet ξ S)
    {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (hP : P.lattice = normalisedUnion W G) (hweak : WeaklyEnveloped S P)
    (harc : RegionCompleteArc C i G.J P) (L : NormalisedWindowLimit W G)
    (n : ℕ) (E : ℕ → Finset Lattice) (j₀ : ℕ)
    (hE : ∀ j, (E j : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
      (P.enlargement n)) :
    ∃ k : ℕ, j₀ ≤ k ∧ ∀ F : Finset Lattice,
      (F : Set Lattice) ⊆ P.enlargement n →
      ∃ l : ℕ, ∀ j ≥ l,
      HasFiniteSweep S ((W.normalised (G.subsequence (L.index j)) : Set Lattice) ∪
        (E k : Set Lattice)) F := by
  obtain ⟨k, hk, hs⟩ := literal_fixed_seed_global_sweep hS W G P hP hweak harc L n E j₀ hE
  refine ⟨k, hk, ?_⟩
  intro F hF
  have h := hs F hF
  have he : P.lattice = ⋃ j, (W.normalised (G.subsequence (L.index j)) : Set Lattice) :=
    hP.trans L.same_union.symm
  rw [he] at h
  exact finite_sweep_eventual_capture ((paidNormalisedMono G).comp L.strict.monotone) h


private theorem finite_sweep_of_confined_placements {S F : Finset Lattice}
    {U : Set Lattice} (p : Lattice) (hp : WindowVertex S p)
    (height : Lattice → ℤ)
    (hheight : ∀ z : Lattice, ∀ q ∈ S.erase p, height z < height (z + (q - p)))
    (hconfined : ∀ z ∈ F, z ∉ U → ∀ q ∈ S.erase p, z + (q - p) ∈ F) :
    HasFiniteSweep S U F := by
  classical
  let M : ℕ := F.sup fun z => (height z).natAbs
  have hM : ∀ z ∈ F, height z ≤ (M : ℤ) := by
    intro z hz
    have hh : (height z).natAbs ≤ M := Finset.le_sup (f := fun z => (height z).natAbs) hz
    exact Int.le_natAbs.trans (by exact_mod_cast hh)
  apply finite_sweep_of_decreasing_placements (fun z => ((M : ℤ) - height z).toNat)
  intro z hz hzU
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hy := hconfined z hz hzU q hq
  refine Or.inr ⟨hy, ?_⟩
  have hzy := hheight z q hq
  have hMz := hM z hz
  have hMy := hM _ hy
  omega

local macro "paidCycleRun" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.RegionArcSweeps).num 0 ++ `ConvexNivat.Colle.cycle_edge_generated_run))
local macro "paidSupportDet" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.FixedPatchSteps).num 0 ++ `ConvexNivat.Colle.support_det_nonneg))

private theorem cycle_terminal_strict_height {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (J : ℤ) (z q : Lattice)
    (hq : q ∈ S.erase (C.vertex (J + 1))) :
    det (C.direction J) z + det (C.direction (J + 1)) z <
      det (C.direction J) (z + (q - C.vertex (J + 1))) +
      det (C.direction (J + 1)) (z + (q - C.vertex (J + 1))) := by
  let w := C.direction J
  let d := C.direction (J + 1)
  let b := C.vertex (J + 1)
  have hqS := Finset.mem_of_mem_erase hq
  have hw : 0 ≤ det w (q - b) := paidSupportDet (C.terminal_mem J) hqS
  have hd : 0 ≤ det d (q - b) := paidSupportDet (C.initial_mem (J + 1)) hqS
  have hD : 0 < det w d := paidCycleTurn C J
  have hpos : 0 < det w (q - b) + det d (q - b) := by
    by_contra hn
    have hw0 : det w (q - b) = 0 := by omega
    have hd0 : det d (q - b) = 0 := by omega
    have hrow : det w b = det w q := by
      have he : det w (q - b) = det w q - det w b := by simp [det]; ring
      rw [he] at hw0
      omega
    obtain ⟨r, hr⟩ := (primitive_row_coordinates w (C.primitive J)).2.1 b q |>.mp hrow
    have hmul : r * det d w = 0 := by
      rw [hr] at hd0
      have he : det d (b + r • w - b) = r * det d w := by simp [det]; ring
      rw [he] at hd0
      exact hd0
    have hdn : det d w ≠ 0 := by
      have he : det d w = -det w d := by simp [det]; ring
      rw [he]
      omega
    have hr0 : r = 0 := (mul_eq_zero.mp hmul).resolve_right hdn
    have hqb : q = b := by simpa [hr0] using hr
    exact (Finset.mem_erase.mp hq).1 hqb
  have he :
      det w (z + (q - b)) + det d (z + (q - b)) =
      det w z + det d z + (det w (q - b) + det d (q - b)) := by
    simp [det]
    ring
  change det w z + det d z < det w (z + (q - b)) + det d (z + (q - b))
  rw [he]
  omega

private theorem cycle_terminal_confined_sweep {S F : Finset Lattice}
    {m : ℕ} (C : AntipodalEdgeCycle S m) (hconvex : LatticeConvex S)
    (J : ℤ) (U : Set Lattice)
    (hconfined : ∀ z ∈ F, z ∉ U → ∀ q ∈ S.erase (C.vertex (J + 1)),
      z + (q - C.vertex (J + 1)) ∈ F) : HasFiniteSweep S U F := by
  obtain ⟨ell, hell, heq, hrow, ha, hb⟩ := paidCycleRun C hconvex J
  exact finite_sweep_of_confined_placements (C.vertex (J + 1)) hb
    (fun z => det (C.direction J) z + det (C.direction (J + 1)) z)
    (cycle_terminal_strict_height C J) hconfined


private theorem candidate_sweep_of_confined_placements {S : Finset Lattice}
    {m : ℕ} (C : AntipodalEdgeCycle S m) (hconvex : LatticeConvex S)
    (J : ℤ) (A E : ℕ → Finset Lattice) (j₀ : ℕ)
    (hconfined : ∃ k : ℕ, j₀ ≤ k ∧ ∀ j ≥ k, ∀ z ∈ E j,
      z ∉ ((A j : Set Lattice) ∪ (E k : Set Lattice)) →
      ∀ q ∈ S.erase (C.vertex (J + 1)), z + (q - C.vertex (J + 1)) ∈ E j) :
    ∃ k : ℕ, j₀ ≤ k ∧ ∀ j ≥ k,
      HasFiniteSweep S ((A j : Set Lattice) ∪ (E k : Set Lattice)) (E j) := by
  obtain ⟨k, hk, hconfined⟩ := hconfined
  exact ⟨k, hk, fun j hj => cycle_terminal_confined_sweep C hconvex J _ (hconfined j hj)⟩

end
end ConvexNivat.Colle
