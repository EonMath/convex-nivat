import NivatTrial.ColleAmbiguity

/-! Low convex complexity supplies a minimal convex window. Every removable
vertex is generated, and deleting any support face consumes fewer patterns
than sites. These are the two assertions of Colle's Lemma 2.4. -/

namespace NivatTrial.ColleGenerating

open NivatTrial.Dynamics NivatTrial.LatticePolygon NivatTrial.Zonotope
open NivatTrial.Nonexpansive NivatTrial.GeneratingWindows NivatTrial.ColleAmbiguity
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def linearScore (v : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun x := v.1 * x.2 - v.2 * x.1
  map_add' x y := by
    simp
    ring
  map_smul' a x := by
    simp [smul_eq_mul]
    ring

theorem linearScore_embed (v : Plane) (z : G) :
    linearScore v (embed z) = score v z := rfl

theorem supportEdge_nonempty (S : Finset G) (v : Plane)
    (hS : S.Nonempty) : (supportEdge S v).Nonempty := by
  obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image S (score v) hS
  exact ⟨g, Finset.mem_filter.mpr ⟨hg, hmin⟩⟩

theorem supportBase_ne (S : Finset G) (v : Plane) (hS : S.Nonempty) :
    supportBase S v ≠ S := by
  obtain ⟨g, hg⟩ := supportEdge_nonempty S v hS
  intro heq
  exact (Finset.mem_sdiff.mp (heq ▸ (supportEdge_subset S v hg))).2 hg

/-- Removing the exposed face preserves lattice convexity. The strict
support inequality is preserved by convex hull. -/
theorem supportBase_latticeConvex (S : Finset G) (v : Plane)
    (hS : IsLatticeConvex S) :
    IsLatticeConvex (supportBase S v) := by
  by_cases hempty : S.Nonempty
  · obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image S (score v) hempty
    have hconv : Convex ℝ {x : Plane | linearScore v (embed g) < linearScore v x} :=
      convex_halfSpace_gt (linearScore v).isLinear (linearScore v (embed g))
    have hsub : embed '' ((supportBase S v : Finset G) : Set G) ⊆
        {x : Plane | linearScore v (embed g) < linearScore v x} := by
      rintro x ⟨z, hz, rfl⟩
      have hzS : z ∈ S := supportBase_subset S v hz
      have hznot : z ∉ supportEdge S v := (Finset.mem_sdiff.mp hz).2
      change score v g < score v z
      by_contra h
      apply hznot
      apply Finset.mem_filter.mpr
      refine ⟨hzS, ?_⟩
      intro s hs
      exact (le_of_not_gt h).trans (hmin s hs)
    intro z
    constructor
    · intro hz
      have hzS : z ∈ S := (hS z).mp
        (convexHull_mono (Set.image_mono (supportBase_subset S v)) hz)
      have hzgt : score v g < score v z := by
        have h := convexHull_min hsub hconv hz
        simpa [linearScore_embed] using h
      have hznot : z ∉ supportEdge S v := by
        intro hedge
        have hzg := (Finset.mem_filter.mp hedge).2 g hg
        linarith
      exact Finset.mem_sdiff.mpr ⟨hzS, hznot⟩
    · exact mem_windowHull_of_mem _
  · have h0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simpa [h0, supportBase, supportEdge] using hS

variable {A : Type*} [Fintype A]

/-- The source's finite η-generating set, expressed by the exact removable
vertex criterion and a support-face budget valid for every real direction. -/
structure GeneratingWindow (θ : G → A) (T : Finset G) : Prop where
  nonempty : T.Nonempty
  latticeConvex : IsLatticeConvex T
  generated_vertex : ∀ g ∈ T, IsLatticeConvex (T.erase g) → Generated θ T g
  strict_edge_budget : ∀ v : Plane,
    patternComplexity θ T <
      patternComplexity θ (supportBase T v) + (supportEdge T v).card

private theorem low_implies_nonempty (θ : G → A) (T : Finset G)
    (hlow : patternComplexity θ T ≤ T.card) : T.Nonempty := by
  by_contra h
  have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [hT, patternComplexity_empty] at hlow

/-- Choose a minimum-cardinality convex low-complexity subwindow. Its strict
proper-subwindow complexity is a conclusion of minimality, not a premise. -/
theorem exists_generating_window (θ : G → A) (S : Finset G)
    (hS : IsLatticeConvex S)
    (hlow : patternComplexity θ S ≤ S.card) :
    ∃ T : Finset G, T ⊆ S ∧ GeneratingWindow θ T ∧
      patternComplexity θ T ≤ T.card := by
  let C : Finset (Finset G) := S.powerset.filter
    (fun U => IsLatticeConvex U ∧ patternComplexity θ U ≤ U.card)
  have hSC : S ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl, hS, hlow⟩
  obtain ⟨T, hTC, hmin⟩ :=
    Finset.exists_min_image C Finset.card ⟨S, hSC⟩
  have hTS : T ⊆ S := (Finset.mem_powerset.mp (Finset.mem_filter.mp hTC).1)
  have hconv : IsLatticeConvex T := (Finset.mem_filter.mp hTC).2.1
  have hlowT : patternComplexity θ T ≤ T.card := (Finset.mem_filter.mp hTC).2.2
  have hT : T.Nonempty := low_implies_nonempty θ T hlowT
  have hproper (U : Finset G) (hUT : U ⊆ T) (hUneq : U ≠ T)
      (hUconv : IsLatticeConvex U) :
      U.card < patternComplexity θ U := by
    by_cases hUempty : U = ∅
    · simp [hUempty, patternComplexity_empty]
    · by_contra h
      have hlowU : patternComplexity θ U ≤ U.card := Nat.le_of_not_gt h
      have hUC : U ∈ C := by
        simp only [C, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hUT.trans hTS, hUconv, hlowU⟩
      have hminU := hmin U hUC
      have hlt := Finset.card_lt_card
        ((Finset.ssubset_iff_subset_ne).mpr ⟨hUT, hUneq⟩)
      omega
  refine ⟨T, hTS, ⟨hT, hconv, ?_, ?_⟩, hlowT⟩
  · intro g hg hconvErase
    have hsub : T.erase g ⊆ T := Finset.erase_subset g T
    have hne : T.erase g ≠ T := by
      intro heq
      have hmem : g ∈ T.erase g := heq.symm ▸ hg
      simp at hmem
    have hstrict := hproper (T.erase g) hsub hne hconvErase
    have hmono := patternComplexity_mono θ hsub
    have hcard : (T.erase g).card + 1 = T.card := by
      simpa using Finset.card_erase_add_one hg
    refine ⟨hg, ?_⟩
    omega
  · intro v
    have hsub : supportBase T v ⊆ T := supportBase_subset T v
    have hne : supportBase T v ≠ T := supportBase_ne T v hT
    have hconvBase := supportBase_latticeConvex T v hconv
    have hstrict := hproper (supportBase T v) hsub hne hconvBase
    have hcard := Finset.card_sdiff_add_card_eq_card (supportEdge_subset T v)
    change (supportBase T v).card + (supportEdge T v).card = T.card at hcard
    omega

end

end NivatTrial.ColleGenerating
