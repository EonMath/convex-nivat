import NivatTrial.GeneratingWindows

/-! The ambiguity multiplicity of a restriction is counted inside the actual
language of a configuration. This is the finite combinatorial budget used in
Colle's semi-ambiguity arguments. -/

namespace NivatTrial.ColleAmbiguity

open NivatTrial.Dynamics NivatTrial.AmbiguityPropagation
open NivatTrial.Nonexpansive NivatTrial.MorseHedlund NivatTrial.Periodicity
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

variable {A : Type*} [Fintype A]

/-- The sites on the exposed support line. This definition works without a
chosen minimizing point and also for an empty window. -/
def supportEdge (S : Finset G) (v : Plane) : Finset G :=
  S.filter (fun g => ∀ s ∈ S, score v g ≤ score v s)

def supportBase (S : Finset G) (v : Plane) : Finset G :=
  S \ supportEdge S v

theorem supportBase_subset (S : Finset G) (v : Plane) :
    supportBase S v ⊆ S := Finset.sdiff_subset

theorem supportEdge_subset (S : Finset G) (v : Plane) :
    supportEdge S v ⊆ S := Finset.filter_subset _ _

theorem supportBase_disjoint_edge (S : Finset G) (v : Plane) :
    Disjoint (supportBase S v) (supportEdge S v) := by
  apply Finset.disjoint_left.mpr
  intro z hzbase hzedge
  exact (Finset.mem_sdiff.mp hzbase).2 hzedge

theorem supportBase_union_edge (S : Finset G) (v : Plane) :
    supportBase S v ∪ supportEdge S v = S := by
  simp [supportBase, Finset.sdiff_union_self_eq_union,
    Finset.union_eq_left.mpr (supportEdge_subset S v)]

/-- The restriction from actual `S` patterns to actual base patterns is
surjective, so every base pattern has at least one extension. -/
def restriction (θ : G → A) (S : Finset G) (v : Plane) :
    patternSet θ S → patternSet θ (supportBase S v) :=
  patternRestriction θ (supportBase_subset S v)

theorem restriction_surjective (θ : G → A) (S : Finset G) (v : Plane) :
    Function.Surjective (restriction θ S v) :=
  patternRestriction_surjective θ (supportBase_subset S v)

def multiplicity (θ : G → A) (S : Finset G) (v : Plane)
    (p : patternSet θ (supportBase S v)) : ℕ :=
  extensionCount (restriction θ S v) p

def AmbiguousPattern (θ : G → A) (S : Finset G) (v : Plane)
    (p : patternSet θ (supportBase S v)) : Prop :=
  2 ≤ multiplicity θ S v p

def ambiguousPatterns (θ : G → A) (S : Finset G) (v : Plane) :
    Finset (patternSet θ (supportBase S v)) :=
  Finset.univ.filter (AmbiguousPattern θ S v)

theorem ambiguity_count_bound (θ : G → A) (S : Finset G) (v : Plane) :
    (ambiguousPatterns θ S v).card +
      patternComplexity θ (supportBase S v) ≤ patternComplexity θ S := by
  have h := multiextension_card_bound (restriction θ S v)
    (restriction_surjective θ S v) (ambiguousPatterns θ S v) (by
      intro p hp
      exact (Finset.mem_filter.mp hp).2)
  simpa [patternComplexity, AmbiguousPattern, multiplicity,
    Nat.card_eq_fintype_card] using h

theorem ambiguity_count_lt_edge (θ : G → A) (S : Finset G)
    (v : Plane)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card) :
    (ambiguousPatterns θ S v).card < (supportEdge S v).card := by
  have h := ambiguity_count_bound θ S v
  omega

/-- Every directional pattern of a fully ambiguous hull point maps to an
ambiguous base pattern of the original configuration. -/
theorem directional_complexity_le_ambiguity_count
    (θ : G → A) (S : Finset G) (v : Plane) (u : G)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hamb : ∀ i : ℤ,
      AmbiguousPattern θ S v
        ⟨patternAt x (supportBase S v) (i • u),
          patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩) :
    directionalComplexity x (supportBase S v) u ≤
      (ambiguousPatterns θ S v).card := by
  let f : directionalPatternSet x (supportBase S v) u →
      {p : patternSet θ (supportBase S v) // p ∈ ambiguousPatterns θ S v} :=
    fun p => by
      refine ⟨⟨p.val.val, patternSet_subset_of_mem_languageHull hx _ p.val.property⟩, ?_⟩
      obtain ⟨i, hi⟩ := p.property
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hval : p.val.val = patternAt x (supportBase S v) (i • u) :=
        congrArg Subtype.val hi.symm
      simpa only [hval] using (hamb i)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : {p : patternSet θ (supportBase S v) //
        p ∈ ambiguousPatterns θ S v} => r.val.val) hpq
  have hcard := Fintype.card_le_of_injective f hf
  simpa [directionalComplexity, Nat.card_eq_fintype_card] using hcard

theorem directional_complexity_lt_edge
    (θ : G → A) (S : Finset G) (v : Plane) (u : G)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card)
    (hamb : ∀ i : ℤ,
      AmbiguousPattern θ S v
        ⟨patternAt x (supportBase S v) (i • u),
          patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩) :
    directionalComplexity x (supportBase S v) u <
      (supportEdge S v).card := by
  have h₁ := directional_complexity_le_ambiguity_count θ S v u hx hamb
  have h₂ := ambiguity_count_lt_edge θ S v hbudget
  omega

/-- A full family of ambiguous extensions forces a periodic row whenever the
base contains a run at least as long as the exposed edge. This is the
Morse--Hedlund counting step in the semi-ambiguity argument. -/
theorem ambiguous_row_periodic
    (θ : G → A) (S : Finset G) (v : Plane) (u w : G) (n : ℕ)
    {x : G → A} (hx : x ∈ languageHull θ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card)
    (hamb : ∀ i : ℤ,
      AmbiguousPattern θ S v
        ⟨patternAt x (supportBase S v) (i • u),
          patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩)
    (hrun : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ supportBase S v)
    (hlen : (supportEdge S v).card ≤ n) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod (rowSequence x w u) (q : ℤ) := by
  have hdir := directional_complexity_lt_edge θ S v u hx hbudget hamb
  have hrow := row_wordComplexity_le_directional x (supportBase S v) w u n hrun
  apply morse_hedlund (n := n)
  omega

end

end NivatTrial.ColleAmbiguity
