import NivatTrial.ColleTailWords

/-! Semi-ambiguous directional anchors occupy only the true extension
surplus. A long row segment in the base then has eventual row periodicity. -/

namespace NivatTrial.ColleSemiAmbiguity

open NivatTrial.Dynamics NivatTrial.AmbiguityPropagation
open NivatTrial.ColleAmbiguity NivatTrial.ColleTailWords NivatTrial.MorseHedlund
open scoped Classical

noncomputable section

abbrev G := ℤ × ℤ
abbrev Plane := ℝ × ℝ

variable {A : Type*} [Fintype A]

/-- The source's positive semi-ambiguity, with an explicit starting anchor.
Membership in the original language is supplied by the hull hypothesis. -/
def SemiAmbiguous (θ : G → A) (S : Finset G) (v : Plane) (u : G)
    (x : G → A) (hx : x ∈ languageHull θ) (τ : ℤ) : Prop :=
  ∀ i : ℤ, τ ≤ i → AmbiguousPattern θ S v
    ⟨patternAt x (supportBase S v) (i • u),
      patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩

/-- Each tail word of a row chooses an ambiguous actual base pattern; distinct
words choose distinct base patterns because the base contains the row run. -/
theorem tail_wordComplexity_le_ambiguity_count
    (θ : G → A) (S : Finset G) (v : Plane) (u w : G)
    (n : ℕ) (τ : ℤ) {x : G → A} (hx : x ∈ languageHull θ)
    (hamb : SemiAmbiguous θ S v u x hx τ)
    (hrun : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ supportBase S v) :
    tailWordComplexity (rowSequence x w u) n τ ≤
      (ambiguousPatterns θ S v).card := by
  let index (p : tailWordSet (rowSequence x w u) n τ) : ℤ :=
    Classical.choose p.property
  have hindex (p : tailWordSet (rowSequence x w u) n τ) :
      τ ≤ index p ∧ p.val = wordAt (rowSequence x w u) n (index p) :=
    Classical.choose_spec p.property
  let f : tailWordSet (rowSequence x w u) n τ →
      {p : patternSet θ (supportBase S v) // p ∈ ambiguousPatterns θ S v} :=
    fun p => by
      let i := index p
      refine ⟨⟨patternAt x (supportBase S v) (i • u),
        patternSet_subset_of_mem_languageHull hx _ ⟨i • u, rfl⟩⟩, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hamb i (hindex p).1⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hpatterns : patternAt x (supportBase S v) (index p • u) =
        patternAt x (supportBase S v) (index q • u) :=
      congrArg (fun r : {p : patternSet θ (supportBase S v) //
        p ∈ ambiguousPatterns θ S v} => r.val.val) hpq
    apply Subtype.ext
    rw [(hindex p).2, (hindex q).2]
    funext j
    have hs := congrFun hpatterns ⟨w + (j.val : ℤ) • u, hrun j⟩
    simpa [patternAt, wordAt, rowSequence, add_smul,
      add_assoc, add_comm, add_left_comm] using hs
  have hcard := Fintype.card_le_of_injective f hf
  simpa [tailWordComplexity, Nat.card_eq_fintype_card] using hcard

theorem semi_ambiguous_row_eventually_periodic
    (θ : G → A) (S : Finset G) (v : Plane) (u w : G)
    (n : ℕ) (τ : ℤ) {x : G → A} (hx : x ∈ languageHull θ)
    (hamb : SemiAmbiguous θ S v u x hx τ)
    (hbudget : patternComplexity θ S <
      patternComplexity θ (supportBase S v) + (supportEdge S v).card)
    (hrun : ∀ j : Fin n, w + (j.val : ℤ) • u ∈ supportBase S v)
    (hlen : (supportEdge S v).card - 1 ≤ n) :
    ∃ N q : ℕ, 0 < q ∧
      ∀ i : ℤ, τ + N ≤ i → x (w + (i + q) • u) = x (w + i • u) := by
  have hcount := tail_wordComplexity_le_ambiguity_count θ S v u w n τ hx hamb hrun
  have hedge := ambiguity_count_lt_edge θ S v hbudget
  obtain ⟨N,q,hq,hper⟩ := tail_morse_hedlund (rowSequence x w u) τ
    (n := n) (by omega)
  exact ⟨N,q,hq,fun i hi => hper i hi⟩

end

end NivatTrial.ColleSemiAmbiguity
