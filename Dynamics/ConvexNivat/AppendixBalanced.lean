import ConvexNivat.AppendixBase
import ConvexNivat.AppendixRows
import ConvexNivat.MorseHedlund

namespace ConvexNivat
open scoped BigOperators

/-- D.5: existence of the sign and actual finite balanced subwindow. -/
theorem lemmaD_5 {A : Type*} [Finite A] (θ : Configuration A)
    (u : Lattice) (hu : Primitive u) (S : Finset Lattice)
    (hS : S.Nonempty) (hconvex : LatticeConvex S) (hlow : complexity θ S ≤ S.card) :
    ∃ σ : ℤ, ∃ B : Finset Lattice, B ⊆ S ∧ BalancedSet θ u σ B := by
  classical
  revert hS hconvex hlow
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS hconvex hlow
    have hnonempty : ∀ σ : ℤ, (extremeRow σ u S hS).Nonempty := by
      intro σ
      by_cases hσ : σ = 1
      · obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_sup' hS (det u)
        exact ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa [extremeRow,hσ,rowMaximum] using he.symm⟩⟩
      · obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_inf' hS (det u)
        exact ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa [extremeRow,hσ,rowMinimum] using he.symm⟩⟩
    obtain ⟨σ, hσ, hsmall⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
        (extremeRow σ u S hS).card ≤ (extremeRow (-σ) u S hS).card := by
      rcases le_total (extremeRow 1 u S hS).card (extremeRow (-1) u S hS).card with h | h
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨-1, Or.inr rfl, by simpa using h⟩
    let E := extremeRow σ u S hS
    let T := S \ E
    have hEsub : E ⊆ S := Finset.filter_subset _ _
    have hEcard : 0 < E.card := Finset.card_pos.mpr (hnonempty σ)
    have hcards : T.card + E.card = S.card := Finset.card_sdiff_add_card_eq_card hEsub
    have hTconvex : LatticeConvex T := delete_extreme_row_convex u S hS hconvex σ hσ
    by_cases hTlow : complexity θ T ≤ T.card
    · have hTne : T.Nonempty := by
        by_contra h
        have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        rw [hTempty, complexity_empty] at hTlow
        simp at hTlow
      have hproper : T ⊂ S := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro he
        have hc := congrArg Finset.card he
        omega
      obtain ⟨τ, B, hBsub, hbalanced⟩ := ih T hproper hTne hTconvex hTlow
      exact ⟨τ, B, hBsub.trans Finset.sdiff_subset, hbalanced⟩
    · refine ⟨σ, S, Finset.Subset.refl S, hS, hconvex, hσ, hlow, ?_, ?_⟩
      · change complexity θ S < complexity θ T + E.card
        omega
      · exact intermediate_row_cardinality u hu S hS hconvex σ hσ hsmall

private theorem d_equal_determines {A : Type*} [Finite A]
    (θ : Configuration A) (D : Finset Lattice) (e : Lattice)
    (h : complexity θ (insert e D) = complexity θ D) : PatternDetermines θ D e := by
  classical
  let P := insert e D
  let r : Pattern A P → Pattern A D := fun w z => w ⟨z.val, Finset.mem_insert_of_mem z.property⟩
  have hrange : r '' patternSet θ P = patternSet θ D := by
    ext w
    constructor
    · rintro ⟨v, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨pattern θ P s, ⟨s, rfl⟩, rfl⟩
  have hinj : Set.InjOn r (patternSet θ P) := by
    apply Set.injOn_of_ncard_image_eq (hs := patternSet_finite θ P)
    rw [hrange]
    exact h.symm
  intro x hx y hy t he
  have hxP : pattern x P t ∈ patternSet θ P :=
    orbitClosure_patternSet_subset θ x hx P (Set.mem_range_self t)
  have hyP : pattern y P t ∈ patternSet θ P :=
    orbitClosure_patternSet_subset θ y hy P (Set.mem_range_self t)
  have hr : r (pattern x P t) = r (pattern y P t) := by
    funext z
    exact (by simpa [r,pattern,add_comm] using he z.val z.property)
  have hp := hinj hxP hyP hr
  simpa [pattern,add_comm] using congrFun hp ⟨e, Finset.mem_insert_self e D⟩

private theorem d_chain_rule {A : Type*} [Finite A]
    (θ : Configuration A) (D E : Finset Lattice) (n : ℕ) (f : ℕ → Lattice)
    (hE : (Finset.range n).image f = E)
    (hgrowth : complexity θ (D ∪ E) < complexity θ D + n) :
    ∃ k < n, PatternDetermines θ (D ∪ (Finset.range k).image f) (f k) := by
  classical
  let F : ℕ → Finset Lattice := fun k => D ∪ (Finset.range k).image f
  have hs : ∀ k, F k ⊆ F (k+1) := by
    intro k
    apply Finset.union_subset_union_right
    exact Finset.image_subset_image (Finset.range_mono (by omega))
  have hlast : F n = D ∪ E := by simp only [F,hE]
  have hfirst : F 0 = D := by simp [F]
  have hflat : ∃ k < n, complexity θ (F (k+1)) = complexity θ (F k) := by
    by_contra h
    have hstrict : ∀ k < n, complexity θ (F k) < complexity θ (F (k+1)) := by
      intro k hk
      apply lt_of_le_of_ne (complexity_mono θ _ _ (hs k))
      intro he
      exact h ⟨k,hk,he.symm⟩
    have hcount : ∀ k ≤ n, complexity θ D + k ≤ complexity θ (F k) := by
      intro k
      induction k with
      | zero => intro hk; rw [hfirst]; omega
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hstep := hstrict k (by omega)
        omega
    have he := hcount n le_rfl
    rw [hlast] at he
    omega
  obtain ⟨k,hk,hflat⟩ := hflat
  refine ⟨k,hk,d_equal_determines θ (F k) (f k) ?_⟩
  have hnext : F (k+1) = insert (f k) (F k) := by
    simp [F,Finset.range_add_one,Finset.union_insert]
  rwa [hnext] at hflat


/-- D.7(2): both left and right finite determination rules from balancedness.
The upper row is indexed starting at zero, so Dₖ determines eₖ. -/
theorem balanced_two_determination_rules {A : Type*} [Finite A]
    (θ : Configuration A) (u : Lattice) (hu : Primitive u)
    (B : Finset Lattice) (hB : BalancedSet θ u 1 B)
    (e : Lattice) (he : ∀ z,
      z ∈ extremeRow 1 u B hB.nonempty ↔
        ∃ j : ℕ, j < (extremeRow 1 u B hB.nonempty).card ∧ z = e + (j : ℤ) • u) :
    ∃ k k' : ℕ,
      k < (extremeRow 1 u B hB.nonempty).card ∧
      k' < (extremeRow 1 u B hB.nonempty).card ∧
      PatternDetermines θ
        ((B \ extremeRow 1 u B hB.nonempty) ∪
          (Finset.range k).image (fun j : ℕ => e + (j : ℤ) • u)) (e + (k : ℤ) • u) ∧
      PatternDetermines θ
        ((B \ extremeRow 1 u B hB.nonempty) ∪
          (Finset.range k').image (fun j =>
            e + ((extremeRow 1 u B hB.nonempty).card - 1 - j : ℕ) • u))
        (e + ((extremeRow 1 u B hB.nonempty).card - 1 - k' : ℕ) • u)  := by
  classical
  let E := extremeRow 1 u B hB.nonempty
  let D := B \ E
  let n := E.card
  have he' : ∀ z, z ∈ E ↔ ∃ j : ℕ, j < n ∧ z = e + (j : ℤ) • u := he
  have hEsub : E ⊆ B := Finset.filter_subset _ _
  have hDE : D ∪ E = B := Finset.sdiff_union_of_subset hEsub
  have hleft : (Finset.range n).image (fun j : ℕ => e + (j : ℤ) • u) = E := by
    ext z
    simp only [Finset.mem_image,Finset.mem_range]
    simpa only [eq_comm] using (he' z).symm
  have hright : (Finset.range n).image (fun j : ℕ => e + ((n-1-j : ℕ) : ℤ) • u) = E := by
    ext z
    simp only [Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact (he' _).mpr ⟨n-1-j,by omega,rfl⟩
    · intro hz
      obtain ⟨j,hj,rfl⟩ := (he' z).mp hz
      refine ⟨n-1-j,by omega,?_⟩
      have hji : n-1-(n-1-j)=j := by omega
      rw [hji]
  have hg : complexity θ (D ∪ E) < complexity θ D + n := by
    rw [hDE]
    exact hB.strict_growth
  obtain ⟨k,hk,hkdet⟩ := d_chain_rule θ D E n (fun j : ℕ => e + (j : ℤ) • u) hleft hg
  obtain ⟨k',hk',hk'det⟩ := d_chain_rule θ D E n
    (fun j : ℕ => e + ((n-1-j : ℕ) : ℤ) • u) hright hg
  exact ⟨k,k',hk,hk',hkdet,hk'det⟩


end ConvexNivat
