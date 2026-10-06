import ConvexNivat.SectorDefinitions

open scoped BigOperators
namespace ConvexNivat
noncomputable section

/-- Lemma 3.0, exact sign conclusion for geometrically adjacent sectors. -/
theorem sectors_adjacent_signs {p : ℕ} (star : StarData p) (i : Fin star.m)
    (σ : RayOrientation) (ε ε' : SectorSigns star)
    (hadj : SectorsAdjacentAtRay star i σ ε ε') :
    ε i ≠ ε' i ∧ ∀ j, j ≠ i →
      ε j = raySide star i j σ ∧ ε' j = raySide star i j σ := by
  have hweak (δ : SectorSigns star)
      (hδ : embed (σ.sign • (star.component i).direction) ∈ closure (sectorCone star δ))
      (j : Fin star.m) :
      match δ j with
      | .left => realHeight (star.component j).direction
          (embed (σ.sign • (star.component i).direction)) ≤ 0
      | .right => 0 ≤ realHeight (star.component j).direction
          (embed (σ.sign • (star.component i).direction)) := by
    have hc : Continuous (realHeight (star.component j).direction) := by
      unfold realHeight
      fun_prop
    cases hd : δ j with
    | left =>
        apply closure_minimal (t := {x | realHeight (star.component j).direction x ≤ 0})
          ?_ (isClosed_le hc continuous_const) hδ
        intro x hx
        exact le_of_lt (by simpa only [sectorCone, Set.mem_ofPred_eq, hd] using hx j)
    | right =>
        apply closure_minimal (t := {x | 0 ≤ realHeight (star.component j).direction x})
          ?_ (isClosed_le continuous_const hc) hδ
        intro x hx
        exact le_of_lt (by simpa only [sectorCone, Set.mem_ofPred_eq, hd] using hx j)
  have heval (j : Fin star.m) :
      realHeight (star.component j).direction
        (embed (σ.sign • (star.component i).direction)) =
      (σ.sign * det (star.component j).direction (star.component i).direction : ℤ) := by
    simp [realHeight, embed, det]
    ring
  have hsign (δ : SectorSigns star)
      (hδ : embed (σ.sign • (star.component i).direction) ∈ closure (sectorCone star δ))
      (j : Fin star.m) (hji : j ≠ i) : δ j = raySide star i j σ := by
    have hn : σ.sign * det (star.component j).direction (star.component i).direction ≠ 0 := by
      apply mul_ne_zero
      · cases σ <;> simp [RayOrientation.sign]
      · exact star.pairwise_nonparallel j i hji
    have hw := hweak δ hδ j
    rw [heval] at hw
    unfold raySide
    split_ifs with hp
    · have hr : (0 : ℝ) <
          (σ.sign * det (star.component j).direction (star.component i).direction : ℤ) := by
        exact_mod_cast hp
      cases hs : δ j <;> simp only [hs] at hw ⊢
      linarith
    · have hr :
          (σ.sign * det (star.component j).direction (star.component i).direction : ℤ) < (0 : ℝ) := by
        exact_mod_cast lt_of_le_of_ne (le_of_not_gt hp) hn
      cases hs : δ j <;> simp only [hs] at hw ⊢
      linarith
  rcases hadj with ⟨_, _, hne, hε, hε'⟩
  have ho : ∀ j, j ≠ i → ε j = raySide star i j σ ∧ ε' j = raySide star i j σ := by
    intro j hji
    exact ⟨hsign ε hε j hji, hsign ε' hε' j hji⟩
  refine ⟨?_, ho⟩
  intro hi
  apply hne
  funext j
  by_cases hji : j = i
  · simpa [hji] using hi
  · exact (ho j hji).1.trans (ho j hji).2.symm


/-- Lemma 3.0, equality of the unordered pair of actual backgrounds. -/
theorem sectors_adjacent_backgrounds {p : ℕ} (star : StarData p)
    (i : Fin star.m) (σ : RayOrientation) (ε ε' : SectorSigns star)
    (hadj : SectorsAdjacentAtRay star i σ ε ε') :
    ({sectorBackground star ε, sectorBackground star ε'} :
      Set (Configuration (ZMod p))) =
    {pureRayBackground star i σ .left, pureRayBackground star i σ .right} := by
  classical
  obtain ⟨hne, hs⟩ := sectors_adjacent_signs star i σ ε ε' hadj
  have heq (δ : SectorSigns star)
      (hδ : ∀ j, j ≠ i → δ j = raySide star i j σ) :
      sectorBackground star δ = pureRayBackground star i σ (δ i) := by
    funext z
    change (∑ j : Fin star.m, componentTail star j (δ j) z) =
      componentTail star i (δ i) z +
        ∑ j ∈ Finset.univ.erase i, rayTail star i j σ z
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hδ j (Finset.mem_erase.mp hj).1]
    simp only [raySide, rayTail]
    split_ifs <;> rfl
  rw [heq ε (fun j hj => (hs j hj).1), heq ε' (fun j hj => (hs j hj).2)]
  cases hε : ε i <;> cases hε' : ε' i
  · exact False.elim (hne (hε.trans hε'.symm))
  · rfl
  · exact Set.pair_comm _ _
  · exact False.elim (hne (hε.trans hε'.symm))


end
end ConvexNivat
