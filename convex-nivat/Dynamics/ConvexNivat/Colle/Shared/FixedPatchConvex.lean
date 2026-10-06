import ConvexNivat.Colle.Shared.FixedPatchLimitSteps
import ConvexNivat.Colle.Shared.SaturationSteps

namespace ConvexNivat.Colle
noncomputable section

local macro "paidNoHoles" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_one_ray_no_holes))
local macro "paidFibres" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_cycle_window_fibres))
local macro "paidRayConvex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.SaturationSteps).num 0 ++ `ConvexNivat.Colle.sat_real_ray_convex))
local macro "paidHullConvex" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.Shared.HullBoundary).num 0 ++ `ConvexNivat.Colle.rj_hull_convex))
local macro "paidTranslatedEnvelope" : term =>
  pure (Lean.mkIdent ((`_private.ConvexNivat.Colle.ArcColle35).num 0 ++ `ConvexNivat.Colle.colle35_translate_enveloped))

private theorem candidate_lattice_convex {S A : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hA : EnvelopedWindow S A) (j : ℤ)
    {v w : Lattice} (P : Region v w) (n : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice) = backwardSaturationCandidate A (C.direction j)
      (P.enlargement n)) : LatticeConvex E := by
  obtain ⟨K, _, hK⟩ := (enlargement_integer_collar P n).2
  have hAC : (A : Set Lattice) = embed ⁻¹' windowHull A := by
    ext z
    exact (hA.2.1 z).symm
  have hsat := paidNoHoles (windowHull A) (windowHull_convex A)
    (C.direction (j + m)) (C.primitive _) (paidFibres C hA (j + m))
  rw [C.antipodal j] at hsat
  let U : Set RealPlane :=
    {x | ∃ y ∈ windowHull A, ∃ r : ℝ, 0 ≤ r ∧
      x = y + r • embed (-C.direction j)} ∩ finiteRayHull K (-v) w
  have hEU : (E : Set Lattice) = embed ⁻¹' U := by
    rw [hE, backwardSaturationCandidate, hAC, hsat, hK]
    rfl
  have hU : Convex ℝ U :=
    (paidRayConvex (windowHull A) (windowHull_convex A) (-C.direction j)).inter
      (paidHullConvex K (-v) w)
  intro z
  constructor
  · intro hz
    have himage : embed '' (E : Set Lattice) ⊆ U := by
      rintro x ⟨q, hq, rfl⟩
      have hq' : q ∈ (E : Set Lattice) := hq
      rw [hEU] at hq'
      exact hq'
    have hh : windowHull E ⊆ U := convexHull_min himage hU
    change z ∈ (E : Set Lattice)
    rw [hEU]
    exact hh hz
  · intro hz
    exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

private theorem normalised_candidate_lattice_convex {ξ xper : Configuration ℤ}
    {S : Finset Lattice} {m : ℕ} {C : AntipodalEdgeCycle S m} {i : ℤ}
    (W : AlternatingWindows ξ xper C i) (G : GrowingSubsequence W)
    (P : Region (C.direction i) (C.direction G.J))
    (L : NormalisedWindowLimit W G) (n j : ℕ) (E : Finset Lattice)
    (hE : (E : Set Lattice) = backwardSaturationCandidate
      (W.normalised (G.subsequence (L.index j))) (C.direction (G.J + 1))
      (P.enlargement n)) : LatticeConvex E := by
  apply candidate_lattice_convex C _ (G.J + 1) P n E hE
  exact paidTranslatedEnvelope S _ (W.A_enveloped _) _

private theorem candidate_nonempty_and_area {A E : Finset Lattice}
    (hne : A.Nonempty) (harea : (interior (windowHull A)).Nonempty)
    (hAE : A ⊆ E) : E.Nonempty ∧ (interior (windowHull E)).Nonempty := by
  refine ⟨hne.mono hAE, harea.mono (interior_mono ?_)⟩
  exact convexHull_mono (Set.image_mono hAE)

end
end ConvexNivat.Colle
