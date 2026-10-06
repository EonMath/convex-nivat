import ConvexNivat.Colle.GeneratingBasic
import ConvexNivat.ReductionJoinElementary

namespace ConvexNivat.Colle
open scoped BigOperators

theorem generating_point_iff_complexity (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (S : Finset Lattice) (z : Lattice) (hz : z ∈ S) :
    PatternDetermines ξ (S.erase z) z ↔ complexity ξ S = complexity ξ (S.erase z) := by
  classical
  let r : Pattern ℤ S → Pattern ℤ (S.erase z) :=
    fun p q => p ⟨q.val, (Finset.mem_erase.mp q.property).2⟩
  have hrange : r '' patternSet ξ S = patternSet ξ (S.erase z) := by
    ext p
    constructor
    · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨pattern ξ S u, ⟨u, rfl⟩, rfl⟩
  have hf := finiteRange_patternSet_finite ξ A hA S
  constructor
  · intro hd
    have hi : Set.InjOn r (patternSet ξ S) := by
      rintro p ⟨u, rfl⟩ q ⟨v, rfl⟩ he
      funext w
      by_cases hw : w.val = z
      · have hdis : ∀ g ∈ S.erase z,
            (translate u ξ) (g + 0) = (translate v ξ) (g + 0) := by
          intro g hg
          simpa [r, pattern, translate, add_comm] using congrFun he ⟨g, hg⟩
        have hletter := hd (translate u ξ) (orbitClosure_translate ξ u)
          (translate v ξ) (orbitClosure_translate ξ v) 0 hdis
        simpa [pattern, translate, hw, add_comm] using hletter
      · exact congrFun he ⟨w.val, Finset.mem_erase.mpr ⟨hw, w.property⟩⟩
    exact ((congrArg Set.ncard hrange).symm.trans hi.ncard_image).symm
  · intro hc
    have hi : Set.InjOn r (patternSet ξ S) := by
      apply Set.injOn_of_ncard_image_eq (hs := hf)
      rw [hrange]
      exact hc.symm
    intro x hx y hy t he
    have hxp : pattern x S t ∈ patternSet ξ S :=
      orbitClosure_patternSet_subset ξ x hx S (Set.mem_range_self t)
    have hyp : pattern y S t ∈ patternSet ξ S :=
      orbitClosure_patternSet_subset ξ y hy S (Set.mem_range_self t)
    have hre : r (pattern x S t) = r (pattern y S t) := by
      funext w
      simpa [r, pattern, add_comm] using he w.val w.property
    simpa [pattern, add_comm] using congrFun (hi hxp hyp hre) ⟨z, hz⟩

theorem generating_set_orbit_inheritance (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (S : Finset Lattice) (hS : GeneratingSet ξ S) :
    GeneratingSet x S := by
  have hsub : OrbitClosure x ⊆ OrbitClosure ξ := by
    intro y hy T
    obtain ⟨u, hu⟩ := hy T
    obtain ⟨v, hv⟩ := hx (T.image (fun z => u + z))
    refine ⟨v + u, ?_⟩
    intro z hz
    rw [hu z hz, hv _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩), add_assoc]
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro z hz y hy w hw t he
  exact hS.2.2 z hz y (hsub hy) w (hsub hw) t he

end ConvexNivat.Colle
