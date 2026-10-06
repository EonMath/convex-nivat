import NivatTrial.ColleWindowWidth
import NivatTrial.ColleRegionDichotomy
import NivatTrial.ExternalInputs

/-! The first geometric branch of Colle's construction: an actual translate
agreeing with a periodic reference on a long-faced half-strip has a periodic
adjacent wedge. All width and direction choices are supplied internally. -/

namespace NivatTrial.ColleCaseOne

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.LatticePolygon
open NivatTrial.Nonexpansive NivatTrial.Periodicity NivatTrial.RegionGeometry
open NivatTrial.ExternalInputs NivatTrial.ColleWindowWidth
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleLongFaces NivatTrial.ColleFiniteEnvelope
open NivatTrial.ColleZonotopeEnvelope NivatTrial.ColleHalfStripEnvelope
open NivatTrial.ColleGenerating
open scoped Classical
noncomputable section

def wedge (u k : Lattice) (c : ℤ) : Set Lattice :=
  {z | 0 ≤ det u z ∧ det k z ≤ c}

theorem wedge_latticeConvex (u k : Lattice) (c : ℤ) :
    LatticeConvexRegion (wedge u k c) := by
  let C : Set (ℝ × ℝ) := {x | (0:ℝ) ≤ linearScore (embed u) x ∧
    linearScore (embed k) x ≤ (c:ℝ)}
  have hC : Convex ℝ C :=
    (convex_halfSpace_ge (linearScore (embed u)).isLinear 0).inter
      (convex_halfSpace_le (linearScore (embed k)).isLinear (c:ℝ))
  refine ⟨C,hC,?_⟩
  ext z
  simp only [wedge,C,Set.mem_ofPred_eq,Set.mem_preimage,linearScore_embed_det]
  norm_cast

theorem wedge_nonempty {u k : Lattice} (huk : 0 < det u k) (c : ℤ) :
    (wedge u k c).Nonempty := by
  refine ⟨(|c|+1 : ℤ)•u,?_,?_⟩
  · simp only [det_zsmul_right,det_self,mul_zero,le_refl]
  · rw [det_zsmul_right,det_swap]
    have hc := neg_abs_le c
    have hnonneg := abs_nonneg c
    nlinarith

theorem wedge_forward_first {u k : Lattice} (huk : 0 < det u k) (c : ℤ) :
    ForwardInvariant (wedge u k c) u := by
  intro z hz
  change 0 ≤ det u (z+u) ∧ det k (z+u) ≤ c
  simp only [det_add_right,det_self,add_zero]
  rw [det_swap k u]
  exact ⟨hz.1,by have := hz.2; omega⟩

theorem wedge_forward_second {u k : Lattice} (huk : 0 < det u k) (c : ℤ) :
    ForwardInvariant (wedge u k c) k := by
  intro z hz
  change 0 ≤ det u (z+k) ∧ det k (z+k) ≤ c
  simp only [det_add_right,det_self,add_zero]
  exact ⟨by have := hz.1; omega,hz.2⟩

theorem periodic_wedge_of_halfStrip_agreement {M m : ℕ}
    (x p : Lattice → Fin M) (E : IntegerDecomposition (integerField x) m)
    (T : Finset Lattice) (u : Lattice)
    (ht : ∃ i, det u (E.period i) ≠ 0)
    (hclosed : IsEnvelope (signedDirections E.period) (T : Set Lattice))
    (hfaces : LongFaces (signedDirections E.period) (T : Set Lattice))
    (hu : u ∈ signedDirections E.period) (hnu : -u ∈ signedDirections E.period)
    (hzero : (0:Lattice) ∈ T) (hlevel : ∀ z ∈ T, 0 ≤ det u z)
    (q : ℕ) (hq : 0 < q) (hp : IsPeriod p (q•u))
    (hxp : AgreeOn x p (halfStrip T u)) :
    ∃ i k c Q, (k = E.period i ∨ k = -E.period i) ∧ 0 < det u k ∧ 0 < Q ∧
      LatticeConvexRegion (wedge u k c) ∧ (wedge u k c).Nonempty ∧
      PeriodicOn x (wedge u k c) (Q•u) ∧ ForwardInvariant (wedge u k c) k := by
  have hbase : ∀ z ∈ halfStrip T u,
      (∑ i,E.component i) (z+q•u) = (∑ i,E.component i) z := by
    intro z hz
    rw [E.sum_eq]
    have hnew := (halfStrip_forward T u).nsmul q z hz
    have he := (hxp (z+q•u) hnew).trans ((hp z).trans (hxp z hz).symm)
    exact congrArg integerCode he
  obtain ⟨i,k,c,Q,hki,huk,hQ,hperiod⟩ := period_on_wedge_of_long_halfStrip
    E.component E.period E.component_period E.period_ne_zero E.independent
    T u ht hclosed hfaces hu hnu hzero hlevel q hq hbase
  refine ⟨i,k,c,Q,hki,huk,hQ,wedge_latticeConvex u k c,wedge_nonempty huk c,
    ⟨hperiod.1,?_⟩,wedge_forward_second huk c⟩
  intro z hz
  apply integerCode_injective M
  have he := hperiod.2 z hz
  rwa [E.sum_eq] at he

theorem periodic_wedge_at_component {M m : ℕ} (hm : 2 ≤ m)
    (x p : Lattice → Fin M) (E : IntegerDecomposition (integerField x) m)
    (T : Finset Lattice) (i : Fin m)
    (hclosed : IsEnvelope (signedDirections E.period) (T : Set Lattice))
    (hfaces : LongFaces (signedDirections E.period) (T : Set Lattice))
    (hzero : (0:Lattice) ∈ T) (hlevel : lowerSupport T (E.period i) = 0)
    (q : ℕ) (hq : 0 < q) (hp : IsPeriod p (q•E.period i))
    (hxp : AgreeOn x p (halfStrip T (E.period i))) :
    ∃ j k c Q, (k = E.period j ∨ k = -E.period j) ∧ 0 < det (E.period i) k ∧ 0 < Q ∧
      LatticeConvexRegion (wedge (E.period i) k c) ∧ (wedge (E.period i) k c).Nonempty ∧
      PeriodicOn x (wedge (E.period i) k c) (Q•E.period i) ∧
      ForwardInvariant (wedge (E.period i) k c) k := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨j,hji⟩ := exists_ne i
  have ht : ∃ j, det (E.period i) (E.period j) ≠ 0 := ⟨j,E.independent i j hji.symm⟩
  apply periodic_wedge_of_halfStrip_agreement x p E T (E.period i) ht hclosed hfaces
  · exact (mem_signedDirections E.period _).mpr ⟨i,Or.inl rfl⟩
  · exact (mem_signedDirections E.period _).mpr ⟨i,Or.inr rfl⟩
  · exact hzero
  · intro z hz
    rw [← hlevel]
    exact lowerSupport_le hz _
  · exact hq
  · exact hp
  · exact hxp

end
end NivatTrial.ColleCaseOne
