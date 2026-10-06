import NivatTrial.ColleZonotopePlacement
import NivatTrial.ColleHalfStripBase

/-! The long-face condition supplies exactly the transverse width required
by the product recurrence. This removes any extra width hypothesis from
period propagation on the half-strips used in Colle's construction. -/

namespace NivatTrial.ColleWindowWidth

open NivatTrial.Geometry NivatTrial.IncrementSupport
open NivatTrial.ColleStripRigidity NivatTrial.ColleWedgePeriod
open NivatTrial.FirstHalfPlane NivatTrial.ColleZonotopePlacement
open NivatTrial.ColleZonotopeEnvelope NivatTrial.ColleLongFaces
open NivatTrial.ColleEnvelopeGeometry NivatTrial.ColleMaximalEnvelope
open NivatTrial.ColleFiniteEnvelope NivatTrial.ColleHalfStripBase
open NivatTrial.LatticePolygon NivatTrial.Periodicity NivatTrial.RegionGeometry
open scoped Classical
noncomputable section

theorem exists_extreme_offsets (π : Lattice →+ ℤ) (hs : List Lattice) :
    ∃ a ∈ offsets hs, ∃ b ∈ offsets hs, π b - π a = widthBudget π hs := by
  induction hs with
  | nil => exact ⟨0,by simp [offsets],0,by simp [offsets],by simp [widthBudget]⟩
  | cons h hs ih =>
    obtain ⟨a,ha,b,hb,he⟩ := ih
    by_cases hp : 0 ≤ π h
    · refine ⟨a,Finset.mem_union_left _ ha,h+b,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩),?_⟩
      rw [map_add,widthBudget,abs_of_nonneg hp]
      omega
    · refine ⟨h+a,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩),
        b,Finset.mem_union_left _ hb,?_⟩
      rw [map_add,widthBudget,abs_of_neg (lt_of_not_ge hp)]
      omega

theorem widthBudget_eq_sum (π : Lattice →+ ℤ) (hs : List Lattice) :
    widthBudget π hs = (hs.map (fun h => |π h|)).sum := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [widthBudget,ih]

theorem widthBudget_finset {ι : Type*} [DecidableEq ι]
    (π : Lattice →+ ℤ) (v : ι → Lattice) (I : Finset ι) :
    widthBudget π (I.toList.map v) = ∑ i ∈ I, |π (v i)| := by
  rw [widthBudget_eq_sum,List.map_map]
  simp

theorem downwardTransverse_width {ι : Type*} [Fintype ι]
    (u : Lattice) (v : ι → Lattice) :
    widthBudget (height u) (downwardTransverse u v) =
      widthBudget (height u) (Finset.univ.toList.map v) := by
  unfold downwardTransverse
  rw [widthBudget_finset,widthBudget_finset]
  have habs (i : ι) : |height u (downward u (v i))| = |height u (v i)| := by
    by_cases hi : 0 ≤ det u (v i)
    · simp only [downward,if_pos hi,map_neg,abs_neg]
    · simp only [downward,if_neg hi]
  simp_rw [habs]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : det u (v i) = 0
  · simp [hi,height]
  · simp [hi]

theorem exists_high_point_of_longFaces {n : ℕ} (v : Fin n → Lattice)
    (T : Finset Lattice) (hT : T.Nonempty) (hconv : IsLatticeConvex T)
    (hfaces : LongFaces (signedDirections v) (T : Set Lattice))
    (hind : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (u : Lattice) (hlevel : ∀ z ∈ T, 0 ≤ det u z) :
    ∃ b ∈ T, widthBudget (height u) (downwardTransverse u v) ≤ det u b := by
  obtain ⟨a,ha⟩ := exists_indexed_offsets_placement v T hT hconv hfaces hind
  obtain ⟨b,hb,c,hc,he⟩ := exists_extreme_offsets (height u) (Finset.univ.toList.map v)
  refine ⟨a+c,ha c hc,?_⟩
  rw [downwardTransverse_width]
  have hlow := hlevel (a+b) (ha b hb)
  change det u c - det u b = _ at he
  rw [det_add_right] at hlow ⊢
  omega

theorem period_on_wedge_of_long_halfStrip {A : Type*} [AddCommGroup A] {n : ℕ}
    (F : Fin n → Lattice → A) (v : Fin n → Lattice)
    (hper : ∀ i, IsPeriod (F i) (v i)) (hzero : ∀ i, v i ≠ 0)
    (hind : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (T : Finset Lattice) (u : Lattice) (ht : ∃ i, det u (v i) ≠ 0)
    (hclosed : IsEnvelope (signedDirections v) (T : Set Lattice))
    (hfaces : LongFaces (signedDirections v) (T : Set Lattice))
    (hu : u ∈ signedDirections v) (hnu : -u ∈ signedDirections v)
    (h0 : (0 : Lattice) ∈ T) (hlevel : ∀ z ∈ T, 0 ≤ det u z)
    (q : ℕ) (hq : 0 < q)
    (hbase : ∀ z ∈ halfStrip T u, (∑ i,F i) (z+q•u) = (∑ i,F i) z) :
    ∃ i k c Q, (k = v i ∨ k = -v i) ∧ 0 < det u k ∧ 0 < Q ∧
      PeriodicOn (∑ i,F i) {z | 0 ≤ det u z ∧ det k z ≤ c} (Q•u) := by
  obtain ⟨b,hb,hwidth⟩ := exists_high_point_of_longFaces v T ⟨0,h0⟩
    (latticeConvex_finset_of_region T hclosed.latticeConvex) hfaces hind u hlevel
  exact period_on_wedge_of_periodic_halfStrip F v hper hzero (signedDirections v) T u ht
    hclosed hfaces hu hnu h0 b hb hwidth q hq hbase

end
end NivatTrial.ColleWindowWidth
