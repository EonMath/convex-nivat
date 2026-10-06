import NivatTrial.AvailableDirections
import NivatTrial.ColleWedgePeriod

/-! An adjacent cone can be selected from the actual component directions.
The selected boundary makes every downward recurrence step stay in the cone. -/

namespace NivatTrial.ColleAdjacentDirections

open NivatTrial.Geometry NivatTrial.AvailableDirections
open NivatTrial.FirstHalfPlane NivatTrial.ColleWedgePeriod
open NivatTrial.Periodicity NivatTrial.RegionGeometry NivatTrial.ColleStripRigidity
open scoped Classical
noncomputable section

def upward (u h : Lattice) : Lattice := if 0 < det u h then h else -h

theorem upward_height {u h : Lattice} (hh : det u h ≠ 0) :
    0 < det u (upward u h) := by
  dsimp [upward]
  split_ifs with hp
  · exact hp
  · rw [det_neg_right]; omega

variable {ι : Type*} [Fintype ι]

theorem exists_adjacent_direction (u : Lattice) (h : ι → Lattice)
    (ht : ∃ i, det u (h i) ≠ 0) :
    ∃ i k, (k = h i ∨ k = -h i) ∧ 0 < det u k ∧
      ∀ j, 0 ≤ det u (h j) * det k (h j) := by
  let C := Finset.univ.filter (fun i => det u (h i) ≠ 0)
  have hC : C.Nonempty := by
    obtain ⟨i,hi⟩ := ht
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨i,hi,hmin⟩ := C.exists_min_image
    (fun j => score (upward u (h j)) (-u)) hC
  have hi0 := (Finset.mem_filter.mp hi).2
  let k := upward u (h i)
  have huk : 0 < det u k := upward_height hi0
  have hku : 0 < det k (-u) := by
    rw [det_neg_right,det_swap]; omega
  have hkw (j : ι) (hj : det u (h j) ≠ 0) :
      0 ≤ det k (upward u (h j)) := by
    by_contra hn
    have hneg : det k (upward u (h j)) < 0 := by omega
    have hjpos : 0 < det (upward u (h j)) (-u) := by
      rw [det_neg_right,det_swap]
      have := upward_height hj
      omega
    have hrev : 0 < det (upward u (h j)) k := by
      rw [det_swap]; omega
    have hlt := (score_lt_iff hjpos hku).mpr hrev
    have hle := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
    exact (not_lt_of_ge hle) hlt
  refine ⟨i,k,?_,huk,?_⟩
  · dsimp [k,upward]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j
    by_cases hj : det u (h j) = 0
    · simp [hj]
    · have hw := hkw j hj
      by_cases hp : 0 < det u (h j)
      · have hnonneg : 0 ≤ det k (h j) := by simpa [upward,hp] using hw
        exact mul_nonneg (le_of_lt hp) hnonneg
      · have hnonpos : det k (h j) ≤ 0 := by
          simpa [upward,hp] using hw
        exact mul_nonneg_of_nonpos_of_nonpos (by omega) hnonpos

theorem exists_adjacent_to_component {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice) (hp : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i : Fin n) :
    ∃ j k, (k = v j ∨ k = -v j) ∧ 0 < det (v i) k ∧
      ∀ t, 0 ≤ det (v i) (v t) * det k (v t) := by
  apply exists_adjacent_direction
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j,hji⟩ := exists_ne i
  exact ⟨j,hp i j hji.symm⟩

theorem period_on_adjacent_wedge {A : Type*} [AddCommGroup A]
    (F : ι → Lattice → A) (h : ι → Lattice)
    (hper : ∀ i, IsPeriod (F i) (h i)) (hzero : ∀ i, h i ≠ 0)
    (u : Lattice) (ht : ∃ i, det u (h i) ≠ 0)
    (q : ℕ) (hq : 0 < q)
    (hbase : ∀ k, 0 < det u k →
      (∀ j, 0 ≤ det u (h j) * det k (h j)) →
      ∃ c : ℤ, ∀ z, 0 ≤ det u z →
        det u z ≤ widthBudget (height u) (downwardTransverse u h) →
        det k z ≤ c → (∑ i,F i) (z+q•u) = (∑ i,F i) z) :
    ∃ i k c Q, (k = h i ∨ k = -h i) ∧ 0 < det u k ∧ 0 < Q ∧
      PeriodicOn (∑ i,F i) {z | 0 ≤ det u z ∧ det k z ≤ c} (Q•u) := by
  obtain ⟨i,k,hki,huk,hside⟩ := exists_adjacent_direction u h ht
  obtain ⟨c,hc⟩ := hbase k huk hside
  have hku : height k u ≤ 0 := by
    change det k u ≤ 0
    rw [det_swap]; omega
  obtain ⟨Q,hQ,hperiod⟩ := period_on_wedge_of_periodic_base_strip
    F h hper hzero u (height k) hku (fun j _ => hside j) q hq c hc
  exact ⟨i,k,c,Q,hki,huk,hQ,hperiod⟩

end
end NivatTrial.ColleAdjacentDirections
