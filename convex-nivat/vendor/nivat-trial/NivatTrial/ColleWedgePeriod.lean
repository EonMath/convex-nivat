import NivatTrial.ColleWedgeRecurrence

/-! Many-component periodicity propagates from a one-sided base strip
into the adjacent cone selected by the component directions. Parallel
components are absorbed into one common period; the remaining product
recurrence has all its predecessors inside the cone. -/

namespace NivatTrial.ColleWedgePeriod

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.RegionGeometry
open NivatTrial.FirstHalfPlane NivatTrial.ColleStripRigidity
open NivatTrial.ColleWedgeRecurrence
open scoped Classical
noncomputable section

def downward (u h : Lattice) : Lattice := if 0 ≤ det u h then -h else h

theorem downward_height {u h : Lattice} (hh : det u h ≠ 0) :
    height u (downward u h) < 0 := by
  dsimp [downward,height]
  split_ifs with hp
  · rw [det_neg_right]; omega
  · omega

theorem downward_support (u h : Lattice) (ψ : Lattice →+ ℤ)
    (hh : det u h ≠ 0) (hs : 0 ≤ det u h * ψ h) : ψ (downward u h) ≤ 0 := by
  dsimp [downward]
  split_ifs with hp
  · rw [map_neg]
    have hd : 0 < det u h := by omega
    nlinarith
  · have hd : det u h < 0 := by omega
    nlinarith

variable {ι A : Type*} [Fintype ι] [AddCommGroup A]

def downwardTransverse (u : Lattice) (h : ι → Lattice) : List Lattice :=
  ((Finset.univ.filter (fun i => det u (h i) ≠ 0)).toList.map (fun i => downward u (h i)))

theorem period_on_wedge_of_oriented_base_strip
    (F : ι → Lattice → A) (h : ι → Lattice)
    (hper : ∀ i, IsPeriod (F i) (h i)) (hzero : ∀ i, h i ≠ 0)
    (u a : Lattice) (ha : a = u ∨ a = -u)
    (ψ : Lattice →+ ℤ) (hψa : ψ a ≤ 0)
    (hside : ∀ i, det u (h i) ≠ 0 → 0 ≤ det u (h i) * ψ (h i))
    (q : ℕ) (hq : 0 < q) (c : ℤ)
    (hbase : ∀ z, 0 ≤ det u z →
      det u z ≤ widthBudget (height u) (downwardTransverse u h) → ψ z ≤ c →
      (∑ i,F i) (z+q•a) = (∑ i,F i) z) :
    ∃ Q : ℕ, 0 < Q ∧
      PeriodicOn (∑ i,F i) {z | 0 ≤ det u z ∧ ψ z ≤ c} (Q•a) := by
  have hua : det u a = 0 := by rcases ha with rfl | rfl <;> simp
  have hchosen (i : ι) : ∃ m : ℕ, 0 < m ∧
      (det u (h i) = 0 → IsPeriod (F i) (m•a)) := by
    by_cases hi : det u (h i) = 0
    · have hdet : det (h i) a = 0 := by
        have hia : det (h i) u = 0 := by rw [det_swap,hi]; simp
        rcases ha with he | he
        · rw [he]; exact hia
        · rw [he,det_neg_right,hia,neg_zero]
      obtain ⟨m,hm,hpm⟩ := parallel_direction_period (hper i) (hzero i) a hdet
      exact ⟨m,hm,fun _ => hpm⟩
    · exact ⟨1,by omega,fun he => (hi he).elim⟩
  choose m hm hmp using hchosen
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  have hMper (i : ι) (hi : det u (h i) = 0) : IsPeriod (F i) (M•a) := by
    obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    dsimp only [M]
    rw [hk]
    simpa only [mul_comm (m i) k,mul_smul] using (hmp i hi).nsmul k
  let Q := q*M
  have hQ : 0 < Q := Nat.mul_pos hq hM
  have hQper (i : ι) (hi : det u (h i) = 0) : IsPeriod (F i) (Q•a) := by
    simpa only [Q,mul_smul] using (hMper i hi).nsmul q
  let hs := downwardTransverse u h
  have hπ : ∀ a ∈ hs, height u a < 0 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact downward_height (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
  have hψ : ∀ a ∈ hs, ψ a ≤ 0 := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have hi' := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    exact downward_support u (h i) ψ hi' (hside i hi')
  let g := increment (∑ i,F i) (Q•a)
  have hann : iteratedIncrement hs g = 0 := by
    rw [show iteratedIncrement hs g = increment (iteratedIncrement hs (∑ i,F i)) (Q•a)
      from iteratedIncrement_commute hs (∑ i,F i) (Q•a),iteratedIncrement_sum]
    funext z
    simp only [increment,Finset.sum_apply,Pi.zero_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : det u (h i) = 0
    · exact sub_eq_zero.mpr ((iteratedIncrement_period hs (hQper i hi)) z)
    · have himem : downward u (h i) ∈ hs := List.mem_map.mpr
        ⟨i,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩),rfl⟩
      have hdp : IsPeriod (F i) (downward u (h i)) := by
        dsimp [downward]
        split_ifs
        · exact (hper i).neg
        · exact hper i
      have hkill := factor_kills_of_mem hs _ himem (F i) hdp
      rw [congrFun hkill (z+Q•a),congrFun hkill z]
      simp
  have hψq : ψ (q•a) ≤ 0 := by
    rw [map_nsmul]
    exact nsmul_nonpos hψa q
  have hbasePeriod : PeriodicOn (∑ i,F i)
      {z | 0 ≤ det u z ∧ det u z ≤ widthBudget (height u) hs ∧ ψ z ≤ c} (q•a) := by
    refine ⟨?_,?_⟩
    · intro z hz
      change 0 ≤ det u (z+q•a) ∧ det u (z+q•a) ≤ widthBudget (height u) hs ∧ ψ (z+q•a) ≤ c
      simp only [det_add_right,det_nsmul_right,hua,mul_zero,add_zero,map_add]
      exact ⟨hz.1,hz.2.1,by have := hz.2.2; omega⟩
    · intro z hz
      exact hbase z hz.1 hz.2.1 hz.2.2
  have hbaseQ := hbasePeriod.nsmul M
  have hg : ∀ z, 0 ≤ height u z → ψ z ≤ c → g z = 0 :=
    zero_on_wedge_of_zero_halfStrip (height u) ψ hs g hπ hψ hann c (by
      intro z hz0 hzw hzψ
      have he := hbaseQ.2 z ⟨hz0,hzw,hzψ⟩
      apply sub_eq_zero.mpr
      simpa only [Q,mul_comm q M,mul_smul] using he)
  refine ⟨Q,hQ,?_,?_⟩
  · intro z hz
    change 0 ≤ det u (z+Q•a) ∧ ψ (z+Q•a) ≤ c
    simp only [det_add_right,det_nsmul_right,hua,mul_zero,add_zero,map_add,map_nsmul]
    exact ⟨hz.1,by have := nsmul_nonpos hψa Q; have := hz.2; omega⟩
  · intro z hz
    exact sub_eq_zero.mp (hg z hz.1 hz.2)

theorem period_on_wedge_of_periodic_base_strip
    (F : ι → Lattice → A) (h : ι → Lattice)
    (hper : ∀ i, IsPeriod (F i) (h i)) (hzero : ∀ i, h i ≠ 0)
    (u : Lattice) (ψ : Lattice →+ ℤ) (hψu : ψ u ≤ 0)
    (hside : ∀ i, det u (h i) ≠ 0 → 0 ≤ det u (h i) * ψ (h i))
    (q : ℕ) (hq : 0 < q) (c : ℤ)
    (hbase : ∀ z, 0 ≤ det u z →
      det u z ≤ widthBudget (height u) (downwardTransverse u h) → ψ z ≤ c →
      (∑ i,F i) (z+q•u) = (∑ i,F i) z) :
    ∃ Q : ℕ, 0 < Q ∧
      PeriodicOn (∑ i,F i) {z | 0 ≤ det u z ∧ ψ z ≤ c} (Q•u) :=
  period_on_wedge_of_oriented_base_strip F h hper hzero u u (Or.inl rfl)
    ψ hψu hside q hq c hbase

end
end NivatTrial.ColleWedgePeriod
