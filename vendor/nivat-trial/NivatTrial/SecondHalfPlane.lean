import NivatTrial.TwoComponentLimits
import NivatTrial.AvailableDirections
import NivatTrial.FirstHalfPlane

/-! Finite induction producing every opposite periodic half-plane, as in
Theorem 8.12. Safe directions and all limits are constructed explicitly. -/

namespace NivatTrial.SecondHalfPlane

open Set Filter Topology
open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.FirstHalfPlane NivatTrial.TwoComponentLimits NivatTrial.LatticePolygon
open scoped Classical

noncomputable section

variable {ι A : Type*} [Fintype ι] [Nontrivial ι] [DecidableEq ι]
variable [AddCommGroup A] [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

def HasLowerTail (F : ι → Lattice → A) (v : ι → Lattice) (i : ι) : Prop :=
  ∃ β : ℤ, ∃ θ : Lattice → A, IsDoublyPeriodic θ ∧
    ∀ z, det (v i) z ≤ β → F i z = θ z

theorem lower_tail_step (F U : ι → Lattice → A) (v : ι → Lattice)
    (g : Lattice) (c : ι → ℤ)
    (hfixed : ∀ i, IsPeriod (F i) (v i))
    (hpos : ∀ i, 0 < det (v i) g)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (hndp : ∀ i, ¬IsDoublyPeriodic (F i))
    (hU : ∀ i, IsDoublyPeriodic (U i))
    (hupper : ∀ i z, c i ≤ det (v i) z → F i z = U i z)
    (S : Finset Lattice) (hSne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (∑ i, F i) S ≤ S.card)
    (O : Finset ι) (hO : O.Nonempty)
    (hknown : ∀ j, j ∉ O → HasLowerTail F v j) :
    ∃ b ∈ O, HasLowerTail F v b := by
  obtain ⟨b, hb, c₀, hcb, ε, hε, hnegative, havailable⟩ :=
    AvailableDirections.available_direction v g hpos hpair O hO
  have hLall (j : ι) : ∃ β : ℤ, ∃ θ : Lattice → A, IsDoublyPeriodic θ ∧
      (j ∉ O → ∀ z, det (v j) z ≤ β → F j z = θ z) := by
    by_cases hj : j ∈ O
    · refine ⟨0, 0, ?_, fun hn => (hn hj).elim⟩
      refine ⟨(1, 0), (0, 1), by norm_num [det], ?_, ?_⟩ <;> intro z <;> rfl
    · obtain ⟨β, θ, hθ, ha⟩ := hknown j hj
      exact ⟨β, θ, hθ, fun _ => ha⟩
  choose β L hL hLagree using hLall
  let tails : Bool × ι → Lattice → A := fun p => if p.1 then U p.2 else L p.2
  have htails : ∀ p, IsDoublyPeriodic (tails p) := by
    rintro ⟨t, j⟩
    cases t
    · exact hL j
    · exact hU j
  obtain ⟨N, hN, hrect⟩ := common_rectangular_periods tails htails
  let w := ε • v c₀
  let d := N • w
  have hUp (j : ι) : IsPeriod (U j) d := by
    have hp := period_in_scaled_direction (tails (true, j)) N w
      (hrect (true, j)).1 (hrect (true, j)).2
    simpa only [tails, if_true] using hp
  have hLp (j : ι) : IsPeriod (L j) d := by
    have hp := period_in_scaled_direction (tails (false, j)) N w
      (hrect (false, j)).1 (hrect (false, j)).2
    simpa only [tails, Bool.false_eq_true, if_false] using hp
  have hdnegative : det (v b) d < 0 := by
    change det (v b) (N • (ε • v c₀)) < 0
    rw [det_nsmul_right]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hN) hnegative
  have hdpositive (j : ι) (hj : j ∈ O) (hjb : j ≠ b) (hjc : j ≠ c₀) :
      0 < det (v j) d := by
    change 0 < det (v j) (N • (ε • v c₀))
    rw [det_nsmul_right]
    exact mul_pos (by exact_mod_cast hN) (havailable j hj hjb hjc)
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> omega
  have hdnonzero (j : ι) (hjc : j ≠ c₀) : det (v j) d ≠ 0 := by
    change det (v j) (N • (ε • v c₀)) ≠ 0
    rw [det_nsmul_right, det_zsmul_right]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hN)
      (mul_ne_zero hεne (hpair j c₀ hjc))
  let B : ι → Lattice → A := fun j => if 0 < det (v j) d then U j else L j
  have hB : ∀ j, j ≠ b → j ≠ c₀ → IsDoublyPeriodic (B j) := by
    intro j _ _
    dsimp [B]
    split
    · exact hU j
    · exact hL j
  have hlimB : ∀ j, j ≠ b → j ≠ c₀ →
      Tendsto (fun n : ℕ => shift (n • d) (F j)) atTop (𝓝 (B j)) := by
    intro j hjb hjc
    by_cases hp : 0 < det (v j) d
    · simp only [B, hp, if_true]
      exact safe_tail_tendsto (F j) (U j) (height (v j)) (c j) d hp (hUp j) (hupper j)
    · have hn : det (v j) d < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hdnonzero j hjc)
      have hjO : j ∉ O := by
        intro hj
        exact hp (hdpositive j hj hjb hjc)
      simp only [B, hp, if_false]
      apply safe_tail_tendsto (F j) (L j) (-(height (v j))) (-β j) d
        (by change 0 < -det (v j) d; omega) (hLp j)
      intro z hz
      apply hLagree j hjO z
      change -β j ≤ -det (v j) z at hz
      omega
  have hfixc : IsPeriod (F c₀) d := ((hfixed c₀).zsmul ε).nsmul N
  have hall (y : Lattice → A)
      (hy : MapClusterPt y atTop (fun n : ℕ => shift (n • d) (F b))) :
      IsDoublyPeriodic y :=
    doublyPeriodic_two_component_cluster F B v b c₀ hcb.symm d hfixed
      (hpair c₀ b hcb) (hndp c₀) hfixc hB hlimB S hSne hS hlow y hy
  obtain ⟨a, θ, hθ, ha⟩ := HalfPlaneLimit.tail_agreement (F b) (v b) d 1 (by omega)
    (by simpa using hfixed b) hdnegative hall
  exact ⟨b, hb, a, θ, hθ, ha⟩

/-- Theorem 8.12: every component obtains an actual doubly periodic tail
on its opposite determinant half-plane. The finite induction has no assumed
safe-direction or cluster-periodicity interface. -/
theorem all_lower_tails (F U : ι → Lattice → A) (v : ι → Lattice)
    (g : Lattice) (c : ι → ℤ)
    (hfixed : ∀ i, IsPeriod (F i) (v i)) (hpos : ∀ i, 0 < det (v i) g)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (hndp : ∀ i, ¬IsDoublyPeriodic (F i)) (hU : ∀ i, IsDoublyPeriodic (U i))
    (hupper : ∀ i z, c i ≤ det (v i) z → F i z = U i z)
    (S : Finset Lattice) (hSne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (∑ i, F i) S ≤ S.card) :
    ∀ i, HasLowerTail F v i := by
  have hgo (O : Finset ι) :
      (∀ j, j ∉ O → HasLowerTail F v j) → ∀ j, HasLowerTail F v j := by
    refine Finset.strongInductionOn O ?_
    intro O ih hknown
    by_cases hO : O.Nonempty
    · obtain ⟨b, hb, hnew⟩ := lower_tail_step F U v g c hfixed hpos hpair
        hndp hU hupper S hSne hS hlow O hO hknown
      apply ih (O.erase b) (Finset.erase_ssubset hb)
      intro j hj
      by_cases hjb : j = b
      · simpa only [hjb] using hnew
      · apply hknown j
        intro hjO
        exact hj (Finset.mem_erase.mpr ⟨hjb, hjO⟩)
    · have he : O = ∅ := Finset.not_nonempty_iff_eq_empty.mp hO
      intro j
      exact hknown j (by simp [he])
  exact hgo Finset.univ (fun j hj => (hj (Finset.mem_univ j)).elim)

theorem disjoint_lower_tails (F U : ι → Lattice → A) (v : ι → Lattice)
    (g : Lattice) (c : ι → ℤ)
    (hfixed : ∀ i, IsPeriod (F i) (v i)) (hpos : ∀ i, 0 < det (v i) g)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (hndp : ∀ i, ¬IsDoublyPeriodic (F i)) (hU : ∀ i, IsDoublyPeriodic (U i))
    (hupper : ∀ i z, c i ≤ det (v i) z → F i z = U i z)
    (S : Finset Lattice) (hSne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (∑ i, F i) S ≤ S.card) :
    ∀ i, ∃ β : ℤ, ∃ θ : Lattice → A, β < c i ∧ IsDoublyPeriodic θ ∧
      (∀ z, det (v i) z ≤ β → F i z = θ z) ∧
      Disjoint {z : Lattice | c i ≤ det (v i) z} {z : Lattice | det (v i) z ≤ β} := by
  intro i
  obtain ⟨β, θ, hθ, ha⟩ := all_lower_tails F U v g c hfixed hpos hpair hndp hU hupper
    S hSne hS hlow i
  refine ⟨min β (c i - 1), θ, by omega, hθ, ?_, ?_⟩
  · intro z hz
    exact ha z (hz.trans (min_le_left _ _))
  · apply Set.disjoint_left.mpr
    intro z hu hl
    change c i ≤ det (v i) z at hu
    change det (v i) z ≤ min β (c i - 1) at hl
    omega

/-- Agreement with a doubly periodic lower tail gives two independent
periods that both preserve the actual lower half-plane. -/
theorem lower_tail_fully_periodic (f θ : Lattice → A) (v g : Lattice) (β : ℤ)
    (hfixed : IsPeriod f v) (hg : 0 < det v g) (hθ : IsDoublyPeriodic θ)
    (ha : ∀ z, det v z ≤ β → f z = θ z) :
    ∃ ell : Lattice, det v ell < 0 ∧
      PeriodicOn f {z : Lattice | det v z ≤ β} v ∧
      PeriodicOn f {z : Lattice | det v z ≤ β} ell ∧ det v ell ≠ 0 := by
  obtain ⟨M, hM, hpM⟩ := direction_period_of_finite_orbit θ (-g)
    (finite_orbit_of_doublyPeriodic θ hθ)
  have hd : det v (M • (-g)) < 0 := by
    rw [det_nsmul_right, det_neg_right]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hM) (neg_neg_of_pos hg)
  have hpres : ∀ z : Lattice, det v z ≤ β → det v (z + M • (-g)) ≤ β := by
    intro z hz
    rw [det_add_right]
    omega
  refine ⟨M • (-g), hd, ?_, ⟨hpres, ?_⟩, ne_of_lt hd⟩
  · constructor
    · intro z hz
      change det v z ≤ β at hz
      change det v (z + v) ≤ β
      simpa only [det_add_right, det_self, add_zero] using hz
    · intro z _
      exact hfixed z
  · intro z hz
    exact (ha (z + M • (-g)) (hpres z hz)).trans ((hpM z).trans (ha z hz).symm)

end
end NivatTrial.SecondHalfPlane
