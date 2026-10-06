import NivatTrial.HalfPlaneLimit
import NivatTrial.PeriodicDifference
import NivatTrial.TwoComponent

/-! Safe translations and the two-component limits of Proposition 8.14. -/

namespace NivatTrial.TwoComponentLimits

open Set Filter Topology
open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.Dynamics
open NivatTrial.PeriodicDifference NivatTrial.LatticePolygon
open scoped Classical

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]

theorem safe_tail_tendsto (f θ : Lattice → A) (π : Lattice →+ ℤ)
    (c : ℤ) (d : Lattice) (hd : 0 < π d) (hperiod : IsPeriod θ d)
    (hagrees : ∀ z, c ≤ π z → f z = θ z) :
    Tendsto (fun n : ℕ => shift (n • d) f) atTop (𝓝 θ) := by
  apply tendsto_pi_nhds.mpr
  intro z
  obtain ⟨N, hN⟩ := positive_direction_enters_halfplane π c d hd z
  have heq : ∀ᶠ n : ℕ in atTop, shift (n • d) f z = θ z := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have ha := hagrees (z + n • d) (hN n hn)
    simpa only [shift, add_comm] using ha.trans (hperiod.nsmul n z)
  exact tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm))

theorem orbitClosure_of_shift_tendsto (f y : Lattice → A) (a : ℕ → Lattice)
    (hlim : Tendsto (fun n => shift (a n) f) atTop (𝓝 y)) : y ∈ orbitClosure f := by
  apply (isClosed_orbitClosure f).mem_of_tendsto hlim
  exact Eventually.of_forall (fun n => orbit_subset_orbitClosure f (shift_mem_orbit f (a n)))

theorem period_of_shift_limit (f y : Lattice → A) (a : ℕ → Lattice)
    (hlim : Tendsto (fun n => shift (a n) f) atTop (𝓝 y)) (h : Lattice)
    (hp : IsPeriod f h) : IsPeriod y h :=
  hp.orbitClosure (orbitClosure_of_shift_tendsto f y a hlim)

section FiniteGroup

variable [AddCommGroup A] [Fintype A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def otherIndices (b c : ι) : Finset ι := (Finset.univ.erase b).erase c

@[simp] theorem mem_otherIndices (b c j : ι) :
    j ∈ otherIndices b c ↔ j ≠ b ∧ j ≠ c := by
  simp [otherIndices, and_comm]

def cofactorSum (F : ι → Lattice → A) (b c : ι) : Lattice → A :=
  ∑ j ∈ otherIndices b c, F j

theorem sum_decomposition (F : ι → Lattice → A) (b c : ι) (hbc : b ≠ c) :
    (∑ j, F j) = F c + cofactorSum F b c + F b := by
  have hfirst := Finset.add_sum_erase Finset.univ F (Finset.mem_univ b)
  have hsecond := Finset.add_sum_erase (Finset.univ.erase b) F
    (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_univ c⟩)
  rw [← hfirst, ← hsecond]
  change F b + (F c + cofactorSum F b c) = F c + cofactorSum F b c + F b
  abel

theorem doublyPeriodic_cofactorSum (B : ι → Lattice → A) (b c : ι)
    (hB : ∀ j, j ≠ b → j ≠ c → IsDoublyPeriodic (B j)) :
    IsDoublyPeriodic (cofactorSum B b c) := by
  have hp : ∀ j : otherIndices b c, IsDoublyPeriodic (B j) := by
    intro j
    obtain ⟨hjb, hjc⟩ := (mem_otherIndices b c j).mp j.property
    exact hB j hjb hjc
  simpa only [cofactorSum, Finset.sum_coe_sort] using
    doublyPeriodic_sum (fun j : otherIndices b c => B j) hp

theorem cofactorSum_tendsto (F B : ι → Lattice → A) (b c : ι)
    (a : ℕ → Lattice)
    (hlim : ∀ j, j ≠ b → j ≠ c →
      Tendsto (fun n => shift (a n) (F j)) atTop (𝓝 (B j))) :
    Tendsto (fun n => cofactorSum (fun j => shift (a n) (F j)) b c)
      atTop (𝓝 (cofactorSum B b c)) := by
  apply tendsto_finsetSum
  intro j hj
  obtain ⟨hjb, hjc⟩ := (mem_otherIndices b c j).mp hj
  exact hlim j hjb hjc

/-- Proposition 8.14 after the safe tail limits have been selected. The
low-complexity hypothesis is transferred to the actual limiting sum. -/
theorem doublyPeriodic_two_component_limit (F B : ι → Lattice → A)
    (v : ι → Lattice) (b c : ι) (hbc : b ≠ c) (d : Lattice)
    (hfixed : ∀ j, IsPeriod (F j) (v j))
    (hdet : det (v c) (v b) ≠ 0) (hnc : ¬IsDoublyPeriodic (F c))
    (hfixc : IsPeriod (F c) d)
    (hB : ∀ j, j ≠ b → j ≠ c → IsDoublyPeriodic (B j))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlimB : ∀ j, j ≠ b → j ≠ c →
      Tendsto (fun n : ℕ => shift (n • d) (F j)) atTop (𝓝 (B j)))
    (y : Lattice → A)
    (hlimy : Tendsto (fun n => shift (φ n • d) (F b)) atTop (𝓝 y))
    (S : Finset Lattice) (hSne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (∑ j, F j) S ≤ S.card) : IsDoublyPeriodic y := by
  let C := cofactorSum B b c
  have hC : IsDoublyPeriodic C := doublyPeriodic_cofactorSum B b c hB
  have hlimC : Tendsto
      (fun n => cofactorSum (fun j => shift (φ n • d) (F j)) b c) atTop (𝓝 C) :=
    cofactorSum_tendsto F B b c (fun n => φ n • d)
      (fun j hjb hjc => (hlimB j hjb hjc).comp hφ.tendsto_atTop)
  have hlimc : Tendsto (fun n => shift (φ n • d) (F c)) atTop (𝓝 (F c)) := by
    have heq : (fun n => shift (φ n • d) (F c)) = fun _ => F c := by
      funext n
      exact (isPeriod_iff_shift (F c) _).mp (hfixc.nsmul (φ n))
    rw [heq]
    exact tendsto_const_nhds
  have hlimtotal : Tendsto (fun n => shift (φ n • d) (∑ j, F j))
      atTop (𝓝 (F c + C + y)) := by
    have h := (hlimc.add hlimC).add hlimy
    apply h.congr'
    filter_upwards [] with n
    rw [← sum_decomposition (fun j => shift (φ n • d) (F j)) b c hbc]
    funext z
    simp [shift]
  have horbit := orbitClosure_of_shift_tendsto (∑ j, F j) (F c + C + y)
    (fun n => φ n • d) hlimtotal
  have hlowlim : patternComplexity (F c + C + y) S ≤ S.card :=
    (patternComplexity_le_of_mem_orbitClosure horbit S).trans hlow
  have hyp := period_of_shift_limit (F b) y (fun n => φ n • d) hlimy (v b) (hfixed b)
  obtain ⟨M, hM, hCp⟩ := direction_period_of_finite_orbit C (v c)
    (finite_orbit_of_doublyPeriodic C hC)
  have hfc : IsPeriod (F c + C) (M • v c) := ((hfixed c).nsmul M).add_config hCp
  have hind : det (M • v c) (v b) ≠ 0 := by
    change det ((M : ℤ) • v c) (v b) ≠ 0
    rw [det_zsmul_left]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hM) hdet
  have hnf : ¬IsDoublyPeriodic (F c + C) := by
    intro hf
    apply hnc
    have hsub := doublyPeriodic_sub (F c + C) C hf hC
    simpa only [add_sub_cancel_right] using hsub
  have hsum := TwoComponent.periodic_of_low_convex_complexity (F c + C) y
    (M • v c) (v b) hfc hyp hind S hSne hS hlowlim
  exact second_component_doublyPeriodic (F c + C) y (M • v c) (v b)
    hfc hyp hind hnf hsum

theorem doublyPeriodic_two_component_cluster (F B : ι → Lattice → A)
    (v : ι → Lattice) (b c : ι) (hbc : b ≠ c) (d : Lattice)
    (hfixed : ∀ j, IsPeriod (F j) (v j)) (hdet : det (v c) (v b) ≠ 0)
    (hnc : ¬IsDoublyPeriodic (F c)) (hfixc : IsPeriod (F c) d)
    (hB : ∀ j, j ≠ b → j ≠ c → IsDoublyPeriodic (B j))
    (hlimB : ∀ j, j ≠ b → j ≠ c →
      Tendsto (fun n : ℕ => shift (n • d) (F j)) atTop (𝓝 (B j)))
    (S : Finset Lattice) (hSne : S.Nonempty) (hS : IsLatticeConvex S)
    (hlow : patternComplexity (∑ j, F j) S ≤ S.card)
    (y : Lattice → A) (hy : MapClusterPt y atTop (fun n : ℕ => shift (n • d) (F b))) :
    IsDoublyPeriodic y := by
  obtain ⟨φ, hφ, hlimy⟩ := hy.tendsto_subseq
  exact doublyPeriodic_two_component_limit F B v b c hbc d hfixed hdet hnc hfixc
    hB φ hφ hlimB y hlimy S hSne hS hlow

end FiniteGroup
end NivatTrial.TwoComponentLimits
