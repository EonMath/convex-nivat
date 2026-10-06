import NivatTrial.CollePeriodicRowPropagation
import NivatTrial.ColleReferencePhaseRepeat

/-! The phase-repeat and generated-row parts of Colle's Claim 4.3. The
remaining geometric seed premise records actual consecutive sites in the
periodic parallel-cell tail; it is separate from the finite-pattern proof. -/

namespace NivatTrial.ColleReferencePropagation

open NivatTrial.Dynamics NivatTrial.Periodicity NivatTrial.BalancedWindows
open NivatTrial.ColleGenerating NivatTrial.ColleLocalSubshift
open NivatTrial.CollePeriodicRowPropagation NivatTrial.ColleReferencePhaseRepeat
open NivatTrial.LatticeCoordinates NivatTrial.RowDetermination
open scoped Classical
noncomputable section

abbrev G := ℤ × ℤ
variable {A : Type*} [Fintype A]

theorem reference_halfPlane_period_of_row_seeds
    (θ : G → A) (B : Finset G) (hB : GeneratingWindow θ B)
    (q : G → A) (hq : q ∈ languageHull θ)
    (P : ℕ) (hP : 0 < P) (hperiod : IsPeriod q (P•horizontal))
    (k : G) (hk : 0 < k.2)
    (hseeds : ∀ N : ℕ, 0 < N → ∃ lo : ℤ, ∀ d : ℤ, lo≤d → ∃ L : ℤ,
      ∀ j : ℤ, L≤j → j<L+((bottomEdge B).card-1 : ℕ) →
        q ((j,d)+(N:ℤ)•k)=q (j,d)) :
    ∃ N : ℕ, 0 < N ∧ ∃ lo : ℤ, ∀ z : G, lo≤z.2 → q (z+(N:ℤ)•k)=q z := by
  let H := upper B-lower B
  obtain ⟨N,hN,_,hrec⟩ := recurrent_periodic_reference_band q P hP hperiod 0 H k hk
  obtain ⟨lo,hseed⟩ := hseeds N hN
  let y := shift ((N:ℤ)•k) q
  have hy : y ∈ languageHull θ := shift_mem_languageHull hq _
  have hhigh : ∀ K : ℤ, ∃ top : ℤ, K≤top ∧
      ∀ z : G, top≤z.2 → z.2≤top+upper B-lower B → q z=y z := by
    intro K
    obtain ⟨R,hR⟩ := exists_nat_gt K
    obtain ⟨r,hr,hm⟩ := hrec R
    have hrR : (R:ℤ)≤r := by exact_mod_cast hr
    have hr0 : (0:ℤ)≤r := by positivity
    refine ⟨(r:ℤ)*k.2,by nlinarith,?_⟩
    intro z hzl hzu
    have hm' := hm z (by change 0≤z.2-(r:ℤ)*k.2; omega)
      (by change z.2-(r:ℤ)*k.2≤H; dsimp [H]; omega)
    simpa only [y,shift_apply,add_comm] using hm'.symm
  have hrow : ∀ d : ℤ, lo≤d → ∃ L : ℤ,
      ∀ j : ℤ, L≤j → j<L+((bottomEdge B).card-1 : ℕ) → q (j,d)=y (j,d) := by
    intro d hd
    obtain ⟨L,hL⟩ := hseed d hd
    refine ⟨L,?_⟩
    intro j hjL hjU
    simpa only [y,shift_apply,add_comm] using (hL j hjL hjU).symm
  have hall := agree_on_halfPlane_of_arbitrarily_high_bands θ B hB
    (localAdmissible_of_hull hq) (localAdmissible_of_hull hy) lo hhigh hrow
  exact ⟨N,hN,lo,fun z hz => by simpa only [y,shift_apply,add_comm] using (hall z hz).symm⟩

end
end NivatTrial.ColleReferencePropagation
