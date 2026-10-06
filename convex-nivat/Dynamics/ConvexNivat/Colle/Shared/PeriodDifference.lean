import ConvexNivat.Colle.Shared.Definitions

namespace ConvexNivat.Colle
noncomputable section

theorem periodDifference_finite_alphabet (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (h : Lattice) :
    ∃ B : Finset ℤ, ∀ z, periodDifference ξ h z ∈ B := by
  classical
  refine ⟨(A.product A).image (fun p => p.1-p.2), ?_⟩
  intro z
  exact Finset.mem_image.mpr ⟨(ξ (z-h),ξ z),
    Finset.mem_product.mpr ⟨hA _,hA _⟩,rfl⟩


theorem periodDifference_zero_on_invariant_agreement (θ xper : Configuration ℤ)
    (U : Set Lattice) (h : Lattice) (hinvariant : ForwardInvariant U (-h))
    (hperiod : HasPeriod xper h) (hagrees : AgreesOn θ xper U) :
    AgreesOn (periodDifference θ h) (fun _ => 0) U := by
  intro z hz
  have hzh : z-h ∈ U := by simpa only [sub_eq_add_neg] using hinvariant z hz
  change θ (z-h) - θ z = 0
  rw [hagrees (z-h) hzh,hagrees z hz]
  have hp := hperiod (z-h)
  rw [sub_add_cancel] at hp
  exact sub_eq_zero.mpr hp.symm


end
end ConvexNivat.Colle
