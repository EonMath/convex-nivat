import NivatTrial.ColleAmbiguousRepeat

/-! A repeat of a full window fixes the phase of the already periodic
inner strip. This is the elementary phase-alignment step in the
nonunique-extension branch. -/

namespace NivatTrial.ColleStripPeriod

open NivatTrial.Periodicity NivatTrial.MorseHedlund
open scoped Classical

noncomputable section

variable {A : Type*}

theorem periodic_sequences_eq_of_block
    (ξ ζ : ℤ → A) (p : ℕ) (hp : 0 < p)
    (hξ : IsPeriod ξ (p : ℤ)) (hζ : IsPeriod ζ (p : ℤ))
    (l : ℤ)
    (hblock : ∀ r : ℤ, 0 ≤ r → r < p → ξ (l+r) = ζ (l+r)) :
    ξ = ζ := by
  funext z
  let r := (z-l) % (p:ℤ)
  have hpos : (0:ℤ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hpos)
  have hrp : r < (p:ℤ) := Int.emod_lt_of_pos _ hpos
  have hdiff : z - (l+r) = ((z-l)/(p:ℤ)) * (p:ℤ) := by
    dsimp [r]
    nlinarith [Int.emod_add_mul_ediv (z-l) (p:ℤ)]
  have hξdiff : IsPeriod ξ (z-(l+r)) := by
    simpa [hdiff, zsmul_eq_mul] using hξ.zsmul ((z-l)/(p:ℤ))
  have hζdiff : IsPeriod ζ (z-(l+r)) := by
    simpa [hdiff, zsmul_eq_mul] using hζ.zsmul ((z-l)/(p:ℤ))
  calc
    ξ z = ξ (l+r) := hξdiff.eq_of_sub
    _ = ζ (l+r) := hblock r hr0 hrp
    _ = ζ z := hζdiff.eq_of_sub.symm

theorem period_of_equal_block
    (ξ : ℤ → A) (p : ℕ) (hp : 0 < p)
    (hξ : IsPeriod ξ (p : ℤ)) (l δ : ℤ)
    (hblock : ∀ r : ℤ, 0 ≤ r → r < p →
      ξ (l+r+δ) = ξ (l+r)) :
    IsPeriod ξ δ := by
  have hshift : IsPeriod (fun z => ξ (z+δ)) (p:ℤ) := by
    intro z
    simpa only [add_assoc,add_comm,add_left_comm] using hξ (z+δ)
  have he := periodic_sequences_eq_of_block ξ (fun z => ξ (z+δ))
    p hp hξ hshift l (fun r hr0 hrp => (hblock r hr0 hrp).symm)
  intro z
  exact (congrFun he z).symm

end

end NivatTrial.ColleStripPeriod
