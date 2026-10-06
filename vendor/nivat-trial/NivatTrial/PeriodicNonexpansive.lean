import NivatTrial.FiniteIncrementFibers
import NivatTrial.RealDirectionGeometry

/-! A singly periodic finite-alphabet field has both orientations of its
period line nonexpansive. If one orientation determined the other side,
the uniform difference-fiber bound would make its entire hull finite. -/

namespace NivatTrial.PeriodicNonexpansive

open NivatTrial.Dynamics NivatTrial.Nonexpansive NivatTrial.Periodicity
open NivatTrial.PeriodicDifference NivatTrial.FiniteIncrementFibers
open NivatTrial.RealDirectionGeometry NivatTrial.Zonotope
open scoped Classical
noncomputable section

abbrev Plane := ℝ × ℝ

variable {A : Type*}

theorem period_passes_to_languageHull {θ x : Lattice → A} {h : Lattice}
    (hp : IsPeriod θ h) (hx : x ∈ languageHull θ) : IsPeriod x h := by
  intro z
  obtain ⟨u,hu⟩ := hx {z,z+h}
  calc
    x (z+h) = θ (u+(z+h)) := (hu _ (by simp)).symm
    _ = θ (u+z) := by simpa [add_assoc] using hp (u+z)
    _ = x z := hu _ (by simp)

theorem increment_zero_in_hull {θ x : Lattice → A} {h : Lattice}
    (w : A → ℤ) (hp : IsPeriod θ h) (hx : x ∈ languageHull θ) :
    increment (encode w x) h = 0 := by
  funext z
  simp [increment, encode, period_passes_to_languageHull hp hx z]

theorem doublyPeriodic_of_period_and_oneSidedExpansive [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (h : Lattice) (hh : h ≠ 0) (hp : IsPeriod θ h)
    (v : Plane) (hv : v ≠ 0) (hvh : score v h = 0)
    (hexp : OneSidedExpansive θ v) : IsDoublyPeriodic θ := by
  obtain ⟨d,hd⟩ := exists_positive_score hv
  have hind := independent_of_score v h d hh hvh (ne_of_gt hd)
  obtain ⟨N,hN⟩ := exists_uniform_fiber_bound θ w hw v hv hexp h d hind hvh hd
  apply doublyPeriodic_of_finite_orbit
  apply Set.Finite.subset (s := languageHull θ) _ (orbit_subset_languageHull θ)
  by_contra hi
  have hInfinite : (languageHull θ).Infinite := hi
  let e : ℕ ↪ languageHull θ := hInfinite.natEmbedding _
  let F : Fin (N+1) → Lattice → A := fun i => (e i.val).val
  have hF (i : Fin (N+1)) : F i ∈ languageHull θ := (e i.val).property
  have hFinj : Function.Injective F := by
    intro i j hij
    apply Fin.ext
    apply e.injective
    exact Subtype.ext hij
  have hinc (i j : Fin (N+1)) :
      increment (encode w (F i)) h = increment (encode w (F j)) h := by
    rw [increment_zero_in_hull w hp (hF i),increment_zero_in_hull w hp (hF j)]
  have := hN (N+1) F hF hFinj hinc
  omega

theorem opposite_nonexpansive_of_period [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (h : Lattice) (hh : h ≠ 0) (hp : IsPeriod θ h)
    (v : Plane) (hv : v ≠ 0) (hvh : score v h = 0)
    (hnot : ¬IsDoublyPeriodic θ) :
    OneSidedNonexpansive θ v ∧ OneSidedNonexpansive θ (-v) := by
  constructor
  · by_contra hn
    exact hnot (doublyPeriodic_of_period_and_oneSidedExpansive θ w hw h hh hp v hv hvh hn)
  · by_contra hn
    exact hnot (doublyPeriodic_of_period_and_oneSidedExpansive θ w hw h hh hp
      (-v) (neg_ne_zero.mpr hv) (by rw [score_neg_direction,hvh,neg_zero]) hn)

theorem exists_opposite_nonexpansive_of_singlyPeriodic [Fintype A]
    (θ : Lattice → A) (hp : IsPeriodic θ) (hnot : ¬IsDoublyPeriodic θ) :
    ∃ v : Plane, v ≠ 0 ∧ OneSidedNonexpansive θ v ∧ OneSidedNonexpansive θ (-v) := by
  let w : A → ℤ := fun a => (Fintype.equivFin A a).val
  have hw : Function.Injective w := by
    intro a b hab
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    dsimp [w] at hab
    exact_mod_cast hab
  obtain ⟨h,hh,hper⟩ := hp
  have hv : embed h ≠ 0 := by
    intro he
    apply hh
    apply Prod.ext
    · have := congrArg Prod.fst he
      simpa [embed] using this
    · have := congrArg Prod.snd he
      simpa [embed] using this
  refine ⟨embed h,hv,opposite_nonexpansive_of_period θ w hw h hh hper (embed h) hv ?_ hnot⟩
  simp [score,embed]
  ring

end
end NivatTrial.PeriodicNonexpansive
