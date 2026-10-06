import NivatTrial.ColleEnvelopeRays
import NivatTrial.ColleOrbitCofactor
import NivatTrial.ColleHalfPlanePeriod

/-! Take an actual directional orbit limit along an infinite boundary.
An eventual regional period becomes a half-plane period of the limit, and
the finite integer decomposition extends it to a global period. -/

namespace NivatTrial.ColleBoundaryLimits

open NivatTrial.Geometry NivatTrial.Zonotope NivatTrial.Dynamics
open NivatTrial.Periodicity NivatTrial.NonexpansiveExistence
open NivatTrial.ColleOrbitCofactor NivatTrial.ColleHalfPlanePeriod
open NivatTrial.ExternalInputs NivatTrial.Nonexpansive
open Filter
open scoped Classical
noncomputable section

theorem exists_directional_limit_with_halfPlane_period {A : Type*} [Fintype A]
    (x : Lattice → A) (q a : Lattice) (b : ℤ)
    (hperiod : ∀ z, b ≤ det q z →
      ∀ᶠ n : ℕ in atTop, x (z+n•q+a) = x (z+n•q)) :
    ∃ y : Lattice → A, DirectionOrbitHull x y q ∧
      ∀ z, b ≤ det q z → y (z+a) = y z := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hx (n : ℕ) : shift (n•q) x ∈ languageHull x :=
    shift_mem_languageHull (self_mem_languageHull x) _
  obtain ⟨y,_,φ,hφ,hlim⟩ := (isCompact_languageHull x).tendsto_subseq hx
  refine ⟨y,?_,?_⟩
  · intro S
    have hevent : ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, shift ((φ n)•q) x z = y z :=
      S.eventually_all.mpr (fun z _ => eventually_coordinate_eq hlim z)
    obtain ⟨n,hn⟩ := hevent.exists
    exact ⟨φ n,by simpa only [shift_apply,natCast_zsmul] using hn⟩
  · intro z hz
    have hp := hφ.tendsto_atTop.eventually (hperiod z hz)
    obtain ⟨n,hpn,he₁,he₂⟩ := (hp.and
      ((eventually_coordinate_eq hlim (z+a)).and (eventually_coordinate_eq hlim z))).exists
    rw [← he₁,← he₂]
    simpa only [Function.comp_apply,shift_apply,add_assoc,add_comm,add_left_comm] using hpn

theorem exists_directional_limit_of_regional_period {A : Type*} [Fintype A]
    (x : Lattice → A) (R : Set Lattice) (q a : Lattice) (b : ℤ)
    (hregion : ∀ z ∈ R, x (z+a) = x z)
    (hfill : ∀ z, b ≤ det q z → ∀ᶠ n : ℕ in atTop, z+n•q ∈ R) :
    ∃ y : Lattice → A, DirectionOrbitHull x y q ∧
      ∀ z, b ≤ det q z → y (z+a) = y z := by
  apply exists_directional_limit_with_halfPlane_period x q a b
  intro z hz
  filter_upwards [hfill z hz] with n hn
  exact hregion (z+n•q) hn

theorem global_period_of_integer_hull_halfPlane_period
    {M m : ℕ} {x y : Lattice → Fin M}
    (D : IntegerDecomposition (integerField x) m)
    (hy : y ∈ languageHull x) (q : Lattice) (hq : q ≠ 0)
    (a : Lattice) (ha : det q a = 0) (b : ℤ)
    (hperiod : ∀ z, b ≤ det q z → y (z+a) = y z) :
    ∃ Q : ℕ, 0 < Q ∧ IsPeriod y (Q•a) := by
  obtain ⟨E⟩ := decomposition_in_languageHull D hy
  have hv : embed q ≠ 0 := by
    intro he
    exact hq (embed_injective (he.trans embed_zero.symm))
  have hscore (z : Lattice) : score (embed q) z = (det q z : ℝ) := by
    simp [score,embed,det]
  have htan : score (embed q) a = 0 := by rw [hscore,ha,Int.cast_zero]
  have hregional : ∀ z, (b:ℝ) ≤ score (embed q) z →
      (∑ i, E.component i) (z+a) = (∑ i, E.component i) z := by
    intro z hz
    rw [hscore] at hz
    have hz' : b ≤ det q z := by exact_mod_cast hz
    rw [E.sum_eq]
    exact congrArg integerCode (hperiod z hz')
  obtain ⟨Q,hQ,hper⟩ := halfPlane_period_extends_of_tangent E.component E.period
    E.component_period E.period_ne_zero (embed q) hv a htan b hregional
  refine ⟨Q,hQ,?_⟩
  intro z
  apply integerCode_injective M
  rw [E.sum_eq] at hper
  exact hper z

theorem exists_periodic_directional_limit
    {M m : ℕ} (x : Lattice → Fin M)
    (D : IntegerDecomposition (integerField x) m)
    (q a : Lattice) (hq : q ≠ 0) (ha : a ≠ 0) (hqa : det q a = 0)
    (b : ℤ) (hperiod : ∀ z, b ≤ det q z →
      ∀ᶠ n : ℕ in atTop, x (z+n•q+a) = x (z+n•q)) :
    ∃ y : Lattice → Fin M, DirectionOrbitHull x y q ∧ IsPeriodic y ∧
      ∃ Q : ℕ, 0 < Q ∧ IsPeriod y (Q•a) := by
  obtain ⟨y,hy,hyp⟩ := exists_directional_limit_with_halfPlane_period x q a b hperiod
  obtain ⟨Q,hQ,hper⟩ := global_period_of_integer_hull_halfPlane_period D
    (directionOrbitHull_mem_languageHull hy) q hq a hqa b hyp
  have hQa : Q•a ≠ 0 := fun he => ha ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hQ)).mp he)
  exact ⟨y,hy,⟨Q•a,hQa,hper⟩,Q,hQ,hper⟩

end
end NivatTrial.ColleBoundaryLimits
